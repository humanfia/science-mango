"""Humanize adapter for the retrieval → Lean proof → repair → kernel-check loop."""
import asyncio
import json
from pathlib import Path
from typing import Annotated, NamedTuple

from hmz.flows import Agent, AgentDefaults, flow
from pydantic import BaseModel, Field

if __package__:
    from .engine import Draft, Spec, run, save
else:
    from quantum_formalize.engine import Draft, Spec, run, save


class Agents(NamedTuple):
    prover: Annotated[Agent, AgentDefaults(goals=False)]


class Config(BaseModel):
    model_config = {'extra': 'forbid', 'frozen': True}
    project: str = Field(description='Existing Lean project whose imports and source are bound to this run')
    result_path: str = Field(description='Controller-owned final result receipt path')
    spec: str = Field(description='Frozen JSON declaration specification; the worker cannot change its target')
    max_rounds: int = Field(default=5, ge=1, le=20, description='Maximum proof attempts, including compiler repair attempts')
    compile_timeout: int = Field(default=180, ge=1, le=3600, description='Timeout in seconds for each build or Lean compiler process')
    turn_timeout: int = Field(default=600, ge=1, le=3600, description='Timeout in seconds for each proof worker turn')


@flow
async def formalize(agents: Agents, task: str, config: Config | None = None) -> None:
    if config is None:
        raise ValueError('formalization requires an explicit project and frozen spec config')
    spec = Spec.model_validate_json(Path(config.spec).read_bytes())

    async def propose(prompt, attempt):
        worker = agents.prover.clone(name=attempt.name, skills=[])
        session = worker.new(attempt)
        session.loads([])
        turn = asyncio.create_task(session.aturn(prompt, schema=Draft))
        try:
            return await asyncio.wait_for(turn, timeout=config.turn_timeout)
        finally:
            try:
                session.close()
            finally:
                worker.stop()
            if not turn.done():
                turn.cancel()
            await asyncio.gather(turn, return_exceptions=True)

    result = await run(spec, config.project, propose, max_rounds=config.max_rounds,
                       timeout=config.compile_timeout)
    save(Path(config.result_path), result)
    print(json.dumps(result, ensure_ascii=False, indent=2))
