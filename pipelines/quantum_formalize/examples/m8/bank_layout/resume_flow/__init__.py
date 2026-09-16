"""Humanize flow: dependency-aware Lean experiments with at most 16 workers."""
import asyncio
import json
from pathlib import Path
from typing import Annotated, NamedTuple

from hmz.flows import Agent, AgentDefaults, flow
from pydantic import BaseModel, Field
from pipelines.quantum_formalize.engine import Draft, save
from pipelines.quantum_formalize.dag_runner import run_graph
from pipelines.quantum_formalize.search import search_with_fallback


class Agents(NamedTuple):
    prover: Annotated[Agent, AgentDefaults(goals=False)]


class Config(BaseModel):
    model_config = {'extra': 'forbid', 'frozen': True}
    project: str = Field(description='Frozen shared Lean project')
    graph: str = Field(description='Controller-owned frozen dependency graph JSON')
    output: str = Field(description='Fresh experiment output directory')
    result_path: str = Field(description='Final experiment receipt file')
    concurrency: int = Field(default=16, ge=1, le=16, description='Maximum simultaneously active proof nodes')
    rounds: int = Field(default=5, ge=1, le=20, description='Proof and repair attempts per node')
    compile_timeout: int = Field(default=180, ge=1, le=3600, description='Seconds per Lean compiler invocation')
    turn_timeout: int = Field(default=600, ge=1, le=3600, description='Seconds per model turn')
    seed_proofs: dict = Field(default_factory=dict, description='Frozen candidate tactic bodies replayed only through normal first-attempt acceptance')


@flow
async def formalize_dag(agents: Agents, task: str, config: Config | None = None) -> None:
    if config is None:
        raise ValueError('explicit DAG config required')

    async def propose(node, prompt, attempt):
        if attempt.name == "attempt-001" and node.id in config.seed_proofs:
            return Draft.model_validate(config.seed_proofs[node.id])
        worker = agents.prover.clone(name=f'{node.id}-{attempt.name}', skills=[])
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

    result = await run_graph(config.graph, config.project, config.output, propose,
                             concurrency=config.concurrency, rounds=config.rounds,
                             timeout=config.compile_timeout, search=lambda queries: search_with_fallback(queries, fallback_queries=["algebra"]))
    save(Path(config.result_path), result)
    print(json.dumps(result, ensure_ascii=False, indent=2))
