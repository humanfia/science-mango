"""User-facing commands for controlled shared-infrastructure admission."""

from __future__ import annotations

from pathlib import Path
from typing import Optional

import typer

from archon import log
from archon.commands.loop.shared_infrastructure import PROJECT_LOCAL_KIND
from archon.commands.loop.shared_infrastructure_admission import (
    SharedInfrastructureAdmissionError,
    admit_explicit_user_architecture_request,
)
from archon.state import next_iter_num


app = typer.Typer(
    name="shared-infrastructure",
    help=(
        "Admit explicit user-authorized project-local shared Lean modules. "
        "Run while the Archon loop is stopped; this command never installs "
        "external dependencies."
    ),
    no_args_is_help=True,
)


@app.command("request")
def request_shared_infrastructure(
    project_path: str = typer.Argument(".", help="Path to the Archon project"),
    module: str = typer.Option(
        ...,
        "--module",
        help="Project-relative .lean module below an allowlisted module root",
    ),
    declarations: list[str] = typer.Option(
        ...,
        "--declaration",
        "-d",
        help="Required fully qualified Lean declaration; repeat as needed",
    ),
    consumers: list[str] = typer.Option(
        ...,
        "--consumer",
        "-c",
        help="Existing project-relative .lean consumer; repeat as needed",
    ),
    reason: str = typer.Option(
        ...,
        "--reason",
        help="Why these targets require one cross-target module",
    ),
    evidence: str = typer.Option(
        "",
        "--evidence",
        help="Optional supporting source, Review, or duplication evidence",
    ),
    iteration: Optional[int] = typer.Option(
        None,
        "--iteration",
        min=1,
        help="Audit iteration; defaults to the next loop iteration",
    ),
) -> None:
    """Queue one project-local module for all named consumers.

    Run this administrative state transition only while the loop is stopped.
    The loop remains responsible for scaffolding, proof completion, axiom
    checking, consumer migration, full builds, and reopening the consumers.
    """
    project = Path(project_path).resolve()
    state_dir = project / ".archon"
    if not state_dir.is_dir():
        log.error(f"Not an Archon project: {project}")
        raise typer.Exit(1)
    iter_num = iteration or next_iter_num(state_dir / "logs")
    try:
        result = admit_explicit_user_architecture_request(
            state_dir=state_dir,
            project_path=project,
            raw_request={
                "kind": PROJECT_LOCAL_KIND,
                "module": module,
                "declarations": declarations,
            },
            consumers=consumers,
            reason=reason,
            evidence=evidence,
            iter_num=iter_num,
        )
    except SharedInfrastructureAdmissionError as exc:
        log.error(f"Shared-infrastructure request rejected: {exc}")
        raise typer.Exit(1) from exc

    log.header("archon shared-infrastructure request")
    log.success(
        f"Queued {result.request['module']} for "
        f"{len(result.consumers)} consumer(s)"
    )
    for consumer in result.consumers:
        log.step(consumer)
    if result.transitioned_from_solved:
        log.info(
            "Moved solved consumer(s) into audited infrastructure quarantine: "
            + ", ".join(result.transitioned_from_solved)
        )
    log.step(
        "Resume `archon loop`; the normal scaffold/build/axiom/migration "
        "gates will process this request."
    )
