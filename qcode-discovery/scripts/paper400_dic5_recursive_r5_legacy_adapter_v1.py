#!/usr/bin/env python3
"""Bind recursive split operations to an exact r5 legacy root.

The frozen recursive v1 supervisor deliberately replays a legacy leaf through
the source tree that created its static record.  r4 and r5 have identical
runner bytes, but their static records bind absolute controller/coordinator
paths, so substituting the r4 path for an r5 root must fail closed.

This adapter is intentionally separate from the frozen v1 source: existing
r4 bundles bind that source by hash.  It temporarily selects the exact r5
legacy runner and adds this adapter's own source binding.  Callers must use
this adapter for every legacy-facing phase of an r5 recursive bundle.
"""

from __future__ import annotations

import contextlib
import hashlib
import os
import sys
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from scripts import paper400_dic5_recursive_split_supervisor_v1 as supervisor


R5_PROJECT = Path("/home/jing/science-mango-r5/qcode-discovery")
R5_RUNNER = R5_PROJECT / "scripts/run_paper400_dic5_nested_width10_child_resume_proof_v1.py"
R5_CONTROLLER = R5_PROJECT / "scripts/run_cadical_dmtcp_resume_v1.py"
R5_COORDINATOR = R5_PROJECT / "scripts/run_paper400_dic5_nested_width10_four_lane_v1.py"
R5_CONTROLLER_SHA256 = "9e57ea9b99a4b041c73a97939f997671790b77b6cb5c7b3d7fe04e1d925f47d2"
R5_COORDINATOR_SHA256 = "595fc59c65ab7d5b2de628b4c6d55d5adfc110d28386a811a235c847db57b60d"


class R5LegacyAdapterError(RuntimeError):
    """An r5 root cannot be safely dispatched through the adapter."""


_ORIGINAL_LEGACY_PROJECT = supervisor.LEGACY_PROJECT
_ORIGINAL_LEGACY_RUNNER = supervisor.LEGACY_RUNNER
_ORIGINAL_SOURCE_BINDING = supervisor._legacy_source_binding
_ORIGINAL_AUDIT_PARENT = supervisor.audit_parent


def _file_binding(path: Path) -> dict[str, Any]:
    target = Path(path).resolve(strict=True)
    payload = supervisor._stable_bytes(target, cap=32 << 20, executable=False)
    return {
        "path": str(target),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


def adapter_source_binding() -> dict[str, Any]:
    """Return the exact code binding for the r5 selection layer."""

    return {
        "method": "exact-source-sha256-replay-v1",
        "r5_legacy_adapter": _file_binding(Path(__file__)),
    }


def _validate_r5_runner() -> None:
    try:
        payload = supervisor._stable_bytes(R5_RUNNER, cap=32 << 20, executable=False)
        controller = supervisor._stable_bytes(R5_CONTROLLER, cap=32 << 20, executable=False)
        coordinator = supervisor._stable_bytes(R5_COORDINATOR, cap=32 << 20, executable=False)
    except supervisor.RecursiveSplitSupervisorError as exc:
        raise R5LegacyAdapterError("r5 legacy source is unavailable") from exc
    if hashlib.sha256(payload).hexdigest() != supervisor.LEGACY_RUNNER_SHA256:
        raise R5LegacyAdapterError("r5 legacy runner hash does not match the frozen runner")
    if hashlib.sha256(controller).hexdigest() != R5_CONTROLLER_SHA256:
        raise R5LegacyAdapterError("r5 DMTCP controller hash is unexpected")
    if hashlib.sha256(coordinator).hexdigest() != R5_COORDINATOR_SHA256:
        raise R5LegacyAdapterError("r5 four-lane coordinator hash is unexpected")


def validate_r5_static_root(root: Path | str) -> None:
    """Require the absolute r5 tool paths that make r5 replay necessary."""

    target = supervisor._safe_directory(Path(root), require_mode_0700=True)
    record = supervisor._read_json(target / "state/00-resume-static.json")
    tools = record.get("toolchain_binding", {}).get("tools")
    if type(tools) is not dict:
        raise R5LegacyAdapterError("legacy static record has no toolchain binding")
    expected = {
        "dmtcp_controller_source": (R5_CONTROLLER, R5_CONTROLLER_SHA256),
        "four_lane_coordinator_source": (R5_COORDINATOR, R5_COORDINATOR_SHA256),
    }
    for role, (path, digest) in expected.items():
        value = tools.get(role)
        if (
            type(value) is not dict
            or value.get("path") != str(path)
            or value.get("sha256") != digest
        ):
            raise R5LegacyAdapterError(
                f"legacy static record is not bound to the exact r5 {role}"
            )


def _r5_legacy_source_binding() -> dict[str, Any]:
    """Extend v1's source binding after it has selected the r5 runner."""

    if supervisor.LEGACY_RUNNER != R5_RUNNER:
        raise R5LegacyAdapterError("r5 adapter source binding used outside r5 context")
    base = _ORIGINAL_SOURCE_BINDING()
    sources = dict(base.get("sources", {}))
    sources["r5_legacy_adapter"] = adapter_source_binding()["r5_legacy_adapter"]
    return {
        "method": "exact-source-sha256-replay-v1",
        "sources": sources,
        "source_sequence_sha256": supervisor.recursive.canonical_sha256(sources),
    }


@contextlib.contextmanager
def r5_legacy_context() -> Iterator[None]:
    """Temporarily configure the frozen supervisor for exact r5 replay.

    Each command is executed in its own Python process in production.  The
    restoration still matters for tests and for callers that compose several
    adapter operations in one process.
    """

    _validate_r5_runner()
    saved = (
        supervisor.LEGACY_PROJECT,
        supervisor.LEGACY_RUNNER,
        supervisor._legacy_source_binding,
        supervisor.audit_parent,
    )

    def audited_r5_parent(root: Path, *, fanout: int) -> tuple[dict[str, Any], dict[str, Any]]:
        validate_r5_static_root(root)
        return _ORIGINAL_AUDIT_PARENT(root, fanout=fanout)

    supervisor.LEGACY_PROJECT = R5_PROJECT
    supervisor.LEGACY_RUNNER = R5_RUNNER
    supervisor._legacy_source_binding = _r5_legacy_source_binding
    supervisor.audit_parent = audited_r5_parent
    try:
        yield
    finally:
        (
            supervisor.LEGACY_PROJECT,
            supervisor.LEGACY_RUNNER,
            supervisor._legacy_source_binding,
            supervisor.audit_parent,
        ) = saved


def main(argv: Sequence[str] | None = None) -> int:
    """Run the frozen supervisor with r5 root selection installed."""

    with r5_legacy_context():
        return supervisor.main(argv)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        R5LegacyAdapterError,
        supervisor.RecursiveSplitSupervisorError,
        supervisor.recursive.RecursiveSplitError,
        supervisor.child_runner.RecursiveChildRunnerError,
        OSError,
        TypeError,
        ValueError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
