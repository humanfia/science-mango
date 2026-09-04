#!/usr/bin/env python3
"""Fail-closed session sealing for one frozen recursive-child start schema.

The immutable v1 recursive child runner intentionally remains untouched: its
child static records bind the runner source byte-for-byte.  The frozen DMTCP
controller used by this campaign records the configuration binding through
its ``start.claim`` (``init_manifest_sha256``) and links that claim from
``start.commit``.  The v1 runner incorrectly expects the configuration hash
directly in the commit.  A process can therefore be fully live, bound,
CPU-pinned, and resource-limited but lack the otherwise ordinary
``state/11-session.json`` receipt.

This sidecar never starts, resumes, checkpoints, kills, or deletes a child.
It can only seal that missing receipt after independently checking the exact
generation-zero controller status, PID start tick, singleton affinity,
resource limits, static material, and the newer controller-config binding.
The additional compatibility receipt makes the schema bridge auditable.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
if str(PROJECT) not in sys.path:
    sys.path.insert(0, str(PROJECT))

from investigations import paper400_dic5_recursive_split_v1 as recursive
from scripts import run_paper400_dic5_recursive_child_resume_proof_v1 as child_runner


SCHEMA_VERSION = 1
GATE = "paper400-dic5-recursive-live-session-compat-v1"
RECEIPT_KIND = "paper400-dic5-recursive-live-session-compat-receipt-v1"
COMPAT_RECEIPT = Path("state/07-live-session-compat-v1.json")


class LiveSessionCompatError(RuntimeError):
    """The existing transport cannot be proven safe to seal."""


def _source_binding() -> dict[str, Any]:
    """Bind this sidecar and the frozen sources it bridges."""

    own = Path(__file__).resolve(strict=True)
    sources = {
        "compat": child_runner._file_binding("compat", own, cap=32 << 20, executable=False),
        "recursive_child_runner": child_runner._file_binding(
            "recursive_child_runner", Path(child_runner.__file__).resolve(strict=True),
            cap=32 << 20, executable=False,
        ),
        "dmtcp_controller": child_runner._file_binding(
            "dmtcp_controller", PROJECT / child_runner.CONTROLLER_RELATIVE,
            cap=32 << 20, executable=False,
        ),
    }
    return {
        "method": "exact-source-sha256-replay-v1",
        "sources": sources,
        "source_sequence_sha256": recursive.canonical_sha256(sources),
    }


def _stable_live_start(
    root: Path, loaded: Mapping[str, Any], *, cpu: int,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], str]:
    """Return only an authenticated, still-live v1 generation-zero start."""

    target = child_runner._safe_root(root)
    if type(cpu) is not int or cpu < 0:
        raise LiveSessionCompatError("compatibility CPU is invalid")
    claim = child_runner._read_start_claim(target, loaded)
    if claim.get("expected_single_cpu") != cpu:
        raise LiveSessionCompatError("compatibility CPU differs from immutable start claim")
    config = child_runner._load_expected_controller_config(target)
    runtime = target / child_runner.RUNTIME_ROOT
    with child_runner._clean_controller_environment():
        status = child_runner.controller.inspect(runtime, verify_hashes=True)
    generations = status.get("generations")
    if (
        status.get("root") != str(runtime)
        or status.get("config_manifest_sha256") != config.get("self_sha256")
        or status.get("state") != "RUNNING"
        or not isinstance(generations, list)
        or len(generations) != 1
        or not isinstance(generations[0], dict)
    ):
        raise LiveSessionCompatError("child is not exactly one live generation-zero transport")
    generation = generations[0]
    active = child_runner.controller._active_commit(
        child_runner.controller._generation_dir(runtime, 0), 0,
    )
    controller_claim = child_runner.controller.read_manifest(
        child_runner.controller._generation_dir(runtime, 0) / "start.claim.json",
        expected_kind="start.claim",
    )
    pid = active.get("pid")
    ticks = active.get("proc_start_ticks")
    if (
        generation.get("generation") != 0
        or generation.get("active_kind") != "start.commit"
        or generation.get("active_manifest_sha256") != active.get("self_sha256")
        or generation.get("pid_identity_alive") is not True
        or generation.get("checkpointed") is not False
        or generation.get("poison_claim") is not None
        or generation.get("stale_tail_injected") is not False
        or active.get("kind") != "start.commit"
        or active.get("generation") != 0
        or type(pid) is not int
        or pid <= 0
        or type(ticks) is not int
        or ticks < 0
    ):
        raise LiveSessionCompatError("live start/config binding is malformed")
    direct = active.get("config_manifest_sha256")
    if direct == config.get("self_sha256"):
        config_field = "config_manifest_sha256"
    elif (
        active.get("claim_sha256") == controller_claim.get("self_sha256")
        and controller_claim.get("generation") == 0
        and controller_claim.get("init_manifest_sha256") == config.get("self_sha256")
    ):
        config_field = "start.claim.init_manifest_sha256"
    else:
        raise LiveSessionCompatError("live start/config binding is malformed")
    observation = recursive.observe_proc_cpu_seconds(pid)
    if (
        observation.get("proc_start_ticks") != ticks
        or observation.get("state") not in {"R", "D"}
    ):
        raise LiveSessionCompatError("live start PID identity changed")
    return claim, config, active, controller_claim, config_field


def _receipt_value(
    root: Path, loaded: Mapping[str, Any], *, claim: Mapping[str, Any],
    config: Mapping[str, Any], active: Mapping[str, Any], controller_claim: Mapping[str, Any],
    config_field: str, session: Mapping[str, Any],
) -> dict[str, Any]:
    static = loaded["static"]
    return child_runner.seal(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": RECEIPT_KIND,
            "gate": GATE,
            "root": str(root),
            "root_identity": child_runner._root_identity(root),
            "static_sha256": static["static_sha256"],
            "start_claim_sha256": claim["record_sha256"],
            "controller_config_sha256": config["self_sha256"],
            "controller_start_sha256": active["self_sha256"],
            "controller_start_claim_sha256": controller_claim["self_sha256"],
            "controller_start_config_field": config_field,
            "controller_start_config_sha256": config["self_sha256"],
            "expected_single_cpu": claim["expected_single_cpu"],
            "session_sha256": session["record_sha256"],
            "source_binding": _source_binding(),
        },
        "record_sha256",
    )


def _publish_exact(path: Path, value: Mapping[str, Any], *, label: str) -> None:
    if path.exists() or path.is_symlink():
        existing = child_runner._read_json(path)
        if existing != value:
            raise LiveSessionCompatError(f"existing {label} conflicts with compatibility replay")
        return
    child_runner._publish_json(path, value)


def seal_live_session(root: Path, *, cpu: int) -> dict[str, Any]:
    """Seal a missing session for a live legacy-schema start, or fail closed.

    The method is intentionally narrow.  A stopped, checkpointed, initialized,
    terminal, or PID-reused root is not repaired here; callers must use their
    normal exact recovery path for those states.
    """

    target = child_runner._safe_root(root)
    with child_runner._root_lock(target):
        loaded = child_runner._load_static(target)
        if (target / child_runner.SESSION_COMMIT).exists():
            session = child_runner._load_session(target, loaded)
            if session.get("expected_single_cpu") != cpu:
                raise LiveSessionCompatError("existing session has a different CPU binding")
            return {
                "state": "ALREADY_SESSION_SEALED",
                "session": session,
                "receipt": None,
            }
        if (target / child_runner.FINAL_COMMIT).exists() or (target / child_runner.TERMINAL_CLAIM).exists():
            raise LiveSessionCompatError("terminal child has no compatibility session")
        claim, config, active, controller_claim, config_field = _stable_live_start(
            target, loaded, cpu=cpu,
        )
        pid = active["pid"]
        affinity = child_runner._verify_live_affinity(pid, cpu)
        limits = child_runner._verify_live_limits(pid, loaded["policy"]["proof_max_bytes"])
        # Re-read the controller after OS-level attestations.  This closes the
        # PID-exit/reuse window immediately before publication.
        checked_claim, checked_config, checked_active, checked_controller_claim, checked_config_field = (
            _stable_live_start(target, loaded, cpu=cpu)
        )
        if (
            checked_claim != claim
            or checked_config != config
            or checked_active != active
            or checked_controller_claim != controller_claim
            or checked_config_field != config_field
        ):
            raise LiveSessionCompatError("live start changed during compatibility attestation")
        session = child_runner._session_value(
            target, loaded, cpu=cpu, config=config, started=active,
            affinity=affinity, limits=limits, admission=claim["resource_admission"],
        )
        _publish_exact(target / child_runner.SESSION_COMMIT, session, label="session receipt")
        receipt = _receipt_value(
            target, loaded, claim=claim, config=config, active=active,
            controller_claim=controller_claim, config_field=config_field, session=session,
        )
        _publish_exact(target / COMPAT_RECEIPT, receipt, label="compatibility receipt")
        return {
            "state": "LIVE_SESSION_SEALED",
            "session": session,
            "receipt": receipt,
        }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="action", required=True)
    seal = sub.add_parser("seal-live", allow_abbrev=False)
    seal.add_argument("--root", type=Path, required=True)
    seal.add_argument("--cpu", type=int, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action != "seal-live":  # pragma: no cover - argparse guards this
        raise LiveSessionCompatError("unsupported compatibility action")
    result = seal_live_session(args.root, cpu=args.cpu)
    sys.stdout.buffer.write(child_runner.canonical_bytes(result) + b"\n")
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        LiveSessionCompatError,
        child_runner.RecursiveChildRunnerError,
        recursive.RecursiveSplitError,
        OSError,
        ValueError,
        TypeError,
    ) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
