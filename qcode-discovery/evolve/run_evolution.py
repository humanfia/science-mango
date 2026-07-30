"""Entry point for running OpenEvolve-based evolutionary search.

This script connects to a LiteLLM-compatible proxy and uses OpenEvolve
to evolve the ``generate_candidates`` function in
``evolve/seed_solution.py``.  It does **not** evolve individual polynomial
pairs -- it evolves the *strategy* for generating them.

Prerequisites
-------------
* A running LiteLLM proxy (or any OpenAI-compatible endpoint).  Pass the
  URL via ``--api-base``, ``$OPENAI_API_BASE``, ``$LITELLM_API_BASE``, or
  let it default to ``http://localhost:4000/v1``.
* The ``evolve`` dependency group: ``uv sync --group dev --group evolve``.

How it works
------------
1. Loads ``evolve/config.yaml`` and applies CLI overrides (model list,
   temperature, api_base, iterations).
2. Passes ``evolve/seed_solution.py`` (initial program) and
   ``evolve/openevolve_evaluator.py`` (fitness function) to OpenEvolve.
3. OpenEvolve mutates the code between ``# EVOLVE-BLOCK-START`` and
   ``# EVOLVE-BLOCK-END`` markers using LLM-generated diffs.
4. Each mutation is evaluated via the two-stage cascade in
   ``openevolve_evaluator.py`` (see that module's docstring for details).
5. MAP-Elites with 5 islands and periodic migration maintains diversity
   across ``lattices_with_high_k`` and ``num_high_k`` feature dimensions.
6. The LLM receives structured evaluation artifacts (best code found,
   per-lattice breakdown, errors) as feedback for the next mutation.

W&B integration
---------------
Pass ``--wandb`` to enable live dashboards.  A background ``WandbSyncer``
thread tails the metrics JSONL file written by evaluator subprocesses
(where ``wandb.run`` is ``None``) and forwards each record to W&B with
running-best tracking.

Output
------
* Best evolved program: ``results/evolution/<run_name>/best_generate_candidates.py``
* OpenEvolve checkpoints: ``results/evolution/<run_name>/checkpoints/``
* Metrics JSONL: ``results/evolution_metrics.jsonl``
* Discovered codes: ``results/discovered_codes.json``

Usage::

    # Single model
    uv run python evolve/run_evolution.py \\
        --model anthropic/claude-sonnet-4-5-20250514 --iterations 100

    # Ensemble of models
    uv run python evolve/run_evolution.py \\
        --models gemini/gemini-2.5-flash anthropic/claude-sonnet-4-5-20250514 \\
        --iterations 200 --run-name ensemble_v1

    # Resume from checkpoint
    uv run python evolve/run_evolution.py \\
        --resume results/evolution/run_20260218/checkpoints/checkpoint_100 \\
        --iterations 200

    # With W&B tracking
    uv run python evolve/run_evolution.py \\
        --model anthropic/claude-sonnet-4-5-20250514 --iterations 100 --wandb
"""

from __future__ import annotations

import argparse
import asyncio
import concurrent.futures
import fcntl
import hashlib
import json
import math
import os
import platform as platform_module
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
from datetime import datetime
from contextlib import contextmanager, nullcontext
from dataclasses import dataclass, field
from pathlib import Path

from typing import Any
# Ensure project root is on path
PROJECT_ROOT = str(Path(__file__).resolve().parent.parent)
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

from evolve.dependency_contract import LOCAL_EVALUATOR_DEPENDENCIES
from evaluation.search_contract import EVOLUTION_LATTICES

SEED_SOLUTION = str(Path(__file__).parent / "seed_solution.py")
SEED_SOLUTION_MILP = str(Path(__file__).parent / "seed_solution_milp.py")
SEED_SOLUTION_NONCSS = str(Path(__file__).parent / "seed_solution_noncss.py")
EVALUATOR = str(Path(__file__).parent / "openevolve_evaluator.py")
EVALUATOR_NONCSS = str(Path(__file__).parent / "openevolve_evaluator_noncss.py")
DEFAULT_CONFIG = str(Path(__file__).parent / "config.yaml")
DEFAULT_CONFIG_NONCSS = str(Path(__file__).parent / "config_noncss.yaml")
EVOLUTION_BASE = str(Path(PROJECT_ROOT) / "results" / "evolution")
METRICS_FILE = str(Path(PROJECT_ROOT) / "results" / "evolution_metrics.jsonl")


EVOLUTION_COMPLETION_SCHEMA_VERSION = 2
EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION = 2
WINNER_PREFLIGHT_CONTRACT_VERSION = 1
WINNER_PREFLIGHT_CONTRACT_ID_ENV = "QCODE_WINNER_PREFLIGHT_CONTRACT_ID"
WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC = (
    "winner_preflight_contract_version"
)
WINNER_PREFLIGHT_CONTRACT_ID_METRIC = "winner_preflight_contract_id"
WINNER_PREFLIGHT_COMPLETE_METRIC = "winner_preflight_complete"
WINNER_PREFLIGHT_INCOMPLETE_METRIC = "winner_preflight_incomplete"
WINNER_PREFLIGHT_LATTICES_METRIC = "winner_preflight_lattices"
WINNER_PREFLIGHT_EVALUATED_METRIC = (
    "winner_preflight_candidate_definitions_evaluated"
)
WINNER_PREFLIGHT_ELIGIBLE_METRIC = (
    "winner_preflight_winner_capable_eligible"
)
WINNER_PREFLIGHT_PERSISTED_METRIC = (
    "winner_preflight_winner_capable_persisted"
)
WINNER_PREFLIGHT_OMITTED_METRIC = "winner_preflight_winner_capable_omitted"
WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC = "winner_preflight_hard_timeout"
WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC = (
    "winner_preflight_subprocess_failed"
)
WINNER_PREFLIGHT_NUMERIC_THREAD_ENV = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS",
)


def _file_identity(path: str | Path, label: str) -> dict[str, object]:
    original = Path(path)
    if original.is_symlink():
        raise RuntimeError(f"{label} may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"{label} is missing: {original}") from exc
    if not resolved.is_file():
        raise RuntimeError(f"{label} is not a regular file: {resolved}")
    digest = hashlib.sha256()
    with resolved.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return {
        "path": str(resolved),
        "sha256": digest.hexdigest(),
        "bytes": resolved.stat().st_size,
    }


def _read_text_snapshot(
    path_value: str | Path,
    label: str,
) -> tuple[str, dict[str, Any]]:
    path = Path(path_value)
    if not path.is_absolute() or path.is_symlink():
        raise RuntimeError(f"{label} path must be absolute and symlink-free")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"{label} is missing: {path}") from exc
    if resolved != path:
        raise RuntimeError(f"{label} path must be canonical: {path}")
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RuntimeError(f"O_NOFOLLOW is required to read {label}")
    fd = os.open(path, os.O_RDONLY | nofollow | getattr(os, "O_CLOEXEC", 0))
    try:
        before = os.fstat(fd)
        path_before = os.stat(path, follow_symlinks=False)
        if (
            not stat.S_ISREG(before.st_mode)
            or not stat.S_ISREG(path_before.st_mode)
            or (before.st_dev, before.st_ino)
            != (path_before.st_dev, path_before.st_ino)
        ):
            raise RuntimeError(f"{label} must be one stable regular file")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        after = os.fstat(fd)
        path_after = os.stat(path, follow_symlinks=False)
        if (
            (before.st_dev, before.st_ino)
            != (after.st_dev, after.st_ino)
            or (after.st_dev, after.st_ino)
            != (path_after.st_dev, path_after.st_ino)
        ):
            raise RuntimeError(f"{label} changed identity while being read")
    finally:
        os.close(fd)
    encoded = b"".join(chunks)
    try:
        text = encoded.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise RuntimeError(f"{label} is not UTF-8 text") from exc
    return text, {
        "path": str(path),
        "sha256": hashlib.sha256(encoded).hexdigest(),
        "bytes": len(encoded),
    }


def _file_sha256(path: Path) -> str:
    return str(_file_identity(path, "checkpoint file")["sha256"])


def _read_json_object(path: Path, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise RuntimeError(f"{label} must be a regular file: {path}")
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"cannot read {label}: {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise RuntimeError(f"{label} must contain a JSON object: {path}")
    return value


SUPPORTED_OPENEVOLVE_VERSION = "0.2.26"
SUPPORTED_OPENEVOLVE_SHA256 = {
    "controller": "4508dfc844e26cd6da7cf48240e8acf0a42d8a927610b41e0ebb0f283d6e88f9",
    "process_parallel": "66f6fa57e7afb5db54cf7bc02130f30d4040175d9cdfdf53faf668787eec2371",
    "database": "4ae70c309d7c33a3f92ad181437ec71f9ca77575d57bd673249791ecf38d754b",
    "api": "c85fcafe18f288148a5dea918b6af5c2312717f39de2a416d26e158b84924eae",
}

def _evaluator_dependency_identities() -> dict[str, dict[str, Any]]:
    project_root = Path(PROJECT_ROOT)
    return {
        name: _file_identity(
            project_root / relative_path,
            f"evolution evaluator dependency {name}",
        )
        for name, relative_path in LOCAL_EVALUATOR_DEPENDENCIES.items()
    }


def _winner_preflight_contract_id(
    evaluator_path: str | Path,
    dependency_identities: dict[str, dict[str, Any]],
) -> int:
    """Bind checkpoint markers to the active evaluator and dependencies."""

    evaluator = _file_identity(
        evaluator_path, "winner preflight evaluator"
    )
    dependency_hashes: dict[str, str] = {}
    for name in sorted(LOCAL_EVALUATOR_DEPENDENCIES):
        identity = dependency_identities.get(name)
        digest = identity.get("sha256") if isinstance(identity, dict) else None
        if (
            not isinstance(digest, str)
            or len(digest) != 64
            or any(character not in "0123456789abcdef" for character in digest)
        ):
            raise RuntimeError(
                f"winner preflight dependency identity is invalid: {name}"
            )
        dependency_hashes[name] = digest
    payload = {
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "evaluator_sha256": evaluator["sha256"],
        "dependency_sha256": dependency_hashes,
        "lattices": [list(lattice) for lattice in EVOLUTION_LATTICES],
    }
    digest = hashlib.sha256(
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    # OpenEvolve treats metrics as JSON numbers and converts cascade metrics
    # to float.  Thirteen hexadecimal digits stay below 2**53, so the id is
    # exactly representable and survives every checkpoint round trip.
    return int(digest[:13], 16)


_WINNER_PREFLIGHT_MARKER_FIELDS = (
    WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC,
    WINNER_PREFLIGHT_CONTRACT_ID_METRIC,
    WINNER_PREFLIGHT_COMPLETE_METRIC,
    WINNER_PREFLIGHT_INCOMPLETE_METRIC,
    WINNER_PREFLIGHT_LATTICES_METRIC,
    WINNER_PREFLIGHT_EVALUATED_METRIC,
    WINNER_PREFLIGHT_ELIGIBLE_METRIC,
    WINNER_PREFLIGHT_PERSISTED_METRIC,
    WINNER_PREFLIGHT_OMITTED_METRIC,
    WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC,
    WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC,
)

_WINNER_PREFLIGHT_FAILURE_BASE_FIELDS = frozenset({
    "combined_score",
    "error",
    "lattices_with_high_k",
    "num_high_k",
    "term_count",
    "pattern_type",
})


def _exact_nonnegative_metric(
    metrics: dict[str, Any],
    name: str,
) -> int:
    value = metrics.get(name)
    if (
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not math.isfinite(float(value))
        or float(value) < 0
        or not float(value).is_integer()
    ):
        raise RuntimeError(f"winner preflight marker is invalid: {name}")
    return int(value)


def _validated_winner_preflight_markers(
    metrics: Any,
    *,
    expected_contract_id: int,
) -> dict[str, float]:
    if not isinstance(metrics, dict):
        raise RuntimeError("winner preflight metrics are not an object")
    values = {
        name: _exact_nonnegative_metric(metrics, name)
        for name in _WINNER_PREFLIGHT_MARKER_FIELDS
    }
    if (
        values[WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC]
        != WINNER_PREFLIGHT_CONTRACT_VERSION
        or values[WINNER_PREFLIGHT_CONTRACT_ID_METRIC]
        != expected_contract_id
        or values[WINNER_PREFLIGHT_COMPLETE_METRIC] != 1
        or values[WINNER_PREFLIGHT_INCOMPLETE_METRIC] != 0
        or values[WINNER_PREFLIGHT_LATTICES_METRIC]
        != len(EVOLUTION_LATTICES)
        or values[WINNER_PREFLIGHT_OMITTED_METRIC] != 0
        or values[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] != 0
        or values[WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC] != 0
        or values[WINNER_PREFLIGHT_PERSISTED_METRIC]
        != values[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
        or values[WINNER_PREFLIGHT_EVALUATED_METRIC]
        < values[WINNER_PREFLIGHT_ELIGIBLE_METRIC]
    ):
        raise RuntimeError(
            "winner preflight markers do not prove complete persistence"
        )
    return {name: float(values[name]) for name in values}


def _exact_incomplete_winner_preflight_markers(
    metrics: Any,
    *,
    expected_contract_id: int,
) -> dict[str, float] | None:
    """Recognize only the evaluator's canonical incomplete-preflight envelope.

    A child with this envelope is a fully observed *failed attempt*, not a
    checkpointable program.  Returning ``None`` is deliberately fail-closed:
    malformed markers, a wrong contract, or an inconsistent claim continue
    through the normal database-add observer and make the whole slice fail.
    """

    expected_fields = _WINNER_PREFLIGHT_FAILURE_BASE_FIELDS.union(
        _WINNER_PREFLIGHT_MARKER_FIELDS
    )
    if (
        not isinstance(metrics, dict)
        or set(metrics) != expected_fields
        or not isinstance(metrics.get("error"), str)
        or not metrics["error"]
    ):
        return None
    for name in (
        "combined_score",
        "lattices_with_high_k",
        "num_high_k",
        "term_count",
        "pattern_type",
    ):
        value = metrics.get(name)
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(float(value))
            or float(value) != 0.0
        ):
            return None
    try:
        values = {
            name: _exact_nonnegative_metric(metrics, name)
            for name in _WINNER_PREFLIGHT_MARKER_FIELDS
        }
    except RuntimeError:
        return None
    if (
        values[WINNER_PREFLIGHT_CONTRACT_VERSION_METRIC]
        != WINNER_PREFLIGHT_CONTRACT_VERSION
        or values[WINNER_PREFLIGHT_CONTRACT_ID_METRIC]
        != expected_contract_id
        or values[WINNER_PREFLIGHT_COMPLETE_METRIC] != 0
        or values[WINNER_PREFLIGHT_INCOMPLETE_METRIC] != 1
        or values[WINNER_PREFLIGHT_LATTICES_METRIC] != 0
        or values[WINNER_PREFLIGHT_EVALUATED_METRIC] != 0
        or values[WINNER_PREFLIGHT_ELIGIBLE_METRIC] != 0
        or values[WINNER_PREFLIGHT_PERSISTED_METRIC] != 0
        or values[WINNER_PREFLIGHT_OMITTED_METRIC] != 0
        or values[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC] not in (0, 1)
        or values[WINNER_PREFLIGHT_SUBPROCESS_FAILED_METRIC] != 1
    ):
        return None
    return {name: float(values[name]) for name in values}


def _checkpoint_preflight_summary(
    checkpoint_path: str | Path,
    *,
    expected_contract_id: int,
) -> dict[str, int]:
    programs_dir = Path(checkpoint_path) / "programs"
    if programs_dir.is_symlink() or not programs_dir.is_dir():
        raise RuntimeError(
            f"checkpoint programs directory is missing: {programs_dir}"
        )
    codes: set[str] = set()
    programs = 0
    for path in sorted(programs_dir.glob("*.json")):
        program = _read_json_object(path, "checkpoint program")
        code = program.get("code")
        if not isinstance(code, str) or not code:
            raise RuntimeError(f"checkpoint program has invalid code: {path}")
        _validated_winner_preflight_markers(
            program.get("metrics"),
            expected_contract_id=expected_contract_id,
        )
        programs += 1
        codes.add(hashlib.sha256(code.encode("utf-8")).hexdigest())
    if programs < 1:
        raise RuntimeError("result checkpoint contains no preflighted programs")
    return {"programs": programs, "unique_program_codes": len(codes)}


def _validate_loaded_checkpoint_database(
    database: Any,
    checkpoint_path: str | Path,
) -> None:
    """Ensure OpenEvolve did not silently skip a checkpoint Program."""

    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict):
        raise RuntimeError("loaded checkpoint program database is invalid")
    expected: dict[str, str] = {}
    programs_dir = Path(checkpoint_path) / "programs"
    for path in sorted(programs_dir.glob("*.json")):
        row = _read_json_object(path, "checkpoint program")
        program_id = row.get("id")
        code = row.get("code")
        if (
            not isinstance(program_id, str)
            or not program_id
            or program_id in expected
            or not isinstance(code, str)
            or not code
        ):
            raise RuntimeError(
                f"checkpoint program identity is invalid: {path}"
            )
        expected[program_id] = code
    if set(programs) != set(expected):
        raise RuntimeError(
            "OpenEvolve did not load the exact checkpoint program set"
        )
    for program_id, code in expected.items():
        if getattr(programs[program_id], "code", None) != code:
            raise RuntimeError(
                f"OpenEvolve changed checkpoint program code: {program_id}"
            )


def _winner_preflight_wall_timeout(configured_timeout: float) -> float:
    if (
        isinstance(configured_timeout, bool)
        or not isinstance(configured_timeout, (int, float))
        or not math.isfinite(float(configured_timeout))
        or configured_timeout <= 60
    ):
        raise RuntimeError(
            "evaluator timeout leaves no winner-preflight wall margin"
        )
    return min(1050.0, float(configured_timeout) - 60.0)


def _terminate_private_worker_group(process: subprocess.Popen) -> None:
    leader_reaped = False
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        process.wait()
        return
    try:
        process.wait(timeout=5)
        leader_reaped = True
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    if not leader_reaped:
        process.wait()


def _preflight_stderr_tail(path: Path, limit: int = 8192) -> str:
    try:
        return path.read_bytes()[-limit:].decode("utf-8", errors="replace")
    except OSError:
        return ""


def _execute_winner_preflight(
    evaluator_path: str | Path,
    code: str,
    *,
    expected_contract_id: int,
    wall_timeout: float,
    cancel_event: threading.Event,
) -> dict[str, float]:
    """Evaluate one unique checkpoint program in a killable process group."""

    with tempfile.TemporaryDirectory(prefix="qcode-checkpoint-preflight-") as root:
        temp_root = Path(root)
        program_path = temp_root / "program.py"
        result_path = temp_root / "result.json"
        stdout_path = temp_root / "stdout.log"
        stderr_path = temp_root / "stderr.log"
        program_path.write_text(code)
        lifecycle_read_fd, lifecycle_write_fd = os.pipe()
        command = [
            sys.executable,
            str(Path(evaluator_path).resolve()),
            "--preflight-worker",
            str(program_path.resolve()),
            str(result_path.resolve()),
            str(os.getpid()),
            str(lifecycle_read_fd),
        ]
        environment = os.environ.copy()
        environment[WINNER_PREFLIGHT_CONTRACT_ID_ENV] = str(
            expected_contract_id
        )
        environment.pop("QCODE_WINNER_PREFLIGHT_REUSE", None)
        for variable in WINNER_PREFLIGHT_NUMERIC_THREAD_ENV:
            environment[variable] = "1"
        try:
            with stdout_path.open("wb") as stdout, stderr_path.open(
                "wb"
            ) as stderr:
                try:
                    process = subprocess.Popen(
                        command,
                        stdin=subprocess.DEVNULL,
                        stdout=stdout,
                        stderr=stderr,
                        close_fds=True,
                        env=environment,
                        pass_fds=(lifecycle_read_fd,),
                        start_new_session=True,
                    )
                finally:
                    os.close(lifecycle_read_fd)
                deadline = time.monotonic() + wall_timeout
                try:
                    while True:
                        if cancel_event.is_set():
                            _terminate_private_worker_group(process)
                            raise RuntimeError(
                                "winner preflight cancelled after peer failure"
                            )
                        remaining = deadline - time.monotonic()
                        if remaining <= 0:
                            _terminate_private_worker_group(process)
                            raise RuntimeError(
                                "winner preflight exceeded its killable wall "
                                "timeout"
                            )
                        try:
                            return_code = process.wait(
                                timeout=min(0.25, remaining)
                            )
                            break
                        except subprocess.TimeoutExpired:
                            continue
                except BaseException:
                    if process.poll() is None:
                        _terminate_private_worker_group(process)
                    raise
        finally:
            os.close(lifecycle_write_fd)

        if return_code != 0:
            tail = _preflight_stderr_tail(stderr_path)
            suffix = f": {tail}" if tail else ""
            raise RuntimeError(
                f"winner preflight subprocess exited with status "
                f"{return_code}{suffix}"
            )
        try:
            payload = json.loads(result_path.read_text())
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise RuntimeError(
                "winner preflight result is unreadable"
            ) from exc
        if (
            not isinstance(payload, dict)
            or set(payload) != {"schema_version", "status", "metrics"}
            or payload.get("schema_version") != 1
            or payload.get("status") != "completed"
            or not isinstance(payload.get("metrics"), dict)
            or set(payload["metrics"]) != set(_WINNER_PREFLIGHT_MARKER_FIELDS)
        ):
            raise RuntimeError("winner preflight result schema is invalid")
        return _validated_winner_preflight_markers(
            payload["metrics"],
            expected_contract_id=expected_contract_id,
        )


def _backfill_checkpoint_programs(
    database: Any,
    *,
    evaluator_path: str | Path,
    expected_contract_id: int,
    max_workers: int,
    wall_timeout: float,
) -> dict[str, Any]:
    """Preflight every unique old checkpoint program before evolution resumes."""

    if (
        isinstance(max_workers, bool)
        or not isinstance(max_workers, int)
        or max_workers < 1
    ):
        raise RuntimeError("winner preflight worker cap must be positive")
    programs = getattr(database, "programs", None)
    if not isinstance(programs, dict) or not programs:
        raise RuntimeError("loaded checkpoint contains no program database")

    groups: dict[tuple[str, str], list[Any]] = {}
    for program_id in sorted(programs):
        program = programs[program_id]
        code = getattr(program, "code", None)
        metrics = getattr(program, "metrics", None)
        if not isinstance(code, str) or not code:
            raise RuntimeError(
                f"loaded checkpoint program has invalid code: {program_id}"
            )
        if not isinstance(metrics, dict):
            raise RuntimeError(
                f"loaded checkpoint program has invalid metrics: {program_id}"
            )
        digest = hashlib.sha256(code.encode("utf-8")).hexdigest()
        groups.setdefault((digest, code), []).append(program)

    pending: list[tuple[tuple[str, str], list[Any]]] = []
    already_complete = 0
    for key, group in sorted(groups.items(), key=lambda item: item[0][0]):
        complete = True
        for program in group:
            try:
                _validated_winner_preflight_markers(
                    program.metrics,
                    expected_contract_id=expected_contract_id,
                )
            except RuntimeError:
                complete = False
                break
        if complete:
            already_complete += len(group)
        else:
            pending.append((key, group))

    results: dict[tuple[str, str], dict[str, float]] = {}
    cancel_event = threading.Event()
    if pending:
        executor = concurrent.futures.ThreadPoolExecutor(
            max_workers=min(max_workers, len(pending)),
            thread_name_prefix="checkpoint-preflight",
        )
        futures = {
            executor.submit(
                _execute_winner_preflight,
                evaluator_path,
                key[1],
                expected_contract_id=expected_contract_id,
                wall_timeout=wall_timeout,
                cancel_event=cancel_event,
            ): key
            for key, _group in pending
        }
        try:
            for future in concurrent.futures.as_completed(futures):
                results[futures[future]] = future.result()
        except BaseException:
            cancel_event.set()
            for future in futures:
                future.cancel()
            executor.shutdown(wait=True, cancel_futures=True)
            raise
        else:
            executor.shutdown(wait=True)

    # Mutate only after every missing unique source completed.  A failure
    # leaves the loaded in-memory DB untouched; the immutable base checkpoint
    # is never opened for writing in either case.
    updated = 0
    for key, group in pending:
        markers = results[key]
        for program in group:
            metrics = dict(program.metrics)
            metrics.update(markers)
            program.metrics = metrics
            updated += 1

    for program in programs.values():
        _validated_winner_preflight_markers(
            program.metrics,
            expected_contract_id=expected_contract_id,
        )
    return {
        "schema_version": 1,
        "status": "completed",
        "contract_version": WINNER_PREFLIGHT_CONTRACT_VERSION,
        "contract_id": expected_contract_id,
        "programs": len(programs),
        "unique_program_codes": len(groups),
        "programs_already_complete": already_complete,
        "unique_program_codes_evaluated": len(pending),
        "programs_updated": updated,
        "worker_cap": min(max_workers, max(1, len(pending))),
    }


def _strong_checkpoint_descriptor(
    output_dir: str | Path,
    checkpoint: str | Path,
    *,
    expected_iteration: int | None = None,
) -> dict[str, Any]:
    checkpoint_root = (Path(output_dir) / "checkpoints").resolve()
    original = Path(checkpoint)
    if original.is_symlink():
        raise RuntimeError(f"checkpoint may not be a symlink: {original}")
    try:
        resolved = original.resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(f"checkpoint is missing: {original}") from exc
    if not resolved.is_dir() or resolved.parent != checkpoint_root:
        raise RuntimeError(f"checkpoint does not belong to this run: {resolved}")
    prefix = "checkpoint_"
    if not resolved.name.startswith(prefix):
        raise RuntimeError(f"invalid checkpoint directory name: {resolved}")
    try:
        named_iteration = int(resolved.name[len(prefix):])
    except ValueError as exc:
        raise RuntimeError(
            f"invalid checkpoint iteration in path: {resolved}"
        ) from exc

    metadata_path = resolved / "metadata.json"
    best_path = resolved / "best_program.py"
    best_info_path = resolved / "best_program_info.json"
    programs_dir = resolved / "programs"
    metadata = _read_json_object(metadata_path, "checkpoint metadata")
    best_info = _read_json_object(
        best_info_path, "checkpoint best-program info"
    )
    if (
        best_path.is_symlink()
        or not best_path.is_file()
        or best_path.stat().st_size < 1
    ):
        raise RuntimeError(
            f"checkpoint best_program.py is missing or empty: {best_path}"
        )
    if programs_dir.is_symlink() or not programs_dir.is_dir():
        raise RuntimeError(
            f"checkpoint programs directory is missing: {programs_dir}"
        )

    iteration = metadata.get("last_iteration")
    if (
        isinstance(iteration, bool)
        or not isinstance(iteration, int)
        or iteration < 0
    ):
        raise RuntimeError(
            f"checkpoint last_iteration is invalid: "
            f"{metadata_path}: {iteration!r}"
        )
    if iteration != named_iteration:
        raise RuntimeError(
            "checkpoint path/metadata iteration mismatch: "
            f"{named_iteration} != {iteration}"
        )
    if expected_iteration is not None and iteration != expected_iteration:
        raise RuntimeError(
            f"checkpoint iteration mismatch: expected "
            f"{expected_iteration}, got {iteration}"
        )

    archive = metadata.get("archive")
    best_id = metadata.get("best_program_id")
    if (
        not isinstance(archive, list)
        or not archive
        or any(not isinstance(item, str) or not item for item in archive)
        or not isinstance(best_id, str)
        or not best_id
    ):
        raise RuntimeError(
            f"checkpoint archive/best_program_id is incomplete: {metadata_path}"
        )
    if (
        best_info.get("id") != best_id
        or best_info.get("current_iteration") != iteration
    ):
        raise RuntimeError(
            "checkpoint best-program info disagrees with metadata: "
            f"{best_info_path}"
        )

    referenced = set(archive)
    referenced.add(best_id)

    def add_optional_reference(value: Any, label: str) -> None:
        if value in (None, ""):
            return
        if not isinstance(value, str):
            raise RuntimeError(
                f"checkpoint {label} contains a non-string program id"
            )
        referenced.add(value)

    islands = metadata.get("islands", [])
    if not isinstance(islands, list) or any(
        not isinstance(island, list) for island in islands
    ):
        raise RuntimeError("checkpoint islands metadata is invalid")
    for island in islands:
        for program_id in island:
            add_optional_reference(program_id, "islands")
    island_best = metadata.get("island_best_programs", [])
    if not isinstance(island_best, list):
        raise RuntimeError(
            "checkpoint island_best_programs metadata is invalid"
        )
    for program_id in island_best:
        add_optional_reference(program_id, "island_best_programs")
    feature_maps = metadata.get("island_feature_maps", [])
    if not isinstance(feature_maps, list) or any(
        not isinstance(feature_map, dict) for feature_map in feature_maps
    ):
        raise RuntimeError(
            "checkpoint island_feature_maps metadata is invalid"
        )
    for feature_map in feature_maps:
        for program_id in feature_map.values():
            add_optional_reference(program_id, "island_feature_maps")

    program_files = sorted(programs_dir.glob("*.json"))
    if not program_files:
        raise RuntimeError(
            f"checkpoint contains no programs: {programs_dir}"
        )
    program_ids: set[str] = set()
    best_program_code: str | None = None
    file_hashes: dict[str, str] = {
        "metadata.json": _file_sha256(metadata_path),
        "best_program.py": _file_sha256(best_path),
        "best_program_info.json": _file_sha256(best_info_path),
    }
    for program_path in program_files:
        program = _read_json_object(program_path, "checkpoint program")
        program_id = program.get("id")
        if program_id != program_path.stem:
            raise RuntimeError(
                f"checkpoint program id/path mismatch: {program_path}"
            )
        code = program.get("code")
        metrics = program.get("metrics")
        if not isinstance(code, str) or not code:
            raise RuntimeError(
                f"checkpoint program has no non-empty code: {program_path}"
            )
        if not isinstance(metrics, dict):
            raise RuntimeError(
                f"checkpoint program metrics is not an object: {program_path}"
            )
        program_ids.add(program_id)
        if program_id == best_id:
            best_program_code = code
        file_hashes[f"programs/{program_path.name}"] = _file_sha256(
            program_path
        )
    missing = sorted(referenced - program_ids)
    if missing:
        raise RuntimeError(
            "checkpoint is missing referenced programs: "
            + ", ".join(missing)
        )
    if (
        best_program_code is None
        or best_path.read_text() != best_program_code
    ):
        raise RuntimeError(
            "checkpoint best_program.py does not match the stored "
            "best program code"
        )
    checkpoint_hash = hashlib.sha256(
        json.dumps(
            file_hashes, sort_keys=True, separators=(",", ":")
        ).encode()
    ).hexdigest()
    return {
        "path": str(resolved),
        "last_iteration": iteration,
        "sha256": checkpoint_hash,
        "programs": len(program_files),
    }


def _checkpoint_last_iteration(checkpoint: str | Path | None) -> int:
    if checkpoint is None:
        return 0
    checkpoint_path = Path(checkpoint)
    output_dir = checkpoint_path.parent.parent
    return int(
        _strong_checkpoint_descriptor(output_dir, checkpoint_path)["last_iteration"]
    )


def _atomic_write_json_artifact(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.tmp-", dir=path.parent
    )
    temporary = Path(temporary_name)
    encoded = (json.dumps(payload, sort_keys=True, indent=2) + "\n").encode()
    try:
        with os.fdopen(temporary_descriptor, "wb") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        descriptor = os.open(
            path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        )
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _slice_iterations_sha256(start_iteration: int, count: int) -> str:
    iterations = list(range(start_iteration, start_iteration + count))
    encoded = json.dumps(iterations, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validate_lifecycle_lease(fd: int, path_value: str) -> Path:
    if isinstance(fd, bool) or not isinstance(fd, int) or fd < 0:
        raise RuntimeError("lifecycle lease fd must be a non-negative integer")
    path = Path(path_value)
    if not path.is_absolute():
        raise RuntimeError("lifecycle lease path must be absolute")
    if path.is_symlink():
        raise RuntimeError(f"lifecycle lease may not be a symlink: {path}")
    try:
        resolved = path.resolve(strict=True)
        descriptor_stat = os.fstat(fd)
        path_stat = os.stat(path, follow_symlinks=False)
    except OSError as exc:
        raise RuntimeError(f"cannot validate lifecycle lease: {path}: {exc}") from exc
    if resolved != path:
        raise RuntimeError(
            f"lifecycle lease path must be canonical and symlink-free: {path}"
        )
    if not stat.S_ISREG(descriptor_stat.st_mode) or not stat.S_ISREG(path_stat.st_mode):
        raise RuntimeError("lifecycle lease must be a regular file")
    if (descriptor_stat.st_dev, descriptor_stat.st_ino) != (
        path_stat.st_dev,
        path_stat.st_ino,
    ):
        raise RuntimeError("lifecycle lease path does not match inherited fd")
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise RuntimeError("O_NOFOLLOW is required for lifecycle leases")
    probe_fd = os.open(path, os.O_RDWR | nofollow | getattr(os, "O_CLOEXEC", 0))
    try:
        try:
            fcntl.flock(probe_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            pass
        else:
            fcntl.flock(probe_fd, fcntl.LOCK_UN)
            raise RuntimeError("lifecycle lease was not locked before inheritance")
    finally:
        os.close(probe_fd)
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    os.set_inheritable(fd, False)
    return path


class _ObservedFuture:
    def __init__(self, raw: Any, iteration: int, observer: "_SliceObserver"):
        self._raw = raw
        self._iteration = iteration
        self._observer = observer

    def done(self) -> bool:
        return self._raw.done()

    def cancel(self) -> bool:
        return self._raw.cancel()

    def cancelled(self) -> bool:
        return self._raw.cancelled()

    def result(self, *args: Any, **kwargs: Any) -> Any:
        try:
            result = self._raw.result(*args, **kwargs)
        except BaseException as exc:
            self._observer.record_future_exception(self._iteration, exc)
            raise
        return self._observer.record_future_result(self._iteration, result)

    def __getattr__(self, name: str) -> Any:
        return getattr(self._raw, name)


@dataclass
class _SliceObserver:
    base_iteration: int
    iterations: int
    result_type: type
    expected_preflight_contract_id: int | None = None
    checkpoint_preflight_required: bool = False
    run_calls: int = 0
    shutdown_requested: bool = False
    submission_attempts: list[dict[str, Any]] = field(default_factory=list)
    consumed: dict[int, int] = field(default_factory=dict)
    outcomes: dict[int, dict[str, Any]] = field(default_factory=dict)
    expected_programs: dict[int, dict[str, Any]] = field(default_factory=dict)
    integrated_programs: dict[int, str] = field(default_factory=dict)
    auxiliary_programs: list[dict[str, Any]] = field(default_factory=list)
    violations: list[str] = field(default_factory=list)
    accounting_complete: bool = False
    checkpoint_saves: list[dict[str, Any]] = field(default_factory=list)
    checkpoint_controller: Any = None
    checkpoint_preflight_report: dict[str, Any] | None = None

    @property
    def start_iteration(self) -> int:
        return self.base_iteration + 1

    @property
    def end_iteration(self) -> int:
        return self.base_iteration + self.iterations

    @property
    def expected_iterations(self) -> list[int]:
        return list(range(self.start_iteration, self.end_iteration + 1))

    def begin(self, start: int, count: int, target_score: Any) -> None:
        self.run_calls += 1
        if self.run_calls != 1:
            self.violations.append("ProcessParallelController.run_evolution called more than once")
        if start != self.start_iteration or count != self.iterations:
            self.violations.append(
                f"evolution range mismatch: {(start, count)} != "
                f"{(self.start_iteration, self.iterations)}"
            )
        if target_score is not None:
            self.violations.append("managed evolution may not use target_score")

    def record_submission(self, iteration: int, island_id: Any, future: Any) -> Any:
        if isinstance(iteration, bool) or not isinstance(iteration, int):
            self.violations.append("submission iteration is not an integer")
        if isinstance(island_id, bool) or not isinstance(island_id, int):
            self.violations.append(
                f"submission {iteration!r} has an invalid island id"
            )
        result = "future" if future is not None else "none"
        self.submission_attempts.append({
            "iteration": iteration,
            "island_id": island_id,
            "result": result,
        })
        if future is None:
            return None
        return _ObservedFuture(future, iteration, self)

    def record_future_exception(self, iteration: int, exc: BaseException) -> None:
        self.consumed[iteration] = self.consumed.get(iteration, 0) + 1
        self.violations.append(
            f"future {iteration} raised {type(exc).__name__}"
        )

    def _record_worker_error(self, iteration: int, error: str) -> None:
        encoded = error.encode("utf-8")
        self.outcomes[iteration] = {
            "iteration": iteration,
            "status": "worker_error",
            "error_sha256": hashlib.sha256(encoded).hexdigest(),
            "error_bytes": len(encoded),
        }

    def record_future_result(self, iteration: int, result: Any) -> Any:
        self.consumed[iteration] = self.consumed.get(iteration, 0) + 1
        if not isinstance(result, self.result_type):
            self.violations.append(
                f"future {iteration} returned a non-SerializableResult"
            )
            return result
        result_iteration = getattr(result, "iteration", None)
        if (
            isinstance(result_iteration, bool)
            or not isinstance(result_iteration, int)
            or result_iteration != iteration
        ):
            self.violations.append(f"future {iteration} returned a mismatched iteration")
            return result
        error = getattr(result, "error", None)
        child = getattr(result, "child_program_dict", None)
        if error is not None:
            if not isinstance(error, str) or not error or child is not None:
                self.violations.append(
                    f"future {iteration} returned an invalid worker error"
                )
                return result
            self._record_worker_error(iteration, error)
            return result
        if not isinstance(child, dict):
            self.violations.append(f"future {iteration} returned neither error nor child")
            return result
        program_id = child.get("id")
        if not isinstance(program_id, str) or not program_id:
            self.violations.append(f"future {iteration} returned an invalid child id")
            return result
        child_iteration = child.get("iteration_found")
        if (
            isinstance(child_iteration, bool)
            or not isinstance(child_iteration, int)
            or child_iteration != iteration
        ):
            self.violations.append(
                f"future {iteration} returned a child with mismatched iteration"
            )
            return result
        if any(
            expected["id"] == program_id
            for expected in self.expected_programs.values()
        ):
            self.violations.append(
                f"future {iteration} reused child program id {program_id}"
            )
            return result
        try:
            encoded_child = json.dumps(
                child,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            self.violations.append(
                f"future {iteration} returned invalid child content: "
                f"{type(exc).__name__}"
            )
            return result
        if self.expected_preflight_contract_id is not None:
            incomplete = _exact_incomplete_winner_preflight_markers(
                child.get("metrics"),
                expected_contract_id=self.expected_preflight_contract_id,
            )
            if incomplete is not None:
                source_error = str(child["metrics"]["error"]).encode("utf-8")
                failure = {
                    "child_program_bytes": len(encoded_child),
                    "child_program_sha256": hashlib.sha256(
                        encoded_child
                    ).hexdigest(),
                    "failure_error_bytes": len(source_error),
                    "failure_error_sha256": hashlib.sha256(
                        source_error
                    ).hexdigest(),
                    "hard_timeout": int(
                        incomplete[WINNER_PREFLIGHT_HARD_TIMEOUT_METRIC]
                    ),
                    "iteration": iteration,
                    "kind": "winner_preflight_incomplete",
                    "preflight_contract_id":
                        self.expected_preflight_contract_id,
                    "program_id": program_id,
                }
                canonical_error = json.dumps(
                    failure,
                    sort_keys=True,
                    separators=(",", ":"),
                    allow_nan=False,
                )
                sanitized = self.result_type(
                    child_program_dict=None,
                    iteration=iteration,
                    error=canonical_error,
                )
                self._record_worker_error(iteration, canonical_error)
                return sanitized
        self.expected_programs[iteration] = {
            "id": program_id,
            "sha256": hashlib.sha256(encoded_child).hexdigest(),
            "bytes": len(encoded_child),
        }
        return result

    def record_program_add(self, iteration: Any, program: Any) -> None:
        if (
            isinstance(iteration, bool)
            or not isinstance(iteration, int)
            or iteration not in self.expected_iterations
        ):
            self.violations.append(
                f"database add used unexpected iteration {iteration!r}"
            )
            return
        program_id = getattr(program, "id", None)
        if not isinstance(program_id, str) or not program_id:
            self.violations.append(
                f"database add for iteration {iteration} has an invalid program id"
            )
            return
        if iteration in self.integrated_programs:
            self.violations.append(f"iteration {iteration} was integrated twice")
            return
        expected = self.expected_programs.get(iteration)
        if expected is None or expected["id"] != program_id:
            self.violations.append(
                f"database add for iteration {iteration} used an unexpected program"
            )
            return
        if getattr(program, "iteration_found", None) != iteration:
            self.violations.append(
                f"database add for iteration {iteration} stored a mismatched iteration"
            )
            return
        if self.expected_preflight_contract_id is not None:
            try:
                _validated_winner_preflight_markers(
                    getattr(program, "metrics", None),
                    expected_contract_id=self.expected_preflight_contract_id,
                )
            except RuntimeError as exc:
                self.violations.append(
                    f"database add for iteration {iteration} has incomplete "
                    f"winner preflight: {exc}"
                )
                return
        to_dict = getattr(program, "to_dict", None)
        value = to_dict() if callable(to_dict) else vars(program)
        if not isinstance(value, dict):
            self.violations.append(
                f"database add for iteration {iteration} is not serializable"
            )
            return
        try:
            encoded = json.dumps(
                value,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            self.violations.append(
                f"database add for iteration {iteration} has invalid content: "
                f"{type(exc).__name__}"
            )
            return
        observed_sha256 = hashlib.sha256(encoded).hexdigest()
        if (
            expected["sha256"] != observed_sha256
            or expected["bytes"] != len(encoded)
        ):
            self.violations.append(
                f"database add for iteration {iteration} changed child content"
            )
            return
        self.integrated_programs[int(iteration)] = str(program_id)
        self.outcomes[int(iteration)] = {
            "iteration": int(iteration),
            "status": "program_added",
            "program_id": program_id,
            "program_sha256": observed_sha256,
            "program_bytes": len(encoded),
        }

    def record_checkpoint_preflight(
        self,
        report: dict[str, Any],
    ) -> None:
        if self.checkpoint_preflight_report is not None:
            self.violations.append(
                "checkpoint winner preflight was recorded more than once"
            )
            return
        if (
            not isinstance(report, dict)
            or report.get("schema_version") != 1
            or report.get("status") != "completed"
            or report.get("contract_version")
            != WINNER_PREFLIGHT_CONTRACT_VERSION
            or report.get("contract_id")
            != self.expected_preflight_contract_id
        ):
            self.violations.append(
                "checkpoint winner preflight report is invalid"
            )
            return
        self.checkpoint_preflight_report = dict(report)

    def record_auxiliary_program_add(
        self,
        *,
        program: Any,
        stored: Any,
        parent: Any,
        target_island: Any,
        num_islands: Any,
    ) -> None:
        """Account for a pinned OpenEvolve migration without treating it as a future.

        ``ProgramDatabase.migrate_programs`` inserts deterministic copies with
        ``iteration=None``.  They are database side effects of an already
        accounted evaluation, not additional submitted futures.  Accept only
        that exact shape; an evaluated child accidentally added without its
        iteration still leaves its expected future unintegrated and fails
        :meth:`verify`.
        """

        program_id = getattr(program, "id", None)
        stored_id = getattr(stored, "id", None)
        parent_id = getattr(program, "parent_id", None)
        metadata = getattr(program, "metadata", None)
        if (
            not isinstance(program_id, str)
            or not program_id
            or stored_id != program_id
            or parent is None
            or not isinstance(parent_id, str)
            or parent_id != getattr(parent, "id", None)
            or isinstance(target_island, bool)
            or not isinstance(target_island, int)
            or isinstance(num_islands, bool)
            or not isinstance(num_islands, int)
            or num_islands < 1
            or not 0 <= target_island < num_islands
            or not isinstance(metadata, dict)
            or metadata.get("migrant") is not True
            or metadata.get("island") != target_island
            # The pinned OpenEvolve Program dataclass defaults omitted
            # ``iteration_found`` to zero for migration copies.
            or getattr(program, "iteration_found", None) != 0
            or getattr(stored, "iteration_found", None) != 0
            or getattr(program, "code", None) != getattr(parent, "code", None)
            or getattr(program, "metrics", None)
            != getattr(parent, "metrics", None)
            or program_id
            in {
                expected["id"]
                for expected in self.expected_programs.values()
            }
            or any(
                item.get("program_id") == program_id
                for item in self.auxiliary_programs
            )
        ):
            self.violations.append(
                "database add with iteration None was not a valid migration"
            )
            return
        to_dict = getattr(stored, "to_dict", None)
        value = to_dict() if callable(to_dict) else vars(stored)
        if not isinstance(value, dict):
            self.violations.append("migration database add is not serializable")
            return
        try:
            encoded = json.dumps(
                value,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        except (TypeError, ValueError) as exc:
            self.violations.append(
                "migration database add has invalid content: "
                f"{type(exc).__name__}"
            )
            return
        self.auxiliary_programs.append(
            {
                "program_id": program_id,
                "parent_id": parent_id,
                "target_island": target_island,
                "program_sha256": hashlib.sha256(encoded).hexdigest(),
                "program_bytes": len(encoded),
            }
        )

    def verify(self, controller: Any) -> None:
        expected = self.expected_iterations
        attempt_ids = [item["iteration"] for item in self.submission_attempts]
        if attempt_ids != expected or any(
            item["result"] != "future" for item in self.submission_attempts
        ):
            self.violations.append("submitted futures are not the exact requested range")
        if self.shutdown_requested or controller.shutdown_event.is_set():
            self.violations.append("shutdown was requested")
        if controller.early_stopping_triggered:
            self.violations.append("early stopping was triggered")
        if any(self.consumed.get(iteration) != 1 for iteration in expected):
            self.violations.append("not every requested future was consumed exactly once")
        if sorted(self.outcomes) != expected:
            self.violations.append("not every requested future produced an accounted outcome")
        successful = sum(
            outcome.get("status") == "program_added"
            for outcome in self.outcomes.values()
        )
        # A worker_error has no checkpoint Program.  It covers both an LLM/diff
        # failure that never produced a child and the exact evaluator-generated
        # incomplete-preflight envelope sanitized before database.add.  Neither
        # outcome claims that a candidate universe was enumerated completely.
        # Malformed/forged marker claims and future exceptions remain
        # violations.
        if successful < 1:
            self.violations.append(
                "the OpenEvolve slice produced no successful evaluations"
            )
        if (
            self.checkpoint_preflight_required
            and self.checkpoint_preflight_report is None
        ):
            self.violations.append(
                "checkpoint winner preflight did not complete"
            )
        for iteration, expected in self.expected_programs.items():
            program_id = expected["id"]
            if self.integrated_programs.get(iteration) != program_id:
                self.violations.append(
                    f"program for iteration {iteration} was not integrated"
                )
        if self.run_calls != 1:
            self.violations.append("managed evolution did not make exactly one run call")
        if self.violations:
            raise RuntimeError("incomplete OpenEvolve slice: " + "; ".join(self.violations))
        self.accounting_complete = True

    def ensure_final_checkpoint(self) -> None:
        if not self.accounting_complete or self.checkpoint_controller is None:
            raise RuntimeError("cannot save a checkpoint before slice accounting")
        if any(
            save.get("iteration") == self.end_iteration
            and save.get("accounting_complete") is True
            and isinstance(save.get("checkpoint_sha256"), str)
            and isinstance(save.get("checkpoint_programs"), int)
            for save in self.checkpoint_saves
        ):
            return
        self.checkpoint_controller._save_checkpoint(self.end_iteration)

    def record_checkpoint_save(self, controller: Any, iteration: int) -> None:
        record: dict[str, Any] = {
            "iteration": iteration,
            "accounting_complete": self.accounting_complete,
            "checkpoint_sha256": None,
            "checkpoint_programs": None,
        }
        checkpoint = (
            Path(controller.output_dir)
            / "checkpoints"
            / f"checkpoint_{iteration}"
        )
        try:
            descriptor = _strong_checkpoint_descriptor(
                controller.output_dir, checkpoint, expected_iteration=iteration
            )
        except RuntimeError:
            if self.accounting_complete and iteration == self.end_iteration:
                raise
        else:
            record["checkpoint_sha256"] = descriptor["sha256"]
            record["checkpoint_programs"] = descriptor["programs"]
        self.checkpoint_saves.append(record)


def _openevolve_source_binding() -> tuple[dict[str, dict[str, Any]], Any, Any]:
    import openevolve
    import openevolve.api as api_module
    import openevolve.controller as controller_module
    import openevolve.database as database_module
    import openevolve.process_parallel as process_module

    if openevolve.__version__ != SUPPORTED_OPENEVOLVE_VERSION:
        raise RuntimeError(
            f"unsupported OpenEvolve version: {openevolve.__version__}; "
            f"expected {SUPPORTED_OPENEVOLVE_VERSION}"
        )
    modules = {
        "controller": controller_module,
        "process_parallel": process_module,
        "database": database_module,
        "api": api_module,
    }
    binding: dict[str, dict[str, Any]] = {}
    for name, module in modules.items():
        identity = _file_identity(module.__file__, f"OpenEvolve {name} source")
        if identity["sha256"] != SUPPORTED_OPENEVOLVE_SHA256[name]:
            raise RuntimeError(f"unsupported OpenEvolve {name} source hash")
        binding[name] = identity
    return binding, controller_module, process_module


@contextmanager
def _verified_slice_controller(
    base_iteration: int,
    iterations: int,
    *,
    expected_preflight_contract_id: int | None = None,
    checkpoint_preflight_required: bool = False,
):
    if isinstance(iterations, bool) or not isinstance(iterations, int) or iterations < 1:
        raise RuntimeError("managed slice iterations must be positive")
    source_binding, controller_module, process_module = _openevolve_source_binding()
    observer = _SliceObserver(
        base_iteration=base_iteration,
        iterations=iterations,
        result_type=process_module.SerializableResult,
        expected_preflight_contract_id=expected_preflight_contract_id,
        checkpoint_preflight_required=checkpoint_preflight_required,
    )
    original_parallel = controller_module.ProcessParallelController
    original_save = controller_module.OpenEvolve._save_checkpoint

    class VerifiedProcessParallelController(original_parallel):
        def request_shutdown(self) -> None:
            observer.shutdown_requested = True
            return super().request_shutdown()

        def _submit_iteration(self, iteration: int, island_id: Any = None) -> Any:
            future = super()._submit_iteration(iteration, island_id)
            return observer.record_submission(iteration, island_id, future)

        async def run_evolution(
            self,
            start_iteration: int,
            max_iterations: int,
            target_score: Any = None,
            checkpoint_callback: Any = None,
        ) -> Any:
            observer.begin(start_iteration, max_iterations, target_score)
            checkpoint_controller = getattr(checkpoint_callback, "__self__", None)
            if checkpoint_controller is None:
                observer.violations.append(
                    "checkpoint callback is not bound to OpenEvolve"
                )
            elif observer.checkpoint_controller not in (None, checkpoint_controller):
                observer.violations.append(
                    "checkpoint controller changed during the slice"
                )
            else:
                observer.checkpoint_controller = checkpoint_controller
            original_add = self.database.add

            def observed_add(program: Any, iteration: Any = None, target_island: Any = None) -> Any:
                parent = (
                    self.database.programs.get(getattr(program, "parent_id", None))
                    if iteration is None
                    else None
                )
                result = original_add(
                    program, iteration=iteration, target_island=target_island
                )
                stored = self.database.programs.get(getattr(program, "id", None))
                if stored is None:
                    observer.violations.append(
                        f"database add for iteration {iteration} did not store the program"
                    )
                elif iteration is None:
                    observer.record_auxiliary_program_add(
                        program=program,
                        stored=stored,
                        parent=parent,
                        target_island=target_island,
                        num_islands=self.num_islands,
                    )
                else:
                    observer.record_program_add(iteration, stored)
                return result

            self.database.add = observed_add
            try:
                result = await super().run_evolution(
                    start_iteration,
                    max_iterations,
                    target_score,
                    checkpoint_callback,
                )
            finally:
                self.database.add = original_add
            observer.verify(self)
            return result

    def observed_save(controller: Any, iteration: int) -> None:
        valid_iteration = (
            not isinstance(iteration, bool)
            and isinstance(iteration, int)
            and observer.start_iteration <= iteration <= observer.end_iteration
        )
        if not observer.accounting_complete:
            if not valid_iteration:
                observer.violations.append(
                    f"checkpoint save used out-of-slice iteration {iteration!r}"
                )
            observer.checkpoint_saves.append({
                "iteration": iteration,
                "accounting_complete": False,
                "checkpoint_sha256": None,
                "checkpoint_programs": None,
                "suppressed": True,
            })
            return
        if iteration != observer.end_iteration:
            observer.violations.append(
                f"post-accounting checkpoint save was not the slice end: {iteration!r}"
            )
            raise RuntimeError(observer.violations[-1])
        original_save(controller, iteration)
        observer.record_checkpoint_save(controller, iteration)

    controller_module.ProcessParallelController = VerifiedProcessParallelController
    controller_module.OpenEvolve._save_checkpoint = observed_save
    try:
        yield observer, source_binding
        observer.ensure_final_checkpoint()
    finally:
        controller_module.OpenEvolve._save_checkpoint = original_save
        controller_module.ProcessParallelController = original_parallel


def _launch_input_identities(
    config_path: str | Path,
    seed_path: str | Path,
    evaluator_path: str | Path,
    context_path: str | Path,
    context_identity: dict[str, Any],
    dependency_identities: dict[str, dict[str, Any]],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
) -> dict[str, dict[str, Any]]:
    observed_context = _file_identity(
        context_path, "evolution humanize context"
    )
    if observed_context != context_identity:
        raise RuntimeError("evolution humanize context changed after snapshot")
    observed_dependencies = _evaluator_dependency_identities()
    if observed_dependencies != dependency_identities:
        raise RuntimeError("evolution evaluator dependencies changed during the slice")
    identities = {
        "config": _file_identity(config_path, "evolution config"),
        "seed": _file_identity(seed_path, "evolution seed"),
        "launcher": _file_identity(Path(__file__), "evolution launcher"),
        "evaluator": _file_identity(evaluator_path, "evolution evaluator"),
        "context": dict(context_identity),
    }
    identities.update(
        {name: dict(value) for name, value in dependency_identities.items()}
    )
    if backend_path is not None:
        identities["backend"] = _file_identity(
            backend_path, "evolution model backend"
        )
    if codex_executable_identity is not None:
        executable_path = codex_executable_identity.get("path")
        if not isinstance(executable_path, str):
            raise RuntimeError("Codex executable identity has no path")
        observed_executable = _file_identity(
            executable_path, "Codex CLI native executable"
        )
        observed_executable["mode"] = stat.S_IMODE(
            Path(executable_path).stat().st_mode
        )
        if observed_executable != codex_executable_identity:
            raise RuntimeError(
                "Codex CLI native executable changed during the slice"
            )
        identities["codex_executable"] = dict(codex_executable_identity)
    return identities


def _resolve_native_codex_path(requested_bin: str) -> Path:
    launcher = shutil.which(requested_bin)
    if launcher is None:
        raise RuntimeError(f"Codex CLI executable is unavailable: {requested_bin}")
    launcher_path = Path(launcher).resolve(strict=True)
    with launcher_path.open("rb") as stream:
        magic = stream.read(4)
    if magic in (b"\x7fELF", b"MZ\x90\x00"):
        return launcher_path
    if launcher_path.name != "codex.js" or launcher_path.parent.name != "bin":
        raise RuntimeError(
            "managed QCODE_CODEX_BIN must be the official codex.js launcher "
            "or a native Codex executable"
        )
    system = platform_module.system().lower()
    machine = platform_module.machine().lower()
    targets = {
        ("linux", "x86_64"): (
            "@openai/codex-linux-x64",
            "x86_64-unknown-linux-musl",
            "codex",
        ),
        ("linux", "aarch64"): (
            "@openai/codex-linux-arm64",
            "aarch64-unknown-linux-musl",
            "codex",
        ),
        ("darwin", "x86_64"): (
            "@openai/codex-darwin-x64",
            "x86_64-apple-darwin",
            "codex",
        ),
        ("darwin", "arm64"): (
            "@openai/codex-darwin-arm64",
            "aarch64-apple-darwin",
            "codex",
        ),
        ("windows", "amd64"): (
            "@openai/codex-win32-x64",
            "x86_64-pc-windows-msvc",
            "codex.exe",
        ),
        ("windows", "arm64"): (
            "@openai/codex-win32-arm64",
            "aarch64-pc-windows-msvc",
            "codex.exe",
        ),
    }
    target = targets.get((system, machine))
    if target is None:
        raise RuntimeError(
            f"unsupported managed Codex platform: {system}/{machine}"
        )
    package_name, target_triple, executable_name = target
    package_root = launcher_path.parent.parent
    candidates = (
        package_root
        / "node_modules"
        / Path(*package_name.split("/"))
        / "vendor"
        / target_triple
        / "bin"
        / executable_name,
        package_root / "vendor" / target_triple / "bin" / executable_name,
    )
    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            continue
        if resolved.is_file():
            return resolved
    raise RuntimeError(
        "cannot resolve the official Codex launcher to its native executable"
    )


def _resolve_codex_execution_binding(
) -> tuple[dict[str, Any], str, str]:
    native_path = _resolve_native_codex_path(
        os.environ.get("QCODE_CODEX_BIN", "codex")
    )
    if not native_path.is_file() or not os.access(native_path, os.X_OK):
        raise RuntimeError(
            f"Codex CLI native binary is not executable: {native_path}"
        )
    identity = _file_identity(native_path, "Codex CLI native executable")
    identity["mode"] = stat.S_IMODE(native_path.stat().st_mode)
    project_root = Path(PROJECT_ROOT).resolve(strict=True)
    requested_cwd = Path(
        os.environ.get("QCODE_CODEX_CWD", str(project_root))
    ).resolve(strict=True)
    if requested_cwd != project_root:
        raise RuntimeError(
            "managed Codex CLI cwd must be the qcode-discovery project root"
        )
    try:
        completed = subprocess.run(
            [str(native_path), "--version"],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise RuntimeError("cannot identify the Codex CLI version") from exc
    version = completed.stdout.strip()
    if not version or len(version) > 500:
        raise RuntimeError("Codex CLI returned an invalid version identity")
    os.environ["QCODE_CODEX_BIN"] = str(native_path)
    os.environ["QCODE_CODEX_CWD"] = str(project_root)
    return identity, version, str(project_root)


def _validated_invocation_binding(
    invocation: dict[str, Any],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
) -> dict[str, Any]:
    expected_fields = {
        "model_names",
        "reasoning_effort",
        "codex_cli",
        "max_parallel_evaluations",
        "api_base",
        "temperature_disabled",
        "codex_version",
        "codex_cwd",
        "codex_executable_mode",
    }
    if not isinstance(invocation, dict) or set(invocation) != expected_fields:
        raise RuntimeError("managed invocation binding fields are incomplete")
    model_names = invocation["model_names"]
    if (
        not isinstance(model_names, list)
        or not model_names
        or any(not isinstance(name, str) or not name for name in model_names)
    ):
        raise RuntimeError("managed invocation model_names are invalid")
    reasoning_effort = invocation["reasoning_effort"]
    if reasoning_effort is not None and (
        not isinstance(reasoning_effort, str) or not reasoning_effort
    ):
        raise RuntimeError("managed invocation reasoning_effort is invalid")
    codex_cli = invocation["codex_cli"]
    if not isinstance(codex_cli, bool):
        raise RuntimeError("managed invocation codex_cli is invalid")
    if codex_cli != (
        backend_path is not None and codex_executable_identity is not None
    ):
        raise RuntimeError("managed invocation backend binding is inconsistent")
    codex_version = invocation["codex_version"]
    codex_cwd = invocation["codex_cwd"]
    codex_mode = invocation["codex_executable_mode"]
    if codex_cli:
        if not isinstance(codex_version, str) or not codex_version:
            raise RuntimeError("managed invocation codex_version is invalid")
        if (
            not isinstance(codex_cwd, str)
            or Path(codex_cwd) != Path(PROJECT_ROOT).resolve()
        ):
            raise RuntimeError("managed invocation codex_cwd is invalid")
        if (
            isinstance(codex_mode, bool)
            or not isinstance(codex_mode, int)
            or codex_mode != codex_executable_identity.get("mode")
        ):
            raise RuntimeError(
                "managed invocation codex_executable_mode is invalid"
            )
    elif any(
        value is not None for value in (codex_version, codex_cwd, codex_mode)
    ):
        raise RuntimeError("non-Codex invocation contains Codex execution fields")
    workers = invocation["max_parallel_evaluations"]
    if isinstance(workers, bool) or not isinstance(workers, int) or workers < 1:
        raise RuntimeError(
            "managed invocation max_parallel_evaluations is invalid"
        )
    api_base = invocation["api_base"]
    if not isinstance(api_base, str) or not api_base:
        raise RuntimeError("managed invocation api_base is invalid")
    if not isinstance(invocation["temperature_disabled"], bool):
        raise RuntimeError("managed invocation temperature_disabled is invalid")
    return dict(invocation)


def _write_slice_witness(
    witness_path: str | Path,
    *,
    observer: _SliceObserver,
    source_binding: dict[str, dict[str, Any]],
    output_dir: str | Path,
    resume_checkpoint: str | Path | None,
    iterations: int,
    config_path: str | Path,
    seed_path: str | Path,
    evaluator_path: str | Path,
    context_path: str | Path,
    context_identity: dict[str, Any],
    dependency_identities: dict[str, dict[str, Any]],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
    invocation: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    if not observer.accounting_complete:
        raise RuntimeError("OpenEvolve slice accounting did not complete")
    effective_invocation = _validated_invocation_binding(
        invocation, backend_path, codex_executable_identity
    )
    current_source_binding, _, _ = _openevolve_source_binding()
    if current_source_binding != source_binding:
        raise RuntimeError("OpenEvolve source binding changed during the slice")
    resolved_output = Path(output_dir).resolve()
    result_checkpoint = _strong_checkpoint_descriptor(
        resolved_output,
        resolved_output / "checkpoints" / f"checkpoint_{observer.end_iteration}",
        expected_iteration=observer.end_iteration,
    )
    if observer.expected_preflight_contract_id is not None:
        _checkpoint_preflight_summary(
            result_checkpoint["path"],
            expected_contract_id=observer.expected_preflight_contract_id,
        )
    if (
        observer.checkpoint_preflight_required
        and observer.checkpoint_preflight_report is None
    ):
        raise RuntimeError(
            "checkpoint winner preflight did not complete before witness"
        )
    if not any(
        save["iteration"] == observer.end_iteration
        and save["accounting_complete"] is True
        and save["checkpoint_sha256"] == result_checkpoint["sha256"]
        and save["checkpoint_programs"] == result_checkpoint["programs"]
        for save in observer.checkpoint_saves
    ):
        raise RuntimeError(
            "expected checkpoint was not saved after complete slice accounting"
        )
    launch_binding = _launch_input_identities(
        config_path,
        seed_path,
        evaluator_path,
        context_path,
        context_identity,
        dependency_identities,
        backend_path,
        codex_executable_identity,
    )
    payload: dict[str, Any] = {
        "schema_version": EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
        "status": "completed",
        "output_dir": str(resolved_output),
        "resume_checkpoint": (
            None if resume_checkpoint is None else str(Path(resume_checkpoint).resolve())
        ),
        "base_last_iteration": observer.base_iteration,
        "iterations_requested": iterations,
        "slice_start_iteration": observer.start_iteration,
        "slice_end_iteration": observer.end_iteration,
        "slice_iteration_count": iterations,
        "slice_iterations_sha256": _slice_iterations_sha256(
            observer.start_iteration, iterations
        ),
        "submission_attempts": sorted(
            observer.submission_attempts, key=lambda item: item["iteration"]
        ),
        "outcomes": [observer.outcomes[i] for i in observer.expected_iterations],
        "successful_evaluations": sum(
            outcome.get("status") == "program_added"
            for outcome in observer.outcomes.values()
        ),
        "worker_errors": sum(
            outcome.get("status") == "worker_error"
            for outcome in observer.outcomes.values()
        ),
        "checkpoint_saves": observer.checkpoint_saves,
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
        "openevolve_version": SUPPORTED_OPENEVOLVE_VERSION,
        "completed_at": datetime.now().astimezone().isoformat(),
    }
    payload.update(effective_invocation)
    for name, identity in launch_binding.items():
        for field_name in ("path", "sha256", "bytes"):
            payload[f"{name}_{field_name}"] = identity[field_name]
    for name, identity in source_binding.items():
        prefix = f"openevolve_{name}"
        for field_name in ("path", "sha256", "bytes"):
            payload[f"{prefix}_{field_name}"] = identity[field_name]
    witness = Path(witness_path)
    if witness.is_symlink() or witness.exists():
        raise RuntimeError(f"refusing to overwrite slice witness: {witness}")
    _atomic_write_json_artifact(witness, payload)
    witness_identity = _file_identity(witness, "OpenEvolve slice witness")
    return result_checkpoint, witness_identity


def _write_completion_marker(
    marker_path: str | Path,
    *,
    output_dir: str | Path,
    resume_checkpoint: str | Path | None,
    iterations: int,
    config_path: str | Path,
    seed_path: str | Path,
    evaluator_path: str | Path,
    context_path: str | Path,
    context_identity: dict[str, Any],
    dependency_identities: dict[str, dict[str, Any]],
    backend_path: str | Path | None,
    codex_executable_identity: dict[str, Any] | None,
    invocation: dict[str, Any],
    result_checkpoint: dict[str, Any],
    slice_witness: dict[str, Any],
) -> None:
    effective_invocation = _validated_invocation_binding(
        invocation, backend_path, codex_executable_identity
    )
    resolved_output = Path(output_dir).resolve()
    launch_binding = _launch_input_identities(
        config_path,
        seed_path,
        evaluator_path,
        context_path,
        context_identity,
        dependency_identities,
        backend_path,
        codex_executable_identity,
    )
    payload: dict[str, Any] = {
        "schema_version": EVOLUTION_COMPLETION_SCHEMA_VERSION,
        "status": "completed",
        "output_dir": str(resolved_output),
        "resume_checkpoint": (
            None if resume_checkpoint is None else str(Path(resume_checkpoint).resolve())
        ),
        "base_last_iteration": result_checkpoint["last_iteration"] - iterations,
        "iterations_requested": iterations,
        "result_checkpoint": result_checkpoint["path"],
        "result_last_iteration": result_checkpoint["last_iteration"],
        "result_checkpoint_sha256": result_checkpoint["sha256"],
        "result_checkpoint_programs": result_checkpoint["programs"],
        "slice_witness_path": slice_witness["path"],
        "slice_witness_sha256": slice_witness["sha256"],
        "slice_witness_bytes": slice_witness["bytes"],
        "completed_at": datetime.now().astimezone().isoformat(),
    }
    payload.update(effective_invocation)
    for name, identity in launch_binding.items():
        for field_name in ("path", "sha256", "bytes"):
            payload[f"{name}_{field_name}"] = identity[field_name]
    marker = Path(marker_path)
    if marker.is_symlink() or marker.exists():
        raise RuntimeError(f"refusing to overwrite completion marker: {marker}")
    _atomic_write_json_artifact(marker, payload)


def _cap_parallel_evaluations(config, cap: int | None) -> tuple[int, int]:
    """Cap OpenEvolve evaluation lanes without increasing the YAML setting."""
    configured = getattr(config.evaluator, "parallel_evaluations", None)
    if (
        isinstance(configured, bool)
        or not isinstance(configured, int)
        or configured < 1
    ):
        raise ValueError(
            "config evaluator.parallel_evaluations must be a positive integer"
        )
    if cap is not None:
        if isinstance(cap, bool) or not isinstance(cap, int) or cap < 1:
            raise ValueError("max parallel evaluations must be a positive integer")
        effective = min(configured, cap)
    else:
        effective = configured
    config.evaluator.parallel_evaluations = effective
    return configured, effective


def _resolve_api_base(args) -> str:
    """Resolve the API base URL from args or environment."""
    if args.api_base:
        return args.api_base
    for var in ("OPENAI_API_BASE", "LITELLM_API_BASE"):
        val = os.environ.get(var)
        if val:
            return val
    return "http://localhost:4000/v1"


def _resolve_output_dir(args) -> str:
    """Compute the output directory from --output or --run-name."""
    if args.output:
        return args.output
    run_name = args.run_name or f"run_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    return str(Path(EVOLUTION_BASE) / run_name)


def _set_reasoning_effort(config, effort: str | None) -> None:
    """Forward reasoning effort, refusing a silent downgrade."""
    if not effort:
        return
    configured = 0
    for model in [*config.llm.models, *config.llm.evaluator_models]:
        if hasattr(model, "reasoning_effort"):
            setattr(model, "reasoning_effort", effort)
            configured += 1
            continue
        for attribute in ("extra_params", "model_kwargs", "extra_body"):
            extra = getattr(model, attribute, None)
            if isinstance(extra, dict):
                extra["reasoning_effort"] = effort
                configured += 1
                break
    if configured == 0:
        raise RuntimeError(
            "This OpenEvolve version cannot forward reasoning_effort; upgrade it."
        )


def _build_config(
    args,
    api_base: str,
    model_names: list[str] | None,
    *,
    humanize_context_text: str | None = None,
):
    """Load config YAML and apply CLI overrides for models, temperature, etc."""
    import yaml
    from openevolve import Config
    from openevolve.config import LLMModelConfig

    config = Config.from_yaml(args.config)
    config.max_iterations = args.iterations
    _cap_parallel_evaluations(
        config,
        getattr(args, "max_parallel_evaluations", None),
    )

    # Propagate api_base to all model configs.
    # Setting config.llm.api_base alone does NOT propagate because
    # __post_init__ already ran during from_yaml().
    config.llm.api_base = api_base
    config.llm.update_model_params({"api_base": api_base}, overwrite=True)

    # Override model list if CLI specifies models; otherwise keep config as-is
    if model_names is not None:
        config.llm.models = [
            LLMModelConfig(name=name, weight=1.0)
            for name in model_names
        ]
        # Propagate ALL shared params to the new models -- not just api_base.
        # Fresh LLMModelConfig objects have None for max_tokens, timeout, retries,
        # etc.  Without propagation the retry loop crashes (range(None + 1)).
        shared = {
            "api_base": api_base,
            "api_key": config.llm.api_key,
            "temperature": config.llm.temperature,
            "top_p": config.llm.top_p,
            "max_tokens": config.llm.max_tokens,
            "timeout": config.llm.timeout,
            "retries": config.llm.retries,
            "retry_delay": config.llm.retry_delay,
            "system_message": config.llm.system_message,
        }
        config.llm.update_model_params(shared, overwrite=False)
        # Force api_base from CLI (overwrite any config default)
        config.llm.update_model_params({"api_base": api_base}, overwrite=True)
        # Reset evaluator_models to match
        config.llm.evaluator_models = config.llm.models.copy()
        config.llm.update_model_params({"api_base": api_base}, overwrite=True)
    else:
        # Using config YAML as-is. Re-apply per-model temperature overrides
        # that were lost during Config.from_yaml() -- OpenEvolve's __post_init__
        # calls update_model_params(overwrite=False), which overwrites explicit
        # null values with the global temperature.
        with open(args.config) as f:
            raw = yaml.safe_load(f)
        for i, model_raw in enumerate(raw.get("llm", {}).get("models", [])):
            if i < len(config.llm.models) and "temperature" in model_raw:
                config.llm.models[i].temperature = model_raw["temperature"]
                if i < len(config.llm.evaluator_models):
                    config.llm.evaluator_models[i].temperature = model_raw["temperature"]

    # Handle temperature: some models (e.g. GPT-5.1 Codex) reject it
    if args.no_temperature:
        config.llm.temperature = None
        config.llm.update_model_params({"temperature": None}, overwrite=True)
    elif args.temperature is not None:
        config.llm.temperature = args.temperature
        config.llm.update_model_params(
            {"temperature": args.temperature}, overwrite=True
        )

    _set_reasoning_effort(config, args.reasoning_effort)
    if args.humanize_context:
        context = (
            humanize_context_text
            if humanize_context_text is not None
            else getattr(args, "_humanize_context_text", None)
            or Path(args.humanize_context).read_text()
        ).strip()
        if context:
            config.prompt.system_message += (
                "\n\nHumanize cross-round memory and reviewer focus:\n" + context
            )
    return config


# ---------------------------------------------------------------------------
# W&B sync: background thread reads JSONL written by evaluator subprocesses
# ---------------------------------------------------------------------------

class WandbSyncer:
    """Tails the metrics JSONL file and logs each new line to W&B.

    The evaluator writes one JSON record per stage-2 evaluation from
    subprocess workers (where wandb.run is None). This thread runs in
    the main process and streams those records to W&B with proper step
    indices, plus running-best tracking.
    """

    def __init__(self, metrics_file: str, poll_interval: float = 5.0):
        self.metrics_file = metrics_file
        self.poll_interval = poll_interval
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._byte_offset = 0
        self._step = 0
        self._best_fom = 0.0

    def start(self):
        # Truncate any stale metrics from a previous run
        Path(self.metrics_file).parent.mkdir(parents=True, exist_ok=True)
        with open(self.metrics_file, "w"):
            pass
        self._byte_offset = 0
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop.set()
        if self._thread:
            self._thread.join(timeout=10)

    def _run(self):
        while not self._stop.is_set():
            self._drain()
            self._stop.wait(self.poll_interval)
        # Final drain to catch any records written during shutdown
        self._drain()

    def _drain(self):
        import wandb

        try:
            with open(self.metrics_file, "r") as f:
                f.seek(self._byte_offset)
                new_data = f.read()
                self._byte_offset = f.tell()
        except FileNotFoundError:
            return

        if not new_data:
            return

        for line in new_data.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue

            self._step += 1
            fom = record.get("best_fom", 0)
            self._best_fom = max(self._best_fom, fom)

            wandb.log({
                # Per-evaluation metrics
                "eval/best_fom": fom,
                "eval/mean_fom": record.get("mean_fom", 0),
                "eval/num_valid_codes": record.get("num_valid", 0),
                "eval/num_high_k_codes": record.get("num_high_k", 0),
                "eval/lattices_with_high_k": record.get("lattices_with_high_k", 0),
                "eval/best_encoding_rate": record.get("best_encoding_rate", 0),
                "eval/codes_above_fom6": record.get("num_above_6", 0),
                "eval/codes_above_fom12": record.get("num_above_12", 0),
                "eval/total_candidates": record.get("total_candidates", 0),
                # Running best across all evaluations
                "progress/running_best_fom": self._best_fom,
            }, step=self._step)


# ---------------------------------------------------------------------------
# Evolution runners
# ---------------------------------------------------------------------------

def _run_fresh(config, output_dir: str, iterations: int,
               seed: str = SEED_SOLUTION, evaluator: str = EVALUATOR):
    """Run a fresh evolution using the high-level API."""
    from openevolve import run_evolution

    return run_evolution(
        initial_program=seed,
        evaluator=evaluator,
        config=config,
        iterations=iterations,
        output_dir=output_dir,
        cleanup=False,
    )


def _run_resume(config, output_dir: str, iterations: int, checkpoint_path: str,
                seed: str = SEED_SOLUTION, evaluator: str = EVALUATOR,
                checkpoint_preflight: Any = None):
    """Resume evolution from a checkpoint using the controller directly.

    The high-level run_evolution() API doesn't expose checkpoint_path,
    so we instantiate the OpenEvolve controller ourselves.
    """
    from openevolve.controller import OpenEvolve

    if checkpoint_preflight is None:
        controller_type = OpenEvolve
    else:
        class PreflightedResumeOpenEvolve(OpenEvolve):
            def _load_checkpoint(self, path: str) -> None:
                super()._load_checkpoint(path)
                checkpoint_preflight(self.database)

        controller_type = PreflightedResumeOpenEvolve

    os.makedirs(output_dir, exist_ok=True)
    controller = controller_type(
        initial_program_path=seed,
        evaluation_file=evaluator,
        config=config,
        output_dir=output_dir,
    )
    best_program = asyncio.run(
        controller.run(iterations=iterations, checkpoint_path=checkpoint_path)
    )
    return best_program


def main():
    parser = argparse.ArgumentParser(
        description="Run OpenEvolve evolutionary search for BB codes."
    )
    # --- Model selection ---
    parser.add_argument(
        "--model", type=str, default=None,
        help="Single LiteLLM model identifier (e.g. anthropic/claude-sonnet-4-5-20250514). "
             "Use --models for ensemble.",
    )
    parser.add_argument(
        "--models", type=str, nargs="+", default=None,
        help="Multiple LiteLLM model identifiers for ensemble evolution "
             "(e.g. --models gemini/gemini-2.5-flash anthropic/claude-sonnet-4-5-20250514). "
             "Takes precedence over --model.",
    )
    # --- Run management ---
    parser.add_argument(
        "--run-name", type=str, default=None,
        help="Run name (output goes to results/evolution/<run-name>/). "
             "Default: auto-generated as run_YYYYMMDD_HHMMSS.",
    )
    parser.add_argument(
        "--resume", type=str, default=None, metavar="CHECKPOINT_PATH",
        help="Resume from a checkpoint directory "
             "(e.g. results/evolution/run_xyz/checkpoints/checkpoint_100).",
    )
    # --- Standard options ---
    parser.add_argument(
        "--iterations", type=int, default=100,
        help="Number of evolutionary iterations.",
    )
    parser.add_argument(
        "--api-base", type=str, default=None,
        help="LiteLLM proxy base URL (default: $OPENAI_API_BASE or "
             "$LITELLM_API_BASE or http://localhost:4000/v1).",
    )
    parser.add_argument(
        "--config", type=str, default=None,
        help="Path to OpenEvolve config YAML (default: config.yaml, "
             "or config_noncss.yaml when --noncss is set).",
    )
    parser.add_argument(
        "--output", type=str, default=None,
        help="Explicit output directory (overrides --run-name).",
    )
    parser.add_argument(
        "--completion-marker", type=str, default=None,
        help="Atomically write a success marker after the final checkpoint is durable.",
    )
    parser.add_argument(
        "--slice-witness", type=str, default=None,
        help="Atomically write exact full-slice accounting before the success marker.",
    )
    parser.add_argument(
        "--lifecycle-lease-fd", type=int, default=None,
        help="Inherited locked lifecycle lease descriptor for managed runs.",
    )
    parser.add_argument(
        "--lifecycle-lease-path", type=str, default=None,
        help="Fixed path matching the inherited lifecycle lease descriptor.",
    )
    parser.add_argument(
        "--max-parallel-evaluations", type=int, default=None,
        help="Cap OpenEvolve evaluator workers without increasing the YAML value.",
    )
    parser.add_argument(
        "--wandb", action="store_true",
        help="Enable Weights & Biases tracking.",
    )
    parser.add_argument(
        "--temperature", type=float, default=None,
        help="LLM temperature (default: from config). Use 0 or omit for models "
             "that don't support it (e.g. GPT-5.1 Codex).",
    )
    parser.add_argument(
        "--no-temperature", action="store_true",
        help="Disable sending temperature parameter (for models that reject it).",
    )
    parser.add_argument(
        "--reasoning-effort", type=str, default=None,
        help="Reasoning effort forwarded to all search/evaluator models; "
             "fails rather than silently downgrading when unsupported.",
    )
    parser.add_argument(
        "--humanize-context", type=str, default=None,
        help="Read-only BitLesson/reviewer context appended to the search prompt.",
    )
    parser.add_argument(
        "--codex-cli", action="store_true",
        help="Use authenticated Codex CLI via OpenEvolve init_client.",
    )
    parser.add_argument(
        "--wandb-project", type=str, default="qcode-discovery",
        help="W&B project name.",
    )
    # --- MILP evolution (Campaign 4+) ---
    parser.add_argument(
        "--milp", action="store_true",
        help="Use MILP exact distance instead of BP-OSD. Requires "
             "evaluate_stage2_milp in the evaluator.",
    )
    # --- Non-CSS PBB evolution ---
    parser.add_argument(
        "--noncss", action="store_true",
        help="Evolve non-CSS PBB codes instead of CSS BB codes. "
             "Uses seed_solution_noncss.py, openevolve_evaluator_noncss.py, "
             "and config_noncss.yaml by default.",
    )
    parser.add_argument(
        "--seed", type=str, default=None,
        help="Path to seed solution file (default: evolve/seed_solution.py, "
             "or evolve/seed_solution_milp.py when --milp is set, "
             "or evolve/seed_solution_noncss.py when --noncss is set).",
    )
    args = parser.parse_args()
    managed_values = (
        args.completion_marker,
        args.slice_witness,
        args.lifecycle_lease_fd,
        args.lifecycle_lease_path,
    )
    managed_requested = any(value is not None for value in managed_values)
    if managed_requested and not all(value is not None for value in managed_values):
        parser.error(
            "--completion-marker, --slice-witness, --lifecycle-lease-fd, and "
            "--lifecycle-lease-path must be supplied together"
        )
    if managed_requested and args.humanize_context is None:
        parser.error("--humanize-context is required for managed evolution")
    if managed_requested:
        _validate_lifecycle_lease(
            args.lifecycle_lease_fd, args.lifecycle_lease_path
        )

    # Resolve model list (None means "use config as-is")
    if args.models:
        model_names = args.models
    elif args.model:
        model_names = [args.model]
    else:
        model_names = None  # use whatever is in the config YAML

    # Resolve config path
    if args.config is None:
        args.config = DEFAULT_CONFIG_NONCSS if args.noncss else DEFAULT_CONFIG

    api_base = _resolve_api_base(args)
    output_dir = _resolve_output_dir(args)

    # Propagate run name to evaluator subprocesses via environment variable.
    # OpenEvolve calls evaluate_stage2(program_path) with no way to pass
    # extra args.  _log_code_jsonl reads QCODE_RUN_NAME to route JSONL
    # to the correct run directory.
    run_name = Path(output_dir).name
    os.environ["QCODE_RUN_NAME"] = run_name

    # Resolve seed solution
    if args.seed:
        seed_path = args.seed
    elif args.noncss:
        seed_path = SEED_SOLUTION_NONCSS
    elif args.milp:
        seed_path = SEED_SOLUTION_MILP
    else:
        seed_path = SEED_SOLUTION
    if not Path(seed_path).exists():
        print(f"Error: seed solution not found: {seed_path}")
        sys.exit(1)

    # When --noncss is set, use the non-CSS evaluator directly (no patching needed).
    if args.noncss:
        EVALUATOR_ACTIVE = EVALUATOR_NONCSS
        if not Path(EVALUATOR_ACTIVE).exists():
            print(f"Error: non-CSS evaluator not found: {EVALUATOR_ACTIVE}")
            sys.exit(1)
        print(f"Non-CSS mode: using openevolve_evaluator_noncss.py")
    # When --milp is set, monkey-patch the evaluator to use MILP stage 2.
    # OpenEvolve calls evaluate_stage2() by name from the evaluator module,
    # so we replace it at module level after import.
    elif args.milp:
        import importlib.util
        spec = importlib.util.spec_from_file_location("oe_evaluator", EVALUATOR)
        _ev_mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(_ev_mod)
        if hasattr(_ev_mod, "evaluate_stage2_milp"):
            _ev_mod.evaluate_stage2 = _ev_mod.evaluate_stage2_milp
            _ev_mod.evaluate = _ev_mod.evaluate_stage2_milp
            # Write a patched copy the evaluator will use
            _milp_eval_path = str(Path(output_dir) / "_evaluator_milp.py")
            os.makedirs(output_dir, exist_ok=True)
            eval_source = Path(EVALUATOR).read_text()
            # Append the alias at the end of the file
            patched = eval_source + (
                "\n\n# --- MILP mode: override stage 2 ---\n"
                "evaluate_stage2 = evaluate_stage2_milp\n"
                "evaluate = evaluate_stage2_milp\n"
            )
            Path(_milp_eval_path).write_text(patched)
            # Use the patched evaluator
            EVALUATOR_ACTIVE = _milp_eval_path
            print(f"MILP mode: using evaluate_stage2_milp (patched evaluator)")
        else:
            print("Warning: evaluate_stage2_milp not found in evaluator, "
                  "falling back to BP-OSD")
            EVALUATOR_ACTIVE = EVALUATOR
    else:
        EVALUATOR_ACTIVE = EVALUATOR

    # Validate resume path
    if args.resume and not Path(args.resume).exists():
        print(f"Error: checkpoint path does not exist: {args.resume}")
        sys.exit(1)

    # Start W&B if requested
    wandb_syncer: WandbSyncer | None = None
    if args.wandb:
        try:
            import wandb
            wandb.init(
                project=args.wandb_project,
                config={
                    "models": model_names or "config-default",
                    "iterations": args.iterations,
                    "config": args.config,
                    "api_base": api_base,
                    "resume": args.resume,
                    "output_dir": output_dir,
                },
            )
            print(f"W&B run: {wandb.run.url}")
            # Start background sync from JSONL → W&B
            wandb_syncer = WandbSyncer(METRICS_FILE)
            wandb_syncer.start()
        except ImportError:
            print("wandb not installed. Run: uv sync --group tracking")
            sys.exit(1)

    # Run OpenEvolve
    observer: _SliceObserver | None = None
    source_binding: dict[str, dict[str, Any]] | None = None
    context_identity: dict[str, Any] | None = None
    dependency_identities: dict[str, dict[str, Any]] | None = None
    codex_executable_identity: dict[str, Any] | None = None
    preflight_contract_id: int | None = None
    try:
        context_text: str | None = None
        if managed_requested:
            context_text, context_identity = _read_text_snapshot(
                args.humanize_context, "evolution humanize context"
            )
            dependency_identities = _evaluator_dependency_identities()
            args._humanize_context_text = context_text
        codex_version: str | None = None
        codex_cwd: str | None = None
        codex_executable_mode: int | None = None
        if managed_requested and args.codex_cli:
            (
                codex_executable_identity,
                codex_version,
                codex_cwd,
            ) = _resolve_codex_execution_binding()
            codex_executable_mode = int(codex_executable_identity["mode"])
        config = _build_config(args, api_base, model_names)
        evaluator_timeout = getattr(config.evaluator, "timeout", None)
        if (
            isinstance(evaluator_timeout, bool)
            or not isinstance(evaluator_timeout, (int, float))
            or not math.isfinite(float(evaluator_timeout))
            or evaluator_timeout <= 0
        ):
            raise RuntimeError(
                "config evaluator.timeout must be a positive finite number"
            )
        os.environ["QCODE_EVALUATOR_OUTER_TIMEOUT_S"] = str(
            float(evaluator_timeout)
        )
        if managed_requested and not args.noncss:
            assert dependency_identities is not None
            preflight_contract_id = _winner_preflight_contract_id(
                EVALUATOR_ACTIVE,
                dependency_identities,
            )
            os.environ[WINNER_PREFLIGHT_CONTRACT_ID_ENV] = str(
                preflight_contract_id
            )
        if args.codex_cli:
            from evolve.codex_cli_llm import make_codex_cli_client
            for model_config in config.llm.models + config.llm.evaluator_models:
                model_config.init_client = make_codex_cli_client

        # Startup banner
        active_models = [m.name for m in config.llm.models]
        invocation_binding = {
            "model_names": active_models,
            "reasoning_effort": args.reasoning_effort,
            "codex_cli": bool(args.codex_cli),
            "max_parallel_evaluations": config.evaluator.parallel_evaluations,
            "api_base": api_base,
            "temperature_disabled": bool(args.no_temperature),
            "codex_version": codex_version,
            "codex_cwd": codex_cwd,
            "codex_executable_mode": codex_executable_mode,
        }
        backend_path = (
            Path(__file__).resolve().parent / "codex_cli_llm.py"
            if args.codex_cli
            else None
        )
        print(f"\nStarting evolution:")
        if len(active_models) == 1:
            print(f"  Model: {active_models[0]}")
        else:
            print(f"  Ensemble ({len(active_models)} models):")
            for name in active_models:
                print(f"    - {name}")
        print(f"  Iterations: {args.iterations}")
        parallel = config.evaluator.parallel_evaluations
        if args.max_parallel_evaluations is None:
            print(f"  Parallel evaluations: {parallel}")
        else:
            print(
                f"  Parallel evaluations: {parallel} "
                f"(cap: {args.max_parallel_evaluations})"
            )
        print(f"  Model backend: {'Codex CLI' if args.codex_cli else api_base}")
        print(f"  Seed: {seed_path}")
        if args.noncss:
            print(f"  Mode: Non-CSS PBB codes")
            print(f"  Distance: BP-OSD multi-channel (non-CSS)")
        elif args.milp:
            print(f"  Distance: MILP (exact or upper bound)")
        else:
            print(f"  Distance: BP-OSD (estimate)")
        print(f"  Output: {output_dir}")
        if managed_requested:
            base_iteration = _checkpoint_last_iteration(args.resume)
            slice_context = _verified_slice_controller(
                base_iteration,
                args.iterations,
                expected_preflight_contract_id=preflight_contract_id,
                checkpoint_preflight_required=(
                    args.resume is not None
                    and preflight_contract_id is not None
                ),
            )
        else:
            slice_context = nullcontext((None, None))
        with slice_context as verification:
            if managed_requested:
                observer, source_binding = verification
            if args.resume:
                print(f"  Resuming from: {args.resume}")
            print()

            if args.resume:
                checkpoint_preflight = None
                if preflight_contract_id is not None:
                    assert observer is not None

                    def checkpoint_preflight(database: Any) -> None:
                        _validate_loaded_checkpoint_database(
                            database,
                            args.resume,
                        )
                        report = _backfill_checkpoint_programs(
                            database,
                            evaluator_path=EVALUATOR_ACTIVE,
                            expected_contract_id=preflight_contract_id,
                            max_workers=config.evaluator.parallel_evaluations,
                            wall_timeout=_winner_preflight_wall_timeout(
                                evaluator_timeout
                            ),
                        )
                        observer.record_checkpoint_preflight(report)

                best_program = _run_resume(
                    config, output_dir, args.iterations, args.resume,
                    seed=seed_path, evaluator=EVALUATOR_ACTIVE,
                    checkpoint_preflight=checkpoint_preflight,
                )
                print(f"\nEvolution complete!")
                if best_program:
                    score = (best_program.metrics or {}).get("combined_score", 0)
                    print(f"  Best score: {score:.4f}")
                    # Save best program
                    best_path = Path(output_dir) / "best_generate_candidates.py"
                    best_path.parent.mkdir(parents=True, exist_ok=True)
                    best_path.write_text(best_program.code)
                    print(f"  Best program: {best_path}")
                print(f"  Output: {output_dir}")
            else:
                result = _run_fresh(config, output_dir, args.iterations,
                                    seed=seed_path, evaluator=EVALUATOR_ACTIVE)

                print(f"\nEvolution complete!")
                print(f"  Best score: {result.best_score:.4f}")
                print(f"  Output: {result.output_dir}")

                # Save best program
                if result.best_code:
                    best_path = Path(output_dir) / "best_generate_candidates.py"
                    best_path.parent.mkdir(parents=True, exist_ok=True)
                    best_path.write_text(result.best_code)
                    print(f"  Best program: {best_path}")

                    if args.wandb:
                        try:
                            import wandb
                            artifact = wandb.Artifact("best-program", type="code")
                            artifact.add_file(str(best_path))
                            wandb.log_artifact(artifact)
                        except Exception:
                            pass

        if managed_requested:
            assert (
                observer is not None
                and source_binding is not None
                and context_identity is not None
                and dependency_identities is not None
            )
            result_checkpoint, witness_identity = _write_slice_witness(
                args.slice_witness,
                observer=observer,
                source_binding=source_binding,
                output_dir=output_dir,
                resume_checkpoint=args.resume,
                iterations=args.iterations,
                config_path=args.config,
                seed_path=seed_path,
                evaluator_path=EVALUATOR_ACTIVE,
                context_path=args.humanize_context,
                context_identity=context_identity,
                dependency_identities=dependency_identities,
                backend_path=backend_path,
                codex_executable_identity=codex_executable_identity,
                invocation=invocation_binding,
            )
            _write_completion_marker(
                args.completion_marker,
                output_dir=output_dir,
                resume_checkpoint=args.resume,
                iterations=args.iterations,
                config_path=args.config,
                seed_path=seed_path,
                evaluator_path=EVALUATOR_ACTIVE,
                context_path=args.humanize_context,
                context_identity=context_identity,
                dependency_identities=dependency_identities,
                backend_path=backend_path,
                codex_executable_identity=codex_executable_identity,
                invocation=invocation_binding,
                result_checkpoint=result_checkpoint,
                slice_witness=witness_identity,
            )

    except SystemExit as exc:
        if managed_requested and (
            exc.code in (None, 0)
            or (observer is not None and observer.shutdown_requested)
        ):
            raise SystemExit(130) from exc
        raise
    except ImportError:
        print("openevolve not installed. Run: uv sync --group evolve")
        sys.exit(1)
    except KeyboardInterrupt:
        print("\nEvolution interrupted by user.")
        raise SystemExit(130)
    finally:
        if wandb_syncer:
            wandb_syncer.stop()
        if args.wandb:
            try:
                import wandb
                wandb.finish()
            except Exception:
                pass


if __name__ == "__main__":
    main()
