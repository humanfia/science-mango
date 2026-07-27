"""Fast pinned and strict rerun integrity checks for the known-answer gate."""

from __future__ import annotations

import hashlib
import importlib.metadata
import json
import math
import platform
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from evaluation.final_gate import validate_known_answer_artifact


def _package_version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def current_environment() -> dict[str, str | None]:
    return {
        "python": platform.python_version(),
        "numpy": _package_version("numpy"),
        "scipy": _package_version("scipy"),
        "qldpc": _package_version("qldpc"),
    }


def file_sha256(path: Path | str) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def semantic_payload(artifact: dict[str, Any]) -> dict[str, Any]:
    """Remove timestamps, wall times, and timeout policy from baseline proof data."""
    baselines = []
    stable_milp_fields = (
        "d_x", "d_z", "k", "exact", "d_x_computed",
        "num_logicals_checked", "logicals_optimal",
        "logicals_incumbent", "total_logicals",
    )
    for row in artifact.get("baselines", []):
        milp = row.get("milp") or {}
        baselines.append({
            "label": row.get("label"),
            "ell": row.get("ell"),
            "m": row.get("m"),
            "A_terms": row.get("A_terms"),
            "B_terms": row.get("B_terms"),
            "expected": row.get("expected"),
            "observed": row.get("observed"),
            "matrix_sha256": row.get("matrix_sha256"),
            "checks": row.get("checks"),
            "status": row.get("status"),
            "milp": {name: milp.get(name) for name in stable_milp_fields},
        })
    return {
        "schema_version": artifact.get("schema_version"),
        "gate": artifact.get("gate"),
        "challenge_source": artifact.get("challenge_source"),
        "environment": artifact.get("environment"),
        "baselines": baselines,
    }


def semantic_sha256(artifact: dict[str, Any]) -> str:
    encoded = json.dumps(
        semantic_payload(artifact),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _positive_timeout_seconds(value: Any, name: str) -> int:
    """Normalize the integer timeout accepted by the baseline runner."""
    if isinstance(value, bool):
        raise ValueError(f"{name} must be a positive finite integer")
    if isinstance(value, int):
        if value <= 0:
            raise ValueError(f"{name} must be a positive finite integer")
        return value
    try:
        numeric = float(value)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValueError(f"{name} must be a positive finite integer") from exc
    if not math.isfinite(numeric) or numeric <= 0 or not numeric.is_integer():
        raise ValueError(f"{name} must be a positive finite integer")
    return int(numeric)


def _strict_wall_timeout(total_timeout_per_code: int) -> int:
    """Allow three per-code budgets plus a modest process/serialization margin."""
    margin = max(60, (total_timeout_per_code + 19) // 20)
    return 3 * total_timeout_per_code + margin


def _output_tail(output: str | bytes | None) -> str:
    if output is None:
        return ""
    if isinstance(output, bytes):
        output = output.decode(errors="replace")
    return str(output)[-2000:]


def _strict_failure(
    fast: dict[str, Any],
    *,
    command: list[str],
    wall_timeout: int,
    failures: list[str],
    output: str | bytes | None = None,
) -> dict[str, Any]:
    return {
        **fast,
        "passed": False,
        "mode": "strict",
        "rerun_command": command,
        "rerun_wall_timeout_s": wall_timeout,
        "rerun_output_tail": _output_tail(output),
        "failures": failures,
    }


def check_fast(
    artifact_path: Path | str,
    trust_path: Path | str,
) -> dict[str, Any]:
    failures: list[str] = []
    artifact_path, trust_path = Path(artifact_path), Path(trust_path)
    try:
        validation = validate_known_answer_artifact(artifact_path)
        failures.extend(validation.get("failures") or [])
        artifact = json.loads(artifact_path.read_text())
        trust = json.loads(trust_path.read_text())
    except (
        OSError, UnicodeError, json.JSONDecodeError,
        AttributeError, TypeError, ValueError,
    ) as exc:
        return {
            "passed": False,
            "mode": "fast",
            "failures": failures + [f"integrity input unavailable or invalid: {exc}"],
        }
    if not isinstance(artifact, dict) or not isinstance(trust, dict):
        return {
            "passed": False,
            "mode": "fast",
            "failures": failures + [
                "integrity artifact and trust manifest must be JSON objects"
            ],
        }
    if trust.get("schema_version") != 1:
        failures.append("trust manifest schema_version must be 1")
    try:
        actual_file_sha = file_sha256(artifact_path)
        actual_semantic_sha = semantic_sha256(artifact)
    except (OSError, UnicodeError, TypeError, ValueError) as exc:
        return {
            "passed": False,
            "mode": "fast",
            "failures": failures + [f"integrity hashing failed: {exc}"],
        }
    if actual_file_sha != trust.get("artifact_sha256"):
        failures.append("known-answer artifact SHA-256 is not repository-pinned")
    if actual_semantic_sha != trust.get("semantic_sha256"):
        failures.append("known-answer semantic SHA-256 is not repository-pinned")
    environment = current_environment()
    if artifact.get("environment") != environment:
        failures.append("known-answer artifact environment differs from verifier")
    if trust.get("environment") != environment:
        failures.append("repository trust environment differs from verifier")
    return {
        "passed": not failures,
        "mode": "fast",
        "artifact_sha256": actual_file_sha,
        "semantic_sha256": actual_semantic_sha,
        "environment": environment,
        "failures": failures,
    }


def check_strict(
    artifact_path: Path | str,
    trust_path: Path | str,
    *,
    timeout_per_logical: int = 300,
    total_timeout_per_code: int = 7200,
) -> dict[str, Any]:
    """Rerun all three baselines, then compare stable evidence to the pin."""
    timeout_per_logical = _positive_timeout_seconds(
        timeout_per_logical, "timeout_per_logical",
    )
    total_timeout_per_code = _positive_timeout_seconds(
        total_timeout_per_code, "total_timeout_per_code",
    )
    wall_timeout = _strict_wall_timeout(total_timeout_per_code)
    fast = check_fast(artifact_path, trust_path)
    project = Path(__file__).resolve().parent.parent
    failures = list(fast.get("failures") or [])
    if fast.get("passed") is not True:
        failures.append("strict rerun skipped because fast pinned integrity failed")
        return _strict_failure(
            fast,
            command=[],
            wall_timeout=wall_timeout,
            failures=failures,
        )
    try:
        temporary = tempfile.TemporaryDirectory(prefix="qcode-known-answer-")
    except OSError as exc:
        failures.append(f"strict temporary directory unavailable: {exc}")
        return _strict_failure(
            fast,
            command=[],
            wall_timeout=wall_timeout,
            failures=failures,
        )
    with temporary as directory:
        rerun_path = Path(directory) / "known_answer_gate.json"
        command = [
            sys.executable,
            str(project / "tests" / "verify_known_answer_gate.py"),
            "--output", str(rerun_path),
            "--timeout-per-logical", str(timeout_per_logical),
            "--total-timeout-per-code", str(total_timeout_per_code),
        ]
        try:
            completed = subprocess.run(
                command, cwd=project, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=wall_timeout,
            )
        except subprocess.TimeoutExpired as exc:
            failures.append(
                f"strict known-answer rerun exceeded wall timeout "
                f"({wall_timeout}s)"
            )
            return _strict_failure(
                fast,
                command=command,
                wall_timeout=wall_timeout,
                failures=failures,
                output=exc.stdout if exc.stdout is not None else exc.output,
            )
        except OSError as exc:
            failures.append(f"strict known-answer rerun could not start: {exc}")
            return _strict_failure(
                fast,
                command=command,
                wall_timeout=wall_timeout,
                failures=failures,
            )
        if completed.returncode != 0 or not rerun_path.is_file():
            failures.append(
                "strict known-answer rerun failed: "
                + _output_tail(completed.stdout)
            )
            return _strict_failure(
                fast,
                command=command,
                wall_timeout=wall_timeout,
                failures=failures,
                output=completed.stdout,
            )
        try:
            rerun = json.loads(rerun_path.read_text())
            trust = json.loads(Path(trust_path).read_text())
        except (OSError, UnicodeError, json.JSONDecodeError) as exc:
            failures.append(f"strict rerun output or trust is invalid: {exc}")
            return _strict_failure(
                fast,
                command=command,
                wall_timeout=wall_timeout,
                failures=failures,
                output=completed.stdout,
            )
        if not isinstance(rerun, dict) or not isinstance(trust, dict):
            failures.append("strict rerun output and trust must be JSON objects")
            return _strict_failure(
                fast,
                command=command,
                wall_timeout=wall_timeout,
                failures=failures,
                output=completed.stdout,
            )
        try:
            validation = validate_known_answer_artifact(rerun_path)
            failures.extend(validation.get("failures") or [])
            rerun_semantic_sha = semantic_sha256(rerun)
        except (
            OSError, UnicodeError, json.JSONDecodeError,
            AttributeError, TypeError, ValueError,
        ) as exc:
            failures.append(f"strict rerun validation failed: {exc}")
            return _strict_failure(
                fast,
                command=command,
                wall_timeout=wall_timeout,
                failures=failures,
                output=completed.stdout,
            )
        if rerun_semantic_sha != trust.get("semantic_sha256"):
            failures.append("strict rerun semantic evidence differs from repository pin")
        return {
            **fast,
            "passed": not failures,
            "mode": "strict",
            "rerun_command": command,
            "rerun_wall_timeout_s": wall_timeout,
            "rerun_semantic_sha256": rerun_semantic_sha,
            "rerun_output_tail": _output_tail(completed.stdout),
            "failures": failures,
        }


def check_known_answer_integrity(
    artifact_path: Path | str,
    trust_path: Path | str,
    *,
    mode: str,
    timeout_per_logical: int = 300,
    total_timeout_per_code: int = 7200,
) -> dict[str, Any]:
    if mode == "fast":
        return check_fast(artifact_path, trust_path)
    if mode == "strict":
        return check_strict(
            artifact_path, trust_path,
            timeout_per_logical=timeout_per_logical,
            total_timeout_per_code=total_timeout_per_code,
        )
    raise ValueError("known-answer mode must be 'fast' or 'strict'")
