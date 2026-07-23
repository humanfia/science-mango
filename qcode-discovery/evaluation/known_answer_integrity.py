"""Fast pinned and strict rerun integrity checks for the known-answer gate."""

from __future__ import annotations

import hashlib
import importlib.metadata
import json
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


def check_fast(
    artifact_path: Path | str,
    trust_path: Path | str,
) -> dict[str, Any]:
    failures: list[str] = []
    artifact_path, trust_path = Path(artifact_path), Path(trust_path)
    validation = validate_known_answer_artifact(artifact_path)
    failures.extend(validation["failures"])
    try:
        artifact = json.loads(artifact_path.read_text())
        trust = json.loads(trust_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {
            "passed": False,
            "mode": "fast",
            "failures": failures + [f"integrity input unavailable or invalid: {exc}"],
        }
    if trust.get("schema_version") != 1:
        failures.append("trust manifest schema_version must be 1")
    actual_file_sha = file_sha256(artifact_path)
    actual_semantic_sha = semantic_sha256(artifact)
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
    fast = check_fast(artifact_path, trust_path)
    project = Path(__file__).resolve().parent.parent
    with tempfile.TemporaryDirectory(prefix="qcode-known-answer-") as directory:
        rerun_path = Path(directory) / "known_answer_gate.json"
        command = [
            sys.executable,
            str(project / "tests" / "verify_known_answer_gate.py"),
            "--output", str(rerun_path),
            "--timeout-per-logical", str(timeout_per_logical),
            "--total-timeout-per-code", str(total_timeout_per_code),
        ]
        completed = subprocess.run(
            command, cwd=project, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        failures = list(fast["failures"])
        if completed.returncode != 0 or not rerun_path.is_file():
            failures.append(
                "strict known-answer rerun failed: "
                + completed.stdout[-2000:]
            )
            return {
                **fast,
                "passed": False,
                "mode": "strict",
                "rerun_command": command,
                "failures": failures,
            }
        rerun = json.loads(rerun_path.read_text())
        validation = validate_known_answer_artifact(rerun_path)
        failures.extend(validation["failures"])
        trust = json.loads(Path(trust_path).read_text())
        rerun_semantic_sha = semantic_sha256(rerun)
        if rerun_semantic_sha != trust.get("semantic_sha256"):
            failures.append("strict rerun semantic evidence differs from repository pin")
        return {
            **fast,
            "passed": not failures,
            "mode": "strict",
            "rerun_semantic_sha256": rerun_semantic_sha,
            "rerun_output_tail": completed.stdout[-2000:],
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
