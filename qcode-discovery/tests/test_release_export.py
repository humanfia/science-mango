"""Tests for fail-closed export of five-stage evidence snapshots."""

from __future__ import annotations

import fcntl
import hashlib
import importlib.util
import json
import marshal
import os
import py_compile
import sys
from pathlib import Path

import pytest

import humanize.release_export as release_export_module
from evaluation.proof_runtime import (
    known_answer_environment,
    proof_runtime_fingerprint,
)
from evaluation.release_gate import canonical_sha256, validate_release_manifest
from humanize.release_export import (
    ReleaseExportError,
    ReleaseNotExportableError,
    export_release,
)


@pytest.fixture(autouse=True)
def _stable_release_runtime_probe(monkeypatch):
    """Release semantics use a stable valid worker; probe attacks test elsewhere."""

    runtime = proof_runtime_fingerprint()
    provenance = {
        "runtime": runtime,
        "interpreter": runtime["interpreter"],
    }
    monkeypatch.setattr(
        release_export_module,
        "probe_python_runtime",
        lambda *_args, **_kwargs: provenance,
    )


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, sort_keys=True, ensure_ascii=False, indent=2) + "\n"
    )


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(
            json.dumps(row, sort_keys=True, ensure_ascii=False) + "\n" for row in rows
        )
    )


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _source_file_identity(path: Path) -> dict:
    metadata = path.lstat()
    return {
        "sha256": _file_sha256(path),
        "bytes": metadata.st_size,
        "mode": metadata.st_mode & 0o7777,
        "device": metadata.st_dev,
        "inode": metadata.st_ino,
        "mtime_ns": metadata.st_mtime_ns,
        "ctime_ns": metadata.st_ctime_ns,
    }


def _payload_sha256(value: dict) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _pipeline_fingerprint(value: object) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        default=str,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _win_gate(n: int, k: int, d: int) -> dict:
    fom = k * d * d / n
    return {
        "schema_version": 1,
        "gate": "qldpc-challenge-final",
        "accepted": True,
        "checks": {
            "challenge_win": True,
            "reported_fom_matches": True,
        },
        "failures": [],
        "candidate": {"n": n, "k": k, "d": d, "fom": fom},
        "win": {
            "passed": True,
            "fom": fom,
            "reasons": ["fom_strictly_above_12"],
        },
    }


def _pipeline_root(repo: Path, run_id: str) -> Path:
    return repo / "results" / "humanize" / "pipelines" / run_id


def _strict_stage_binding(
    repo: Path,
    root: Path,
    config: dict,
) -> tuple[list[str], dict, str]:
    stage4_certificates = root / "artifacts" / "stage4-certificates.jsonl"
    stage5 = root / "artifacts" / "stage5-final-gate.json"
    finalizer = repo / "scripts" / "finalize_challenge.py"
    strict_runner = repo / "tests" / "verify_known_answer_gate.py"
    registry = repo / "results" / "known_code_registry.json"
    source_files = sorted((repo / "evaluation").rglob("*.py")) + [
        repo / "humanize" / "pipeline.py",
        finalizer,
        strict_runner,
        registry,
    ]
    source_fingerprint = _pipeline_fingerprint(
        {
            str(path): _source_file_identity(path)
            for path in sorted(set(source_files))
        }
    )
    runtime = proof_runtime_fingerprint()
    runtime_provenance = {
        "runtime": runtime,
        "interpreter": runtime["interpreter"],
    }
    stage_config = {
        "controller_source_sha256": _file_sha256(
            repo / "humanize" / "pipeline.py"
        ),
        "mode": "strict",
        "source_fingerprint": source_fingerprint,
        "known_code_registry_sha256": _file_sha256(registry),
        "strict_runner_sha256": _file_sha256(strict_runner),
        "proof_runtime": runtime_provenance["runtime"],
        "proof_interpreter": runtime_provenance["interpreter"],
        "known_answer_timeout_per_logical": config[
            "known_answer_timeout_per_logical"
        ],
        "known_answer_total_timeout": config["known_answer_total_timeout"],
        "verification_timeout_per_logical": config[
            "verification_timeout_per_logical"
        ],
        "verification_total_timeout": config["verification_total_timeout"],
        "verification_solver_workers": config["certificate_solver_workers"],
    }
    command = [
        config["python_executable"],
        "-I",
        "-B",
        str(finalizer),
        str(stage4_certificates),
        "--known-answer-artifact",
        config["known_answer_artifact"],
        "--known-answer-trust",
        config["known_answer_trust"],
        "--known-answer-timeout-per-logical",
        str(config["known_answer_timeout_per_logical"]),
        "--known-answer-total-timeout",
        str(config["known_answer_total_timeout"]),
        "--verification-timeout-per-logical",
        str(config["verification_timeout_per_logical"]),
        "--verification-total-timeout",
        str(config["verification_total_timeout"]),
        "--verification-solver-workers",
        str(config["certificate_solver_workers"]),
        "--verification-state-dir",
        str(root / "solver-state" / "strict-verification"),
        "--resume" if config["resume"] else "--no-resume",
        "--output",
        str(stage5),
    ]
    return (
        command,
        stage_config,
        _pipeline_fingerprint(
            {"command": command, "stage_config": stage_config}
        ),
    )


def _refresh_state_hashes(repo: Path, run_id: str) -> None:
    root = _pipeline_root(repo, run_id)
    state_path = root / "state.json"
    state = json.loads(state_path.read_text())
    stage4_certificates = root / "artifacts" / "stage4-certificates.jsonl"
    stage4_summary = root / "artifacts" / "stage4-summary.json"
    stage5 = root / "artifacts" / "stage5-final-gate.json"
    known_answer = repo / "results" / "known_answer_gate.json"
    known_code_registry = repo / "results" / "known_code_registry.json"
    trust = repo / "results" / "known_answer_trust.json"
    finalizer = repo / "scripts" / "finalize_challenge.py"
    strict_runner = repo / "tests" / "verify_known_answer_gate.py"
    state["stages"]["stage4_certificate_merge"]["output_hashes"] = {
        str(stage4_certificates): _file_sha256(stage4_certificates),
        str(stage4_summary): _file_sha256(stage4_summary),
    }
    state["stages"]["stage5_strict_gate"]["output_hashes"] = {
        str(stage5): _file_sha256(stage5),
    }
    state["stages"]["stage5_strict_gate"]["input_hashes"] = {
        str(stage4_certificates): _file_sha256(stage4_certificates),
        str(known_answer): _file_sha256(known_answer),
        str(known_code_registry): _file_sha256(known_code_registry),
        str(trust): _file_sha256(trust),
        str(finalizer): _file_sha256(finalizer),
        str(strict_runner): _file_sha256(strict_runner),
    }
    _write_json(state_path, state)


def _make_synthetic_completed_win(
    tmp_path: Path,
    *,
    run_id: str = "release-export-test",
    certificate_count: int = 2,
    base_n: int = 72,
    logical_k: int = 16,
    distance: int = 8,
) -> tuple[Path, str]:
    repo = tmp_path / "qcode"
    results = repo / "results"
    root = _pipeline_root(repo, run_id)
    artifacts = root / "artifacts"
    source_certificates = root / "solver-state" / "certificates"
    source_verifications = root / "solver-state" / "verifications"
    source_certificates.mkdir(parents=True)
    source_verifications.mkdir(parents=True)
    artifacts.mkdir(parents=True)
    (root / "pipeline.lock").write_text("")
    scripts = repo / "scripts"
    scripts.mkdir(parents=True)
    (scripts / "finalize_challenge.py").write_text("# fake finalizer\n")
    tests = repo / "tests"
    tests.mkdir(parents=True)
    (tests / "verify_known_answer_gate.py").write_text("# fake strict runner\n")
    evaluation = repo / "evaluation"
    evaluation.mkdir()
    (evaluation / "verifier.py").write_text("# fake Stage 5 verifier\n")
    humanize = repo / "humanize"
    humanize.mkdir()
    (humanize / "pipeline.py").write_text("# fake pipeline controller\n")

    known_answer = results / "known_answer_gate.json"
    known_answer.parent.mkdir(parents=True, exist_ok=True)
    known_answer.write_text('{"gate":"known-answer","passed":true}\n')
    _write_json(results / "known_code_registry.json", {"schema_version": 1})
    known_answer_sha = _file_sha256(known_answer)
    environment = known_answer_environment()
    trust = {
        "schema_version": 1,
        "artifact_sha256": known_answer_sha,
        "semantic_sha256": "a" * 64,
        "environment": environment,
    }
    trust_path = results / "known_answer_trust.json"
    _write_json(trust_path, trust)

    certificates: list[dict] = []
    summary_entries: list[dict] = []
    evaluations: list[dict] = []
    for index in range(certificate_count):
        digest = f"canonical-{index}"
        n, k, d = base_n + index, logical_k, distance
        fom = k * d * d / n
        certificate = {
            "schema_version": 1,
            "certificate_type": "qldpc-css-bb-exact",
            "formulation": "test",
            "known_answer": {"artifact_sha256": known_answer_sha},
            "passed": True,
            "claim": {
                "canonical_digest": digest,
                "n": n,
                "k": k,
                "d": d,
                "fom": fom,
            },
            "milp": {
                "exact": True,
                "expected_directions": 2 * k,
                "completed_directions": 2 * k,
                "distance": d,
                "directions": [
                    {"success": True, "mip_gap": 0.0, "objective": d}
                    for _ in range(2 * k)
                ],
            },
            "final_gate": _win_gate(n, k, d),
        }
        certificate["certificate_sha256"] = canonical_sha256(
            certificate,
            omit="certificate_sha256",
        )
        certificates.append(certificate)

        certificate_path = source_certificates / f"{digest}.json"
        _write_json(certificate_path, certificate)
        payload_sha = _payload_sha256(certificate)
        verification_path = source_verifications / f"{digest}.json"
        envelope = {
            "schema_version": 2,
            "kind": "qldpc-certificate-verification-cache",
            "canonical_digest": digest,
            "known_answer_sha256": known_answer_sha,
            "certificate_sha256": certificate["certificate_sha256"],
            "certificate_payload_sha256": payload_sha,
            "verification": {
                "passed": True,
                "final_gate": {"accepted": True},
            },
        }
        _write_json(verification_path, envelope)
        summary_entries.append(
            {
                "source_stage": (
                    "stage2_sector_audit" if index == 0 else "stage3_direction_audit"
                ),
                "canonical_digest": digest,
                "certificate_path": str(certificate_path),
                "verification_path": str(verification_path),
                "certificate_sha256": certificate["certificate_sha256"],
                "certificate_payload_sha256": payload_sha,
                "file_sha256": _file_sha256(certificate_path),
                "verification_file_sha256": _file_sha256(verification_path),
            }
        )
        evaluations.append(
            {
                "source_index": index,
                "claim": certificate["claim"],
                "certificate_sha256": certificate["certificate_sha256"],
                "certificate_payload_sha256": _payload_sha256(certificate),
                "disposition": "ACCEPTED",
                "result": {
                    "passed": True,
                    "replay_complete": True,
                    "checks": {
                        "schema": True,
                        "certificate_sha256": True,
                        "known_answer_sha256": True,
                        "matrix_sha256": True,
                        "direction_count": True,
                        "stored_direction_evidence": True,
                        "milp_rerun": True,
                        "distance_recomputed": True,
                        "final_gate": True,
                        "certificate_passed_flag": True,
                    },
                    "failures": [],
                    "distance": d,
                    "directions_verified": 2 * k,
                    "directions_total": 2 * k,
                    "final_gate": _win_gate(n, k, d),
                },
            }
        )

    stage4_certificates = artifacts / "stage4-certificates.jsonl"
    _write_jsonl(stage4_certificates, certificates)
    stage4_summary = artifacts / "stage4-summary.json"
    _write_json(
        stage4_summary,
        {
            "schema_version": 1,
            "gate": "qcode-five-stage-certificate-merge",
            "generated_at": "2026-07-27T00:00:00+00:00",
            "passed": True,
            "verified_certificates": certificate_count,
            "certificate_output": str(stage4_certificates),
            "entries": summary_entries,
            "routing": "STRICT_GATE",
        },
    )
    integrity = {
        "passed": True,
        "mode": "strict",
        "artifact_sha256": known_answer_sha,
        "semantic_sha256": trust["semantic_sha256"],
        "rerun_semantic_sha256": trust["semantic_sha256"],
        "environment": environment,
        "failures": [],
    }
    stage5 = artifacts / "stage5-final-gate.json"
    _write_json(
        stage5,
        {
            "schema_version": 1,
            "gate": "qldpc-challenge-final-batch",
            "generated_at": "2026-07-27T00:01:00+00:00",
            "passed": True,
            "outcome": "WIN",
            "known_answer_integrity": integrity,
            "summary": {
                "accepted": certificate_count,
                "rejected": 0,
                "incomplete": 0,
                "total": certificate_count,
            },
            "evaluations": evaluations,
        },
    )
    pipeline_config = {
        "repo_dir": str(repo),
        "run_id": run_id,
        "known_answer_artifact": str(known_answer),
        "known_answer_trust": str(trust_path),
        "python_executable": sys.executable,
        "resume": True,
        "certificate_solver_workers": 1,
        "known_answer_timeout_per_logical": 300,
        "known_answer_total_timeout": 7200,
        "verification_timeout_per_logical": 300,
        "verification_total_timeout": 7200,
    }
    strict_command, strict_stage_config, strict_fingerprint = (
        _strict_stage_binding(repo, root, pipeline_config)
    )
    state = {
        "schema_version": 1,
        "gate": "qcode-humanize-five-stage-pipeline",
        "run_id": run_id,
        "status": "COMPLETED_WIN",
        "active_stage": None,
        "config_fingerprint": "c" * 64,
        "completed_at": "2026-07-27T00:02:00+00:00",
        "config": pipeline_config,
        "stages": {
            "stage1_search": {
                "ordinal": 1,
                "attempt": 1,
                "stage_fingerprint": "1" * 64,
                "command": ["internal:stage1"],
                "command_sha256": _pipeline_fingerprint(["internal:stage1"]),
                "status": "COMPLETED",
                "machine_status": "COMPLETED",
                "exit_code": 0,
            },
            "stage2_sector_audit": {
                "ordinal": 2,
                "attempt": 1,
                "stage_fingerprint": "2" * 64,
                "command": ["internal:stage2"],
                "command_sha256": _pipeline_fingerprint(["internal:stage2"]),
                "status": "COMPLETED",
                "machine_status": "COMPLETED",
                "exit_code": 0,
            },
            "stage3_direction_audit": {
                "ordinal": 3,
                "attempt": 1,
                "stage_fingerprint": "3" * 64,
                "command": ["internal:stage3"],
                "command_sha256": _pipeline_fingerprint(["internal:stage3"]),
                "status": "COMPLETED",
                "machine_status": "COMPLETED",
                "exit_code": 0,
            },
            "stage4_certificate_merge": {
                "ordinal": 4,
                "attempt": 1,
                "stage_fingerprint": "d" * 64,
                "command": ["internal:stage4"],
                "command_sha256": _pipeline_fingerprint(["internal:stage4"]),
                "status": "COMPLETED",
                "machine_status": "COMPLETED",
                "exit_code": 0,
            },
            "stage5_strict_gate": {
                "ordinal": 5,
                "attempt": 1,
                "stage_config": strict_stage_config,
                "stage_fingerprint": strict_fingerprint,
                "command": strict_command,
                "command_sha256": _pipeline_fingerprint(strict_command),
                "status": "COMPLETED",
                "machine_status": "COMPLETED",
                "exit_code": 0,
            },
        },
        "result": {
            "verified_certificates": certificate_count,
            "stage4_summary": str(stage4_summary),
            "strict_gate": str(stage5),
        },
    }
    state["config_fingerprint"] = _pipeline_fingerprint(state["config"])
    _write_json(root / "state.json", state)
    _refresh_state_hashes(repo, run_id)
    return repo, run_id


def test_export_release_builds_bound_synthetic_snapshot_and_is_idempotent(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)

    first = export_release(repo_dir=repo, run_id=run_id)

    assert first["status"] == "exported"
    assert first["certificates"] == 2
    manifest_path = Path(first["manifest"])
    manifest = json.loads(manifest_path.read_text())
    assert manifest["generated_at"] == "2026-07-27T00:02:00+00:00"
    source = manifest["source_pipeline"]
    state = json.loads((_pipeline_root(repo, run_id) / "state.json").read_text())
    assert source["config_fingerprint"] == state["config_fingerprint"]
    assert set(source["stages"]) == {
        "stage1_search",
        "stage2_sector_audit",
        "stage3_direction_audit",
        "stage4_certificate_merge",
        "stage5_strict_gate",
    }
    assert len(source["stage4"]["certificates_sha256"]) == 64
    assert len(source["stage5"]["final_gate_sha256"]) == 64
    assert len(source["stage5"]["controller_source_sha256"]) == 64
    assert len(source["stage5"]["source_fingerprint"]) == 64
    assert len(source["stage5"]["known_code_registry_sha256"]) == 64
    assert len(source["stage5"]["strict_runner_sha256"]) == 64
    runtime = proof_runtime_fingerprint()
    runtime_provenance = {
        "runtime": runtime,
        "interpreter": runtime["interpreter"],
    }
    assert source["stage5"]["proof_runtime"] == runtime_provenance["runtime"]
    assert (
        source["stage5"]["proof_interpreter"]
        == runtime_provenance["interpreter"]
    )
    assert manifest["source_total"] == 2
    assert manifest["accepted"] == 2
    assert manifest["rejected"] == 0
    assert manifest["incomplete"] == 0
    assert (
        manifest["stage5_artifact_sha256"]
        == source["stage5"]["final_gate_sha256"]
    )
    assert all(
        entry["file"].startswith("certificates/")
        and not Path(entry["file"]).is_absolute()
        and ".." not in Path(entry["file"]).parts
        for entry in manifest["certificates"]
    )
    validation = validate_release_manifest(
        manifest_path,
        known_answer_trust_path=repo / "results" / "known_answer_trust.json",
        expected_run_id=run_id,
    )
    assert validation["passed"], validation["failures"]

    second = export_release(repo_dir=repo, run_id=run_id)

    assert second == {**first, "status": "already-exported"}


@pytest.mark.parametrize(
    ("package", "classification"),
    [
        ("ortools", "STAGE5_PROVENANCE_MISMATCH"),
        ("numpy", "TRUST_INVALID"),
    ],
)
def test_export_release_rejects_stale_proof_runtime(
    tmp_path,
    monkeypatch,
    package,
    classification,
):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    changed = json.loads(json.dumps(proof_runtime_fingerprint()))
    changed["packages"][package] = "runtime-changed"
    changed["package_artifacts"][package]["version"] = "runtime-changed"
    state = json.loads(
        (
            _pipeline_root(repo, run_id)
            / "state.json"
        ).read_text()
    )
    interpreter = state["stages"]["stage5_strict_gate"]["stage_config"][
        "proof_interpreter"
    ]
    changed["interpreter"] = interpreter
    monkeypatch.setattr(
        release_export_module,
        "probe_python_runtime",
        lambda *_args, **_kwargs: {
            "runtime": changed,
            "interpreter": interpreter,
        },
    )

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == classification


def test_export_release_rejects_changed_worker_interpreter_identity(
    tmp_path,
    monkeypatch,
):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state = json.loads(
        (_pipeline_root(repo, run_id) / "state.json").read_text()
    )
    recorded = state["stages"]["stage5_strict_gate"]["stage_config"]
    changed_runtime = json.loads(json.dumps(recorded["proof_runtime"]))
    changed_interpreter = json.loads(
        json.dumps(recorded["proof_interpreter"])
    )
    changed_interpreter["invocation_lstat"]["inode"] += 1
    changed_runtime["interpreter"] = changed_interpreter
    monkeypatch.setattr(
        release_export_module,
        "probe_python_runtime",
        lambda *_args, **_kwargs: {
            "runtime": changed_runtime,
            "interpreter": changed_interpreter,
        },
    )

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_PROVENANCE_MISMATCH"


def test_export_release_rejects_changed_installed_package_contents(
    tmp_path,
    monkeypatch,
):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state = json.loads(
        (_pipeline_root(repo, run_id) / "state.json").read_text()
    )
    recorded = state["stages"]["stage5_strict_gate"]["stage_config"]
    changed_runtime = json.loads(json.dumps(recorded["proof_runtime"]))
    changed_runtime["package_artifacts"]["scipy"]["files_sha256"] = "f" * 64
    interpreter = recorded["proof_interpreter"]
    monkeypatch.setattr(
        release_export_module,
        "probe_python_runtime",
        lambda *_args, **_kwargs: {
            "runtime": changed_runtime,
            "interpreter": interpreter,
        },
    )

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_PROVENANCE_MISMATCH"


def test_export_release_never_executes_state_named_unapproved_interpreter(
    tmp_path,
    monkeypatch,
):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    state["config"]["python_executable"] = "/bin/false"
    state["config_fingerprint"] = _pipeline_fingerprint(state["config"])
    _write_json(state_path, state)

    def must_not_probe(*_args, **_kwargs):
        raise AssertionError("unapproved state interpreter was executed")

    monkeypatch.setattr(
        release_export_module,
        "probe_python_runtime",
        must_not_probe,
    )

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "RUNTIME_INVALID"


def test_export_release_publishes_only_strict_accepted_subset(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    stage5_path = (
        _pipeline_root(repo, run_id) / "artifacts" / "stage5-final-gate.json"
    )
    stage5 = json.loads(stage5_path.read_text())
    stage5["evaluations"][1]["disposition"] = "INCOMPLETE"
    stage5["evaluations"][1]["result"] = {
        "passed": False,
        "replay_complete": False,
        "failures": ["strict replay batch timeout exhausted"],
    }
    stage5["summary"] = {
        "accepted": 1,
        "rejected": 0,
        "incomplete": 1,
        "total": 2,
    }
    _write_json(stage5_path, stage5)
    _refresh_state_hashes(repo, run_id)

    result = export_release(repo_dir=repo, run_id=run_id)

    assert result["certificates"] == 1
    manifest = json.loads(Path(result["manifest"]).read_text())
    assert {
        name: manifest[name]
        for name in ("source_total", "accepted", "rejected", "incomplete")
    } == {
        "source_total": 2,
        "accepted": 1,
        "rejected": 0,
        "incomplete": 1,
    }
    assert len(manifest["certificates"]) == 1
    certificate_dir = Path(result["manifest"]).parent / "certificates"
    assert {path.name for path in certificate_dir.iterdir()} == {
        f"{manifest['certificates'][0]['certificate_sha256']}.json"
    }
    assert validate_release_manifest(
        result["manifest"],
        known_answer_trust_path=repo / "results" / "known_answer_trust.json",
        expected_run_id=run_id,
    )["passed"]


def test_export_release_rejects_promoted_unaccepted_peer(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    stage5_path = (
        _pipeline_root(repo, run_id) / "artifacts" / "stage5-final-gate.json"
    )
    stage5 = json.loads(stage5_path.read_text())
    stage5["evaluations"][1]["disposition"] = "ACCEPTED"
    stage5["evaluations"][1]["result"] = {
        "passed": False,
        "replay_complete": False,
        "failures": ["strict replay batch timeout exhausted"],
    }
    stage5["summary"] = {
        "accepted": 2,
        "rejected": 0,
        "incomplete": 0,
        "total": 2,
    }
    _write_json(stage5_path, stage5)
    _refresh_state_hashes(repo, run_id)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_BINDING_MISMATCH"


def test_export_release_reports_completed_no_win_separately(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    state["status"] = "COMPLETED_NO_WIN"
    state["stages"]["stage5_strict_gate"]["status"] = "SKIPPED"
    state["stages"]["stage5_strict_gate"]["machine_status"] = "SKIPPED"
    _write_json(state_path, state)

    with pytest.raises(ReleaseNotExportableError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "NO_CERTIFIED_WIN"


def test_export_release_rejects_incomplete_stage_topology(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    state["stages"].pop("stage2_sector_audit")
    _write_json(state_path, state)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STATE_INVALID"


def test_export_release_rejects_forged_config_fingerprint(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    state["config_fingerprint"] = "f" * 64
    _write_json(state_path, state)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STATE_INVALID"


def test_export_release_rejects_busy_pipeline_lock(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    lock_path = _pipeline_root(repo, run_id) / "pipeline.lock"
    descriptor = os.open(lock_path, os.O_RDWR)
    fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
    try:
        with pytest.raises(ReleaseExportError) as failure:
            export_release(repo_dir=repo, run_id=run_id)
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)

    assert failure.value.classification == "PIPELINE_BUSY"


def test_export_release_rejects_state_output_hash_mismatch(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    stage5 = _pipeline_root(repo, run_id) / "artifacts" / "stage5-final-gate.json"
    value = json.loads(stage5.read_text())
    value["generated_at"] = "tampered"
    _write_json(stage5, value)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STATE_HASH_MISMATCH"


@pytest.mark.parametrize(
    "mutation",
    [
        lambda evaluation: evaluation.__setitem__("source_index", 1),
        lambda evaluation: evaluation.__setitem__("certificate_sha256", "b" * 64),
        lambda evaluation: evaluation.__setitem__(
            "certificate_payload_sha256", "b" * 64
        ),
        lambda evaluation: evaluation.__setitem__(
            "claim", {**evaluation["claim"], "n": 999}
        ),
        lambda evaluation: evaluation["result"].__setitem__("passed", False),
        lambda evaluation: evaluation["result"]["final_gate"].__setitem__(
            "accepted", False
        ),
    ],
    ids=["index", "hash", "payload-hash", "claim", "result", "final-gate"],
)
def test_export_release_rejects_stage5_binding_mismatch(tmp_path, mutation):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    stage5 = _pipeline_root(repo, run_id) / "artifacts" / "stage5-final-gate.json"
    value = json.loads(stage5.read_text())
    mutation(value["evaluations"][0])
    _write_json(stage5, value)
    _refresh_state_hashes(repo, run_id)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_BINDING_MISMATCH"


def test_export_release_rejects_unpinned_stage5_provenance(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    stage5 = _pipeline_root(repo, run_id) / "artifacts" / "stage5-final-gate.json"
    value = json.loads(stage5.read_text())
    value["known_answer_integrity"]["semantic_sha256"] = "b" * 64
    value["known_answer_integrity"]["rerun_semantic_sha256"] = "b" * 64
    _write_json(stage5, value)
    _refresh_state_hashes(repo, run_id)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_INVALID"


def test_export_release_rejects_conflicting_existing_snapshot(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    result = export_release(repo_dir=repo, run_id=run_id)
    manifest_path = Path(result["manifest"])
    manifest = json.loads(manifest_path.read_text())
    manifest["generated_at"] = "2026-07-27T23:59:59+00:00"
    manifest["manifest_sha256"] = canonical_sha256(
        manifest,
        omit="manifest_sha256",
    )
    _write_json(manifest_path, manifest)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "DESTINATION_CONFLICT"


def test_export_release_rejects_source_certificate_path_escape(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    root = _pipeline_root(repo, run_id)
    outside = repo / "outside-certificate.json"
    outside.write_text("{}\n")
    summary_path = root / "artifacts" / "stage4-summary.json"
    summary = json.loads(summary_path.read_text())
    summary["entries"][0]["certificate_path"] = str(outside)
    _write_json(summary_path, summary)
    _refresh_state_hashes(repo, run_id)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "UNSAFE_PATH"


def test_export_release_rejects_symlink_destination_escape(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    runs = repo / "results" / "runs"
    runs.mkdir()
    outside = tmp_path / "outside-release"
    outside.mkdir()
    (runs / run_id).symlink_to(outside, target_is_directory=True)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "UNSAFE_PATH"
    assert list(outside.iterdir()) == []


def test_export_release_rejects_symlink_source_artifact(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    root = _pipeline_root(repo, run_id)
    summary = root / "artifacts" / "stage4-summary.json"
    outside = tmp_path / "outside-summary.json"
    outside.write_bytes(summary.read_bytes())
    summary.unlink()
    summary.symlink_to(outside)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification in {"SOURCE_INVALID", "UNSAFE_PATH"}


def test_export_release_rejects_forged_non_winning_claim(tmp_path):
    repo, run_id = _make_synthetic_completed_win(
        tmp_path, certificate_count=1, logical_k=1, distance=4
    )

    with pytest.raises(ReleaseExportError, match="does not satisfy"):
        export_release(repo_dir=repo, run_id=run_id)


def test_export_release_rejects_changed_stage5_finalizer(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    finalizer = repo / "scripts" / "finalize_challenge.py"
    finalizer.write_text("# changed after Stage 5\n")

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STATE_HASH_MISMATCH"


@pytest.mark.parametrize(
    "relative_path",
    [
        "tests/verify_known_answer_gate.py",
        "results/known_code_registry.json",
    ],
    ids=["strict-runner", "known-code-registry"],
)
def test_export_release_rejects_changed_stage5_dependency(tmp_path, relative_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    dependency = repo / relative_path
    dependency.write_bytes(dependency.read_bytes() + b"# changed after Stage 5\n")

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STATE_HASH_MISMATCH"


@pytest.mark.parametrize(
    "relative_path",
    [
        "tests/verify_known_answer_gate.py",
        "results/known_code_registry.json",
    ],
    ids=["strict-runner", "known-code-registry"],
)
def test_export_release_rejects_missing_stage5_dependency(tmp_path, relative_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    (repo / relative_path).unlink()

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "SOURCE_INVALID"


@pytest.mark.parametrize(
    "relative_path",
    [
        "tests/verify_known_answer_gate.py",
        "results/known_code_registry.json",
    ],
    ids=["strict-runner", "known-code-registry"],
)
def test_export_release_rejects_symlinked_stage5_dependency(
    tmp_path, relative_path
):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    dependency = repo / relative_path
    outside = tmp_path / f"outside-{dependency.name}"
    outside.write_bytes(dependency.read_bytes())
    dependency.unlink()
    dependency.symlink_to(outside)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification in {"SOURCE_INVALID", "UNSAFE_PATH"}


def test_export_release_rejects_symlink_anywhere_in_stage5_source_tree(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    target = repo / "evaluation-metadata.txt"
    target.write_text("metadata\n")
    (repo / "evaluation" / "metadata.txt").symlink_to(target)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "UNSAFE_PATH"


@pytest.mark.parametrize("suffix", [".so", ".pyc"])
def test_export_release_rejects_unhashed_import_artifact(tmp_path, suffix):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    (repo / "evaluation" / f"verifier{suffix}").write_bytes(b"executable")

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "UNSAFE_PATH"


def test_export_release_rejects_sourceless_module_inside_pycache(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    cache = repo / "evaluation" / "__pycache__"
    cache.mkdir()
    (cache / "evil.pyc").write_bytes(b"executable")

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "UNSAFE_PATH"


def test_release_pep3147_cache_must_be_inert_or_match_current_source(tmp_path):
    source = tmp_path / "evaluation" / "verifier.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(importlib.util.cache_from_source(str(source)))
    py_compile.compile(
        str(source),
        cfile=str(cache),
        doraise=True,
        invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP,
    )

    assert not release_export_module._is_untrusted_import_artifact(cache)

    source.write_text("VALUE = 222\n")
    assert not release_export_module._is_untrusted_import_artifact(cache)

    py_compile.compile(
        str(source),
        cfile=str(cache),
        doraise=True,
        invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP,
    )
    header = cache.read_bytes()[:16]
    forged = compile("VALUE = 'forged'\n", str(source), "exec")
    cache.write_bytes(header + marshal.dumps(forged))
    assert release_export_module._is_untrusted_import_artifact(cache)


@pytest.mark.parametrize("optimisation", [0, 1, 2])
def test_release_accepts_dotted_source_name_pep3147_cache(
    tmp_path, optimisation
):
    source = tmp_path / "evaluation" / "verifier.extra.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(
        importlib.util.cache_from_source(
            str(source),
            optimization=None if optimisation == 0 else optimisation,
        )
    )
    py_compile.compile(
        str(source),
        cfile=str(cache),
        doraise=True,
        optimize=optimisation,
    )

    assert not release_export_module._is_untrusted_import_artifact(cache)


def test_release_rejects_different_magic_pep3147_cache(tmp_path):
    source = tmp_path / "evaluation" / "verifier.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(importlib.util.cache_from_source(str(source)))
    py_compile.compile(str(source), cfile=str(cache), doraise=True)
    raw = bytearray(cache.read_bytes())
    raw[0] ^= 0xFF
    cache.write_bytes(raw)

    assert release_export_module._is_untrusted_import_artifact(cache)


def test_release_ignores_foreign_tag_and_magic_pep3147_cache(tmp_path):
    source = tmp_path / "evaluation" / "verifier.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(importlib.util.cache_from_source(str(source)))
    py_compile.compile(str(source), cfile=str(cache), doraise=True)
    current_tag = sys.implementation.cache_tag
    assert current_tag is not None
    foreign = cache.with_name(
        cache.name.replace(current_tag, "cpython-999")
    )
    raw = bytearray(cache.read_bytes())
    raw[0] ^= 0xFF
    foreign.write_bytes(raw)
    cache.unlink()

    assert not release_export_module._is_untrusted_import_artifact(foreign)


@pytest.mark.parametrize(
    "relative_path",
    [
        "tests/verify_known_answer_gate.py",
        "results/known_code_registry.json",
    ],
    ids=["strict-runner", "known-code-registry"],
)
def test_export_release_rejects_synced_input_hash_with_opaque_fingerprint(
    tmp_path, relative_path
):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    dependency = repo / relative_path
    dependency.write_bytes(dependency.read_bytes() + b"# forged after Stage 5\n")
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    stage5_record = state["stages"]["stage5_strict_gate"]
    stage5_record["input_hashes"][str(dependency)] = _file_sha256(dependency)
    stage5_record["stage_fingerprint"] = "f" * 64
    _write_json(state_path, state)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_PROVENANCE_MISMATCH"


def test_export_release_requires_exact_stage5_config_not_legacy_cache(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    state["stages"]["stage5_strict_gate"].pop("stage_config")
    _write_json(state_path, state)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_PROVENANCE_MISMATCH"


@pytest.mark.parametrize("mutation", ["missing", "extra"])
def test_export_release_requires_exact_stage5_input_set(tmp_path, mutation):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    inputs = state["stages"]["stage5_strict_gate"]["input_hashes"]
    if mutation == "missing":
        inputs.pop(str(repo / "results" / "known_code_registry.json"))
    else:
        inputs[str(repo / "unexpected-stage5-input")] = "f" * 64
    _write_json(state_path, state)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STATE_HASH_MISMATCH"


def test_export_release_rejects_inconsistent_strict_replay(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    stage5 = _pipeline_root(repo, run_id) / "artifacts" / "stage5-final-gate.json"
    value = json.loads(stage5.read_text())
    value["evaluations"][0]["result"]["checks"]["milp_rerun"] = False
    _write_json(stage5, value)
    _refresh_state_hashes(repo, run_id)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_INVALID"


def test_export_release_rejects_missing_required_replay_check(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    stage5 = _pipeline_root(repo, run_id) / "artifacts" / "stage5-final-gate.json"
    value = json.loads(stage5.read_text())
    value["evaluations"][0]["result"]["checks"].pop("schema")
    _write_json(stage5, value)
    _refresh_state_hashes(repo, run_id)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STAGE5_INVALID"


def test_certificate_validation_requires_exact_direction_objects(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path, certificate_count=1)
    certificate_path = (
        _pipeline_root(repo, run_id) / "artifacts" / "stage4-certificates.jsonl"
    )
    certificate = json.loads(certificate_path.read_text())
    certificate["milp"]["directions"].pop()
    known_answer_sha = _file_sha256(repo / "results" / "known_answer_gate.json")

    with pytest.raises(ReleaseExportError, match="exactly 2k direction objects"):
        release_export_module._validate_certificate(
            certificate, index=0, known_answer_sha256=known_answer_sha
        )


def test_export_release_does_not_create_missing_pipeline_lock(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    lock = _pipeline_root(repo, run_id) / "pipeline.lock"
    lock.unlink()

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "UNSAFE_LOCK"
    assert not lock.exists()


def test_export_release_rejects_boolean_verified_count(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path, certificate_count=1)
    state_path = _pipeline_root(repo, run_id) / "state.json"
    state = json.loads(state_path.read_text())
    state["result"]["verified_certificates"] = True
    _write_json(state_path, state)

    with pytest.raises(ReleaseExportError) as failure:
        export_release(repo_dir=repo, run_id=run_id)

    assert failure.value.classification == "STATE_INVALID"


def test_export_release_preserves_existing_humanize_run_files(tmp_path):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    destination = repo / "results" / "runs" / run_id
    destination.mkdir(parents=True)
    original_identity = (destination.stat().st_dev, destination.stat().st_ino)
    existing_files = {
        "evaluations.jsonl": b'{"candidate":"kept"}\n',
        "run_meta.json": b'{"status":"completed"}\n',
    }
    for name, content in existing_files.items():
        (destination / name).write_bytes(content)

    first = export_release(repo_dir=repo, run_id=run_id)

    assert first["status"] == "exported"
    assert (destination.stat().st_dev, destination.stat().st_ino) == original_identity
    for name, content in existing_files.items():
        assert (destination / name).read_bytes() == content
    assert (destination / "challenge_manifest.json").is_file()
    assert (destination / "certificates").is_dir()

    second = export_release(repo_dir=repo, run_id=run_id)

    assert second["status"] == "already-exported"
    for name, content in existing_files.items():
        assert (destination / name).read_bytes() == content
    assert not [
        path
        for path in destination.parent.iterdir()
        if path.name.startswith(f".{run_id}.release-")
    ]


def test_atomic_publish_never_replaces_racing_empty_destination(tmp_path, monkeypatch):
    repo, run_id = _make_synthetic_completed_win(tmp_path)
    destination = repo / "results" / "runs" / run_id
    original = release_export_module._rename_noreplace
    raced_identity = {}

    def create_racing_destination(source, target):
        if target == destination and not target.exists():
            target.mkdir()
            raced_identity["value"] = (target.stat().st_dev, target.stat().st_ino)
        return original(source, target)

    monkeypatch.setattr(
        release_export_module, "_rename_noreplace", create_racing_destination
    )
    result = export_release(repo_dir=repo, run_id=run_id)

    assert result["status"] == "exported"
    assert (destination.stat().st_dev, destination.stat().st_ino) == raced_identity[
        "value"
    ]
    assert (destination / "challenge_manifest.json").is_file()
    assert (destination / "certificates").is_dir()
