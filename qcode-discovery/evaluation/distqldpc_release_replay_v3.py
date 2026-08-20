"""Relocatable pure replay for the final typed DistQLDPC release.

The scientific replay remains the v2 zero-solver implementation.  This module
only replaces the strict known-answer runner binding with a two-phase contract:
the exporter proves that the historical command ran the same runner bytes as
the bound repository, while a later validator (possibly in another clean
checkout) proves that its current relative runner has the sealed SHA256.  No
solver, subprocess, or filesystem write is performed here.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping

from evaluation import distqldpc_release_replay_v2 as _v2


DistQLDPCReleaseReplayError = _v2.DistQLDPCReleaseReplayError
KNOWN_ANSWER_RUNNER = _v2.KNOWN_ANSWER_RUNNER
REQUIRED_BASELINES = _v2.REQUIRED_BASELINES
REQUIRED_VERIFICATION_CHECKS = _v2.REQUIRED_VERIFICATION_CHECKS
TRUST_POLICY = _v2.TRUST_POLICY
canonical_sha256 = _v2.canonical_sha256
fail = _v2.fail
read_json_object = _v2.read_json_object
read_regular = _v2.read_regular
require_sha256 = _v2.require_sha256
sha256_bytes = _v2.sha256_bytes


def _runner_suffix(path: Path) -> bool:
    expected = Path(KNOWN_ANSWER_RUNNER).parts
    return path.is_absolute() and path.parts[-len(expected):] == expected


def _strict_known_answer_binding(
    certificate: Mapping[str, Any],
    *,
    repo_dir: Path | str,
    known_answer_artifact: Path | str,
    known_answer_trust: Path | str,
    known_answer_integrity: Path | str,
    proof_runtime: Mapping[str, Any],
    phase: str,
    expected_runner_sha256: str | None,
) -> dict[str, Any]:
    if phase not in {"export", "relocated-validate"}:
        fail("KNOWN_ANSWER_INVALID", "unknown strict runner validation phase")
    artifact, artifact_raw = read_json_object(
        known_answer_artifact, label="known-answer artifact",
    )
    trust, trust_raw = read_json_object(
        known_answer_trust, label="known-answer trust",
    )
    integrity, integrity_raw = read_json_object(
        known_answer_integrity, label="strict known-answer integrity sidecar",
    )
    artifact_sha = sha256_bytes(artifact_raw)
    trust_environment = trust.get("environment")
    integrity_environment = integrity.get("environment")
    try:
        current_environment = _v2.known_answer_environment(proof_runtime)
    except (KeyError, TypeError, ValueError) as exc:
        fail("KNOWN_ANSWER_INVALID", f"current environment is invalid: {exc}")
    if (
        artifact.get("schema_version") != 1
        or artifact.get("gate") != "qldpc-known-answer-baselines"
        or artifact.get("passed") is not True
        or trust.get("schema_version") != 1
        or trust.get("trust_policy") != TRUST_POLICY
        or trust.get("required_baselines") != REQUIRED_BASELINES
        or trust.get("artifact_sha256") != artifact_sha
        or not isinstance(trust.get("semantic_sha256"), str)
        or not isinstance(trust_environment, Mapping)
        or not isinstance(certificate.get("known_answer"), Mapping)
        or certificate["known_answer"].get("artifact_sha256") != artifact_sha
    ):
        fail("KNOWN_ANSWER_INVALID", "known-answer artifact/trust policy failed")
    semantic_sha = require_sha256(trust["semantic_sha256"], "semantic_sha256")
    if (
        integrity.get("passed") is not True
        or integrity.get("mode") != "strict"
        or integrity.get("failures") != []
        or integrity.get("artifact_sha256") != artifact_sha
        or integrity.get("semantic_sha256") != semantic_sha
        or integrity.get("rerun_semantic_sha256") != semantic_sha
        or not isinstance(integrity_environment, Mapping)
        or canonical_sha256(dict(integrity_environment))
        != canonical_sha256(dict(trust_environment))
        or canonical_sha256(dict(integrity_environment))
        != canonical_sha256(dict(current_environment))
    ):
        fail("KNOWN_ANSWER_INVALID", "strict replay/trust/environment binding failed")

    command = integrity.get("rerun_command")
    interpreter = proof_runtime.get("interpreter")
    if not isinstance(interpreter, Mapping):
        fail("KNOWN_ANSWER_INVALID", "proof runtime interpreter is missing")
    try:
        repo = Path(repo_dir).resolve(strict=True)
        current_runner = (repo / KNOWN_ANSWER_RUNNER).resolve(strict=True)
        current_runner.relative_to(repo)
        current_runner_raw = read_regular(
            current_runner, label="current known-answer runner",
        )
    except (OSError, ValueError) as exc:
        fail("KNOWN_ANSWER_INVALID", f"current known-answer runner failed: {exc}")
    current_runner_sha = sha256_bytes(current_runner_raw)
    command_valid = bool(
        isinstance(command, list)
        and len(command) == 10
        and all(isinstance(item, str) for item in command)
        and command[0] == interpreter.get("reported_sys_executable")
        and command[1:3] == ["-I", "-B"]
        and command[4] == "--output"
        and Path(command[5]).is_absolute()
        and command[6] == "--timeout-per-logical"
        and command[8] == "--total-timeout-per-code"
        and _runner_suffix(Path(command[3]))
    )
    if command_valid:
        try:
            command_valid = bool(
                Path(command[0]).resolve(strict=True)
                == Path(str(interpreter["realpath"])).resolve(strict=True)
                and int(command[7]) > 0
                and str(int(command[7])) == command[7]
                and int(command[9]) > 0
                and str(int(command[9])) == command[9]
            )
        except (KeyError, OSError, TypeError, ValueError):
            command_valid = False
    if not command_valid:
        fail("KNOWN_ANSWER_INVALID", "strict rerun command/runtime is not pinned")

    historical_runner = Path(command[3])
    if phase == "export":
        try:
            historical_raw = read_regular(
                historical_runner, label="historical known-answer runner",
            )
        except DistQLDPCReleaseReplayError:
            raise
        if sha256_bytes(historical_raw) != current_runner_sha:
            fail(
                "KNOWN_ANSWER_INVALID",
                "historical and current known-answer runner bytes differ",
            )
    else:
        expected = require_sha256(
            expected_runner_sha256, "expected_runner_sha256",
        )
        if current_runner_sha != expected:
            fail("KNOWN_ANSWER_INVALID", "current runner differs from sealed SHA256")
        # If the historical path still exists, it must not contradict the seal.
        try:
            historical_exists = historical_runner.exists() or historical_runner.is_symlink()
        except OSError:
            historical_exists = True
        if historical_exists:
            historical_raw = read_regular(
                historical_runner, label="historical known-answer runner",
            )
            if sha256_bytes(historical_raw) != expected:
                fail("KNOWN_ANSWER_INVALID", "historical runner differs from seal")

    return {
        "passed": True,
        "mode": "strict",
        "failures": [],
        "trust_policy": TRUST_POLICY,
        "required_baselines": list(REQUIRED_BASELINES),
        "artifact_sha256": artifact_sha,
        "semantic_sha256": semantic_sha,
        "rerun_semantic_sha256": semantic_sha,
        "environment": dict(current_environment),
        "trust_file_sha256": sha256_bytes(trust_raw),
        "rerun_command": list(command),
        "runner_source": {
            "path": KNOWN_ANSWER_RUNNER,
            "sha256": current_runner_sha,
            "historical_command_path": command[3],
            "binding": "export-byte-equality/relocated-sealed-sha256",
        },
        "sidecar_file_sha256": sha256_bytes(integrity_raw),
        "sidecar_payload_sha256": canonical_sha256(integrity),
        "sidecar": dict(integrity),
    }


def validate_release_inputs(
    certificate: Mapping[str, Any],
    verification: Mapping[str, Any],
    *,
    repo_dir: Path | str,
    stage3_artifact: Path | str,
    known_answer_artifact: Path | str,
    known_answer_trust: Path | str,
    known_answer_integrity: Path | str,
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
    phase: str,
    expected_runner_sha256: str | None = None,
) -> dict[str, Any]:
    """Replay all scientific inputs and the relocatable runner provenance."""

    _v2._validate_expected_bindings(
        certificate,
        expected_candidate_digest=expected_candidate_digest,
        expected_certificate_sha256=expected_certificate_sha256,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
    )
    try:
        internal_certificate_sha = canonical_sha256(
            certificate, omit="certificate_sha256",
        )
    except (TypeError, ValueError) as exc:
        fail("CERTIFICATE_INVALID", f"certificate cannot be hashed: {exc}")
    backend = certificate.get("lower_proof_backend")
    if (
        certificate.get("schema_version") != 1
        or certificate.get("certificate_type") != _v2._certificate.CERTIFICATE_TYPE
        or certificate.get("formulation") != _v2._certificate.FORMULATION
        or certificate.get("passed") is not True
        or internal_certificate_sha != certificate.get("certificate_sha256")
        or not isinstance(backend, Mapping)
        or backend.get("backend") != "distqldpc"
    ):
        fail("CERTIFICATE_INVALID", "typed certificate header/selfhash is invalid")
    stage3 = _v2._stage3_static_rebuild(
        certificate,
        stage3_artifact=stage3_artifact,
        known_answer_artifact=known_answer_artifact,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
    )
    context, static = _v2._static_replay(
        certificate, known_answer_artifact=known_answer_artifact,
    )
    proof = context["proof"]
    upper = proof.get("upper_witness")
    upper_evidence = upper.get("solver_evidence") if isinstance(upper, Mapping) else None
    anchors = list(context["anchors"])
    stored_final = certificate.get("final_gate")
    final_checks = stored_final.get("checks") if isinstance(stored_final, Mapping) else None
    if (
        not anchors
        or not isinstance(upper, Mapping)
        or not isinstance(upper_evidence, Mapping)
        or upper.get("sector") != "X"
        or upper.get("anchor_cube") is not None
        or upper_evidence.get("outcome") != "sat"
        or upper_evidence.get("objective") != context["distance"]
        or upper_evidence.get("anchor_indices") != anchors
        or not isinstance(final_checks, Mapping)
        or any(value is not True for value in final_checks.values())
        or final_checks.get("typed_exact_sector_distqldpc_proof") is not True
        or final_checks.get("typed_proof_dispatch_transparent") is not True
        or final_checks.get("structural_audit_present") is not True
        or final_checks.get("structural_audit_reproduced") is not True
        or final_checks.get("expanded_registry_novel") is not True
        or final_checks.get("challenge_win") is not True
        or final_checks.get("reported_fom_matches") is not True
        or not isinstance(context.get("fom"), (int, float))
        or not _v2.math.isclose(
            float(certificate["claim"]["fom"]), float(context["fom"]),
            rel_tol=0.0, abs_tol=1e-9,
        )
    ):
        fail("CERTIFICATE_INVALID", "upper/novelty/FOM/final gate is invalid")
    fresh = _v2._fresh_evidence_replay(
        certificate, verification, context=context, static=static,
    )
    runtime = _v2._runtime_binding()
    known = _strict_known_answer_binding(
        certificate,
        repo_dir=repo_dir,
        known_answer_artifact=known_answer_artifact,
        known_answer_trust=known_answer_trust,
        known_answer_integrity=known_answer_integrity,
        proof_runtime=runtime,
        phase=phase,
        expected_runner_sha256=expected_runner_sha256,
    )
    return {
        "context": context,
        "static_verification": static,
        "fresh": fresh,
        "stage3": stage3,
        "proof_runtime": runtime,
        "known_answer_integrity": known,
    }


__all__ = [
    "DistQLDPCReleaseReplayError",
    "KNOWN_ANSWER_RUNNER",
    "REQUIRED_BASELINES",
    "REQUIRED_VERIFICATION_CHECKS",
    "TRUST_POLICY",
    "canonical_sha256",
    "fail",
    "read_json_object",
    "read_regular",
    "require_sha256",
    "sha256_bytes",
    "validate_release_inputs",
]
