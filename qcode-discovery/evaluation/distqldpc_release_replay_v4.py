"""Portable scientific replay with a single audited path normalization.

Stage-4 certificates embed the absolute known-answer artifact path inside the
final-gate report.  A clean checkout therefore rebuilds a different certificate
SHA even when every scientific byte is identical.  This module permits exactly
that derived relocation: both certificates must have valid self hashes, the
official builder/verifier must accept the current artifact, and deep equality
must hold after replacing only ``final_gate.known_answer.path`` by a sentinel
and removing each already-validated ``certificate_sha256``.  No other field is
normalized and no solver, subprocess, or write is performed.
"""

from __future__ import annotations

import copy
from pathlib import Path
from typing import Any, Mapping

from evaluation import distqldpc_release_replay_v3 as _v3


_v2 = _v3._v2
DistQLDPCReleaseReplayError = _v3.DistQLDPCReleaseReplayError
KNOWN_ANSWER_RUNNER = _v3.KNOWN_ANSWER_RUNNER
REQUIRED_BASELINES = _v3.REQUIRED_BASELINES
REQUIRED_VERIFICATION_CHECKS = _v3.REQUIRED_VERIFICATION_CHECKS
TRUST_POLICY = _v3.TRUST_POLICY
canonical_sha256 = _v3.canonical_sha256
fail = _v3.fail
read_json_object = _v3.read_json_object
read_regular = _v3.read_regular
require_sha256 = _v3.require_sha256
sha256_bytes = _v3.sha256_bytes
PATH_SENTINEL = "@KNOWN_ANSWER_ARTIFACT"


def _selfhash(certificate: Mapping[str, Any], *, label: str) -> str:
    value = certificate.get("certificate_sha256")
    if (
        not isinstance(value, str)
        or value != canonical_sha256(certificate, omit="certificate_sha256")
    ):
        fail("CERTIFICATE_INVALID", f"{label} certificate selfhash is invalid")
    return value


def _normalized_final_gate(value: Any, *, label: str) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        fail("CERTIFICATE_INVALID", f"{label} final gate is missing")
    result = copy.deepcopy(dict(value))
    known = result.get("known_answer")
    if not isinstance(known, dict):
        fail("CERTIFICATE_INVALID", f"{label} known-answer report is missing")
    embedded_path = known.get("path")
    if not isinstance(embedded_path, str) or not Path(embedded_path).is_absolute():
        fail("CERTIFICATE_INVALID", f"{label} known-answer path is not absolute")
    known["path"] = PATH_SENTINEL
    return result


def _normalized_certificate(
    certificate: Mapping[str, Any],
    *,
    label: str,
) -> dict[str, Any]:
    _selfhash(certificate, label=label)
    result = copy.deepcopy(dict(certificate))
    result.pop("certificate_sha256", None)
    result["final_gate"] = _normalized_final_gate(
        result.get("final_gate"), label=label,
    )
    return result


def _stage3_relocated_rebuild(
    certificate: Mapping[str, Any],
    *,
    stage3_artifact: Path | str,
    known_answer_artifact: Path | str,
    expected_stage3_artifact_sha256: str,
    phase: str,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    stage3, stage3_raw = read_json_object(
        stage3_artifact, label="physical source-bound Stage-3 artifact",
    )
    internal_sha = stage3.get("artifact_sha256")
    if (
        not isinstance(internal_sha, str)
        or internal_sha != canonical_sha256(stage3, omit="artifact_sha256")
        or stage3.get("gate") != _v2._adapter.STAGE3_GATE
        or stage3.get("status") != "EXACT_PROVEN"
    ):
        fail("STAGE3_INVALID", "physical Stage-3 selfhash/status is invalid")
    handoff_artifact_sha = canonical_sha256(stage3)
    if handoff_artifact_sha != expected_stage3_artifact_sha256:
        fail("STAGE3_INVALID", "physical Stage-3 handoff hash is not expected")
    try:
        handoff = _v2._sector.claim_from_sector_sat_artifact(stage3)
    except (KeyError, TypeError, ValueError) as exc:
        fail("STAGE3_INVALID", f"production Stage-3 importer failed: {exc}")
    request = handoff.get(_v2._sector.REQUEST_FIELD)
    if (
        not isinstance(request, Mapping)
        or request.get("stage3_artifact_sha256") != handoff_artifact_sha
        or request.get("stage3_status") != "EXACT_PROVEN"
        or request.get("lower_bound_backend") != "distqldpc"
        or request.get("requested_lower_backend") != "distqldpc"
        or certificate.get("source_stage3", {}).get("artifact_sha256")
        != handoff_artifact_sha
    ):
        fail("STAGE3_INVALID", "production Stage-3 handoff binding is invalid")
    try:
        rebuilt = _v2._certificate.build_distqldpc_sector_certificate(
            handoff, known_answer_artifact=known_answer_artifact,
        )
    except (KeyError, OSError, TypeError, ValueError) as exc:
        fail("STAGE3_INVALID", f"zero-solver Stage-4 rebuild failed: {exc}")
    if not isinstance(rebuilt, dict):
        fail("STAGE3_INVALID", "official Stage-4 builder returned no certificate")
    stored_normalized = _normalized_certificate(certificate, label="stored")
    rebuilt_normalized = _normalized_certificate(rebuilt, label="rebuilt")
    known_raw = read_regular(
        known_answer_artifact, label="current known-answer artifact",
    )
    known_sha = sha256_bytes(known_raw)
    stored_known = certificate.get("known_answer")
    rebuilt_known = rebuilt.get("known_answer")
    stored_path = certificate.get("final_gate", {}).get("known_answer", {}).get("path")
    rebuilt_path = rebuilt.get("final_gate", {}).get("known_answer", {}).get("path")
    try:
        current_path = Path(known_answer_artifact).resolve(strict=True)
        rebuilt_resolved = Path(str(rebuilt_path)).resolve(strict=True)
    except OSError as exc:
        fail("CERTIFICATE_INVALID", f"current rebuilt known-answer path failed: {exc}")
    if (
        not isinstance(stored_known, Mapping)
        or not isinstance(rebuilt_known, Mapping)
        or stored_known.get("artifact_sha256") != known_sha
        or rebuilt_known.get("artifact_sha256") != known_sha
        or stored_normalized != rebuilt_normalized
        or not isinstance(stored_path, str)
        or not Path(stored_path).is_absolute()
        or rebuilt_resolved != current_path
    ):
        fail(
            "CERTIFICATE_RELOCATION_INVALID",
            "Stage-4 rebuild differs beyond the known-answer path/selfhash",
        )
    if phase == "export":
        try:
            if Path(stored_path).resolve(strict=True) != current_path:
                fail(
                    "CERTIFICATE_RELOCATION_INVALID",
                    "export certificate does not use the current known-answer path",
                )
        except OSError as exc:
            fail("CERTIFICATE_RELOCATION_INVALID", f"stored path failed: {exc}")
    else:
        historical = Path(stored_path)
        try:
            historical_exists = historical.exists() or historical.is_symlink()
        except OSError:
            historical_exists = True
        if historical_exists and sha256_bytes(
            read_regular(historical, label="historical known-answer artifact"),
        ) != known_sha:
            fail(
                "CERTIFICATE_RELOCATION_INVALID",
                "historical known-answer artifact contradicts its sealed SHA256",
            )
    normalized_sha = canonical_sha256(stored_normalized)
    normalization = {
        "schema_version": 1,
        "mode": "known-answer-path-only-relocation-v1",
        "allowed_nonsemantic_fields": [
            "certificate_sha256",
            "final_gate.known_answer.path",
        ],
        "path_sentinel": PATH_SENTINEL,
        "stored_certificate_sha256": certificate["certificate_sha256"],
        "normalized_certificate_payload_sha256": normalized_sha,
        "known_answer_artifact_sha256": known_sha,
        "official_rebuild_equivalent": True,
    }
    stage3_result = {
        "gate": stage3["gate"],
        "status": stage3["status"],
        "internal_artifact_sha256": internal_sha,
        "handoff_artifact_sha256": handoff_artifact_sha,
        "file_sha256": sha256_bytes(stage3_raw),
        "payload_sha256": canonical_sha256(stage3),
        "handoff_claim_sha256": canonical_sha256(handoff),
        "static_certificate_sha256": certificate["certificate_sha256"],
        "static_rebuild_equal_after_path_normalization": True,
        "path_normalization_sha256": canonical_sha256(normalization),
    }
    return stage3_result, rebuilt, normalization


def _static_replay_relocated(
    certificate: Mapping[str, Any],
    rebuilt: Mapping[str, Any],
    *,
    known_answer_artifact: Path | str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    try:
        context = _v2._certificate.validate_distqldpc_exact_proof(
            certificate["claim"],
        )
        static = _v2._certificate.verify_distqldpc_sector_certificate(
            rebuilt, known_answer_artifact=known_answer_artifact, rerun=False,
        )
    except (KeyError, OSError, TypeError, ValueError) as exc:
        fail("CERTIFICATE_INVALID", f"relocated static replay failed: {exc}")
    checks = static.get("checks")
    if (
        static.get("passed") is not False
        or static.get("replay_complete") is not False
        or static.get("failures") != ["distqldpc_rerun"]
        or not isinstance(checks, Mapping)
        or set(checks) != REQUIRED_VERIFICATION_CHECKS
        or checks.get("distqldpc_rerun") is not False
        or any(value is not True for name, value in checks.items() if name != "distqldpc_rerun")
        or static.get("typed_lower") is not True
        or static.get("upper") is not True
        or static.get("novelty") is not True
        or static.get("fom_target") is not True
        or static.get("distqldpc_decisions_verified") != 0
        or static.get("distqldpc_decisions_total") != 1
        or static.get("logical_partitions_verified") != 0
        or static.get("logical_partitions_total") != 1
        or rebuilt.get("final_gate") != static.get("final_gate")
        or _normalized_final_gate(
            certificate.get("final_gate"), label="stored static",
        ) != _normalized_final_gate(
            static.get("final_gate"), label="rebuilt static",
        )
    ):
        fail("CERTIFICATE_INVALID", "relocated zero-solver verifier was not clean")
    portable_static = copy.deepcopy(dict(static))
    portable_static["final_gate"] = copy.deepcopy(certificate["final_gate"])
    return context, portable_static


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
    """Replay scientific evidence with the audited path-only relocation rule."""

    if phase not in {"export", "relocated-validate"}:
        fail("CERTIFICATE_RELOCATION_INVALID", "unknown relocation phase")
    _v2._validate_expected_bindings(
        certificate,
        expected_candidate_digest=expected_candidate_digest,
        expected_certificate_sha256=expected_certificate_sha256,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
    )
    stored_sha = _selfhash(certificate, label="stored")
    backend = certificate.get("lower_proof_backend")
    if (
        certificate.get("schema_version") != 1
        or certificate.get("certificate_type") != _v2._certificate.CERTIFICATE_TYPE
        or certificate.get("formulation") != _v2._certificate.FORMULATION
        or certificate.get("passed") is not True
        or stored_sha != expected_certificate_sha256
        or not isinstance(backend, Mapping)
        or backend.get("backend") != "distqldpc"
    ):
        fail("CERTIFICATE_INVALID", "typed certificate header/selfhash is invalid")
    stage3, rebuilt, normalization = _stage3_relocated_rebuild(
        certificate,
        stage3_artifact=stage3_artifact,
        known_answer_artifact=known_answer_artifact,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
        phase=phase,
    )
    context, static = _static_replay_relocated(
        certificate, rebuilt, known_answer_artifact=known_answer_artifact,
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
    known = _v3._strict_known_answer_binding(
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
        "path_normalization": normalization,
    }


__all__ = [
    "DistQLDPCReleaseReplayError",
    "KNOWN_ANSWER_RUNNER",
    "PATH_SENTINEL",
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
