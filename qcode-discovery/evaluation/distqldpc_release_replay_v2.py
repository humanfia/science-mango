"""Pure fail-closed replay core for typed DistQLDPC release export.

This module performs no solver invocation and writes no files.  It reconstructs
the production Stage-3-to-Stage-4 handoff, repeats the static certificate
verifier, replays captured fresh DistQLDPC evidence with both official evidence
verifiers, and validates the separately produced strict known-answer sidecar.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import stat
from pathlib import Path
from typing import Any, Iterable, Mapping

from evaluation import distance_distqldpc as _distance
from evaluation import distqldpc_sector_adapter as _adapter
from evaluation import distqldpc_sector_certificate as _certificate
from evaluation import sector_certificate as _sector
from evaluation.proof_runtime import (
    RuntimeProbeError,
    known_answer_environment,
    proof_runtime_fingerprint,
    validate_proof_runtime_fingerprint,
)
from evaluation.release_gate import canonical_sha256


TRUST_POLICY = "repository-pinned-known-answer-v1"
REQUIRED_BASELINES = ["[[72,12,6]]", "[[90,8,10]]", "[[144,12,12]]"]
KNOWN_ANSWER_RUNNER = "tests/verify_known_answer_gate.py"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")
REQUIRED_VERIFICATION_CHECKS = frozenset({
    "schema",
    "certificate_sha256",
    "known_answer_sha256",
    "typed_lower_evidence",
    "upper_witness",
    "matrix_sha256",
    "typed_counts",
    "source_stage3_binding",
    "lower_backend_metadata",
    "static_build_metadata",
    "certificate_target_binding",
    "target_and_fom",
    "final_gate",
    "stored_final_gate",
    "novelty",
    "certificate_passed_flag",
    "distqldpc_rerun",
})


class DistQLDPCReleaseReplayError(RuntimeError):
    """A classified input/replay failure."""

    def __init__(self, classification: str, message: str):
        super().__init__(message)
        self.classification = classification


def fail(classification: str, message: str) -> None:
    raise DistQLDPCReleaseReplayError(classification, message)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def require_sha256(value: Any, label: str) -> str:
    if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
        fail("BINDING_INVALID", f"{label} must be a lowercase SHA256 digest")
    return value


def strict_json_loads(raw: bytes, *, source: Path) -> Any:
    def unique_object(pairs: Iterable[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key!r}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON value: {value}")

    try:
        return json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=unique_object,
            parse_constant=reject_constant,
        )
    except (UnicodeError, ValueError, json.JSONDecodeError) as exc:
        fail("SOURCE_INVALID", f"invalid strict JSON in {source}: {exc}")


def read_regular(path: Path | str, *, label: str) -> bytes:
    source = Path(path)
    try:
        metadata = source.lstat()
    except OSError as exc:
        fail("SOURCE_INVALID", f"{label} is unavailable: {source}: {exc}")
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        fail("SOURCE_INVALID", f"{label} must be a regular non-symlink file")
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(source, flags)
        try:
            opened = os.fstat(descriptor)
            if (
                not stat.S_ISREG(opened.st_mode)
                or (opened.st_dev, opened.st_ino)
                != (metadata.st_dev, metadata.st_ino)
            ):
                fail("SOURCE_INVALID", f"{label} changed while being opened")
            chunks: list[bytes] = []
            while True:
                chunk = os.read(descriptor, 1024 * 1024)
                if not chunk:
                    break
                chunks.append(chunk)
            return b"".join(chunks)
        finally:
            os.close(descriptor)
    except OSError as exc:
        fail("SOURCE_INVALID", f"cannot read {label}: {source}: {exc}")


def read_json_object(
    path: Path | str,
    *,
    label: str,
) -> tuple[dict[str, Any], bytes]:
    raw = read_regular(path, label=label)
    value = strict_json_loads(raw, source=Path(path))
    if not isinstance(value, dict):
        fail("SOURCE_INVALID", f"{label} must be one JSON object")
    return value, raw


def _runtime_binding() -> dict[str, Any]:
    try:
        return validate_proof_runtime_fingerprint(proof_runtime_fingerprint())
    except (KeyError, OSError, RuntimeError, TypeError, ValueError, RuntimeProbeError) as exc:
        fail("RUNTIME_INVALID", f"proof runtime fingerprint failed: {exc}")


def _validate_expected_bindings(
    certificate: Mapping[str, Any],
    *,
    expected_candidate_digest: str,
    expected_certificate_sha256: str,
    expected_stage3_artifact_sha256: str,
) -> None:
    expected_candidate_digest = require_sha256(
        expected_candidate_digest, "expected_candidate_digest",
    )
    expected_certificate_sha256 = require_sha256(
        expected_certificate_sha256, "expected_certificate_sha256",
    )
    expected_stage3_artifact_sha256 = require_sha256(
        expected_stage3_artifact_sha256, "expected_stage3_artifact_sha256",
    )
    claim = certificate.get("claim")
    source = certificate.get("source_stage3")
    if (
        not isinstance(claim, Mapping)
        or claim.get("canonical_digest") != expected_candidate_digest
        or certificate.get("certificate_sha256") != expected_certificate_sha256
        or not isinstance(source, Mapping)
        or source.get("artifact_sha256") != expected_stage3_artifact_sha256
        or source.get("gate") != _adapter.STAGE3_GATE
        or source.get("status") != "EXACT_PROVEN"
    ):
        fail("BINDING_MISMATCH", "explicit release binding does not match input")


def _stage3_static_rebuild(
    certificate: Mapping[str, Any],
    *,
    stage3_artifact: Path | str,
    known_answer_artifact: Path | str,
    expected_stage3_artifact_sha256: str,
) -> dict[str, Any]:
    stage3, stage3_raw = read_json_object(
        stage3_artifact,
        label="physical source-bound Stage-3 artifact",
    )
    internal_sha = stage3.get("artifact_sha256")
    if (
        not isinstance(internal_sha, str)
        or _SHA256_RE.fullmatch(internal_sha) is None
        or internal_sha != canonical_sha256(stage3, omit="artifact_sha256")
        or stage3.get("gate") != _adapter.STAGE3_GATE
        or stage3.get("status") != "EXACT_PROVEN"
    ):
        fail("STAGE3_INVALID", "physical Stage-3 selfhash/status is invalid")
    handoff_artifact_sha = canonical_sha256(stage3)
    if handoff_artifact_sha != expected_stage3_artifact_sha256:
        fail("STAGE3_INVALID", "physical Stage-3 handoff hash is not expected")
    try:
        handoff = _sector.claim_from_sector_sat_artifact(stage3)
    except (KeyError, TypeError, ValueError) as exc:
        fail("STAGE3_INVALID", f"production Stage-3 importer failed: {exc}")
    request = handoff.get(_sector.REQUEST_FIELD)
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
        rebuilt = _certificate.build_distqldpc_sector_certificate(
            handoff,
            known_answer_artifact=known_answer_artifact,
        )
    except (KeyError, OSError, TypeError, ValueError) as exc:
        fail("STAGE3_INVALID", f"zero-solver Stage-4 rebuild failed: {exc}")
    if rebuilt != certificate:
        fail("STAGE3_INVALID", "Stage-3 production rebuild differs from certificate")
    return {
        "gate": stage3["gate"],
        "status": stage3["status"],
        "internal_artifact_sha256": internal_sha,
        "handoff_artifact_sha256": handoff_artifact_sha,
        "file_sha256": sha256_bytes(stage3_raw),
        "payload_sha256": canonical_sha256(stage3),
        "handoff_claim_sha256": canonical_sha256(handoff),
        "static_certificate_sha256": certificate["certificate_sha256"],
        "static_rebuild_equal": True,
    }


def _static_replay(
    certificate: Mapping[str, Any],
    *,
    known_answer_artifact: Path | str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    try:
        context = _certificate.validate_distqldpc_exact_proof(certificate["claim"])
        static = _certificate.verify_distqldpc_sector_certificate(
            certificate,
            known_answer_artifact=known_answer_artifact,
            rerun=False,
        )
    except (KeyError, OSError, TypeError, ValueError) as exc:
        fail("CERTIFICATE_INVALID", f"static certificate replay failed: {exc}")
    checks = static.get("checks")
    if (
        static.get("passed") is not False
        or static.get("replay_complete") is not False
        or static.get("failures") != ["distqldpc_rerun"]
        or not isinstance(checks, Mapping)
        or set(checks) != REQUIRED_VERIFICATION_CHECKS
        or checks.get("distqldpc_rerun") is not False
        or any(
            value is not True
            for name, value in checks.items()
            if name != "distqldpc_rerun"
        )
        or static.get("typed_lower") is not True
        or static.get("upper") is not True
        or static.get("novelty") is not True
        or static.get("fom_target") is not True
        or static.get("distqldpc_decisions_verified") != 0
        or static.get("distqldpc_decisions_total") != 1
        or static.get("logical_partitions_verified") != 0
        or static.get("logical_partitions_total") != 1
    ):
        fail("CERTIFICATE_INVALID", "zero-solver static verifier was not clean")
    return context, static


def _fresh_evidence_replay(
    certificate: Mapping[str, Any],
    verification: Mapping[str, Any],
    *,
    context: Mapping[str, Any],
    static: Mapping[str, Any],
) -> dict[str, Any]:
    checks = verification.get("checks")
    if (
        verification.get("passed") is not True
        or verification.get("replay_complete") is not True
        or verification.get("failures") != []
        or not isinstance(checks, Mapping)
        or set(checks) != REQUIRED_VERIFICATION_CHECKS
        or any(value is not True for value in checks.values())
        or any(
            checks.get(name) != static["checks"].get(name)
            for name in checks
            if name != "distqldpc_rerun"
        )
        or verification.get("distance") != context["distance"]
        or verification.get("lower_bound_backend") != "distqldpc"
        or verification.get("typed_lower") is not True
        or verification.get("upper") is not True
        or verification.get("novelty") is not True
        or verification.get("fom_target") is not True
        or verification.get("distqldpc_decisions_verified") != 1
        or verification.get("distqldpc_decisions_total") != 1
        or verification.get("logical_partitions_verified") != 1
        or verification.get("logical_partitions_total") != 1
        or verification.get("final_gate") != certificate.get("final_gate")
        or verification.get("final_gate") != static.get("final_gate")
        or "sat_rerun" in checks
        or "sat_rerun" in verification
    ):
        fail("VERIFICATION_INVALID", "final verification contract is incomplete")
    rerun = verification.get("distqldpc_rerun")
    source_identity = context.get("stage3_checkpoint_identity")
    if not isinstance(rerun, Mapping) or not isinstance(source_identity, Mapping):
        fail("VERIFICATION_INVALID", "fresh/source DistQLDPC identity is missing")
    try:
        expected_identity = _adapter.certificate_bound_distqldpc_checkpoint_identity(
            certificate_type=_certificate.CERTIFICATE_TYPE,
            certificate_sha256=certificate["certificate_sha256"],
            candidate=context["claim"],
            cardinality_mode=context["cardinality_mode"],
            required_distance=context["required_distance"],
            exact_distance=context["distance"],
            max_weight=context["distance"] - 1,
            logical_detector=context["detector"],
            translation_symmetry=context["translation"],
            xz_sector_isometry=context["xz_isometry"],
            source_stage3_checkpoint_identity=source_identity,
        )
    except (KeyError, TypeError, ValueError) as exc:
        fail("VERIFICATION_INVALID", f"fresh identity did not rebuild: {exc}")
    evidence = rerun.get("solver_evidence")
    if not isinstance(evidence, Mapping):
        fail("VERIFICATION_INVALID", "fresh solver evidence is missing")
    try:
        exact_failures = _distance.verify_distqldpc_exact_evidence(
            evidence,
            context["hx"], context["hz"], context["lx"], context["lz"],
            max_weight=context["distance"] - 1,
            cardinality_mode=context["cardinality_mode"],
            expected_checkpoint_identity=expected_identity,
        )
        lower_failures = _distance.verify_distqldpc_lower_evidence(
            evidence,
            context["hx"], context["hz"], context["lx"], context["lz"],
            max_weight=context["distance"] - 1,
            cardinality_mode=context["cardinality_mode"],
            expected_checkpoint_identity=expected_identity,
        )
    except (KeyError, TypeError, ValueError) as exc:
        fail("VERIFICATION_INVALID", f"official fresh replay raised: {exc}")
    proof = context["proof"]
    source_sha = proof["source_stage3_checkpoint_identity_sha256"]
    evidence_sha = evidence.get("evidence_sha256")
    if (
        exact_failures
        or lower_failures
        or rerun.get("verified") is not True
        or rerun.get("failures") != []
        or rerun.get("lower_bound_backend") != "distqldpc"
        or rerun.get("cardinality_mode") != context["cardinality_mode"]
        or rerun.get("max_weight") != context["distance"] - 1
        or rerun.get("exact_distance") != context["distance"]
        or rerun.get("checkpoint_identity") != expected_identity
        or rerun.get("source_stage3_checkpoint_identity_sha256") != source_sha
        or canonical_sha256(source_identity) != source_sha
        or expected_identity == source_identity
        or _SHA256_RE.fullmatch(str(evidence_sha)) is None
    ):
        fail("VERIFICATION_INVALID", "fresh DistQLDPC evidence did not replay")
    fresh_wrapper = {
        "sector": "XZ",
        "partition_index": None,
        "anchor_cube": None,
        "cardinality_mode": context["cardinality_mode"],
        "checkpoint_identity": expected_identity,
        "solver_evidence": dict(evidence),
    }
    if rerun.get("fresh_decision") not in (None, fresh_wrapper):
        fail("VERIFICATION_INVALID", "stored fresh wrapper is inconsistent")
    return {
        "checkpoint_identity": expected_identity,
        "checkpoint_identity_sha256": canonical_sha256(expected_identity),
        "source_stage3_checkpoint_identity_sha256": source_sha,
        "solver_evidence_sha256": evidence_sha,
        "fresh_wrapper": fresh_wrapper,
    }


def _strict_known_answer_binding(
    certificate: Mapping[str, Any],
    *,
    repo_dir: Path | str,
    known_answer_artifact: Path | str,
    known_answer_trust: Path | str,
    known_answer_integrity: Path | str,
    proof_runtime: Mapping[str, Any],
) -> dict[str, Any]:
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
        current_environment = known_answer_environment(proof_runtime)
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
        or _SHA256_RE.fullmatch(str(trust.get("semantic_sha256"))) is None
        or not isinstance(trust_environment, Mapping)
        or not isinstance(certificate.get("known_answer"), Mapping)
        or certificate["known_answer"].get("artifact_sha256") != artifact_sha
    ):
        fail("KNOWN_ANSWER_INVALID", "known-answer artifact/trust policy failed")
    semantic_sha = trust["semantic_sha256"]
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
        expected_runner = (repo / KNOWN_ANSWER_RUNNER).resolve(strict=True)
    except OSError as exc:
        fail("KNOWN_ANSWER_INVALID", f"known-answer runner is unavailable: {exc}")
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
    )
    if command_valid:
        try:
            command_valid = bool(
                Path(command[0]).resolve(strict=True)
                == Path(str(interpreter["realpath"])).resolve(strict=True)
                and Path(command[3]).resolve(strict=True) == expected_runner
                and int(command[7]) > 0
                and str(int(command[7])) == command[7]
                and int(command[9]) > 0
                and str(int(command[9])) == command[9]
            )
        except (KeyError, OSError, TypeError, ValueError):
            command_valid = False
    if not command_valid:
        fail("KNOWN_ANSWER_INVALID", "strict rerun command/runtime is not pinned")
    integrity_file_sha = sha256_bytes(integrity_raw)
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
        "sidecar_file_sha256": integrity_file_sha,
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
) -> dict[str, Any]:
    """Replay all release inputs without writing or invoking a solver."""

    _validate_expected_bindings(
        certificate,
        expected_candidate_digest=expected_candidate_digest,
        expected_certificate_sha256=expected_certificate_sha256,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
    )
    try:
        internal_certificate_sha = canonical_sha256(
            certificate,
            omit="certificate_sha256",
        )
    except (TypeError, ValueError) as exc:
        fail("CERTIFICATE_INVALID", f"certificate cannot be hashed: {exc}")
    backend = certificate.get("lower_proof_backend")
    if (
        certificate.get("schema_version") != 1
        or certificate.get("certificate_type") != _certificate.CERTIFICATE_TYPE
        or certificate.get("formulation") != _certificate.FORMULATION
        or certificate.get("passed") is not True
        or internal_certificate_sha != certificate.get("certificate_sha256")
        or not isinstance(backend, Mapping)
        or backend.get("backend") != "distqldpc"
    ):
        fail("CERTIFICATE_INVALID", "typed certificate header/selfhash is invalid")
    stage3 = _stage3_static_rebuild(
        certificate,
        stage3_artifact=stage3_artifact,
        known_answer_artifact=known_answer_artifact,
        expected_stage3_artifact_sha256=expected_stage3_artifact_sha256,
    )
    context, static = _static_replay(
        certificate,
        known_answer_artifact=known_answer_artifact,
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
        or not math.isclose(
            float(certificate["claim"]["fom"]),
            float(context["fom"]),
            rel_tol=0.0,
            abs_tol=1e-9,
        )
    ):
        fail("CERTIFICATE_INVALID", "upper/novelty/FOM/final gate is invalid")
    fresh = _fresh_evidence_replay(
        certificate,
        verification,
        context=context,
        static=static,
    )
    runtime = _runtime_binding()
    known = _strict_known_answer_binding(
        certificate,
        repo_dir=repo_dir,
        known_answer_artifact=known_answer_artifact,
        known_answer_trust=known_answer_trust,
        known_answer_integrity=known_answer_integrity,
        proof_runtime=runtime,
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
    "fail",
    "read_json_object",
    "read_regular",
    "require_sha256",
    "sha256_bytes",
    "validate_release_inputs",
]
