"""Typed, fail-closed reasons for certificate and replay failures.

Only a mathematically conclusive candidate-gate failure may be cached as a
terminal rejection.  Missing dependencies, incomplete solver work, runtime
failures, and contradictions in an already-passed certificate all remain
retryable.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any, Mapping


FAILURE_DISPOSITION_SCHEMA_VERSION = 1
CERTIFICATE_CACHE_SCHEMA_VERSION = 3
CANDIDATE_REJECTED = "CANDIDATE_REJECTED"
INCOMPLETE = "INCOMPLETE"
EVIDENCE_CONTRADICTION = "EVIDENCE_CONTRADICTION"
FAILURE_STATUSES = frozenset(
    {CANDIDATE_REJECTED, INCOMPLETE, EVIDENCE_CONTRADICTION}
)
FAILURE_DOMAINS = frozenset(
    {
        "candidate",
        "evidence",
        "io",
        "known_answer",
        "registry",
        "runtime",
        "schema",
        "solver",
    }
)
_CODE = re.compile(r"[A-Z][A-Z0-9_]*")

_CSS_FORMULATION = "css-logical-anticommutation-milp-v1"
_NONCSS_FORMULATION = "symplectic-logical-anticommutation-milp-v1"
_BB_CSS_TYPE = "qldpc-css-bb-exact"
_MATRIX_CSS_TYPE = "qldpc-css-matrix-exact"
_PBB_NONCSS_TYPE = "qldpc-pbb-noncss-exact"
_MATRIX_NONCSS_TYPE = "qldpc-noncss-matrix-exact"
_REGISTRY_REPLAY_POLICY = "explicit-construction-matrix-replay"
_REGISTRY_REPLAY_INDEX_FIELDS = [
    "code_type",
    "n",
    "k",
    "canonical_digest",
]
_SHA256 = re.compile(r"[0-9a-f]{64}")

_BB_CSS_GATE_CHECKS = frozenset(
    {
        "known_answer_gate",
        "css_bb_candidate",
        "candidate_rebuild",
        "css_commutation",
        "weight_and_degree_at_most_6",
        "connected_tanner_graph",
        "reported_n_matches",
        "reported_k_matches",
        "qldpc_k_crosscheck",
        "positive_reported_distance",
        "all_2k_milp_directions_optimal",
        "structural_audit_present",
        "structural_audit_reproduced",
        "expanded_registry_novel",
        "challenge_win",
        "reported_fom_matches",
    }
)
_MATRIX_CSS_GATE_CHECKS = frozenset(
    {
        "known_answer_gate",
        "css_commutation",
        "positive_dimension",
        "weight_and_degree_at_most_6",
        "connected_tanner_graph",
        "all_2k_milp_directions_optimal",
        "expanded_registry_novel",
        "challenge_win",
    }
)
_NONCSS_GATE_CHECKS = frozenset(
    {
        "known_answer_gate",
        "symplectic_commutation",
        "positive_dimension",
        "weight_and_degree_at_most_6",
        "connected_tanner_graph",
        "all_2k_milp_directions_optimal",
        "expanded_registry_novel",
        "challenge_win",
    }
)
_TERMINAL_GATE_SHAPES = {
    _BB_CSS_TYPE: (_CSS_FORMULATION, _BB_CSS_GATE_CHECKS),
    _MATRIX_CSS_TYPE: (_CSS_FORMULATION, _MATRIX_CSS_GATE_CHECKS),
    _PBB_NONCSS_TYPE: (_NONCSS_FORMULATION, _NONCSS_GATE_CHECKS),
    _MATRIX_NONCSS_TYPE: (_NONCSS_FORMULATION, _NONCSS_GATE_CHECKS),
}


def _terminal_registry_match_valid(novelty: Any) -> bool:
    """Require complete construction replay before rejecting a known code."""

    if (
        not isinstance(novelty, Mapping)
        or novelty.get("checked") is not True
        or novelty.get("novel") is not False
    ):
        return False
    matched_entries = novelty.get("matched_entries")
    replay_policy = novelty.get("replay_policy")
    if (
        not isinstance(matched_entries, list)
        or not matched_entries
        or any(not isinstance(entry, Mapping) for entry in matched_entries)
        or not isinstance(replay_policy, Mapping)
        or type(replay_policy.get("schema_version")) is not int
        or replay_policy.get("schema_version") != 1
        or replay_policy.get("policy") != _REGISTRY_REPLAY_POLICY
        or replay_policy.get("digest_terminal") is not False
        or replay_policy.get("index_fields") != _REGISTRY_REPLAY_INDEX_FIELDS
        or replay_policy.get("entry_construction_required") is not True
        or replay_policy.get("explicit_matrix_replay_required") is not True
        or replay_policy.get("complete") is not True
    ):
        return False
    indexed_entries = replay_policy.get("indexed_entries")
    verified_entries = replay_policy.get("verified_entries")
    if (
        type(indexed_entries) is not int
        or type(verified_entries) is not int
        or indexed_entries <= 0
        or indexed_entries != verified_entries
        or verified_entries != len(matched_entries)
    ):
        return False
    return all(
        isinstance(entry.get("construction_sha256"), str)
        and _SHA256.fullmatch(entry["construction_sha256"]) is not None
        and isinstance(entry.get("replay"), Mapping)
        and entry["replay"].get("verified") is True
        for entry in matched_entries
    )


def _terminal_gate_shape_valid(
    certificate: Mapping[str, Any],
    final_gate: Any,
) -> bool:
    """Bind a negative result to one complete, supported final-gate schema."""

    certificate_type = certificate.get("certificate_type")
    if not isinstance(certificate_type, str):
        return False
    shape = _TERMINAL_GATE_SHAPES.get(certificate_type)
    if (
        shape is None
        or type(certificate.get("schema_version")) is not int
        or certificate.get("schema_version") != 1
        or certificate.get("formulation") != shape[0]
        or not isinstance(final_gate, Mapping)
    ):
        return False
    if certificate_type == _BB_CSS_TYPE and (
        type(final_gate.get("schema_version")) is not int
        or final_gate.get("schema_version") != 1
        or final_gate.get("gate") != "qldpc-challenge-final"
    ):
        return False
    checks = final_gate.get("checks")
    if (
        not isinstance(checks, Mapping)
        or set(checks) != shape[1]
        or any(type(value) is not bool for value in checks.values())
    ):
        return False
    failed_checks = sorted(
        str(name) for name, value in checks.items() if value is False
    )
    failures = final_gate.get("failures")
    win = final_gate.get("win")
    return bool(
        failed_checks
        and final_gate.get("accepted") is False
        and isinstance(failures, list)
        and all(isinstance(item, str) for item in failures)
        and len(failures) == len(failed_checks)
        and len(failures) == len(set(failures))
        and set(failures) == set(failed_checks)
        and isinstance(win, Mapping)
        and win.get("passed") is checks.get("challenge_win")
    )


def make_failure_disposition(
    status: str,
    domain: str,
    codes: list[str] | tuple[str, ...],
) -> dict[str, Any]:
    """Build and validate the minimal machine-readable failure envelope."""

    value = {
        "schema_version": FAILURE_DISPOSITION_SCHEMA_VERSION,
        "status": status,
        "domain": domain,
        "codes": list(codes),
    }
    return validate_failure_disposition(value)


def validate_failure_disposition(value: Any) -> dict[str, Any]:
    """Return a normalized disposition or raise for an untrusted envelope."""

    if not isinstance(value, Mapping):
        raise ValueError("failure_disposition must be an object")
    if (
        type(value.get("schema_version")) is not int
        or value.get("schema_version") != FAILURE_DISPOSITION_SCHEMA_VERSION
    ):
        raise ValueError("unsupported failure_disposition schema")
    status = value.get("status")
    domain = value.get("domain")
    codes = value.get("codes")
    if status not in FAILURE_STATUSES:
        raise ValueError("invalid failure_disposition status")
    if domain not in FAILURE_DOMAINS:
        raise ValueError("invalid failure_disposition domain")
    if (
        not isinstance(codes, list)
        or not codes
        or any(
            not isinstance(code, str) or _CODE.fullmatch(code) is None
            for code in codes
        )
        or len(codes) != len(set(codes))
    ):
        raise ValueError("failure_disposition codes must be unique typed codes")
    if status == CANDIDATE_REJECTED and domain != "candidate":
        raise ValueError("CANDIDATE_REJECTED must use the candidate domain")
    return {
        "schema_version": FAILURE_DISPOSITION_SCHEMA_VERSION,
        "status": str(status),
        "domain": str(domain),
        "codes": list(codes),
    }


def terminal_candidate_rejection(certificate: Any) -> bool:
    """Validate a terminal rejection against the complete certificate.

    A syntactically valid envelope is not proof: cache files and stage summaries
    are untrusted inputs.  Recompute the build classification from the exact
    certificate's final gate and require byte-for-byte semantic agreement with
    the stored disposition.
    """

    if not isinstance(certificate, Mapping):
        return False
    unsigned = dict(certificate)
    stored_sha256 = unsigned.pop("certificate_sha256", None)
    try:
        encoded = json.dumps(
            unsigned,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    except (TypeError, ValueError):
        return False
    if (
        not isinstance(stored_sha256, str)
        or stored_sha256 != hashlib.sha256(encoded).hexdigest()
    ):
        return False
    milp = certificate.get("milp")
    if (
        certificate.get("passed") is not False
        or not isinstance(milp, Mapping)
        or milp.get("exact") is not True
    ):
        return False
    expected = milp.get("expected_directions")
    completed = milp.get("completed_directions")
    directions = milp.get("directions")
    claim = certificate.get("claim")
    if (
        type(expected) is not int
        or type(completed) is not int
        or not isinstance(directions, list)
        or any(not isinstance(item, Mapping) for item in directions)
        or not isinstance(claim, Mapping)
        or type(claim.get("k")) is not int
    ):
        return False
    if (
        expected <= 0
        or claim["k"] <= 0
        or expected != 2 * claim["k"]
        or completed != expected
        or len(directions) != expected
    ):
        return False
    final_gate = certificate.get("final_gate")
    if not _terminal_gate_shape_valid(certificate, final_gate):
        return False
    try:
        disposition = validate_failure_disposition(
            certificate.get("failure_disposition"),
        )
    except ValueError:
        return False
    if disposition["status"] != CANDIDATE_REJECTED:
        return False
    recomputed = classify_build_failure(
        exact=True,
        passed=False,
        final_gate=final_gate,
    )
    return recomputed == disposition


def classify_build_failure(
    *,
    exact: bool,
    passed: bool,
    final_gate: Any,
) -> dict[str, Any] | None:
    """Classify a certificate build without inferring trust from prose.

    The final gate's typed checks are authoritative.  Dependency failures take
    precedence over candidate failures because they prevent a conclusive
    negative result.
    """

    if passed:
        return None
    if not exact:
        return make_failure_disposition(
            INCOMPLETE,
            "solver",
            ["MILP_DIRECTIONS_INCOMPLETE"],
        )
    if not isinstance(final_gate, Mapping):
        return make_failure_disposition(
            INCOMPLETE,
            "schema",
            ["FINAL_GATE_MISSING"],
        )
    checks = final_gate.get("checks")
    if not isinstance(checks, Mapping) or not checks:
        return make_failure_disposition(
            INCOMPLETE,
            "schema",
            ["FINAL_GATE_CHECKS_MISSING"],
        )
    if checks.get("known_answer_gate") is not True:
        return make_failure_disposition(
            INCOMPLETE,
            "known_answer",
            ["KNOWN_ANSWER_GATE_UNVERIFIED"],
        )

    registry_checks = {
        name
        for name in (
            "structural_audit_present",
            "structural_audit_reproduced",
            "expanded_registry_novel",
        )
        if name in checks and checks.get(name) is not True
    }
    if registry_checks:
        novelty = final_gate.get(
            "expanded_structural_novelty",
            final_gate.get("structural_novelty"),
        )
        if (
            "expanded_registry_novel" in registry_checks
            and _terminal_registry_match_valid(novelty)
        ):
            return make_failure_disposition(
                CANDIDATE_REJECTED,
                "candidate",
                ["KNOWN_CODE_REGISTRY_MATCH"],
            )
        return make_failure_disposition(
            INCOMPLETE,
            "registry",
            ["REGISTRY_BINDING_UNVERIFIED"],
        )

    failed_checks = sorted(
        str(name)
        for name, value in checks.items()
        if value is not True
    )
    if not failed_checks:
        return make_failure_disposition(
            INCOMPLETE,
            "schema",
            ["FINAL_GATE_REJECTION_UNTYPED"],
        )
    evidence_checks = {
        "reported_n_matches",
        "reported_k_matches",
        "qldpc_k_crosscheck",
        "reported_fom_matches",
        "all_2k_milp_directions_optimal",
    }
    if evidence_checks.intersection(failed_checks):
        return make_failure_disposition(
            INCOMPLETE,
            "evidence",
            ["CANDIDATE_EVIDENCE_BINDING_MISMATCH"],
        )
    codes = [
        "GATE_" + re.sub(r"[^A-Z0-9]+", "_", name.upper()).strip("_")
        for name in failed_checks
    ]
    return make_failure_disposition(
        CANDIDATE_REJECTED,
        "candidate",
        codes,
    )


def incomplete_result_disposition(
    *,
    domain: str,
    code: str,
) -> dict[str, Any]:
    """Short form used by runtime and reconstruction failure paths."""

    return make_failure_disposition(INCOMPLETE, domain, [code])


def contradiction_disposition(code: str) -> dict[str, Any]:
    """Describe a failed replay of an artifact that claimed to have passed."""

    return make_failure_disposition(
        EVIDENCE_CONTRADICTION,
        "evidence",
        [code],
    )


def classify_replay_failure(
    *,
    passed: bool,
    replay_complete: bool,
) -> dict[str, Any] | None:
    """Classify a verifier result independently of human-readable failures."""

    if passed:
        return None
    if not replay_complete:
        return incomplete_result_disposition(
            domain="solver",
            code="CERTIFICATE_REPLAY_INCOMPLETE",
        )
    return contradiction_disposition("CERTIFICATE_REPLAY_MISMATCH")
