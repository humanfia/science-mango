import hashlib
import json

import pytest

from evaluation.failure_disposition import (
    classify_build_failure,
    terminal_candidate_rejection,
)

_GATE_CHECKS = {
    "qldpc-css-bb-exact": {
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
    },
    "qldpc-css-matrix-exact": {
        "known_answer_gate",
        "css_commutation",
        "positive_dimension",
        "weight_and_degree_at_most_6",
        "connected_tanner_graph",
        "all_2k_milp_directions_optimal",
        "expanded_registry_novel",
        "challenge_win",
    },
    "qldpc-pbb-noncss-exact": {
        "known_answer_gate",
        "symplectic_commutation",
        "positive_dimension",
        "weight_and_degree_at_most_6",
        "connected_tanner_graph",
        "all_2k_milp_directions_optimal",
        "expanded_registry_novel",
        "challenge_win",
    },
    "qldpc-noncss-matrix-exact": {
        "known_answer_gate",
        "symplectic_commutation",
        "positive_dimension",
        "weight_and_degree_at_most_6",
        "connected_tanner_graph",
        "all_2k_milp_directions_optimal",
        "expanded_registry_novel",
        "challenge_win",
    },
}


def _sealed_negative(
    failure_disposition: dict,
    *,
    final_gate: dict,
    certificate_type: str = "qldpc-css-bb-exact",
    normalize_gate: bool = True,
) -> dict:
    if normalize_gate:
        supplied_checks = final_gate.get("checks", {})
        checks = {
            name: supplied_checks.get(name, True)
            for name in _GATE_CHECKS[certificate_type]
        }
        final_gate = {
            **final_gate,
            "accepted": all(checks.values()),
            "checks": checks,
            "failures": sorted(
                name for name, value in checks.items() if value is False
            ),
            "win": {"passed": checks["challenge_win"]},
        }
        if certificate_type == "qldpc-css-bb-exact":
            final_gate.update({
                "schema_version": 1,
                "gate": "qldpc-challenge-final",
            })
    certificate = {
        "schema_version": 1,
        "certificate_type": certificate_type,
        "formulation": (
            "symplectic-logical-anticommutation-milp-v1"
            if "noncss" in certificate_type
            else "css-logical-anticommutation-milp-v1"
        ),
        "passed": False,
        "claim": {"k": 1},
        "milp": {
            "exact": True,
            "completed_directions": 2,
            "expected_directions": 2,
            "directions": [{}, {}],
        },
        "final_gate": final_gate,
        "failure_disposition": failure_disposition,
    }
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            certificate,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    return certificate


def _verified_registry_match() -> dict:
    return {
        "checked": True,
        "novel": False,
        "matched_entries": [{
            "id": "known-code",
            "construction_sha256": "f" * 64,
            "replay": {"verified": True},
        }],
        "replay_policy": {
            "schema_version": 1,
            "policy": "explicit-construction-matrix-replay",
            "digest_terminal": False,
            "index_fields": [
                "code_type",
                "n",
                "k",
                "canonical_digest",
            ],
            "entry_construction_required": True,
            "explicit_matrix_replay_required": True,
            "indexed_entries": 1,
            "verified_entries": 1,
            "complete": True,
        },
    }


def test_explicit_registry_match_is_a_terminal_candidate_rejection():
    result = classify_build_failure(
        exact=True,
        passed=False,
        final_gate={
            "checks": {
                "known_answer_gate": True,
                "structural_audit_present": False,
                "structural_audit_reproduced": True,
                "expanded_registry_novel": False,
            },
            "expanded_structural_novelty": _verified_registry_match(),
        },
    )

    assert result == {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["KNOWN_CODE_REGISTRY_MATCH"],
    }


@pytest.mark.parametrize(
    "mutate",
    (
        lambda novelty: novelty["matched_entries"].clear(),
        lambda novelty: novelty.pop("replay_policy"),
        lambda novelty: novelty["matched_entries"][0]["replay"].update(
            verified=False,
        ),
        lambda novelty: novelty["matched_entries"][0].update(
            construction_sha256="not-a-sha256",
        ),
        lambda novelty: novelty["replay_policy"].update(indexed_entries=2),
    ),
    ids=(
        "forged-novel-false",
        "missing-policy",
        "entry-replay-false",
        "invalid-construction-sha256",
        "replay-count-mismatch",
    ),
)
def test_unverified_registry_match_is_not_terminal(mutate):
    novelty = _verified_registry_match()
    mutate(novelty)

    result = classify_build_failure(
        exact=True,
        passed=False,
        final_gate={
            "checks": {
                "known_answer_gate": True,
                "expanded_registry_novel": False,
            },
            "expanded_structural_novelty": novelty,
        },
    )

    assert result == {
        "schema_version": 1,
        "status": "INCOMPLETE",
        "domain": "registry",
        "codes": ["REGISTRY_BINDING_UNVERIFIED"],
    }


def test_registry_binding_failure_is_retryable():
    result = classify_build_failure(
        exact=True,
        passed=False,
        final_gate={
            "checks": {
                "known_answer_gate": True,
                "structural_audit_present": True,
                "structural_audit_reproduced": False,
                "expanded_registry_novel": True,
            },
            "expanded_structural_novelty": {
                "checked": True,
                "novel": True,
                "matched_entries": [],
            },
        },
    )

    assert result == {
        "schema_version": 1,
        "status": "INCOMPLETE",
        "domain": "registry",
        "codes": ["REGISTRY_BINDING_UNVERIFIED"],
    }


@pytest.mark.parametrize(
    "dependency_code",
    (
        "KNOWN_ANSWER_GATE_UNVERIFIED",
        "REGISTRY_BINDING_UNVERIFIED",
        "CERTIFICATE_REPLAY_INCOMPLETE",
    ),
)
def test_dependency_code_cannot_masquerade_as_terminal_candidate_rejection(
    dependency_code,
):
    certificate = _sealed_negative(
        {
            "schema_version": 1,
            "status": "CANDIDATE_REJECTED",
            "domain": "candidate",
            "codes": [dependency_code],
        },
        final_gate={
            "checks": {
                "known_answer_gate": False,
                "challenge_win": False,
            },
        },
    )

    assert terminal_candidate_rejection(certificate) is False


def test_terminal_candidate_rejection_requires_exact_recomputed_gate_and_self_hash():
    disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }
    certificate = _sealed_negative(
        disposition,
        final_gate={
            "checks": {
                "known_answer_gate": True,
                "challenge_win": False,
            },
        },
    )

    assert terminal_candidate_rejection(certificate) is True

    certificate["certificate_sha256"] = "0" * 64
    assert terminal_candidate_rejection(certificate) is False


def test_terminal_negative_accepts_builder_check_order_not_alphabetic_order():
    disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN", "GATE_CSS_COMMUTATION"],
    }
    certificate = _sealed_negative(
        disposition,
        final_gate={
            "checks": {
                "css_commutation": False,
                "challenge_win": False,
            },
        },
    )
    certificate["final_gate"]["failures"] = [
        "css_commutation",
        "challenge_win",
    ]
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            {
                key: value
                for key, value in certificate.items()
                if key != "certificate_sha256"
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()

    assert terminal_candidate_rejection(certificate) is True


@pytest.mark.parametrize("certificate_type", tuple(_GATE_CHECKS))
def test_every_supported_certificate_kind_has_a_typed_complete_terminal_gate(
    certificate_type,
):
    disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }
    certificate = _sealed_negative(
        disposition,
        certificate_type=certificate_type,
        final_gate={"checks": {"challenge_win": False}},
    )

    assert terminal_candidate_rejection(certificate) is True


@pytest.mark.parametrize(
    "omitted_check",
    (
        "known_answer_gate",
        "reported_n_matches",
        "structural_audit_reproduced",
        "css_commutation",
        "all_2k_milp_directions_optimal",
        "challenge_win",
    ),
)
def test_terminal_negative_rejects_omitted_gate_dependency(omitted_check):
    disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }
    certificate = _sealed_negative(
        disposition,
        final_gate={"checks": {"challenge_win": False}},
    )
    del certificate["final_gate"]["checks"][omitted_check]
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            {
                key: value
                for key, value in certificate.items()
                if key != "certificate_sha256"
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()

    assert terminal_candidate_rejection(certificate) is False


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("expected_directions", True),
        ("expected_directions", "2"),
        ("completed_directions", True),
        ("completed_directions", "2"),
    ),
)
def test_terminal_negative_rejects_coerced_direction_counts(field, value):
    disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }
    certificate = _sealed_negative(
        disposition,
        final_gate={"checks": {"challenge_win": False}},
    )
    certificate["milp"][field] = value
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            {
                key: item
                for key, item in certificate.items()
                if key != "certificate_sha256"
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()

    assert terminal_candidate_rejection(certificate) is False


@pytest.mark.parametrize(
    ("path", "value"),
    (
        (("schema_version",), True),
        (("final_gate", "schema_version"), True),
        (("certificate_type",), ["qldpc-css-bb-exact"]),
    ),
)
def test_terminal_negative_rejects_malformed_typed_schema(path, value):
    disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }
    certificate = _sealed_negative(
        disposition,
        final_gate={"checks": {"challenge_win": False}},
    )
    target = certificate
    for name in path[:-1]:
        target = target[name]
    target[path[-1]] = value
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            {
                key: item
                for key, item in certificate.items()
                if key != "certificate_sha256"
            },
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()

    assert terminal_candidate_rejection(certificate) is False
