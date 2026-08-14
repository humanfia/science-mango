"""Schema-v2 scientific formal-audit allocation contract tests."""

from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from evaluation.algebraic_mechanisms import RELATION_TYPES
from evaluation.formal_audit_quota import (
    ASSIGNMENT_FIELD,
    MINIMUM_SUPPORT_SPLITS,
    NEGATIVE_WITNESS_SELECTOR_POLICY,
    audited_filled_slot_counts,
    assigned_candidate,
    build_negative_witness_context,
    build_selector_context,
    load_quota_contract,
    quota_slot_schedule,
    round_quota_slots,
    selection_report,
    support_split_minimum_deficits,
    validate_selection_report,
    validate_selection_report_sequence,
    validate_selector_context,
)


PROJECT = Path(__file__).resolve().parents[1]
QUOTA_V1 = PROJECT / "configs/twisted_torus_ansatz_v3.formal_audit_quota.v1.json"
QUOTA_V2 = PROJECT / "configs/twisted_torus_ansatz_v3.formal_audit_quota.v2.json"
ALL_SPLITS = ("2+2", "2+3", "3+2", "2+4", "4+2", "3+3")


def _canonical_sha256(value) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()).hexdigest()


def _write_contract(tmp_path: Path, value: dict) -> Path:
    path = tmp_path / "quota.json"
    path.write_text(json.dumps(value), encoding="utf-8")
    return path


def _selected_row(
    slot: dict[str, int],
    *,
    candidate_key: str,
    mechanism: str,
    split: str,
) -> dict:
    volume = slot["volume"]
    twist = slot["slot_index"] % volume
    return assigned_candidate(
        {"candidate_key_for_test": candidate_key},
        slot=slot,
        strata={
            "published_volume": volume,
            "lattice_q": [1, volume, twist],
            "algebraic_mechanism": mechanism,
            "support_split": split,
        },
    )


def _round_rows(contract: dict, round_number: int) -> list[dict]:
    return [
        _selected_row(
            slot,
            candidate_key=f"{slot['slot_index'] + 1:020x}",
            mechanism=RELATION_TYPES[slot["slot_index"] % len(RELATION_TYPES)],
            split=ALL_SPLITS[slot["slot_index"] % len(MINIMUM_SUPPORT_SPLITS)],
        )
        for slot in round_quota_slots(contract, round_number)
    ]


def _report(
    contract: dict,
    round_number: int,
    *,
    prior_reports: list[dict],
    rows: list[dict] | None = None,
    selector_context: dict | None = None,
) -> dict:
    return selection_report(
        contract=contract,
        round_number=round_number,
        selected_fresh=(
            _round_rows(contract, round_number) if rows is None else rows
        ),
        retry_candidate_keys=[],
        candidate_key_fn=lambda row: row["candidate_key_for_test"],
        prior_reports=prior_reports,
        selector_context=selector_context,
    )


def test_v1_report_shape_and_golden_hash_are_unchanged():
    contract = load_quota_contract(QUOTA_V1)
    contract["contract_path"] = "/fixed/quota-v1.json"
    contract["contract_sha256"] = "a" * 64
    slot = dict(round_quota_slots(contract, 1)[0])
    selected = _selected_row(
        slot,
        candidate_key="1" * 20,
        mechanism="affine_orbit",
        split="2+2",
    )
    selected[ASSIGNMENT_FIELD]["strata"]["lattice_q"] = [5, 21, 0]

    report = selection_report(
        contract=contract,
        round_number=1,
        selected_fresh=[selected],
        retry_candidate_keys=[],
        candidate_key_fn=lambda row: row["candidate_key_for_test"],
    )

    assert report["schema_version"] == 1
    assert set(report) == {
        "schema_version",
        "kind",
        "representation_id",
        "contract_path",
        "contract_sha256",
        "round",
        "round_slot_range",
        "slots",
        "retry_candidate_keys",
        "filled_fresh_slots",
        "unfilled_fresh_slots",
        "bp_osd_positive_promotion",
        "report_sha256",
    }
    assert report["report_sha256"] == (
        "f8c9d12cc8d6d50a3260848a5b25d89f3b6ab1e3a797f3196d6b538d644f28da"
    )
    assert selection_report(
        contract=contract,
        round_number=1,
        selected_fresh=[selected],
        retry_candidate_keys=[],
        candidate_key_fn=lambda row: row["candidate_key_for_test"],
        prior_reports=[{"ignored_by_schema_v1": True}],
    ) == report
    assert validate_selection_report(
        report,
        contract=contract,
        round_number=1,
    ) == report


def test_v2_contract_preregisters_minima_gate_and_same_volume_schedule():
    v1 = load_quota_contract(QUOTA_V1)
    v2 = load_quota_contract(QUOTA_V2)

    assert v2["schema_version"] == 2
    assert quota_slot_schedule(v2) == quota_slot_schedule(v1)
    assert v2["support_split_minimum_quotas"] == [
        {"support_split": split, "minimum_fresh_audits": 6}
        for split in MINIMUM_SUPPORT_SPLITS
    ]
    assert v2["automatic_representation_switch_gate"] == {
        "minimum_terminal_fresh_audits": 48,
        "stagnation_rounds": 4,
        "minimum_proven_fom_improvement": 0.01,
        "retain_family_if_lower_bound_at_least": 9,
        "retain_family_if_target_gap_at_most": 3,
        "minimum_distinct_lattice_q": 24,
        "minimum_algebraic_mechanism_audits": [
            {"algebraic_mechanism": mechanism, "minimum_fresh_audits": 4}
            for mechanism in RELATION_TYPES
        ],
        "require_zero_unresolved": True,
        "require_all_audited_target_negative": True,
    }


@pytest.mark.parametrize(
    "mutate",
    [
        lambda value: value.__setitem__("unexpected", True),
        lambda value: value.__setitem__("schema_version", 2.0),
        lambda value: value["support_split_minimum_quotas"][0].__setitem__(
            "extra", 1
        ),
        lambda value: value["support_split_minimum_quotas"][0].__setitem__(
            "minimum_fresh_audits", 0
        ),
        lambda value: value["support_split_minimum_quotas"].reverse(),
        lambda value: value["automatic_representation_switch_gate"].__setitem__(
            "extra", 1
        ),
        lambda value: value["automatic_representation_switch_gate"][
            "minimum_algebraic_mechanism_audits"
        ].pop(),
        lambda value: value["automatic_representation_switch_gate"].__setitem__(
            "require_zero_unresolved", False
        ),
    ],
)
def test_v2_contract_is_closed_and_fail_closed(tmp_path, mutate):
    value = json.loads(QUOTA_V2.read_text())
    mutate(value)

    with pytest.raises(ValueError, match="formal-audit"):
        load_quota_contract(_write_contract(tmp_path, value))


def test_selector_context_is_closed_hash_bound_and_negative_only():
    negative = build_negative_witness_context(
        source_rows_sha256="b" * 64,
        source_rows=17,
        target_mode="gist-pareto-challenge-v1",
        representation_id=(
            "css-bb-twisted-torus-published-volume-ansatz-generator-v3"
        ),
        risk_index_sha256="e" * 64,
    )
    reviewer = {
        "source_round": 4,
        "artifact_sha256": "c" * 64,
        "action_sha256": "d" * 64,
        "intent": "explore_undercovered",
        "focus": [
            {
                "dimension": "support_split_type",
                "value": "2+3",
                "direction": "increase",
                "priority": "high",
            }
        ],
    }
    context = build_selector_context(
        reviewer_focus=reviewer,
        negative_witness_context=negative,
    )

    assert context["policy_version"] == 7
    assert context["negative_witness_policy"] == (
        NEGATIVE_WITNESS_SELECTOR_POLICY
    )
    assert context["negative_witness_context"]["unknown_semantics"] == (
        "fail-open-no-vote"
    )
    assert context["negative_witness_context"]["bp_osd_positive_credit"] is False
    assert context["negative_witness_context"]["target_mode"] == (
        "gist-pareto-challenge-v1"
    )
    assert context["negative_witness_context"]["risk_index_sha256"] == "e" * 64
    assert validate_selector_context(context) == context

    for mutation in (
        lambda value: value.__setitem__("extra", 1),
        lambda value: value.__setitem__("policy_version", 6),
        lambda value: value["reviewer_focus"]["focus"][0].__setitem__(
            "direction", "decrease"
        ),
        lambda value: value["negative_witness_context"].__setitem__(
            "unknown_semantics", "fail-closed"
        ),
        lambda value: value["negative_witness_context"].__setitem__(
            "target_mode", "scalar-fom-strict-v1"
        ),
        lambda value: value["negative_witness_context"].__setitem__(
            "representation_id", None
        ),
        lambda value: value["negative_witness_context"].__setitem__(
            "risk_index_sha256", "f" * 64
        ),
    ):
        changed = copy.deepcopy(context)
        mutation(changed)
        with pytest.raises(ValueError, match="selector|witness|reviewer"):
            validate_selector_context(changed)


def test_v2_reports_count_only_filled_slots_and_chain_coverage():
    contract = load_quota_contract(QUOTA_V2)
    round1_rows = _round_rows(contract, 1)[:5]
    retry_key = "f" * 20
    report1 = selection_report(
        contract=contract,
        round_number=1,
        selected_fresh=round1_rows,
        retry_candidate_keys=[retry_key],
        candidate_key_fn=lambda row: row["candidate_key_for_test"],
        prior_reports=[],
    )
    report2 = _report(contract, 2, prior_reports=[report1])

    validated = validate_selection_report_sequence(
        [report1, report2],
        contract=contract,
    )
    counts = audited_filled_slot_counts(validated, contract=contract)
    deficits = support_split_minimum_deficits(contract, counts)

    assert report1["schema_version"] == 2
    assert report1["slots"][-1]["unfilled_reason"] == "retry-lane-reserved"
    assert counts["filled_fresh_slots"] == 11
    assert sum(counts["support_split"].values()) == 11
    assert retry_key not in {
        slot["candidate_key"]
        for report in validated
        for slot in report["slots"]
        if slot["status"] == "FILLED"
    }
    assert deficits == {"2+2": 2, "2+3": 2, "3+2": 3}
    assert report2["formal_audit_coverage_before"] == report1[
        "formal_audit_coverage_after"
    ]
    assert report2["formal_audit_coverage_after"]["filled_fresh_slots"] == 11


def test_v2_report_rejects_self_hashed_context_for_another_representation():
    contract = load_quota_contract(QUOTA_V2)
    negative = build_negative_witness_context(
        source_rows_sha256="b" * 64,
        source_rows=17,
        target_mode="gist-pareto-challenge-v1",
        representation_id="another-representation",
        risk_index_sha256="e" * 64,
    )

    with pytest.raises(ValueError, match="representation is incompatible"):
        _report(
            contract,
            1,
            prior_reports=[],
            selector_context=build_selector_context(
                negative_witness_context=negative,
            ),
        )


def test_24_balanced_filled_slots_satisfy_only_coverage_gate_components():
    contract = load_quota_contract(QUOTA_V2)
    reports: list[dict] = []
    for round_number in range(1, 5):
        reports.append(_report(
            contract,
            round_number,
            prior_reports=reports,
        ))

    coverage = reports[-1]["formal_audit_coverage_after"]
    components = coverage["gate_satisfied_components"]
    assert coverage["filled_fresh_slots"] == 24
    assert coverage["distinct_lattice_q"] == 24
    assert [row["count"] for row in coverage["algebraic_mechanism_counts"]] == [
        5,
        5,
        5,
        5,
        4,
    ]
    assert [row["count"] for row in coverage["support_split_counts"][:3]] == [
        8,
        8,
        8,
    ]
    assert components["coverage_components_satisfied"] is True
    assert components["outcome_components_evaluated"] is False


def test_mandatory_volume_is_an_independent_coverage_gate_component():
    contract = load_quota_contract(QUOTA_V2)
    reports: list[dict] = []
    for round_number in range(1, 7):
        rows = [
            row
            for row in _round_rows(contract, round_number)
            if row[ASSIGNMENT_FIELD]["volume"] != 127
        ]
        reports.append(_report(
            contract,
            round_number,
            prior_reports=reports,
            rows=rows,
        ))

    coverage = reports[-1]["formal_audit_coverage_after"]
    gate = coverage["gate_satisfied_components"]
    mandatory = {
        row["published_volume"]: row
        for row in gate["mandatory_audited_volumes"]
    }
    assert coverage["distinct_lattice_q"] >= 24
    assert all(
        row["satisfied"] for row in gate["support_split_minimum_quotas"]
    )
    assert all(
        row["satisfied"]
        for row in gate["minimum_algebraic_mechanism_audits"]
    )
    assert mandatory[127]["satisfied"] is False
    assert mandatory[132]["satisfied"] is True
    assert gate["coverage_components_satisfied"] is False


def test_v2_report_rejects_semantic_tamper_even_with_recomputed_self_hash():
    contract = load_quota_contract(QUOTA_V2)
    report = _report(contract, 1, prior_reports=[])
    changed = copy.deepcopy(report)
    changed["formal_audit_coverage_after"]["distinct_lattice_q"] -= 1
    unsigned = dict(changed)
    unsigned.pop("report_sha256")
    changed["report_sha256"] = _canonical_sha256(unsigned)

    with pytest.raises(ValueError, match="coverage"):
        validate_selection_report(
            changed,
            contract=contract,
            round_number=1,
        )


def test_v2_report_sequence_rejects_repeated_fresh_candidate():
    contract = load_quota_contract(QUOTA_V2)
    report1 = _report(contract, 1, prior_reports=[])
    rows = _round_rows(contract, 2)
    rows[0]["candidate_key_for_test"] = report1["slots"][0]["candidate_key"]

    with pytest.raises(ValueError, match="repeats a fresh candidate"):
        _report(contract, 2, prior_reports=[report1], rows=rows)


def test_assignment_schema_remains_v1_and_contains_only_scheduling_metadata():
    contract = load_quota_contract(QUOTA_V2)
    row = _round_rows(contract, 1)[0]
    assignment = row[ASSIGNMENT_FIELD]

    assert assignment["schema_version"] == 1
    assert set(assignment) == {
        "schema_version",
        "slot_index",
        "volume",
        "strata",
        "semantics",
    }
