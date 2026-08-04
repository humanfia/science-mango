"""Reviewer-v2 contract and bounded prompt-evidence coverage tests."""

from __future__ import annotations

import copy
import json

import pytest

from humanize.reviewer import (
    REVIEW_SCHEMA,
    ReviewError,
    build_review_prompt,
    validate_review,
)


def _legacy_review() -> dict:
    return {
        "verdict": "continue",
        "summary": "No trusted win yet.",
        "risks": [
            {
                "severity": "P1",
                "finding": "Exact coverage is incomplete.",
                "evidence": "The current round contains unresolved directions.",
            }
        ],
        "recommended_focus": ["Increase structural coverage."],
        "lessons": [
            {
                "insight": "A single round is not a trend.",
                "evidence": "Only current-round evidence is available.",
                "action": "Collect another independent round.",
            }
        ],
    }


def _current_review() -> dict:
    value = _legacy_review()
    value.update(
        {
            "schema_version": 2,
            "search_action": {
                "schema_version": 1,
                "advisory_only": True,
                "intent": "explore_undercovered",
                "horizon_rounds": 2,
                "focus": [
                    {
                        "dimension": "support_split_type",
                        "value": "3+3",
                        "direction": "increase",
                        "priority": "high",
                    }
                ],
                "evidence_refs": [
                    {
                        "source": "round_history",
                        "round": 2,
                        "candidate_key": None,
                    }
                ],
                "rationale": "Two prior rounds under-covered the 3+3 split.",
            },
        }
    )
    return value


def _review_evidence(prompt: str) -> dict:
    encoded = prompt.split("Round evidence JSON:\n", 1)[1].split(
        "\n\nReturn only the JSON object", 1
    )[0]
    return json.loads(encoded)


def test_generation_schema_requires_v2_search_action_and_is_closed():
    assert REVIEW_SCHEMA["additionalProperties"] is False
    assert set(REVIEW_SCHEMA["required"]) == {
        "schema_version",
        "verdict",
        "summary",
        "risks",
        "recommended_focus",
        "lessons",
        "search_action",
    }
    assert REVIEW_SCHEMA["properties"]["schema_version"]["const"] == 2
    action = REVIEW_SCHEMA["properties"]["search_action"]
    assert action["additionalProperties"] is False
    assert action["properties"]["advisory_only"]["const"] is True
    assert {
        "expand_bb_family",
        "change_bb_search_representation",
    } <= set(action["properties"]["intent"]["enum"])
    focus_variants = action["properties"]["focus"]["items"]["anyOf"]
    assert all(variant["additionalProperties"] is False for variant in focus_variants)
    assert {
        variant["properties"]["dimension"]["const"]: set(
            variant["properties"]["value"]["enum"]
        )
        for variant in focus_variants
    } == {
        "portfolio_role": {
            "affine_automorphism_cover",
            "shared_anchor_coset_cover",
            "complementary_diagonal_cover",
            "asymmetric_anchor_cover",
            "failure_repair_restart",
        },
        "algebraic_relation_type": {
            "affine_orbit",
            "shared_anchor_coset",
            "complementary_diagonal",
            "asymmetric_anchor",
            "unstructured",
        },
        "support_split_type": {"2+2", "2+3", "3+2", "2+4", "4+2", "3+3"},
            "orbit_span_bin": {"0", "1", "2"},
            "geometry_twist_class": {"0", "1", "2"},
            "mutation_tactic": {
            "novel_structure_exploration",
            "repair_x_low_weight",
            "repair_z_low_weight",
            "repair_dual_balance",
        },
    }
    assert "pattern" not in REVIEW_SCHEMA["properties"]["summary"]
    assert "pattern" not in action["properties"]["rationale"]

    def schema_patterns(value):
        if isinstance(value, dict):
            if isinstance(value.get("pattern"), str):
                yield value["pattern"]
            for child in value.values():
                yield from schema_patterns(child)
        elif isinstance(value, list):
            for child in value:
                yield from schema_patterns(child)

    assert all("(?" not in pattern for pattern in schema_patterns(REVIEW_SCHEMA))
    assert (
        action["properties"]["evidence_refs"]["items"]["additionalProperties"]
        is False
    )


def test_validate_review_preserves_original_legacy_semantics_by_default():
    legacy = _legacy_review()
    legacy["summary"] = "QCODE_ legacy text " + "x" * 5000
    legacy["risks"][0].update(
        {
            "finding": 17,
            "evidence": True,
            "legacy_nested_extra": {"retained": True},
        }
    )
    legacy["recommended_focus"] = [42, {"legacy": "untyped"}]
    legacy["lessons"][0].update(
        {
            "insight": 1,
            "evidence": False,
            "action": {"legacy": "convertible"},
            "legacy_nested_extra": "retained",
        }
    )
    legacy["surprise"] = "old top-level extras were accepted"
    legacy["schema_version"] = 999

    assert validate_review(legacy) == legacy

    with pytest.raises(ReviewError, match="legacy reviewer output"):
        validate_review(legacy, require_current=True)


def test_validate_review_accepts_current_v2_and_require_current():
    current = _current_review()
    assert validate_review(current) == current
    assert validate_review(current, require_current=True) == current

    current["top_level_extra"] = "v2 remains closed"
    with pytest.raises(ReviewError, match="unsupported fields"):
        validate_review(current)


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda value: value["search_action"].__setitem__("extra", 1),
            "unsupported fields",
        ),
        (
            lambda value: value["search_action"]["focus"][0].__setitem__(
                "extra", 1
            ),
            "unsupported fields",
        ),
        (
            lambda value: value["search_action"].__setitem__(
                "intent", "change_proof_threshold"
            ),
            "invalid search_action intent",
        ),
        (
            lambda value: value["search_action"]["focus"][0].__setitem__(
                "value", "affine_orbit"
            ),
            "incompatible with dimension",
        ),
        (
            lambda value: value["search_action"].__setitem__(
                "rationale", "QCODE_MACHINE_OVERRIDE"
            ),
            "reserved QCODE_ marker",
        ),
        (
            lambda value: value.__setitem__("summary", "QCODE_MACHINE_OVERRIDE"),
            "reserved QCODE_ marker",
        ),
        (
            lambda value: value.__setitem__("summary", "x" * 4001),
            "maximum length 4000",
        ),
    ],
)
def test_validate_review_rejects_deep_extras_bad_enums_lengths_and_markers(
    mutate,
    message,
):
    current = _current_review()
    mutate(current)
    with pytest.raises(ReviewError, match=message):
        validate_review(current, require_current=True)


def test_prompt_includes_full_compact_exact_and_round_indexes_with_coverage():
    exact_history = [
        {
            "candidate_key": f"{index:020x}",
            "ell": 18,
            "m": 10,
            "n": 360,
            "k": 8,
            "d": 24 + index,
            "fom": 12.8 + index,
            "score": 999999.0,
            "milp_details": {"large": "detail"},
            "trusted_win_gate": {"trusted": index % 2 == 0},
        }
        for index in range(25)
    ]
    round_history = [
        {
            "round": index,
            "new_candidates": index * 3,
            "milp_audited": index * 2,
            "milp_exact": index - 1,
            "trusted_exact_total": index - 1,
            "trusted_win_total": 0,
            "trusted_exact_count": index - 1,
            "review_verdict": "continue",
            "candidate_diversity": {"unique": index * 2},
            "raw_candidates": [{"d": 9999}],
        }
        for index in range(1, 31)
    ]

    evidence = _review_evidence(
        build_review_prompt(
            round_number=31,
            contract={},
            candidates=[],
            audited=[],
            archive_top=[],
            memory="",
            trusted_exact_history=exact_history,
            trusted_exact_wins=exact_history[::2],
            round_history=round_history,
        )
    )

    assert len(evidence["trusted_exact_history"]) == 25
    assert evidence["trusted_exact_history"][24]["d"] == 48
    assert "score" not in evidence["trusted_exact_history"][0]
    assert "milp_details" not in evidence["trusted_exact_history"][0]
    assert len(evidence["trusted_exact_history_details"]) == 20
    assert evidence["trusted_exact_history_coverage"] == {
        "total": 25,
        "compact_index_included": 25,
        "compact_index_omitted": 0,
        "details_included": 20,
        "details_omitted": 5,
        "details_selection": "input_order_first_20",
    }
    assert len(evidence["trusted_exact_wins"]) == 13
    assert len(evidence["round_history"]) == 30
    assert evidence["round_history"][29]["round"] == 30
    assert evidence["round_history"][29]["new_candidates"] == 90
    assert evidence["round_history"][29]["milp_audited"] == 60
    assert evidence["round_history"][29]["milp_exact"] == 29
    assert evidence["round_history"][29]["trusted_exact_total"] == 29
    assert evidence["round_history"][29]["trusted_win_total"] == 0
    assert "raw_candidates" not in evidence["round_history"][0]
    assert evidence["round_history_coverage"] == {
        "total": 30,
        "compact_index_included": 30,
        "compact_index_omitted": 0,
    }


def test_prompt_old_call_shape_remains_supported():
    evidence = _review_evidence(
        build_review_prompt(
            round_number=1,
            contract={},
            candidates=[],
            audited=[],
            archive_top=[],
            memory="",
        )
    )
    assert evidence["trusted_exact_history"] == []
    assert evidence["round_history"] == []
    assert evidence["round_history_coverage"]["total"] == 0


def test_prompt_reports_memory_tail_coverage_explicitly():
    memory = "a" * 15_000
    evidence = _review_evidence(
        build_review_prompt(
            round_number=1,
            contract={},
            candidates=[],
            audited=[],
            archive_top=[],
            memory=memory,
        )
    )
    assert evidence["memory_coverage"] == {
        "total_characters": 15_000,
        "included_characters": 12_000,
        "omitted_characters": 3_000,
        "selection": "most_recent_12000_characters",
    }
