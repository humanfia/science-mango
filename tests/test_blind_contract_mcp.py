from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


MODULE_PATH = (
    Path(__file__).resolve().parents[1]
    / "src/archon/.archon-src/tools/lean-lsp-mcp/src/lean_lsp_mcp/blind_contract.py"
)
SPEC = importlib.util.spec_from_file_location("answer_blind_mcp_contract", MODULE_PATH)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
blind_contract_hashes = MODULE.blind_contract_hashes


def _numeric_candidate() -> dict[str, object]:
    return {
        "schema_version": 1,
        "protocol": "icho-answer-blind-v1",
        "phase": "solve",
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "id": "icho_2026_t4_a8",
        "blind_record_sha256": "a" * 64,
        "result_kind": "numeric",
        "raw_result": {
            "expression": "P*Q/(R*T) times the raw enthalpy",
            "lean_expression": "IchoBlindT4A8.rawDailyEnergy",
            "derivation_spec": "IchoBlindT4A8.RawDailyEnergySpec",
            "certified_interval": {
                "lower": "7034786013887/1",
                "upper": "7034786013888/1",
            },
            "value": "703478601388779/100",
            "unit": "J day^-1",
        },
        "reported_result": {
            "value": "7030000000000",
            "unit": "J day^-1",
            "precision": {
                "kind": "significant_figures",
                "digits": 3,
                "source": "uniform_blind_evaluation_default",
            },
            "rounding_rule": "half_away_from_zero",
        },
        "reporting_rule_source": {
            "intermediate_rounding": "forbidden",
            "explicit_precision": "use_only_precision_requested_in_problem",
            "default_final_display": "three_significant_figures",
            "final_precision": {
                "kind": "significant_figures",
                "digits": 3,
                "source": "uniform_blind_evaluation_default",
            },
            "tie_rule": "half_away_from_zero",
            "raw_result_required": True,
        },
        "tolerance_provenance": {
            "measurement_policy": {
                "stipulated_constants": "exact_as_printed_unless_problem_calls_them_measured",
                "measured_display_half_width": "one_half_of_last_displayed_quantum",
                "derived_tolerances": "must_be_proved_from_source_measurement_intervals",
            }
        },
        "candidate_domain_provenance": {
            "candidate_domain_policy": {
                "allowed_sources": ["problem_text", "trusted_general_law"],
                "previous_part_results": "derive_inline_from_problem_only_material_or_use_problem_stated_fallback",
                "unjustified_search_bounds": "forbidden",
                "underdetermined_result": "must_be_reported",
            },
            "derivation": {"energy": "raw physical law and printed constants"},
        },
    }


def test_pure_mcp_helper_matches_review_contract_helpers():
    from archon.commands.loop.review_source_contract import (
        blind_result_payload_sha256,
        expected_numeric_result_types,
        lean_result_type_sha256,
    )

    candidate = _numeric_candidate()
    expected_types = expected_numeric_result_types(candidate)
    assert expected_types is not None
    for role in ("raw_result", "reported_result"):
        result = blind_contract_hashes(json.dumps(candidate), role)
        assert result == {
            "role": role,
            "expected_type": expected_types[role],
            "expected_type_sha256": lean_result_type_sha256(expected_types[role]),
            "result_payload_sha256": blind_result_payload_sha256(candidate, role),
        }


@pytest.mark.parametrize("role", ["wrong", "", "RAW"])
def test_pure_mcp_helper_rejects_invalid_role(role: str):
    with pytest.raises(Exception, match="role must"):
        blind_contract_hashes(json.dumps(_numeric_candidate()), role)


def test_pure_mcp_helper_rejects_answer_seen_and_oversize():
    candidate = _numeric_candidate()
    candidate["official_answer_seen"] = True
    with pytest.raises(Exception, match="official_answer_seen=false"):
        blind_contract_hashes(json.dumps(candidate), "raw_result")
    with pytest.raises(Exception, match="1 MB"):
        blind_contract_hashes(" " * 1_000_001, "raw_result")
