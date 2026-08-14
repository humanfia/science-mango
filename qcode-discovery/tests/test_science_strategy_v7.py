"""End-to-end policy boundaries for the opt-in scientific selector."""

from __future__ import annotations

import copy
import json
from dataclasses import replace
from pathlib import Path

import pytest

import humanize.flow as flow_module
import evolve.run_evolution as launcher_module
from evolve.dependency_contract import (
    ANSATZ_V3_SCIENCE_STRATEGY_DEPENDENCIES,
    ANSATZ_V3_SCIENCE_STRATEGY_ENV,
    ANSATZ_V3_SCIENCE_STRATEGY_ID,
    ANSATZ_V3_SCIENCE_STRATEGY_INVOCATION_FIELD,
)
from evaluation.formal_audit_quota import (
    ASSIGNMENT_FIELD,
    candidate_audit_strata,
    load_quota_contract,
)
from evaluation.target_policy import TARGET_MODE_SCALAR
from evaluation.search_contract import (
    PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
)
from humanize.flow import (
    CANDIDATE_BATCH_POLICY_SCIENTIFIC_SELECTOR_VERSION,
    _advance_search_regime,
    _normal_search_regime,
    select_for_milp,
)
from humanize.pipeline import PipelineConfig
from humanize.state import code_key


PROJECT = Path(__file__).resolve().parents[1]
QUOTA = (
    PROJECT
    / "configs/twisted_torus_ansatz_v3.formal_audit_quota.v2.json"
)
PIPELINE = (
    PROJECT
    / "configs/five_stage_campaign.twisted_torus_ansatz_v3_science_strategy_v2.json"
)
LEGACY_PIPELINE = (
    PROJECT
    / "configs/five_stage_campaign.twisted_torus_ansatz_v3_preregistered.json"
)


def _row(
    tag: str,
    *,
    split: tuple[int, int] = (2, 3),
    mechanism: str = "complementary_diagonal",
) -> dict:
    supports = {
        "complementary_diagonal": (
            [(0, 0), (1, 0), (2, 0), (3, 0)],
            [(0, 0), (0, 1), (0, 2), (0, 3)],
        ),
        "shared_anchor_coset": (
            [(5, 2), (1, 5), (4, 4), (2, 2)],
            [(1, 5), (1, 3), (3, 2), (0, 4)],
        ),
        "unstructured": (
            [(2, 1), (1, 3), (4, 0), (5, 5)],
            [(5, 4), (0, 2), (3, 2), (1, 0)],
        ),
    }
    a_count, b_count = split
    a_terms, b_terms = supports[mechanism]
    row = {
        "test_tag": tag,
        "search_representation_id": (
            "css-bb-twisted-torus-published-volume-ansatz-generator-v3"
        ),
        "ell": 6,
        "m": 6,
        "n": 72,
        "k": 8,
        # These decoder-derived magnitudes are deliberately untrusted.
        "d": 99,
        "fom": 9999.0,
        "score": 9999.0,
        "stage": "osd_cs",
        "A_terms": [list(term) for term in a_terms[:a_count]],
        "B_terms": [list(term) for term in b_terms[:b_count]],
    }
    strata = candidate_audit_strata(row)
    assert strata is not None
    assert strata["support_split"] == f"{a_count}+{b_count}"
    assert strata["algebraic_mechanism"] == mechanism
    return row


def _claim_lower_bound(row: dict, lower_bound: int = 5) -> dict:
    claimed = copy.deepcopy(row)
    claimed.update({
        "distance_lower_bound": lower_bound,
        "distance_lower_bound_proven": True,
        "distance_lower_bound_status": "search_oracle_proven",
    })
    return claimed


class _Risk:
    def __init__(self, keys: dict[str, tuple[int, ...]]):
        self._keys = keys

    def priority_key(self, row):
        return self._keys.get(row["test_tag"], (0,) * 12)


def _select(rows, *, reviewer=None, risk=None):
    contract = load_quota_contract(QUOTA)
    return select_for_milp(
        rows,
        None,
        set(),
        1,
        policy_version=CANDIDATE_BATCH_POLICY_SCIENTIFIC_SELECTOR_VERSION,
        target_mode=TARGET_MODE_SCALAR,
        replay_structural_negatives=False,
        formal_audit_slots=[{"slot_index": 0, "volume": 36}],
        formal_audit_contract=contract,
        prior_audit_reports=[],
        prior_audit_rows=[],
        reviewer_selector_focus=reviewer,
        negative_witness_risk_index=risk,
    )


def test_hard_split_minimum_precedes_replayed_lower_bound(monkeypatch):
    proof = _claim_lower_bound(
        _row("proof", split=(4, 2), mechanism="complementary_diagonal")
    )
    deficit = _row("deficit", split=(2, 3), mechanism="complementary_diagonal")
    monkeypatch.setattr(
        flow_module,
        "_replayable_search_lower_bound_for_audit",
        lambda row: 5 if row.get("test_tag") == "proof" else None,
    )

    [selected] = _select([proof, deficit])

    assert selected["test_tag"] == "deficit"
    assert selected[ASSIGNMENT_FIELD]["strata"]["support_split"] == "2+3"


def test_replayed_lower_bound_precedes_reviewer_and_negative_risk(monkeypatch):
    proof = _claim_lower_bound(
        _row("proof", mechanism="shared_anchor_coset")
    )
    advised = _row("advised", mechanism="unstructured")
    monkeypatch.setattr(
        flow_module,
        "_replayable_search_lower_bound_for_audit",
        lambda row: 5 if row.get("test_tag") == "proof" else None,
    )
    reviewer = {
        "focus": [{
            "dimension": "algebraic_relation_type",
            "value": "unstructured",
            "direction": "increase",
            "priority": "high",
        }]
    }
    risk = _Risk({
        "proof": (-8,) * 12,
        "advised": (0,) * 12,
    })

    [selected] = _select([advised, proof], reviewer=reviewer, risk=risk)

    assert selected["test_tag"] == "proof"


def test_reviewer_focus_changes_one_tied_slot_but_bp_does_not():
    first = _row("first", mechanism="shared_anchor_coset")
    advised = _row("advised", mechanism="unstructured")
    # Ask for whichever tied stratum the stable baseline did not choose, then
    # vary only decoder telemetry under the same authenticated focus.
    [baseline] = _select([first, advised])
    requested = advised if baseline["test_tag"] == "first" else first
    reviewer = {
        "focus": [{
            "dimension": "algebraic_relation_type",
            "value": candidate_audit_strata(requested)[
                "algebraic_mechanism"
            ],
            "direction": "increase",
            "priority": "high",
        }]
    }
    [focused_before] = _select([first, advised], reviewer=reviewer)
    first["d"], first["fom"], first["score"] = 1000, 1e12, 1e12
    advised["d"], advised["fom"], advised["score"] = 1, 0.0, 0.0

    [focused_after] = _select([first, advised], reviewer=reviewer)

    assert focused_before["test_tag"] == requested["test_tag"]
    assert code_key(focused_before) == code_key(focused_after)
    assert code_key(baseline) != code_key(focused_before)


def test_negative_risk_breaks_only_an_unproven_tie_and_unknown_survives():
    risky = _row("risky", mechanism="shared_anchor_coset")
    unknown = _row("unknown", mechanism="shared_anchor_coset")
    risky["A_terms"] = [[0, 0], [1, 0]]
    risky["B_terms"] = [[0, 0], [0, 1], [1, 1]]
    unknown["A_terms"] = [[0, 0], [2, 0]]
    unknown["B_terms"] = [[0, 0], [0, 1], [2, 1]]
    assert candidate_audit_strata(risky)["algebraic_mechanism"] == (
        "shared_anchor_coset"
    )
    assert candidate_audit_strata(unknown)["algebraic_mechanism"] == (
        "shared_anchor_coset"
    )
    unknown.update({
        "low_weight_oracle_outcome": "UNKNOWN",
        "oracle_retryable": True,
    })
    risk = _Risk({"risky": (-1,) * 12, "unknown": (0,) * 12})

    [selected] = _select([risky, unknown], risk=risk)

    assert selected["test_tag"] == "unknown"


@pytest.mark.parametrize(
    "priority",
    [
        (0,) * 11,
        (0,) * 11 + (1,),
        (0,) * 11 + (0.0,),
    ],
)
def test_negative_risk_boundary_rejects_nonnegative_only_keys(priority):
    row = _row("candidate", mechanism="shared_anchor_coset")

    with pytest.raises(ValueError, match="12-component negative-only"):
        _select([row], risk=_Risk({"candidate": priority}))


def test_scientific_progress_recomputes_report_strata_from_audited_row():
    row = _row("audited", split=(2, 3), mechanism="unstructured")
    strata = candidate_audit_strata(row)
    report = {
        "slots": [{
            "status": "FILLED",
            "candidate_key": code_key(row),
            "strata": copy.deepcopy(strata),
        }]
    }
    flow_module._validate_formal_audit_report_strata(report, [row])

    forged = copy.deepcopy(report)
    forged["slots"][0]["strata"]["support_split"] = "4+2"
    with pytest.raises(flow_module.RoundTransactionError, match="strata"):
        flow_module._validate_formal_audit_report_strata(forged, [row])


def _progress(
    round_number: int,
    *,
    best_lb: int = 5,
    target_gap: int = 8,
    unresolved: int = 0,
    coverage_ready: bool = True,
) -> dict:
    return {
        "progress_sha256": f"{round_number:064x}",
        "automatic_representation_switch_gate": {
            "minimum_terminal_fresh_audits": 48,
            "stagnation_rounds": 4,
            "minimum_proven_fom_improvement": 0.01,
            "retain_family_if_lower_bound_at_least": 9,
            "retain_family_if_target_gap_at_most": 3,
        },
        "formal_audit_coverage": {
            "gate_satisfied_components": {
                "coverage_components_satisfied": coverage_ready,
            }
        },
        "filled_fresh_candidates": 48,
        "unique_audited_candidates": 48,
        "target_negative_candidates": 48,
        "fresh_terminal_target_negative_candidates": 48,
        "unresolved_candidates": unresolved,
        "best_distance_lower_bound": best_lb,
        "minimum_target_gap": target_gap,
        "best_proven_fom": {
            "candidate_key": "a" * 20,
            "numerator": 25,
            "denominator": 72,
            "distance_lower_bound": 5,
            "proof_source": "replayed-two-sector-search-lower-bound",
            "target_gap": 8,
        },
    }


def _rounds(**progress_overrides):
    return [
        {
            "round": number,
            "trusted_win_total": 0,
            "sealed_scientific_progress": _progress(
                number,
                **progress_overrides,
            ),
        }
        for number in range(5, 9)
    ]


def test_v5_machine_gate_switches_only_after_complete_negative_plateau():
    regime = _advance_search_regime(
        _normal_search_regime(4),
        _rounds(),
        policy_version=5,
        max_rounds=12,
    )

    assert regime["status"] == "representation_change_required"
    assert regime["evidence"]["reviewer_execution_authority"] is False
    assert regime["evidence"]["bp_osd_positive_credit"] is False


@pytest.mark.parametrize(
    "overrides",
    [
        {"unresolved": 1},
        {"coverage_ready": False},
        {"best_lb": 9},
        {"target_gap": 3},
    ],
)
def test_v5_unknown_coverage_or_positive_lb_signal_blocks_switch(overrides):
    regime = _advance_search_regime(
        _normal_search_regime(4),
        _rounds(**overrides),
        policy_version=5,
        max_rounds=12,
    )

    assert regime["status"] != "representation_change_required"


def test_science_strategy_pipeline_loads_as_fresh_scalar_v5():
    config = PipelineConfig.from_json(PIPELINE, repo_dir=PROJECT)
    config.flow_config.validate()

    assert config.flow_config.target_mode == TARGET_MODE_SCALAR
    assert config.flow_config.search_regime_policy_version == 5
    assert config.flow_config.stop_on_representation_change is True


def test_science_strategy_contract_pairs_are_not_interchangeable():
    science = PipelineConfig.from_json(PIPELINE, repo_dir=PROJECT).flow_config
    legacy = PipelineConfig.from_json(
        LEGACY_PIPELINE,
        repo_dir=PROJECT,
    ).flow_config

    with pytest.raises(ValueError, match="are incompatible"):
        replace(
            science,
            finite_search_domain_contract=legacy.finite_search_domain_contract,
        ).validate()
    with pytest.raises(ValueError, match="are incompatible"):
        replace(
            legacy,
            finite_search_domain_contract=science.finite_search_domain_contract,
        ).validate()
    with pytest.raises(ValueError, match="quota v2 requires"):
        replace(
            legacy,
            formal_audit_quota_contract=science.formal_audit_quota_contract,
            finite_search_domain_contract=science.finite_search_domain_contract,
        ).validate()


def test_science_strategy_dependencies_are_conditional_and_parent_child_bound(
    monkeypatch,
):
    science = PipelineConfig.from_json(PIPELINE, repo_dir=PROJECT).flow_config
    legacy = PipelineConfig.from_json(
        LEGACY_PIPELINE,
        repo_dir=PROJECT,
    ).flow_config

    legacy_parent = flow_module._evolution_dependencies(legacy)
    science_parent = flow_module._evolution_dependencies(science)
    assert not set(ANSATZ_V3_SCIENCE_STRATEGY_DEPENDENCIES).intersection(
        legacy_parent
    )
    for name, relative_path in ANSATZ_V3_SCIENCE_STRATEGY_DEPENDENCIES.items():
        assert science_parent[name] == relative_path
    noncodex_science = replace(science, codex_cli=False)
    fresh_invocation = flow_module._fresh_invocation_binding(
        noncodex_science,
        codex_identity=None,
        codex_version=None,
        codex_cwd=None,
    )
    assert fresh_invocation[
        ANSATZ_V3_SCIENCE_STRATEGY_INVOCATION_FIELD
    ] == ANSATZ_V3_SCIENCE_STRATEGY_ID
    assert ANSATZ_V3_SCIENCE_STRATEGY_INVOCATION_FIELD in (
        flow_module._expected_evolution_invocation_fields(
            science,
            set(science_parent),
            PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
        )
    )
    assert ANSATZ_V3_SCIENCE_STRATEGY_INVOCATION_FIELD not in (
        flow_module._expected_evolution_invocation_fields(
            legacy,
            set(legacy_parent),
            PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
        )
    )

    monkeypatch.setattr(
        launcher_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    monkeypatch.delenv(ANSATZ_V3_SCIENCE_STRATEGY_ENV, raising=False)
    legacy_child = launcher_module._active_evaluator_dependencies()
    assert not set(ANSATZ_V3_SCIENCE_STRATEGY_DEPENDENCIES).intersection(
        legacy_child
    )

    monkeypatch.setenv(
        ANSATZ_V3_SCIENCE_STRATEGY_ENV,
        ANSATZ_V3_SCIENCE_STRATEGY_ID,
    )
    science_child = launcher_module._active_evaluator_dependencies()
    for name, relative_path in ANSATZ_V3_SCIENCE_STRATEGY_DEPENDENCIES.items():
        assert science_child[name] == relative_path

    invocation = {
        "model_names": ["gpt-test"],
        "reasoning_effort": "xhigh",
        "codex_cli": False,
        "max_parallel_evaluations": 1,
        "api_base": "http://localhost/v1",
        "temperature_disabled": True,
        "codex_version": None,
        "codex_cwd": None,
        "codex_executable_mode": None,
        "search_geometry_contract": (
            PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT
        ),
        ANSATZ_V3_SCIENCE_STRATEGY_INVOCATION_FIELD: (
            ANSATZ_V3_SCIENCE_STRATEGY_ID
        ),
    }
    assert launcher_module._validated_invocation_binding(
        invocation, None, None
    ) == invocation
    changed = dict(invocation)
    changed[ANSATZ_V3_SCIENCE_STRATEGY_INVOCATION_FIELD] = "unknown"
    with pytest.raises(RuntimeError, match="science-strategy binding"):
        launcher_module._validated_invocation_binding(changed, None, None)


def test_unknown_or_non_v3_science_strategy_environment_fails_closed(
    monkeypatch,
):
    monkeypatch.setattr(
        launcher_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    monkeypatch.setenv(ANSATZ_V3_SCIENCE_STRATEGY_ENV, "unknown")
    with pytest.raises(RuntimeError, match="environment is invalid"):
        launcher_module._active_evaluator_dependencies()


def test_policy_v5_child_context_is_bidirectionally_bound_to_strategy_env(
    monkeypatch,
):
    monkeypatch.setattr(
        launcher_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        PUBLISHED_VOLUME_ANSATZ_V3_GEOMETRY_CONTRACT,
    )
    regime = {
        "schema_version": 1,
        "kind": "qcode-humanize-search-regime",
        "status": "expand_required",
        "reason": "science-strategy-test",
        "evidence": {"rounds": [1, 2, 3, 4]},
    }
    encoded = json.dumps(regime, sort_keys=True, separators=(",", ":"))
    monkeypatch.setenv(
        ANSATZ_V3_SCIENCE_STRATEGY_ENV,
        ANSATZ_V3_SCIENCE_STRATEGY_ID,
    )
    parsed = launcher_module._validated_search_regime(
        launcher_module.SEARCH_REGIME_POLICY_V5_PREFIX + encoded
    )
    assert parsed == {**regime, "policy_version": 5}
    with pytest.raises(RuntimeError, match="binding disagree"):
        launcher_module._validated_search_regime(
            launcher_module.SEARCH_REGIME_POLICY_V4_PREFIX + encoded
        )
    with pytest.raises(RuntimeError, match="requires a policy-v5"):
        launcher_module._validated_search_regime("")

    monkeypatch.delenv(ANSATZ_V3_SCIENCE_STRATEGY_ENV)
    with pytest.raises(RuntimeError, match="binding disagree"):
        launcher_module._validated_search_regime(
            launcher_module.SEARCH_REGIME_POLICY_V5_PREFIX + encoded
        )

    monkeypatch.setattr(
        launcher_module,
        "ACTIVE_GEOMETRY_CONTRACT",
        "legacy-css-bb",
    )
    monkeypatch.setenv(
        ANSATZ_V3_SCIENCE_STRATEGY_ENV,
        ANSATZ_V3_SCIENCE_STRATEGY_ID,
    )
    with pytest.raises(RuntimeError, match="environment is invalid"):
        launcher_module._active_evaluator_dependencies()
