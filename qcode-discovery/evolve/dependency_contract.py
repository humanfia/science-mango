"""Shared source-binding contract for managed OpenEvolve slices."""

from __future__ import annotations


# These files are imported by the fitness evaluator but execute outside the
# mutable evolve block.  Parent preparation and child witness generation must
# use this exact shared mapping or a completed slice cannot be authenticated.
LOCAL_EVALUATOR_DEPENDENCIES = {
    "evaluation_evaluator": "evaluation/evaluator.py",
    "evaluation_results": "evaluation/results.py",
    "evaluation_structural_dedup": "evaluation/structural_dedup.py",
    "evaluation_bb_code": "evaluation/bb_code.py",
    "evaluation_geometry": "evaluation/geometry.py",
    "evaluation_pbb_code": "evaluation/pbb_code.py",
    "evaluation_css_logical_detector": "evaluation/css_logical_detector.py",
    "evaluation_distance": "evaluation/distance.py",
    "evaluation_distance_sat": "evaluation/distance_sat.py",
    "evaluation_low_weight_oracle": "evaluation/low_weight_oracle.py",
    "evaluation_distance_milp": "evaluation/distance_milp.py",
    "evaluation_proof_runtime": "evaluation/proof_runtime.py",
    "evaluation_final_gate": "evaluation/final_gate.py",
    "evaluation_target_policy": "evaluation/target_policy.py",
    "evaluation_search_contract": "evaluation/search_contract.py",
    "evaluation_algebraic_mechanisms": "evaluation/algebraic_mechanisms.py",
    "evaluation_structural_features": "evaluation/structural_features.py",
    "evaluation_tanner_equivalence": "evaluation/tanner_equivalence.py",
    "evolution_dependency_contract": "evolve/dependency_contract.py",
}


# Additional executable and preregistered inputs for the checkpoint-
# incompatible full-support published-volume ansatz.  They are conditional so
# historical representations retain their exact dependency shape.
ANSATZ_V3_EVALUATOR_DEPENDENCIES = {
    "ansatz_v3_formal_audit_quota": (
        "configs/twisted_torus_ansatz_v3.formal_audit_quota.v1.json"
    ),
    "ansatz_v3_finite_domain": (
        "configs/twisted_torus_ansatz_v3.finite_domain.v1.json"
    ),
    "ansatz_v3_dual_track_preregistration": (
        "configs/twisted_torus_ansatz_v3.dual_track.v1.json"
    ),
    "ansatz_v3_contract_validator": "evaluation/ansatz_v3_contract.py",
    "ansatz_v3_program_capability_guard": (
        "evaluation/ansatz_v3_program_guard.py"
    ),
    "ansatz_v3_codex_sanitized_view": (
        "evolve/ansatz_v3_codex_view.py"
    ),
    "ansatz_v3_dual_track_planner": (
        "evaluation/ansatz_v3_dual_track.py"
    ),
    "ansatz_v3_formal_audit_selector": "evaluation/formal_audit_quota.py",
    "ansatz_v3_witness_fingerprint": (
        "evaluation/ansatz_witness_fingerprint.py"
    ),
    "ansatz_v3_blind_calibration": (
        "scripts/verify_blind_ansatz_v3_calibration.py"
    ),
    "ansatz_v3_realized_domain_manifest": (
        "scripts/build_ansatz_v3_domain_manifest.py"
    ),
    "ansatz_v3_family_switch_gate": (
        "scripts/evaluate_ansatz_v3_family_switch.py"
    ),
    "ansatz_v3_dual_track_plan_builder": (
        "scripts/build_ansatz_v3_dual_track_plan.py"
    ),
}


# Extra immutable inputs used only by the coset two-block evaluator.  Keep
# this mapping shared by the launcher and Humanize transaction verifier: a
# dependency present on just one side would either make a completed slice
# unreplayable or, worse, leave executable search semantics unbound.
COSET_EVALUATOR_DEPENDENCIES = {
    "coset_search_contract": "evolve/coset_search_contract.py",
    "coset_policy_dsl": "evolve/coset_policy_dsl.py",
    "coset_policy_dsl_v3": "evolve/coset_policy_dsl_v3.py",
    "coset_policy_dispatch": "evolve/coset_policy_dispatch.py",
    "coset_mutation_preflight": "evolve/coset_mutation_preflight.py",
    "coset_negative_archive": "evolve/coset_negative_archive.py",
    "coset_candidate_log_wal": "evolve/openevolve_evaluator.py",
    "coset_construction_adapter": "evaluation/construction.py",
    "coset_builder": "evaluation/coset_two_block.py",
    "coset_sparse_kernel_oracle": (
        "evaluation/two_block_sparse_kernel_oracle.py"
    ),
    "coset_stage2_cache_binding_producer": (
        "scripts/audit_candidate_pool.py"
    ),
    "coset_witness_symmetry_verifier": "scripts/screen_frontier_sat.py",
    "coset_reviewer_contract": "humanize/reviewer.py",
    "coset_reviewer_activation": "humanize/coset_renderer_review.py",
    "coset_action_catalog_parser": "evaluation/coset_action_catalog.py",
    "coset_action_catalog": "evaluation/coset_two_block_actions.v1.json",
    "coset_action_catalog_v2": "evaluation/coset_two_block_actions.v2.json",
}
