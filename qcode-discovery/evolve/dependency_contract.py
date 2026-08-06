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
    "evaluation_search_contract": "evaluation/search_contract.py",
    "evaluation_algebraic_mechanisms": "evaluation/algebraic_mechanisms.py",
    "evaluation_structural_features": "evaluation/structural_features.py",
    "evaluation_tanner_equivalence": "evaluation/tanner_equivalence.py",
    "evolution_dependency_contract": "evolve/dependency_contract.py",
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
