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
    "evaluation_pbb_code": "evaluation/pbb_code.py",
    "evaluation_distance": "evaluation/distance.py",
    "evaluation_distance_milp": "evaluation/distance_milp.py",
    "evaluation_proof_runtime": "evaluation/proof_runtime.py",
    "evaluation_final_gate": "evaluation/final_gate.py",
    "evaluation_search_contract": "evaluation/search_contract.py",
    "evaluation_algebraic_mechanisms": "evaluation/algebraic_mechanisms.py",
    "evaluation_structural_features": "evaluation/structural_features.py",
    "evaluation_tanner_equivalence": "evaluation/tanner_equivalence.py",
    "evolution_dependency_contract": "evolve/dependency_contract.py",
}
