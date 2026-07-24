import numpy as np

from scripts.search_frontier_mutations import (
    FRONTIER_SEEDS,
    candidate_key,
    mutate_seed,
)



def test_frontier_mutation_is_bounded_and_does_not_alias_seed():
    seed = FRONTIER_SEEDS[0]
    rng = np.random.default_rng(7)
    mutated = mutate_seed(rng, seed, radius=1, max_edits=2)
    assert mutated["A_terms"] is not seed["A_terms"]
    assert mutated["B_terms"] is not seed["B_terms"]
    assert len(mutated["A_terms"]) == len(seed["A_terms"])
    assert len(mutated["B_terms"]) == len(seed["B_terms"])
    for name in ("A_terms", "B_terms"):
        assert all(
            0 <= x < seed["ell"] and 0 <= y < seed["m"]
            for x, y in mutated[name]
        )


def test_frontier_key_ignores_order_and_binds_shape():
    seed = FRONTIER_SEEDS[0]
    reordered = {
        **seed,
        "A_terms": list(reversed(seed["A_terms"])),
    }
    reshaped = {**seed, "ell": 24}
    assert candidate_key(seed) == candidate_key(reordered)
    assert candidate_key(seed) != candidate_key(reshaped)


def test_second_generation_contains_two_distinct_d16_parents():
    labels = {seed["label"] for seed in FRONTIER_SEEDS}
    assert {"d16-trial-641", "d16-trial-2788"} <= labels


def test_small_pareto_fronts_are_search_seeds():
    labels = {seed["label"] for seed in FRONTIER_SEEDS}
    assert {
        "pareto-72-12-6", "pareto-90-8-10", "pareto-108-8-10",
    } <= labels
