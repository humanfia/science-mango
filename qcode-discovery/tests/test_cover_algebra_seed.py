"""Contracts for the cover/algebra-mechanism campaign seed."""

from collections import Counter
from pathlib import Path

from evaluation.algebraic_mechanisms import RELATION_TYPES, classify_algebraic_mechanism
from evaluation.search_contract import EVOLUTION_LATTICES
from evaluation.structural_dedup import check_css_static_eligibility
from evolve import run_evolution as launcher
from evolve.seed_solution_cover_algebra import (
    CHALLENGE_TERM_SPLITS,
    MAX_SEED_PER_CELL,
    QUOTIENT_LIFT_BASES,
    _canonical_candidate_key,
    _lift_quotient_pair,
    generate_candidates,
)
from humanize.pipeline import PipelineConfig
from openevolve import Config


PROJECT = Path(__file__).resolve().parents[1]


def test_cover_algebra_seed_is_deterministic_and_challenge_legal():
    first = generate_candidates(12, 12)
    second = generate_candidates(12, 12)

    assert first == second
    assert 200 <= len(first) <= 500
    assert len({(tuple(A), tuple(B)) for A, B in first}) == len(first)
    assert len(
        {_canonical_candidate_key(A, B, 12, 12) for A, B in first}
    ) == len(first)
    for A, B in first:
        assert (len(A), len(B)) in CHALLENGE_TERM_SPLITS
        assert len(A) + len(B) <= 6
        assert len(A) == len(set(A))
        assert len(B) == len(set(B))
        assert sorted(A) != sorted(B)
        assert all(0 <= x < 12 and 0 <= y < 12 for x, y in A + B)


def test_cover_algebra_seed_covers_every_mechanism_and_support_split():
    candidates = generate_candidates(12, 12)
    mechanisms = Counter(
        classify_algebraic_mechanism(A, B, ell=12, m=12)["relation_type"]
        for A, B in candidates
    )
    splits = Counter((len(A), len(B)) for A, B in candidates)

    assert set(mechanisms) == set(RELATION_TYPES)
    assert set(splits) == set(CHALLENGE_TERM_SPLITS)
    # Affine equivalence requires equal cardinality, so under the immutable
    # per-cell cap it has only the 2+2 and 3+3 cells available.  Requiring both
    # cells to fill is the strongest balanced lower bound compatible with the
    # 300-row global cap.
    assert min(mechanisms.values()) >= 2 * MAX_SEED_PER_CELL
    assert min(splits.values()) >= MAX_SEED_PER_CELL


def test_small_preflight_lattices_retain_all_mechanism_lanes():
    for ell, m in ((6, 6), (12, 6)):
        observed = {
            classify_algebraic_mechanism(A, B, ell=ell, m=m)["relation_type"]
            for A, B in generate_candidates(ell, m)
        }
        assert observed == set(RELATION_TYPES)


def test_seed_canonical_key_removes_common_translations_and_a_b_exchange():
    ell, m = 12, 6
    A = [(11, 5), (0, 0), (2, 1)]
    B = [(4, 3), (7, 2)]
    translated_a = [((x + 5) % ell, (y + 4) % m) for x, y in A]
    translated_b = [((x + 5) % ell, (y + 4) % m) for x, y in B]

    expected = _canonical_candidate_key(A, B, ell, m)
    assert _canonical_candidate_key(
        translated_a, translated_b, ell, m
    ) == expected
    assert _canonical_candidate_key(B, A, ell, m) == expected
    assert _canonical_candidate_key(
        translated_b, translated_a, ell, m
    ) == expected


def test_explicit_quotient_lift_projects_to_declared_base_support():
    base = next(item for item in QUOTIENT_LIFT_BASES if item[1:3] == (6, 6))
    _name, base_ell, base_m, base_a, base_b = base
    target_a, target_b = _lift_quotient_pair(
        base, 12, 12, fiber_pattern=1
    )

    assert {
        (x % base_ell, y % base_m) for x, y in target_a
    } == set(base_a)
    assert {
        (x % base_ell, y % base_m) for x, y in target_b
    } == set(base_b)
    generated = {
        _canonical_candidate_key(A, B, 12, 12)
        for A, B in generate_candidates(12, 12)
    }
    assert _canonical_candidate_key(target_a, target_b, 12, 12) in generated


def test_full_contract_seed_volume_is_bounded():
    pools = {
        lattice: generate_candidates(*lattice)
        for lattice in EVOLUTION_LATTICES
    }
    counts = {lattice: len(rows) for lattice, rows in pools.items()}

    assert len(counts) == 21
    assert min(counts.values()) >= 200
    assert max(counts.values()) <= 500
    assert sum(counts.values()) <= 10_000
    for (ell, m), rows in pools.items():
        mechanisms = {
            classify_algebraic_mechanism(A, B, ell=ell, m=m)["relation_type"]
            for A, B in rows
        }
        splits = {(len(A), len(B)) for A, B in rows}
        assert mechanisms == set(RELATION_TYPES), (ell, m, mechanisms)
        assert splits == set(CHALLENGE_TERM_SPLITS), (ell, m, splits)


def test_real_stage1_seed_has_three_static_eligible_candidates_per_mechanism():
    for ell, m in ((6, 6), (12, 6)):
        eligible = Counter()
        for A, B in generate_candidates(ell, m):
            audit = check_css_static_eligibility(ell, m, A, B)
            if audit["eligible"]:
                relation = classify_algebraic_mechanism(
                    A, B, ell=ell, m=m
                )["relation_type"]
                eligible[relation] += 1
        assert set(eligible) == set(RELATION_TYPES), (ell, m, eligible)
        assert min(eligible.values()) >= 3, (ell, m, eligible)


def test_cover_campaign_configs_bind_the_new_geometry_and_seed():
    evolution = Config.from_yaml(
        str(PROJECT / "evolve/config_cover_algebra.yaml")
    )
    assert launcher._validated_search_portfolio_config(evolution) == 42
    pipeline = PipelineConfig.from_json(
        PROJECT / "configs/five_stage_campaign.cover_algebra.json",
        repo_dir=PROJECT,
        run_id="cover-algebra-config-test",
    )
    assert pipeline.flow_config is not None
    assert pipeline.flow_config.evolution_config == (
        PROJECT / "evolve/config_cover_algebra.yaml"
    )
    assert pipeline.flow_config.evolution_seed == (
        PROJECT / "evolve/seed_solution_cover_algebra.py"
    )
    assert pipeline.flow_config.milp_top == 6
