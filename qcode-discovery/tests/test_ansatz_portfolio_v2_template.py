"""Fresh-launch contract for the CSS BB ansatz portfolio-v2 resource."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
from openevolve import Config

from evolve import run_evolution as launcher
from evolve import seed_solution_ansatz, seed_solution_noncss
from humanize.pipeline import PipelineConfig


PROJECT = Path(__file__).resolve().parents[1]
EVOLUTION_CONFIG = PROJECT / "evolve/config_ansatz_portfolio_v2.yaml"
CSS_SEED = PROJECT / "evolve/seed_solution_ansatz.py"
NONCSS_CONFIG = PROJECT / "evolve/config_noncss.yaml"
REPRESENTATION_ID = "css-bb-novel-ansatz-generator-v2"


def test_pipeline_config_loads_fresh_css_bb_representation_template(tmp_path):
    pipeline_path = tmp_path / "pipeline.json"
    pipeline_path.write_text(
        json.dumps(
            {
                "stage1": {
                    "evolution_config": "evolve/config_ansatz_portfolio_v2.yaml",
                    "evolution_seed": "evolve/seed_solution_ansatz.py",
                    "search_representation_id": REPRESENTATION_ID,
                    "max_rounds": 1,
                    "iterations_per_round": 1,
                    "milp_top": 0,
                },
                "stage2": {"top": 1},
                "stage3": {"top": 0},
            }
        )
    )

    pipeline = PipelineConfig.from_json(
        pipeline_path,
        repo_dir=PROJECT,
        run_id="ansatz-portfolio-v2-template-test",
    )

    assert pipeline.candidate_inputs == ()
    assert pipeline.flow_config is not None
    assert pipeline.flow_config.evolution_config == EVOLUTION_CONFIG
    assert pipeline.flow_config.evolution_seed == CSS_SEED
    assert pipeline.flow_config.search_representation_id == REPRESENTATION_ID


def test_portfolio_v2_config_uses_fixed_mechanism_support_orbit_geometry():
    config = Config.from_yaml(str(EVOLUTION_CONFIG))

    assert launcher._search_portfolio_requested(EVOLUTION_CONFIG) is True
    assert launcher._validated_search_portfolio_config(config) == 42
    assert config.database.num_islands == launcher.SEARCH_PORTFOLIO_ISLAND_COUNT
    assert config.database.feature_dimensions == list(
        launcher.SEARCH_PORTFOLIO_FEATURE_DIMENSIONS
    )
    assert config.database.feature_bins == launcher.SEARCH_PORTFOLIO_FEATURE_BINS


def test_matching_seed_is_css_two_polynomial_interface():
    candidates = seed_solution_ansatz.generate_candidates(6, 6)

    assert candidates
    assert all(isinstance(candidate, tuple) and len(candidate) == 2
               for candidate in candidates)
    for A_terms, B_terms in candidates:
        assert isinstance(A_terms, list)
        assert isinstance(B_terms, list)
        assert 2 <= len(A_terms)
        assert 2 <= len(B_terms)
        assert len(A_terms) + len(B_terms) <= 6
        assert all(
            isinstance(term, tuple)
            and len(term) == 2
            and all(isinstance(exponent, int) for exponent in term)
            for term in [*A_terms, *B_terms]
        )


def test_decoder_reference_weights_are_typed_only_as_upper_bounds():
    decoder_rows = [
        row
        for row in seed_solution_ansatz.KNOWN_CODES
        if "<=" in row["name"]
    ]

    assert decoder_rows
    for row in decoder_rows:
        assert row["expected"][2:] == (None, None)
        assert isinstance(row["distance_upper_bound"], int)
        assert row["distance_upper_bound"] > 0
        assert isinstance(row["fom_upper_bound"], float)
        assert row["fom_upper_bound"] > 0


def test_noncss_resources_cannot_masquerade_as_portfolio_v2_css_template():
    noncss_config = Config.from_yaml(str(NONCSS_CONFIG))
    noncss_candidates = seed_solution_noncss.generate_candidates(6, 6)

    assert launcher._search_portfolio_requested(NONCSS_CONFIG) is False
    with pytest.raises(RuntimeError, match="exactly five islands"):
        launcher._validated_search_portfolio_config(noncss_config)
    assert noncss_candidates
    assert all(isinstance(candidate, tuple) and len(candidate) == 4
               for candidate in noncss_candidates)
    assert not any(len(candidate) == 2 for candidate in noncss_candidates)
