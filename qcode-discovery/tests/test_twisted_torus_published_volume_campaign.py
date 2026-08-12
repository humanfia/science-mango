"""Contracts for the published-volume generalized-toric experiment."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path

from openevolve import Config

from evaluation.bb_code import build_bb_code, validate_terms
from evaluation.registry import check_code_novelty
from evaluation.structural_dedup import canonical_digest
from evaluation.search_contract import (
    FINAL_GATE_PARETO_LATTICES,
    PUBLISHED_VOLUME_CELL_VOLUMES,
    PUBLISHED_VOLUME_CONTINUITY_LATTICE,
    PUBLISHED_VOLUME_CONTINUITY_TWIST,
    PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    PUBLISHED_VOLUME_REPRESENTATION_ID,
    PUBLISHED_VOLUME_STAGE1_FITNESS_LATTICES,
    PUBLISHED_VOLUME_STAGE2_FITNESS_LATTICES,
    PUBLISHED_VOLUME_TARGET_LATTICES,
    PUBLISHED_VOLUME_THIN_LATTICE,
    PUBLISHED_VOLUME_THIN_TWIST,
    TWISTED_TORUS_GEOMETRY_CONTRACT,
    TWISTED_TARGET_LATTICES,
    allowed_twists,
    geometry_contract_for_representation,
    lattices_for_geometry_contract,
    stage2_deep_lattices_for_geometry_contract,
)
from evolve import run_evolution as launcher
from evolve.seed_solution_twisted_torus_published import (
    _expand_twist_quota,
    _normalise_support,
    _parameter_fallbacks,
)
from humanize.pipeline import PipelineConfig


PROJECT = Path(__file__).resolve().parents[1]
EVOLUTION_CONFIG = PROJECT / "evolve/config_twisted_torus_published.yaml"
PIPELINE_CONFIG = PROJECT / (
    "configs/five_stage_campaign."
    "twisted_torus_published_volume_v2_gpt56sol_20260812.json"
)
ANCHOR_MANIFEST = (
    PROJECT / "evaluation/twisted_torus_published_anchors.v1.json"
)
DECISION_RELEASE = PROJECT / (
    "configs/post_r4_decision.twisted_torus_lb_replay_20260812.json"
)
BROADER_DESIGN = PROJECT / (
    "configs/post_r4_broader_published_volume_coverage_design.v1.json"
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _published_seed_snapshot() -> dict:
    script = r'''import json
from collections import Counter
from evaluation.bb_code import build_bb_code
from evaluation.registry import check_code_novelty
from evaluation.search_contract import (
    EVOLUTION_LATTICES,
    PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    allowed_twists,
)
from evolve.seed_solution_twisted_torus_published import (
    PUBLISHED_CALIBRATION_ANCHORS,
    _normalise_support,
    generate_candidates,
)

total = 0
strata = 0
minimum = None
anchors = []
pools = {}
for ell, m in EVOLUTION_LATTICES:
    rows = generate_candidates(ell, m)
    pools[(ell, m)] = rows
    total += len(rows)
    counts = Counter(int(row["geometry"]["twist"]) for row in rows)
    required = set(allowed_twists(
        ell, m, contract=PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    ))
    assert set(counts) == required
    strata += len(required)
    minimum = min(counts.values()) if minimum is None else min(
        minimum, min(counts.values())
    )
for (ell, m, twist), anchor in PUBLISHED_CALIBRATION_ANCHORS.items():
    rows = pools.get((ell, m))
    if rows is None:
        rows = generate_candidates(ell, m)
    target_a = list(_normalise_support(
        [(0, 0), (1, 0), anchor["third_a"]], ell, m, twist=twist
    ))
    target_b = list(_normalise_support(
        [(0, 0), (0, 1), anchor["third_b"]], ell, m, twist=twist
    ))
    matches = [
        row for row in rows
        if int(row["geometry"]["twist"]) == twist
        and row["A_terms"] == target_a
        and row["B_terms"] == target_b
    ]
    assert len(matches) == 1
    row = matches[0]
    code = build_bb_code(
        ell, m, row["A_terms"], row["B_terms"], geometry=row["geometry"]
    )
    novelty = check_code_novelty(code, code_type="css")
    literature = [
        item for item in novelty["matched_entries"]
        if item["id"].startswith("literature-liang-")
    ]
    anchors.append({
        "key": [ell, m, twist],
        "nk": [int(code.num_qudits), int(code.dimension)],
        "reported": list(anchor["parameters"][:2]),
        "novel": novelty["novel"],
        "replayed": [item["replay"]["verified"] for item in literature],
    })
print(json.dumps({
    "lattices": len(EVOLUTION_LATTICES),
    "strata": strata,
    "rows": total,
    "minimum": minimum,
    "anchors": sorted(anchors, key=lambda item: item["key"]),
}))
'''
    environment = dict(os.environ)
    environment["QCODE_SEARCH_GEOMETRY_CONTRACT"] = (
        PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    )
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    completed = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=PROJECT,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(completed.stdout)


def test_published_volume_contract_expands_only_missing_fertile_volumes():
    expected = (
        (1, 127),
        *(
            (ell, volume // ell)
            for volume in PUBLISHED_VOLUME_CELL_VOLUMES
            if volume != 127
            for ell in range(2, volume)
            if volume % ell == 0 and volume // ell >= 2
        ),
    )
    assert PUBLISHED_VOLUME_TARGET_LATTICES == expected
    assert len(PUBLISHED_VOLUME_TARGET_LATTICES) == 41
    assert all(ell * m != 144 for ell, m in PUBLISHED_VOLUME_TARGET_LATTICES)
    assert set(PUBLISHED_VOLUME_TARGET_LATTICES).isdisjoint(
        set(TWISTED_TARGET_LATTICES)
    )
    contracted = lattices_for_geometry_contract(
        PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    )
    assert contracted[:3] == FINAL_GATE_PARETO_LATTICES
    assert len(contracted) == 44
    assert sum(
        len(allowed_twists(
            ell, m, contract=PUBLISHED_VOLUME_GEOMETRY_CONTRACT
        ))
        for ell, m in contracted
    ) == 822
    assert allowed_twists(
        *PUBLISHED_VOLUME_THIN_LATTICE,
        contract=PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    ) == (PUBLISHED_VOLUME_THIN_TWIST,)
    assert allowed_twists(
        *PUBLISHED_VOLUME_CONTINUITY_LATTICE,
        contract=PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
    ) == (PUBLISHED_VOLUME_CONTINUITY_TWIST,)
    assert PUBLISHED_VOLUME_STAGE2_FITNESS_LATTICES == (
        (5, 21), (2, 62), (7, 18), (1, 127),
        (2, 66), (12, 12), (7, 21), (5, 34),
    )
    assert len(stage2_deep_lattices_for_geometry_contract(
        PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    )) == 11
    assert geometry_contract_for_representation(
        PUBLISHED_VOLUME_REPRESENTATION_ID
    ) == PUBLISHED_VOLUME_GEOMETRY_CONTRACT


def test_published_seed_fills_contracted_q_strata_and_replays_known_controls():
    result = _published_seed_snapshot()
    assert result["lattices"] == 44
    assert result["strata"] == 822
    assert result["rows"] == 3627
    assert result["minimum"] >= 3
    assert len(result["anchors"]) == 8
    for anchor in result["anchors"]:
        assert anchor["nk"] == anchor["reported"]
        assert anchor["novel"] is False
        assert anchor["replayed"] == [True]


def test_thin_published_lane_survives_empty_or_malformed_mutations():
    for proposals in ([], [None, {}, {"a": True, "b": 0, "c": 0, "d": 1}]):
        rows = _expand_twist_quota(1, 127, proposals, limit=60)
        assert len(rows) >= 3
        assert {int(row["geometry"]["twist"]) for row in rows} == {25}
        identities = {
            (
                tuple(map(tuple, row["A_terms"])),
                tuple(map(tuple, row["B_terms"])),
            )
            for row in rows
        }
        assert len(identities) == len(rows)
        canonical_a_anchors = set(_normalise_support(
            [(0, 0), (1, 0)], 1, 127, twist=25
        ))
        canonical_b_anchors = set(_normalise_support(
            [(0, 0), (0, 1)], 1, 127, twist=25
        ))
        for row in rows:
            assert canonical_a_anchors <= set(map(tuple, row["A_terms"]))
            assert canonical_b_anchors <= set(map(tuple, row["B_terms"]))
            validate_terms(1, 127, row["A_terms"], "A")
            validate_terms(1, 127, row["B_terms"], "B")
        codes = [
            build_bb_code(
                1,
                127,
                row["A_terms"],
                row["B_terms"],
                geometry=row["geometry"],
            )
            for row in rows
        ]
        matrix_digests = {canonical_digest(code) for code in codes}
        assert len(matrix_digests) >= 4
        assert {
            (int(code.num_qudits), int(code.dimension)) for code in codes[:4]
        } == {(254, 14)}
    assert _parameter_fallbacks(2, 62, 25) == []


def test_published_anchor_manifest_contains_only_strict_fom_controls():
    from evolve.seed_solution_twisted_torus_published import (
        PUBLISHED_CALIBRATION_ANCHORS,
    )

    manifest = json.loads(ANCHOR_MANIFEST.read_text(encoding="utf-8"))
    assert manifest["schema_version"] == 1
    assert manifest["source"]["arxiv"] == "2503.03827v3"
    assert len(manifest["anchors"]) == 8
    expected = {
        (row["ell"], row["m"], row["twist"]): {
            "third_a": tuple(row["third_a"]),
            "third_b": tuple(row["third_b"]),
            "parameters": (row["n"], row["k"], row["d"]),
        }
        for row in manifest["anchors"]
    }
    assert PUBLISHED_CALIBRATION_ANCHORS == expected
    for anchor in manifest["anchors"]:
        assert anchor["k"] * anchor["d"] ** 2 > 12 * anchor["n"]


def test_published_campaign_binds_model_target_seed_and_geometry():
    evolution = Config.from_yaml(str(EVOLUTION_CONFIG))
    assert launcher._search_portfolio_schema_version(EVOLUTION_CONFIG) == 3
    assert launcher._validated_search_portfolio_config(
        evolution, schema_version=3
    ) == 43
    assert evolution.evaluator.timeout == 2400

    pipeline = PipelineConfig.from_json(
        PIPELINE_CONFIG,
        repo_dir=PROJECT,
        run_id="published-volume-contract-test",
    )
    assert pipeline.target_mode == "scalar-fom-strict-v1"
    assert pipeline.max_total_workers == 12
    assert pipeline.flow_config is not None
    assert pipeline.flow_config.model == "gpt-5.6-sol"
    assert pipeline.flow_config.reasoning_effort == "xhigh"
    assert pipeline.flow_config.search_representation_id == (
        PUBLISHED_VOLUME_REPRESENTATION_ID
    )
    assert pipeline.flow_config.evolution_config == EVOLUTION_CONFIG
    assert pipeline.flow_config.evolution_seed == (
        PROJECT / "evolve/seed_solution_twisted_torus_published.py"
    )
    assert pipeline.stage3_backend == "sat-sectors"


def test_published_decision_release_binds_final_design_and_config():
    release = json.loads(DECISION_RELEASE.read_text(encoding="utf-8"))
    selected = release["selected_experiment"]
    assert release["decision"]["action"] == (
        "broader_published_volume_coverage"
    )
    assert release["decision"]["launch_authorized"] is True
    assert release["metrics"] == {
        "distinct_terminal_audits": 24,
        "lower_bound_audits": 20,
        "trusted_upper_bound_le_8": 17,
        "unknown_audits": 0,
        "exact_audits": 0,
        "wins": 0,
    }
    assert selected["design_sha256"] == _sha256(BROADER_DESIGN)
    assert selected["pipeline_config_sha256"] == _sha256(PIPELINE_CONFIG)


def test_published_private_evaluator_binds_v2_without_changing_v1():
    script = (
        "import json; "
        "from evaluation.search_contract import "
        "ACTIVE_GEOMETRY_CONTRACT,EVOLUTION_LATTICES; "
        "from evolve.openevolve_evaluator import "
        "STAGE1_LATTICES,STAGE2_DEEP_LATTICES; "
        "from evolve.run_evolution import _validated_search_geometry_contract; "
        "print(json.dumps([ACTIVE_GEOMETRY_CONTRACT,len(EVOLUTION_LATTICES),"
        "STAGE1_LATTICES,len(STAGE2_DEEP_LATTICES),"
        "_validated_search_geometry_contract(3)]))"
    )
    environment = dict(os.environ)
    environment["QCODE_SEARCH_GEOMETRY_CONTRACT"] = (
        PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    )
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    completed = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=PROJECT,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )
    active, count, probes, deep, bound = json.loads(completed.stdout)
    assert active == bound == PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    assert count == 44
    assert probes == [list(item) for item in PUBLISHED_VOLUME_STAGE1_FITNESS_LATTICES]
    assert deep == 11
    assert geometry_contract_for_representation(
        "css-bb-twisted-torus-generator-v1"
    ) == TWISTED_TORUS_GEOMETRY_CONTRACT


def test_published_invocation_rejects_cross_bound_v1_contract():
    script = r'''import json
from evolve import run_evolution as launcher

base = {
    "model_names": ["test-model"],
    "reasoning_effort": None,
    "codex_cli": False,
    "max_parallel_evaluations": 1,
    "api_base": "http://localhost:4000/v1",
    "temperature_disabled": False,
    "codex_version": None,
    "codex_cwd": None,
    "codex_executable_mode": None,
}
accepted = launcher._validated_invocation_binding({
    **base,
    launcher.SEARCH_GEOMETRY_CONTRACT_FIELD:
        "twisted-torus-published-volume-v2",
}, None, None)
rejected = False
try:
    launcher._validated_invocation_binding({
        **base,
        launcher.SEARCH_GEOMETRY_CONTRACT_FIELD: "twisted-torus-v1",
    }, None, None)
except RuntimeError:
    rejected = True
print(json.dumps([accepted[launcher.SEARCH_GEOMETRY_CONTRACT_FIELD], rejected]))
'''
    environment = dict(os.environ)
    environment["QCODE_SEARCH_GEOMETRY_CONTRACT"] = (
        PUBLISHED_VOLUME_GEOMETRY_CONTRACT
    )
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    completed = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=PROJECT,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )
    assert json.loads(completed.stdout) == [
        PUBLISHED_VOLUME_GEOMETRY_CONTRACT,
        True,
    ]


def test_reviewer_replays_witness_on_v2_only_lattice():
    """The reviewer allow-list must not silently discard new-volume evidence."""

    import copy
    import numpy as np

    from evaluation.distance_milp import symplectic_weight_witness
    from humanize.reviewer import build_review_prompt

    # A deterministic v2-only seed row whose replayable basis witness is
    # already below the strict challenge cutoff.
    ell, m, twist = 2, 66, 32
    geometry = {
        "schema_version": 1,
        "family": "twisted_torus",
        "twist": twist,
    }
    a_terms = [(0, 0), (0, 1), (1, 0)]
    b_terms = [(0, 0), (0, 1), (0, 65)]
    code = build_bb_code(ell, m, a_terms, b_terms, geometry=geometry)
    witness = symplectic_weight_witness(code)
    assert witness is not None
    assert int(np.sum(witness["bits"])) == witness["weight"]
    audited = {
        "ell": ell,
        "m": m,
        "n": int(code.num_qudits),
        "k": int(code.dimension),
        "A_terms": a_terms,
        "B_terms": b_terms,
        "geometry": geometry,
        "d_is_exact": False,
        "distance_trusted": True,
        "distance_status": "upper_bound",
        "distance_upper_bound": witness["weight"],
        "threshold_rejection_proven": True,
        "final_gate_excluded_by_upper_bound": True,
        "audit_attempt": {"schema_version": 2, "evidence": {}},
        "milp_details": {
            "minimum_direction_witness": copy.deepcopy(witness),
        },
    }
    prompt = build_review_prompt(
        round_number=1,
        contract={},
        candidates=[],
        audited=[audited],
        archive_top=[],
        memory="",
    )
    body = prompt.split("Round evidence JSON:\n", 1)[1]
    evidence = json.loads(
        body.split("\n\nReturn only the JSON object", 1)[0]
    )
    [projected] = evidence["milp_audited"]
    replayed = projected["replayed_low_weight_witness"]
    assert replayed["ell"] == ell
    assert replayed["m"] == m
    assert replayed["geometry"] == geometry
    assert replayed["weight"] == witness["weight"]
