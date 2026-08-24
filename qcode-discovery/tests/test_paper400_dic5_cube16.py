from __future__ import annotations

import ast
import copy
from pathlib import Path

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from investigations import paper400_dic5_cube16 as cube16


def _synthetic_instance() -> optimized.OptimizedInstance:
    hx = np.zeros((200, 400), dtype=np.uint8)
    hz = np.zeros_like(hx)
    lx = np.zeros((16, 400), dtype=np.uint8)
    lx[0, 0] = 1
    lz = np.zeros_like(lx)
    cnf = {
        "num_variables": 400,
        "num_clauses": 1,
        "operator_variables": list(range(1, 401)),
        "logical_variables": [1],
        "native_atmost": None,
        "clauses": [[1]],
    }
    cnf["cnf_sha256"] = optimized.canonical_sha256({
        "num_variables": cnf["num_variables"],
        "clauses": cnf["clauses"],
        "native_atmost": None,
    })
    report = optimized.seal({
        "schema_version": 1,
        "solver_invoked": False,
        "baseline": {"preflight_sha256": "a" * 64},
    }, "report_sha256")
    return optimized.OptimizedInstance(
        hx=hx,
        hz=hz,
        lx=lx,
        lz=lz,
        basis_checks=hx[:192].copy(),
        active_logical=lx[:1].copy(),
        cnf=cnf,
        dimacs=optimized.render_dimacs(cnf),
        report=report,
    )


@pytest.fixture()
def synthetic() -> optimized.OptimizedInstance:
    return _synthetic_instance()


@pytest.fixture()
def manifest(synthetic: optimized.OptimizedInstance) -> dict:
    return cube16.build_coverage_manifest(
        synthetic, strict_base=False, split_variables=(1, 2, 3, 4)
    )


def _forbid_solver(*args, **kwargs):  # type: ignore[no-untyped-def]
    raise AssertionError("a solver was invoked by a zero-solver path")


def test_source_has_no_solver_import_or_solve_call() -> None:
    path = Path(cube16.__file__)
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imports.add(node.module)
    assert "pysat" not in imports
    assert "pysat.solvers" not in imports
    assert ".solve(" not in source
    assert "subprocess" not in imports
    assert "multiprocessing" not in imports


def test_fake_cover_is_exact_mutually_exclusive_and_exhaustive(
    monkeypatch: pytest.MonkeyPatch,
    synthetic: optimized.OptimizedInstance,
    manifest: dict,
) -> None:
    monkeypatch.setattr(
        optimized, "solve_optimized_instance_in_process", _forbid_solver
    )
    assert manifest["test_only"] is True
    assert manifest["base"]["authority_status"] == cube16.AUTHORITY_TEST_ONLY
    assert manifest["split"]["variables_dimacs"] == [1, 2, 3, 4]
    assert len(manifest["cubes"]) == 16
    assert [cube["assignment_bits"] for cube in manifest["cubes"]] == [
        [int(bit) for bit in f"{index:04b}"] for index in range(16)
    ]
    assert manifest["coverage"]["pair_count_checked"] == 120
    assert manifest["coverage"]["mutually_exclusive"] is True
    assert manifest["coverage"]["exhaustive"] is True
    assert manifest["coverage"]["cube_sha256_sequence_sha256"] == (
        cube16._canonical_sha256([
            cube["cube_sha256"] for cube in manifest["cubes"]
        ])
    )
    assert len(manifest["coverage"]["cube_cnf_sha256_sequence_sha256"]) == 64
    for cube in manifest["cubes"]:
        assert cube["cube_num_clauses"] == 5
        assert cube["unit_clauses"] == [
            [variable if bit else -variable]
            for variable, bit in zip(
                (1, 2, 3, 4), cube["assignment_bits"], strict=True
            )
        ]
    replay = cube16.verify_coverage_manifest(
        manifest, synthetic, strict_base=False
    )
    assert replay["valid"] is True
    assert replay["coverage_mutually_exclusive"] is True
    assert replay["coverage_exhaustive"] is True
    assert replay["solver_invoked"] is False


def test_resealed_manifest_semantic_tamper_fails_replay(
    synthetic: optimized.OptimizedInstance,
    manifest: dict,
) -> None:
    changed = copy.deepcopy(manifest)
    changed["cubes"][0]["unit_clauses"][0] = [1]
    changed["cubes"][0] = cube16._seal(
        changed["cubes"][0], "cube_sha256"
    )
    changed = cube16._seal(changed, "manifest_sha256")
    replay = cube16.verify_coverage_manifest(
        changed, synthetic, strict_base=False
    )
    assert replay["valid"] is False
    assert "exact current-source canonical replay" in " ".join(
        replay["binding_failures"]
    )


def test_bundle_round_trip_and_byte_tamper(
    tmp_path: Path,
    synthetic: optimized.OptimizedInstance,
    manifest: dict,
) -> None:
    root = tmp_path / "cube-cover"
    cube16.write_bundle(root, manifest, synthetic, strict_base=False)
    replay = cube16.verify_bundle(root, synthetic, strict_base=False)
    assert replay["valid"] is True
    assert replay["artifact_count_checked"] == 17

    target = root / manifest["cubes"][3]["dimacs_relative_path"]
    target.write_bytes(target.read_bytes() + b"c tamper\n")
    changed = cube16.verify_bundle(root, synthetic, strict_base=False)
    assert changed["valid"] is False
    assert any("artifact" in failure for failure in changed["binding_failures"])


def test_fake_all_unsat_exercises_policy_without_scientific_claim(
    monkeypatch: pytest.MonkeyPatch,
    synthetic: optimized.OptimizedInstance,
    manifest: dict,
) -> None:
    monkeypatch.setattr(
        optimized, "solve_optimized_instance_in_process", _forbid_solver
    )
    results = [
        cube16.build_cube_terminal(
            manifest,
            synthetic,
            cube_index=index,
            outcome="unsat",
            elapsed_s=0.01,
            solver_time_s=0.005,
            solver_stats={"conflicts": index},
        )
        for index in range(16)
    ]
    aggregate = cube16.aggregate_cube_terminals(
        manifest, results, synthetic, strict_base=False
    )
    assert aggregate["all_16_indices_exactly_once"] is True
    assert aggregate["all_16_clean_current_source_unsat"] is True
    assert aggregate["status"] == (
        "TEST_ONLY_ALL_CUBES_UNSAT_NO_SCIENTIFIC_CLAIM"
    )
    assert aggregate["distance_lower_bound"] is None


@pytest.mark.parametrize("mode", ["unknown", "missing", "duplicate"])
def test_unknown_missing_or_duplicate_is_unresolved(
    mode: str,
    synthetic: optimized.OptimizedInstance,
    manifest: dict,
) -> None:
    results = [
        cube16.build_cube_terminal(
            manifest,
            synthetic,
            cube_index=index,
            outcome="unsat",
            elapsed_s=0.01,
            solver_time_s=0.005,
        )
        for index in range(16)
    ]
    if mode == "unknown":
        results[7] = cube16.build_cube_terminal(
            manifest,
            synthetic,
            cube_index=7,
            outcome="unknown",
            elapsed_s=0.01,
            solver_time_s=0.005,
        )
    elif mode == "missing":
        results.pop()
    else:
        results[-1] = copy.deepcopy(results[-2])
    aggregate = cube16.aggregate_cube_terminals(
        manifest, results, synthetic, strict_base=False
    )
    assert aggregate["status"] == "UNRESOLVED"
    assert aggregate["distance_lower_bound"] is None


def test_sat_needs_complete_cube_model_and_full_hx_lx_replay(
    synthetic: optimized.OptimizedInstance,
    manifest: dict,
) -> None:
    model = np.zeros(400, dtype=np.uint8)
    model[0] = 1
    sat = cube16.build_cube_terminal(
        manifest,
        synthetic,
        cube_index=8,  # bits 1000
        outcome="sat",
        full_model=model,
        elapsed_s=0.01,
        solver_time_s=0.005,
    )
    replay = cube16.classify_cube_terminal(sat, manifest, synthetic)
    assert replay["classification"] == "VERIFIED_SAT_LOW_OPERATOR"
    assert replay["official_full_matrix_witness_verifier_invoked"] is True
    assert replay["official_full_matrix_witness_failures"] == []

    wrong_cube = cube16.build_cube_terminal(
        manifest,
        synthetic,
        cube_index=0,
        outcome="sat",
        full_model=model,
        elapsed_s=0.01,
        solver_time_s=0.005,
    )
    wrong_cube_replay = cube16.classify_cube_terminal(
        wrong_cube, manifest, synthetic
    )
    assert wrong_cube_replay["classification"] == "INVALID"
    assert any(
        "does not satisfy bound cube CNF" in failure
        for failure in wrong_cube_replay["binding_failures"]
    )

    bad_hx = synthetic.hx.copy()
    bad_hx[0, 0] = 1
    changed = optimized.OptimizedInstance(
        hx=bad_hx,
        hz=synthetic.hz,
        lx=synthetic.lx,
        lz=synthetic.lz,
        basis_checks=bad_hx[:192],
        active_logical=synthetic.active_logical,
        cnf=synthetic.cnf,
        dimacs=synthetic.dimacs,
        report=synthetic.report,
    )
    official_failure = cube16.classify_cube_terminal(sat, manifest, changed)
    assert official_failure["classification"] == "INVALID"
    assert "operator has nonzero stabilizer syndrome" in official_failure[
        "official_full_matrix_witness_failures"
    ]


def test_verified_sat_short_circuits_other_unresolved_cubes(
    synthetic: optimized.OptimizedInstance,
    manifest: dict,
) -> None:
    model = np.zeros(400, dtype=np.uint8)
    model[0] = 1
    sat = cube16.build_cube_terminal(
        manifest,
        synthetic,
        cube_index=8,
        outcome="sat",
        full_model=model,
        elapsed_s=0.01,
        solver_time_s=0.005,
    )
    aggregate = cube16.aggregate_cube_terminals(
        manifest, [sat], synthetic, strict_base=False
    )
    assert aggregate["status"] == "REJECTED_LOW_OPERATOR"
    assert aggregate["strict_verified_sat_count"] == 1


def test_actual_final_v13_zero_solver_static_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        optimized, "solve_optimized_instance_in_process", _forbid_solver
    )
    instance = optimized.build_optimized_instance()
    manifest = cube16.build_coverage_manifest(instance, strict_base=True)
    assert manifest["base"]["cnf_sha256"] == cube16.EXPECTED_BASE_CNF_SHA256
    assert manifest["base"]["dimacs_sha256"] == (
        cube16.EXPECTED_BASE_DIMACS_SHA256
    )
    assert manifest["split"]["variables_dimacs"] == [173, 180, 195, 212]
    certificate = manifest["split"]["selection_certificate"]
    assert certificate["pairwise_clause_disjoint"] is True
    assert [
        (
            record["positive_occurrences"],
            record["negative_occurrences"],
        )
        for record in certificate["selected_occurrences"]
    ] == [(8, 34)] * 4
    assert manifest["coverage"]["mutually_exclusive"] is True
    assert manifest["coverage"]["exhaustive"] is True
    assert manifest["base"]["authority_status"] == (
        cube16.AUTHORITY_AUDITED_BASE
    )
    assert manifest["base"]["audit_binding"]["status"] == "PASS"
    assert manifest["base"]["audit_binding"]["focused_pytest"] == {
        "passed": 21, "failed": 0,
        "test_file": "tests/test_paper400_dic5_optimized_cnf_final_v13_final2.py",
    }
    assert manifest["resource_estimate"]["recommended_initial_parallelism"] == 2
