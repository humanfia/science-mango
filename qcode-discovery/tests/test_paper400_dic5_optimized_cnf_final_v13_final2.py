from __future__ import annotations

import ast
import copy
import json
import os
import re
import shutil
import subprocess
import sys
import types
from pathlib import Path
from typing import Any, Callable

import numpy as np
import pytest

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized
from scripts import run_paper400_dic5_w6_optimized_cnf_final_v13 as runner


@pytest.fixture(scope="module")
def instance() -> optimized.OptimizedInstance:
    return optimized.build_optimized_instance()


def _imports(path: Path) -> set[str]:
    result: set[str] = set()
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
        if isinstance(node, ast.Import):
            result.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            result.add(node.module)
    return result


def _synthetic() -> optimized.OptimizedInstance:
    hx = np.zeros((1, 400), dtype=np.uint8)
    hz = np.zeros_like(hx)
    lx = np.zeros((1, 400), dtype=np.uint8)
    lx[0, 0] = 1
    cnf = {
        "num_variables": 400,
        "clauses": [[1]],
        "native_atmost": None,
        "logical_variables": [1],
        "num_clauses": 1,
    }
    cnf["cnf_sha256"] = optimized.canonical_sha256({
        "num_variables": 400, "clauses": [[1]], "native_atmost": None,
    })
    report = optimized.seal({
        "baseline": {"preflight_sha256": "1" * 64},
        "coset_minimal_certificate": {"reduced_clause_sha256": "2" * 64},
    }, "report_sha256")
    return optimized.OptimizedInstance(
        hx, hz, lx, np.zeros_like(lx), hx.copy(), lx.copy(), cnf,
        optimized.render_dimacs(cnf), report,
    )


def _identity(label: str = "a") -> dict[str, Any]:
    return optimized.seal({
        "schema_version": optimized.SCHEMA_VERSION,
        "label": label,
        "resume": False,
        "execution_mode": "single-process-in-process-v1",
    }, "identity_sha256")


def _rewrite(path: Path, value: dict[str, Any]) -> None:
    path.write_bytes(optimized.canonical_bytes(value) + b"\n")


def _production_context(root: Path, sources: dict[str, Any]) -> dict[str, Any]:
    runner_path = (runner.PROJECT / sources["runner_relative_path"]).resolve()
    checks = {
        "module_is_main": True,
        "main_file_is_runner": True,
        "argv0_is_runner": True,
        "argv_is_exact": True,
        "isolated_flag_is_one": True,
        "dont_write_bytecode_flag_is_one": True,
        "root_is_absolute": True,
    }
    early = optimized.seal({
        "schema_version": 1,
        "method": "direct-isolated-bytecode-free-cli-context-v1",
        "runner_realpath": str(runner_path),
        "main_file_realpath": str(runner_path),
        "argv0_realpath": str(runner_path),
        "normalized_invocation": ["run", "--root", str(root)],
        "checks": checks,
        "passed": True,
    }, "context_sha256")
    return optimized.seal({
        **{key: value for key, value in early.items() if key != "context_sha256"},
        "early_context_sha256": early["context_sha256"],
        "command_path_hash_matches_source_closure": True,
        "passed": True,
    }, "context_sha256")


def _safe_resource() -> dict[str, Any]:
    return runner._FROZEN_CALLABLES["baseline_resource_evaluator"](
        cpu=0,
        busy_percent=[0.0, 0.0, 0.0],
        niceness=19,
        affinity=[0],
        memory_current=0,
        memory_max=None,
        memory_stat={},
        memory_events={"oom": 0, "oom_kill": 0, "oom_group_kill": 0},
        memory_pressure={
            "full": {"avg10": 0.0, "avg60": 0.0, "avg300": 0.0, "total": 0}
        },
        thread_environment={name: "1" for name in runner.baseline.THREAD_ENV},
    )


def _build_production_fixture(
    root: Path, instance: optimized.OptimizedInstance,
) -> dict[str, Any]:
    output = runner.baseline.create_isolated_root(root)
    sources = runner.source_bundle()
    context = _production_context(output, sources)
    resource = _safe_resource()
    assert resource["passed"] is True
    assert runner._production_context_is_valid(context, output, sources)
    assert runner._resource_gate_is_valid(resource, enforced=True)
    dimacs = output / "input" / "optimized.cnf"
    manifest_path = output / "input" / "manifest.json"
    evidence_path = output / "state" / "evidence.json"
    progress_path = output / "state" / "progress.json"
    record_path = output / "sectors" / "Z.json"
    terminal_path = output / "terminal.json"
    runner._write_new_bytes(dimacs, instance.dimacs)
    campaign = runner._build_campaign_binding(
        output, sources, instance, dimacs, evidence_path, progress_path,
        context, solver_callback_injected=False, production_cli_requested=True,
        resource_gate_enforced=True,
    )
    identity = runner._build_checkpoint_identity(
        sources, instance, campaign, dimacs, evidence_path, progress_path,
    )
    manifest = runner._build_manifest(
        sources, resource, context, instance, campaign, identity,
        production_intent=True,
    )
    runner._write_new_json(manifest_path, manifest)
    evidence = optimized.build_terminal_evidence(
        instance, identity, outcome="unsat", elapsed_s=0.01,
        solver_time_s=0.005, solver_stats={"conflicts": 0},
    )
    record = optimized.classify_evidence(evidence, instance, identity)
    assert record["strict_current_source_unsat"] is True
    runner._write_new_json(evidence_path, evidence)
    runner._write_new_json(record_path, record)
    terminal = runner._build_terminal_payload(
        output, manifest_path, evidence_path, record_path, sources, instance,
        campaign, identity, context, record, evidence, production_intent=True,
    )
    assert runner._terminal_payload_failures(
        terminal, terminal_path, authoritative_terminal_present=False,
    ) == []
    runner._commit_new_json(terminal_path, terminal)
    return terminal


def _reseal_campaign_alias(
    root: Path, instance: optimized.OptimizedInstance,
    mutate: Callable[[dict[str, Any]], None],
) -> None:
    manifest_path = root / "input" / "manifest.json"
    evidence_path = root / "state" / "evidence.json"
    record_path = root / "sectors" / "Z.json"
    terminal_path = root / "terminal.json"
    manifest = runner._strict_json(manifest_path)
    campaign = copy.deepcopy(manifest["campaign_binding"])
    mutate(campaign)
    campaign = optimized.seal(campaign, "binding_sha256")
    identity = copy.deepcopy(manifest["checkpoint_identity"])
    identity["campaign_binding_sha256"] = campaign["binding_sha256"]
    identity = optimized.seal(identity, "identity_sha256")
    evidence = optimized.build_terminal_evidence(
        instance, identity, outcome="unsat", elapsed_s=0.01,
        solver_time_s=0.005,
    )
    record = optimized.classify_evidence(evidence, instance, identity)
    manifest["campaign_binding"] = campaign
    manifest["checkpoint_identity"] = identity
    manifest = optimized.seal(manifest, "manifest_sha256")
    _rewrite(manifest_path, manifest)
    _rewrite(evidence_path, evidence)
    _rewrite(record_path, record)
    terminal = runner._build_terminal_payload(
        root, manifest_path, evidence_path, record_path,
        manifest["source_bundle"], instance, campaign, identity,
        manifest["production_context"], record, evidence,
        production_intent=True,
    )
    _rewrite(terminal_path, terminal)


def test_only_final_v5_baseline_no_old_optimized_or_process_api() -> None:
    module = Path(optimized.__file__)
    cli = Path(runner.__file__)
    imports = _imports(module) | _imports(cli)
    source = module.read_text(encoding="utf-8") + cli.read_text(encoding="utf-8")
    assert "run_paper400_dic5_w6_lower_final_v5 as baseline" in source
    for version in list(range(1, 13)) + [100]:
        assert re.search(
            rf"optimized_cnf_final_v{version}\\b", source
        ) is None
    assert "multiprocessing" not in imports
    assert "subprocess" not in imports
    assert "marshal" not in imports
    assert "os.fork" not in source
    assert "Process(" not in source
    assert "__code__" not in source
    assert optimized.SOLVER_BUDGET_S == 43200.0
    assert optimized.REQUIRED_OUTER_HARD_TIMEOUT_S == 43600.0
    run_source = source[source.index("def run_campaign("):]
    assert run_source.index('"baseline_resource_gate"') < run_source.index(
        "sources_before = source_bundle()"
    ) < run_source.index('"optimized_builder"') < run_source.index(
        '"baseline_root_builder"'
    )


def test_formula_and_all_zero_solver_certificates(
    instance: optimized.OptimizedInstance,
) -> None:
    assert instance.report["solver_invoked"] is False
    assert instance.report["baseline"]["name"].endswith("final_v5")
    assert instance.report["baseline"]["preflight_sha256"] == (
        optimized.EXPECTED_BASELINE_PREFLIGHT_SHA256
    )
    assert (
        instance.cnf["num_variables"], instance.cnf["num_clauses"],
        instance.cnf["cnf_sha256"], len(instance.dimacs),
    ) == (
        2955, 12022, optimized.EXPECTED_OPTIMIZED_CNF_SHA256, 203044,
    )
    assert optimized.file_sha256(Path(sys.executable).resolve()) == (
        optimized.deterministic_runtime_seal()["python_executable_file_sha256"]
    )
    rowspace = instance.report["rowspace_certificate"]
    assert rowspace["full_rank"] == rowspace["basis_rank"] == 192
    assert rowspace["rowspace_equal"] is True
    assert len(rowspace["dropped_row_coefficients"]) == 8
    for row in rowspace["dropped_row_coefficients"]:
        coefficients = optimized._unpack_bits(
            row["coefficients"], expected_length=192,
        )
        assert np.array_equal(
            (coefficients @ instance.basis_checks) & 1,
            instance.hx[row["row_index"]],
        )
    projection = instance.report["logical_projection_certificate"]
    assert projection["active_logical_indices"] == [0]
    assert projection["operator_projection_equisatisfiable"] is True
    assert projection["xor_gate_truth_table"]["verified"] is True
    coset = instance.report["coset_minimal_certificate"]
    assert (coset["original_clause_count"], coset["reduced_clause_count"]) == (5000, 3000)
    assert coset["removed_subsumed_clause_count"] == 2000
    assert coset["truth_table_assignments_checked"] == 64
    assert coset["truth_table_equivalent"] is True
    assert coset["coset_representative_reduction_sound"] is True
    for name in ("w6", "logical_detector", "parity", "logical_symmetry", "xz_isometry"):
        assert type(instance.report["candidate_bindings"][name]) is dict


def test_clean_cli_and_imported_preflight_are_byte_equal() -> None:
    local = runner.build_preflight()
    command = [
        sys.executable, "-I", "-B", str(Path(runner.__file__).resolve()),
        "preflight",
    ]
    first = subprocess.run(
        command, check=True, capture_output=True, env=dict(os.environ), timeout=120,
    ).stdout
    second = subprocess.run(
        command, check=True, capture_output=True, env=dict(os.environ), timeout=120,
    ).stdout
    expected = optimized.canonical_bytes(local) + b"\n"
    assert first == second == expected
    closure = local["source_bundle"]["deterministic_project_source_closure"]
    assert len(closure["files_sha256"]) == 14
    assert closure["loaded_physical_sources"] == sorted(closure["files_sha256"])
    assert closure["complete"] is True
    runtime = local["source_bundle"]["deterministic_runtime_seal"]
    assert type(runtime["python_executable_file_sha256"]) is str
    assert set(runtime["modules"]) == {"pysat", "pysat.solvers", "pysolvers"}
    assert local["source_bundle"]["frozen_callable_seal"]["passed"] is True


def test_closure_rejects_alias_outside_and_originless_module() -> None:
    assert optimized.deterministic_source_closure()["complete"] is True
    cases = (
        ("evaluation.unapproved_alias", str(optimized.PROJECT / "evaluation/proof_runtime.py")),
        ("evaluation.outside_alias", "/tmp/outside_alias.py"),
        ("evaluation.no_origin", None),
        ("scripts.no_origin", None),
    )
    for name, origin in cases:
        module = types.ModuleType(name)
        if origin is not None:
            module.__file__ = origin
        sys.modules[name] = module
        try:
            with pytest.raises(optimized.Dic5OptimizedCnfFinalV13Error):
                optimized.deterministic_source_closure()
        finally:
            del sys.modules[name]


def test_strict_unsat_and_sat_full_matrix_replay() -> None:
    current = _synthetic()
    identity = _identity()
    unsat = optimized.build_terminal_evidence(
        current, identity, outcome="unsat", elapsed_s=0.01,
        solver_time_s=0.005,
    )
    lower = optimized.classify_evidence(unsat, current, identity)
    assert lower["status"] == "CURRENT_SOURCE_LOWER_20"
    assert type(lower["distance_lower_bound"]) is int
    assert lower["publication_certificate"] is False
    assert lower["upload_authorized"] is False
    model = np.zeros(400, dtype=np.uint8)
    model[0] = 1
    sat = optimized.build_terminal_evidence(
        current, identity, outcome="sat", full_model=model,
        elapsed_s=0.01, solver_time_s=0.005,
    )
    rejection = optimized.classify_evidence(sat, current, identity)
    assert rejection["status"] == "REJECTED_LOW_OPERATOR"
    assert rejection["official_full_matrix_witness_failures"] == []
    changed = _synthetic()
    changed.hx[0, 0] = 1
    replay = optimized.classify_evidence(sat, changed, identity)
    assert replay["status"] == "UNRESOLVED"
    assert "operator has nonzero stabilizer syndrome" in replay[
        "official_full_matrix_witness_failures"
    ]


def test_unsat_all_nested_json_aliases_fail_closed() -> None:
    current = _synthetic()
    identity = _identity()
    base = optimized.build_terminal_evidence(
        current, identity, outcome="unsat", elapsed_s=0.01,
        solver_time_s=0.005, solver_stats={"conflicts": 0},
    )
    changes: list[tuple[str, Callable[[dict[str, Any]], None]]] = [
        ("schema-bool", lambda e: e.__setitem__("schema_version", True)),
        ("schema-float", lambda e: e.__setitem__("schema_version", float(optimized.SCHEMA_VERSION))),
        ("kind-type", lambda e: e.__setitem__("evidence_kind", 1)),
        ("formulation-type", lambda e: e.__setitem__("formulation", True)),
        ("sector-type", lambda e: e.__setitem__("sector", 1)),
        ("weight-bool", lambda e: e.__setitem__("max_weight", True)),
        ("weight-float", lambda e: e.__setitem__("max_weight", 18.0)),
        ("partition-bool", lambda e: e.__setitem__("partition_index", False)),
        ("partition-float", lambda e: e.__setitem__("partition_index", 0.0)),
        ("anchors-tuple", lambda e: e.__setitem__("anchor_indices", ())),
        ("budget-int", lambda e: e.__setitem__("solver_budget_s", 43200)),
        ("outer-int", lambda e: e.__setitem__("required_outer_hard_timeout_s", 43600)),
        ("resumed-int", lambda e: e.__setitem__("resumed", 0)),
        ("timed-int", lambda e: e.__setitem__("timed_out", 0)),
        ("workers-bool", lambda e: e.__setitem__("workers", True)),
        ("workers-float", lambda e: e.__setitem__("workers", 1.0)),
        ("seed-bool", lambda e: e.__setitem__("random_seed", False)),
        ("calls-bool", lambda e: e.__setitem__("solver_invocations", True)),
        ("decision-int", lambda e: e.__setitem__("decision_complete", 1)),
        ("infeasible-int", lambda e: e.__setitem__("threshold_infeasible", 1)),
        ("success-int", lambda e: e.__setitem__("success", 0)),
        ("retry-int", lambda e: e.__setitem__("retryable", 0)),
        ("operator-nonnull", lambda e: e.__setitem__("operator", {})),
        ("objective-nonnull", lambda e: e.__setitem__("objective", 0)),
        ("syndrome-nonnull", lambda e: e.__setitem__("logical_syndrome", [])),
        ("model-nonnull", lambda e: e.__setitem__("full_model", {})),
        ("elapsed-int", lambda e: e.__setitem__("elapsed_s", 0)),
        ("solve-time-int", lambda e: e.__setitem__("solver_time_s", 0)),
        ("stats-bool", lambda e: e.__setitem__("solver_stats", {"conflicts": True})),
        ("drat-int", lambda e: e.__setitem__("durable_proof", {"drat": 0, "lrat": False})),
        ("publication-int", lambda e: e.__setitem__("publication_certificate", 0)),
        ("upload-int", lambda e: e.__setitem__("upload_authorized", 0)),
        ("instance-workers", lambda e: e["instance"].__setitem__("workers", True)),
        ("instance-extra", lambda e: e["instance"].__setitem__("extra", False)),
        ("cnf-count-float", lambda e: e["cnf"].__setitem__("num_variables", 400.0)),
        ("cnf-extra", lambda e: e["cnf"].__setitem__("extra", 0)),
        ("backend-extra", lambda e: e["backend"].__setitem__("extra", 0)),
        ("top-extra", lambda e: e.__setitem__("extra", 0)),
    ]
    for label, change in changes:
        forged = copy.deepcopy(base)
        change(forged)
        forged = optimized.seal(forged, "evidence_sha256")
        result = optimized.classify_evidence(forged, current, identity)
        assert result["status"] == "UNRESOLVED", label
        assert result["distance_lower_bound"] is None, label
        assert result["publication_certificate"] is False, label
        assert result["upload_authorized"] is False, label


def test_timing_budget_and_sat_packed_aliases_fail_closed() -> None:
    current = _synthetic()
    identity = _identity()
    unsat = optimized.build_terminal_evidence(
        current, identity, outcome="unsat", elapsed_s=0.01,
        solver_time_s=0.005,
    )
    for elapsed, solver_time in ((43200.001, 1.0), (1.0, 1.001)):
        forged = dict(unsat)
        forged["elapsed_s"] = elapsed
        forged["solver_time_s"] = solver_time
        forged = optimized.seal(forged, "evidence_sha256")
        assert optimized.classify_evidence(forged, current, identity)["status"] == "UNRESOLVED"
    nonfinite = dict(unsat)
    nonfinite["elapsed_s"] = float("inf")
    with pytest.raises(ValueError):
        optimized.seal(nonfinite, "evidence_sha256")
    with pytest.raises(ValueError):
        optimized.classify_evidence(nonfinite, current, identity)
    model = np.zeros(400, dtype=np.uint8)
    model[0] = 1
    sat = optimized.build_terminal_evidence(
        current, identity, outcome="sat", full_model=model,
        elapsed_s=0.01, solver_time_s=0.005,
    )
    changes = (
        lambda e: e.__setitem__("objective", True),
        lambda e: e.__setitem__("objective", 1.0),
        lambda e: e.__setitem__("logical_syndrome", [True]),
        lambda e: e["operator"].__setitem__("length", 400.0),
        lambda e: e["operator"].__setitem__("weight", True),
        lambda e: e["operator"].__setitem__("extra", 0),
        lambda e: e["full_model"].__setitem__("length", True),
        lambda e: e["full_model"].__setitem__("packed_hex", "00"),
        lambda e: e["full_model"].__setitem__("sha256", True),
    )
    for change in changes:
        forged = copy.deepcopy(sat)
        change(forged)
        forged = optimized.seal(forged, "evidence_sha256")
        assert optimized.classify_evidence(forged, current, identity)["status"] == "UNRESOLVED"
    with pytest.raises(optimized.Dic5OptimizedCnfFinalV13Error):
        optimized.build_terminal_evidence(
            current, identity, outcome="sat", full_model=np.zeros((1, 400)),
            elapsed_s=0.0, solver_time_s=0.0,
        )


@pytest.mark.parametrize("answer", [1, 0, 1.0, 0.0, np.bool_(True), np.bool_(False), None])
def test_solver_accepts_only_exact_bool(
    answer: Any, monkeypatch: pytest.MonkeyPatch,
) -> None:
    current = _synthetic()

    class FakeSolver:
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            pass

        def __enter__(self) -> "FakeSolver":
            return self

        def __exit__(self, *args: Any) -> None:
            return None

        def solve(self) -> Any:
            return answer

        def get_model(self) -> None:
            return None

        def time(self) -> float:
            return 0.0

        def accum_stats(self) -> dict[str, int]:
            return {}

    import pysat.solvers

    monkeypatch.setattr(pysat.solvers, "Solver", FakeSolver)
    with pytest.raises(optimized.Dic5OptimizedCnfFinalV13Error):
        optimized.solve_optimized_instance_in_process(current, _identity())


def test_resource_gate_is_first_and_failure_creates_nothing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[str] = []

    def gate() -> dict[str, Any]:
        calls.append("gate")
        raise runner.baseline.Paper400ValidationError("blocked")

    def forbidden(*args: Any, **kwargs: Any) -> Any:
        calls.append("forbidden")
        raise AssertionError("called after failed gate")

    monkeypatch.setitem(runner._FROZEN_CALLABLES, "baseline_resource_gate", gate)
    monkeypatch.setitem(runner._FROZEN_CALLABLES, "optimized_builder", forbidden)
    root = tmp_path / "gate-fail"
    with pytest.raises(runner.baseline.Paper400ValidationError):
        runner.run_campaign(root, solver_callback=forbidden, enforce_resource_gate=True)
    assert calls == ["gate"]
    assert not root.exists()


def test_imported_fake_unsat_is_never_promoted(
    tmp_path: Path,
) -> None:
    calls: list[str] = []

    def fake(
        current: optimized.OptimizedInstance, identity: dict[str, Any],
    ) -> dict[str, Any]:
        calls.append(identity["identity_sha256"])
        return optimized.build_terminal_evidence(
            current, identity, outcome="unsat", elapsed_s=0.01,
            solver_time_s=0.005,
        )

    root = tmp_path / "api-unsat"
    terminal = runner.run_campaign(
        root, solver_callback=fake, enforce_resource_gate=False,
    )
    assert len(calls) == 1
    assert terminal["status"] == "TEST_ONLY_UNRESOLVED"
    assert terminal["scientific_record_status"] == "CURRENT_SOURCE_LOWER_20"
    assert terminal["distance_lower_bound"] is None
    assert terminal["production_eligible"] is False
    assert terminal["strict_current_source_unsat"] is False
    assert terminal["publication_certificate"] is False
    assert terminal["upload_authorized"] is False
    replay = runner.validate_authoritative_terminal(root / "terminal.json")
    assert replay["valid"] is True
    assert replay["authoritative_current_source_lower"] is False


def test_unknown_and_sector_only_never_create_authoritative_terminal(
    tmp_path: Path,
) -> None:
    def unknown(
        current: optimized.OptimizedInstance, identity: dict[str, Any],
    ) -> dict[str, Any]:
        return optimized.build_terminal_evidence(
            current, identity, outcome="unknown", elapsed_s=0.01,
            solver_time_s=0.005, message="UNKNOWN",
        )

    root = tmp_path / "unknown"
    with pytest.raises(optimized.Dic5OptimizedCnfFinalV13Error):
        runner.run_campaign(
            root, solver_callback=unknown, enforce_resource_gate=False,
        )
    assert not (root / "terminal.json").exists()
    assert (root / "sectors" / "Z.json").is_file()
    assert runner.validate_authoritative_terminal(
        root / "terminal.json"
    )["authoritative_current_source_lower"] is False


def test_cli_without_bytecode_free_flag_fails_before_root(tmp_path: Path) -> None:
    root = tmp_path / "not-bytecode-free"
    completed = subprocess.run(
        [
            sys.executable, "-I", str(Path(runner.__file__).resolve()),
            "run", "--root", str(root),
        ],
        capture_output=True, env=dict(os.environ), timeout=30,
    )
    assert completed.returncode != 0
    assert b"production requires direct python -I -B" in completed.stderr
    assert not root.exists()


def test_atomic_commit_observer_never_sees_partial(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    target = tmp_path / "terminal.json"
    payload = optimized.seal({"schema_version": 1, "value": "complete"}, "sha256")
    expected = optimized.canonical_bytes(payload) + b"\n"
    observed: list[bytes] = []
    original_link = os.link

    def observing_link(
        source: str, destination: str, *, src_dir_fd: int,
        dst_dir_fd: int, follow_symlinks: bool,
    ) -> None:
        assert destination == target.name
        assert not target.exists()
        descriptor = os.open(source, os.O_RDONLY, dir_fd=src_dir_fd)
        try:
            observed.append(os.read(descriptor, len(expected) + 1))
        finally:
            os.close(descriptor)
        original_link(
            source, destination, src_dir_fd=src_dir_fd,
            dst_dir_fd=dst_dir_fd, follow_symlinks=follow_symlinks,
        )

    monkeypatch.setattr(os, "link", observing_link)
    runner._commit_new_json(target, payload)
    assert observed == [expected]
    assert target.read_bytes() == expected
    assert not list(tmp_path.glob(".terminal.json.private-*"))
    monkeypatch.setattr(os, "link", original_link)
    with pytest.raises(FileExistsError):
        runner._commit_new_json(target, payload)


def test_production_contract_fixture_and_coherent_aliases_fail_closed(
    tmp_path: Path, instance: optimized.OptimizedInstance,
) -> None:
    original = tmp_path / "production-fixture"
    terminal = _build_production_fixture(original, instance)
    assert terminal["production_eligible"] is True
    assert terminal["status"] == "CURRENT_SOURCE_LOWER_20"
    assert type(terminal["distance_lower_bound"]) is int
    replay = runner.validate_authoritative_terminal(original / "terminal.json")
    assert replay["valid"] is True
    assert replay["authoritative_current_source_lower"] is True
    mutations: tuple[tuple[str, Callable[[dict[str, Any]], None]], ...] = (
        ("schema-float", lambda c: c.__setitem__("schema_version", float(runner.SCHEMA_VERSION))),
        ("workers-bool", lambda c: c.__setitem__("workers", True)),
        ("partition-bool", lambda c: c.__setitem__("partition_index", False)),
        ("weight-float", lambda c: c.__setitem__("max_weight", 18.0)),
        ("injected-int", lambda c: c.__setitem__("solver_callback_injected", 0)),
        ("enforced-int", lambda c: c.__setitem__("resource_gate_enforced", 1)),
        ("extra-key", lambda c: c.__setitem__("extra", False)),
    )
    for label, mutate in mutations:
        clone = tmp_path / f"alias-{label}"
        shutil.copytree(original, clone)
        _reseal_campaign_alias(clone, instance, mutate)
        rejected = runner.validate_authoritative_terminal(clone / "terminal.json")
        assert rejected["valid"] is False, label
        assert rejected["authoritative_current_source_lower"] is False, label


def test_terminal_float_lower_and_extra_empty_or_partial_tree_rejected(
    tmp_path: Path, instance: optimized.OptimizedInstance,
) -> None:
    original = tmp_path / "original"
    _build_production_fixture(original, instance)
    floated = tmp_path / "float-lower"
    shutil.copytree(original, floated)
    terminal_path = floated / "terminal.json"
    terminal = runner._strict_json(terminal_path)
    terminal["root"] = str(floated)
    for role, relative in (
        ("manifest", "input/manifest.json"),
        ("evidence", "state/evidence.json"),
        ("record", "sectors/Z.json"),
    ):
        terminal[f"{role}_path"] = str(floated / relative)
    terminal["distance_lower_bound"] = 20.0
    terminal = optimized.seal(terminal, "terminal_sha256")
    _rewrite(terminal_path, terminal)
    rejected = runner.validate_authoritative_terminal(terminal_path)
    assert rejected["valid"] is False
    assert rejected["authoritative_current_source_lower"] is False
    extra = tmp_path / "extra-dir"
    shutil.copytree(original, extra)
    (extra / "unexpected-empty").mkdir()
    assert runner.validate_authoritative_terminal(
        extra / "terminal.json"
    )["valid"] is False
    partial = tmp_path / "partial"
    partial.mkdir()
    (partial / "terminal.json").write_bytes(b'{"schema_version":')
    assert runner.validate_authoritative_terminal(
        partial / "terminal.json"
    )["authoritative_current_source_lower"] is False
