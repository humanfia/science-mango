#!/usr/bin/env python3
"""Production runner for the self-contained optimized Dic5 final-v5 CNF.

The only production entrypoint is a direct ``python -I -B`` execution of this
file.  It performs the frozen final-v5 shared-host gate before rebuilding any
source, candidate, or CNF artifact.  The actual CaDiCaL call is in-process and
single-threaded.  A fixed 43200 second solver budget is evidence policy; an
external 43600 second watchdog is required and is deliberately not claimed as
internally enforced.  A watchdog kill cannot expose a partial authoritative terminal commit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any, Callable, Mapping


THREAD_ENV = (
    "OMP_NUM_THREADS", "OMP_THREAD_LIMIT", "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS",
    "BLIS_NUM_THREADS", "NUMBA_NUM_THREADS", "GOTO_NUM_THREADS",
)
for _environment_name in THREAD_ENV:
    os.environ[_environment_name] = "1"

PROJECT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT))

from evaluation import paper400_dic5_optimized_cnf_final_v13 as optimized  # noqa: E402
from scripts import run_paper400_dic5_w6_lower_final_v5 as baseline  # noqa: E402
import pysat.solvers as pysat_solvers  # noqa: E402


SCHEMA_VERSION = 14
GATE = "qcode-paper400-dic5-optimized-coset-cnf-runner-final-v13"
SolverCallback = Callable[..., Mapping[str, Any]]
_PRODUCTION_CLI_NONCE = object()
TERMINAL_FIELDS = frozenset({
    "schema_version", "gate", "status", "scientific_record_status",
    "distance_lower_bound", "root", "manifest_path", "manifest_file_sha256",
    "manifest_sha256", "evidence_path", "evidence_file_sha256",
    "evidence_sha256", "record_path", "record_file_sha256", "record_sha256",
    "source_bundle_sha256", "runtime_sha256", "optimized_report_sha256",
    "campaign_binding_sha256", "checkpoint_identity_sha256",
    "production_context", "solver_invocations", "execution_mode",
    "solver_budget_s", "required_outer_hard_timeout_s",
    "outer_watchdog_policy", "outer_watchdog_internally_enforced", "resume",
    "workers", "production_eligible", "test_only",
    "strict_verified_sat_rejection", "strict_current_source_unsat",
    "official_full_matrix_witness_failures", "publication_certificate",
    "upload_authorized", "publication_blocker", "terminal_sha256",
})


_CALLABLE_SPECS = (
    ("optimized_builder", optimized, "build_optimized_instance"),
    ("optimized_solver", optimized, "solve_optimized_instance_in_process"),
    ("optimized_source_closure", optimized, "deterministic_source_closure"),
    ("optimized_runtime_seal", optimized, "deterministic_runtime_seal"),
    ("optimized_classifier", optimized, "classify_evidence"),
    ("optimized_terminal_builder", optimized, "build_terminal_evidence"),
    ("baseline_resource_gate", baseline, "require_resource_gate"),
    ("baseline_resource_evaluator", baseline, "_evaluate_resource_gate"),
    ("baseline_official_witness", baseline, "verify_css_threshold_sat_witness"),
    ("baseline_root_builder", baseline, "create_isolated_root"),
    ("baseline_source_bundle", baseline, "source_bundle"),
)
_FROZEN_CALLABLES = {
    label: getattr(owner, attribute)
    for label, owner, attribute in _CALLABLE_SPECS
}
_FROZEN_PYSAT_SOLVER = pysat_solvers.Solver


def _callable_seal() -> dict[str, Any]:
    records: dict[str, Any] = {}
    passed = True
    for label, owner, attribute in _CALLABLE_SPECS:
        frozen = _FROZEN_CALLABLES[label]
        current = getattr(owner, attribute, None)
        same_object = current is frozen
        expected_module = (
            "evaluation.distance_sat"
            if label == "baseline_official_witness"
            else owner.__name__
        )
        expected_relative = (
            "evaluation/paper400_dic5_optimized_cnf_final_v13.py"
            if owner is optimized
            else "scripts/run_paper400_dic5_w6_lower_final_v5.py"
        )
        owner_origin = getattr(owner, "__file__", None)
        try:
            owner_path = Path(owner_origin).resolve(strict=True)
            owner_relative = owner_path.relative_to(PROJECT.resolve()).as_posix()
            owner_file_sha256 = optimized.file_sha256(owner_path)
        except (TypeError, OSError, RuntimeError, ValueError):
            owner_relative = None
            owner_file_sha256 = None
        record_passed = bool(
            same_object
            and getattr(frozen, "__module__", None) == expected_module
            and getattr(frozen, "__name__", None) == attribute
            and getattr(frozen, "__qualname__", None) == attribute
            and owner_relative == expected_relative
            and type(owner_file_sha256) is str
            and len(owner_file_sha256) == 64
        )
        records[label] = {
            "module": getattr(frozen, "__module__", None),
            "name": getattr(frozen, "__name__", None),
            "qualname": getattr(frozen, "__qualname__", None),
            "owner_relative_path": owner_relative,
            "owner_file_sha256": owner_file_sha256,
            "same_object": same_object,
            "passed": record_passed,
        }
        passed = passed and record_passed
    solver_origin = Path(pysat_solvers.__file__).resolve(strict=True)
    solver_same_object = pysat_solvers.Solver is _FROZEN_PYSAT_SOLVER
    solver_record = {
        "module": getattr(_FROZEN_PYSAT_SOLVER, "__module__", None),
        "name": getattr(_FROZEN_PYSAT_SOLVER, "__name__", None),
        "qualname": getattr(_FROZEN_PYSAT_SOLVER, "__qualname__", None),
        "owner_realpath": str(solver_origin),
        "owner_file_sha256": optimized.file_sha256(solver_origin),
        "same_object": solver_same_object,
        "passed": bool(
            solver_same_object
            and getattr(_FROZEN_PYSAT_SOLVER, "__module__", None) == "pysat.solvers"
            and getattr(_FROZEN_PYSAT_SOLVER, "__name__", None) == "Solver"
            and getattr(_FROZEN_PYSAT_SOLVER, "__qualname__", None) == "Solver"
        ),
    }
    records["pysat_solver_class"] = solver_record
    passed = passed and solver_record["passed"]
    return optimized.seal({
        "schema_version": 2,
        "method": "frozen-callables-and-pysat-solver-physical-source-v2",
        "records": records,
        "passed": passed,
    }, "callable_seal_sha256")


def _write_new_bytes(path: Path, payload: bytes) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(target, flags, 0o600)
    try:
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise OSError("short write while sealing artifact")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    directory = os.open(target.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def _write_new_json(path: Path, value: Mapping[str, Any]) -> None:
    _write_new_bytes(path, optimized.canonical_bytes(value) + b"\n")


def _commit_new_json(path: Path, value: Mapping[str, Any]) -> None:
    """Expose a complete terminal through an atomic no-replace hard link."""

    target = Path(path)
    parent = target.parent
    if (
        not parent.is_dir() or parent.is_symlink()
        or parent.resolve(strict=True) != parent
        or target.name in {"", ".", ".."}
    ):
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            "terminal parent is not a canonical real directory"
        )
    payload = optimized.canonical_bytes(value) + b"\n"
    directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    directory_flags |= getattr(os, "O_NOFOLLOW", 0)
    directory = os.open(parent, directory_flags)
    temporary_name = (
        f".{target.name}.private-{os.getpid()}-{os.urandom(16).hex()}"
    )
    temporary_created = False
    try:
        before = os.fstat(directory)
        lexical = os.stat(parent, follow_symlinks=False)
        if (before.st_dev, before.st_ino) != (lexical.st_dev, lexical.st_ino):
            raise optimized.Dic5OptimizedCnfFinalV13Error(
                "terminal parent inode changed before commit"
            )
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
        flags |= getattr(os, "O_NOFOLLOW", 0)
        descriptor = os.open(temporary_name, flags, 0o600, dir_fd=directory)
        temporary_created = True
        try:
            view = memoryview(payload)
            while view:
                written = os.write(descriptor, view)
                if written <= 0:
                    raise OSError("short write while staging terminal")
                view = view[written:]
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        os.link(
            temporary_name, target.name,
            src_dir_fd=directory, dst_dir_fd=directory, follow_symlinks=False,
        )
        os.fsync(directory)
        os.unlink(temporary_name, dir_fd=directory)
        temporary_created = False
        os.fsync(directory)
        after = os.fstat(directory)
        lexical_after = os.stat(parent, follow_symlinks=False)
        if (
            (before.st_dev, before.st_ino) != (after.st_dev, after.st_ino)
            or (before.st_dev, before.st_ino)
            != (lexical_after.st_dev, lexical_after.st_ino)
        ):
            raise optimized.Dic5OptimizedCnfFinalV13Error(
                "terminal parent inode changed during commit"
            )
    finally:
        if temporary_created:
            try:
                os.unlink(temporary_name, dir_fd=directory)
                os.fsync(directory)
            except FileNotFoundError:
                pass
        os.close(directory)


def _strict_json(path: Path) -> dict[str, Any]:
    target = Path(path)
    if not target.is_file() or target.is_symlink():
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            f"not a regular evidence file: {target}"
        )
    before = target.stat()
    payload = target.read_bytes()
    after = target.stat()
    identity_before = (
        before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns,
        before.st_ctime_ns,
    )
    identity_after = (
        after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if identity_before != identity_after or len(payload) != before.st_size:
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            f"evidence file changed while reading: {target}"
        )

    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, item in items:
            if type(key) is not str or key in result:
                raise ValueError("duplicate or non-string JSON key")
            result[key] = item
        return result

    def reject_constant(value: str) -> Any:
        raise ValueError(f"non-finite JSON constant: {value}")

    try:
        value = json.loads(
            payload.decode("utf-8"), object_pairs_hook=pairs,
            parse_constant=reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            f"invalid strict JSON: {target}"
        ) from exc
    if type(value) is not dict:
        raise optimized.Dic5OptimizedCnfFinalV13Error("JSON root must be exact object")
    if payload != optimized.canonical_bytes(value) + b"\n":
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            f"JSON bytes are not canonical: {target}"
        )
    return value


def _selfhash_valid(value: Any, field: str) -> bool:
    if type(value) is not dict or type(value.get(field)) is not str:
        return False
    unsigned = dict(value)
    stored = unsigned.pop(field)
    try:
        return stored == optimized.canonical_sha256(unsigned)
    except (TypeError, ValueError):
        return False


def _early_direct_cli_context(root: Path) -> dict[str, Any]:
    runner_path = Path(__file__).resolve()
    main_module = sys.modules.get("__main__")
    main_origin = getattr(main_module, "__file__", None)
    try:
        main_realpath = None if main_origin is None else str(Path(main_origin).resolve())
        argv0_realpath = str(Path(sys.argv[0]).resolve())
    except (OSError, RuntimeError):
        main_realpath = argv0_realpath = None
    normalized_root = str(Path(root))
    exact_argv = [str(sys.argv[0]), "run", "--root", normalized_root]
    checks = {
        "module_is_main": __name__ == "__main__",
        "main_file_is_runner": main_realpath == str(runner_path),
        "argv0_is_runner": argv0_realpath == str(runner_path),
        "argv_is_exact": list(sys.argv) == exact_argv,
        "isolated_flag_is_one": type(sys.flags.isolated) is int and sys.flags.isolated == 1,
        "dont_write_bytecode_flag_is_one": (
            type(sys.flags.dont_write_bytecode) is int
            and sys.flags.dont_write_bytecode == 1
        ),
        "root_is_absolute": Path(root).is_absolute(),
    }
    return optimized.seal({
        "schema_version": 1,
        "method": "direct-isolated-bytecode-free-cli-context-v1",
        "runner_realpath": str(runner_path),
        "main_file_realpath": main_realpath,
        "argv0_realpath": argv0_realpath,
        "normalized_invocation": ["run", "--root", normalized_root],
        "checks": checks,
        "passed": all(value is True for value in checks.values()),
    }, "context_sha256")


def source_bundle() -> dict[str, Any]:
    closure = _FROZEN_CALLABLES["optimized_source_closure"]()
    runtime = _FROZEN_CALLABLES["optimized_runtime_seal"]()
    callables = _callable_seal()
    runner_relative = "scripts/run_paper400_dic5_w6_optimized_cnf_final_v13.py"
    module_relative = "evaluation/paper400_dic5_optimized_cnf_final_v13.py"
    baseline_relative = "scripts/run_paper400_dic5_w6_lower_final_v5.py"
    result = optimized.seal({
        "schema_version": SCHEMA_VERSION,
        "deterministic_project_source_closure": closure,
        "deterministic_runtime_seal": runtime,
        "frozen_callable_seal": callables,
        "baseline_final_v5_source_bundle": (
            _FROZEN_CALLABLES["baseline_source_bundle"]()
        ),
        "runner_relative_path": runner_relative,
        "runner_file_sha256": closure["files_sha256"][runner_relative],
        "optimized_module_relative_path": module_relative,
        "optimized_module_file_sha256": closure["files_sha256"][module_relative],
        "baseline_relative_path": baseline_relative,
        "baseline_file_sha256": closure["files_sha256"][baseline_relative],
        "optimized_predecessor_dependency": False,
    }, "source_bundle_sha256")
    if callables["passed"] is not True:
        raise optimized.Dic5OptimizedCnfFinalV13Error("frozen callable seal failed")
    return result


def build_preflight() -> dict[str, Any]:
    sources_before = source_bundle()
    instance = _FROZEN_CALLABLES["optimized_builder"]()
    sources_after = source_bundle()
    if not optimized.json_type_equal(sources_after, sources_before):
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            "source/runtime closure changed during preflight rebuild"
        )
    return optimized.seal({
        "schema_version": SCHEMA_VERSION,
        "gate": GATE,
        "solver_invoked": False,
        "optimized_report": instance.report,
        "source_bundle": sources_before,
        "dimacs": {
            "sha256": hashlib.sha256(instance.dimacs).hexdigest(),
            "bytes": len(instance.dimacs),
            "cnf_sha256": instance.cnf["cnf_sha256"],
            "num_variables": instance.cnf["num_variables"],
            "num_clauses": instance.cnf["num_clauses"],
        },
        "execution": {
            "mode": "single-process-in-process-v1",
            "workers": 1,
            "resume": False,
            "solver_budget_s": optimized.SOLVER_BUDGET_S,
            "required_outer_hard_timeout_s": optimized.REQUIRED_OUTER_HARD_TIMEOUT_S,
            "outer_watchdog_policy": optimized.OUTER_WATCHDOG_POLICY,
            "outer_watchdog_internally_enforced": False,
            "hard_timeout_terminal_semantics": "no-valid-authoritative-terminal-is-unresolved",
            "required_production_python_flags": ["-I", "-B"],
            "recommended_outer_prefix": [
                "timeout", "43600", "choom", "-n", "1000", "ionice", "-c", "3",
            ],
        },
        "publication_certificate": False,
        "upload_authorized": False,
    }, "preflight_sha256")


def _write_wrapper_error(
    output_root: Path, manifest_sha256: str, calls: int, exc: BaseException,
) -> None:
    failure = optimized.seal({
        "schema_version": SCHEMA_VERSION,
        "gate": GATE,
        "status": "WRAPPER_ERROR_UNRESOLVED",
        "error_type": type(exc).__name__,
        "error": str(exc),
        "solver_invocations": calls,
        "manifest_sha256": manifest_sha256,
        "terminal_written": False,
        "publication_certificate": False,
        "upload_authorized": False,
    }, "failure_sha256")
    _write_new_json(output_root / "wrapper-error.json", failure)


def _authority() -> dict[str, Any]:
    return {
        "sat_requires_full_Hx_Lx_official_replay": True,
        "unsat_is_current_source_lower_only": True,
        "unknown_is_unresolved": True,
        "hard_timeout_produces_no_valid_authoritative_terminal": True,
        "outer_watchdog_internally_enforced": False,
        "resume": False,
        "workers": 1,
        "durable_drat_present": False,
        "durable_lrat_present": False,
        "publication_certificate": False,
        "upload_authorized": False,
    }


def _build_campaign_binding(
    output_root: Path, sources: Mapping[str, Any],
    instance: optimized.OptimizedInstance, dimacs_path: Path,
    evidence_path: Path, progress_path: Path, production_context: Mapping[str, Any],
    *, solver_callback_injected: bool, production_cli_requested: bool,
    resource_gate_enforced: bool,
) -> dict[str, Any]:
    return optimized.seal({
        "schema_version": SCHEMA_VERSION,
        "gate": GATE,
        "root": str(output_root),
        "source_bundle_sha256": sources["source_bundle_sha256"],
        "runtime_sha256": sources["deterministic_runtime_seal"]["runtime_sha256"],
        "callable_seal_sha256": sources["frozen_callable_seal"]["callable_seal_sha256"],
        "optimized_report_sha256": instance.report["report_sha256"],
        "cnf_sha256": instance.cnf["cnf_sha256"],
        "dimacs_path": str(dimacs_path),
        "dimacs_file_sha256": optimized.file_sha256(dimacs_path),
        "sector": "Z",
        "max_weight": 18,
        "partition_index": 0,
        "anchor_indices": [],
        "solver": "cadical195",
        "cardinality_encoding": "kmtotalizer",
        "workers": 1,
        "resume": False,
        "execution_mode": "single-process-in-process-v1",
        "solver_budget_s": optimized.SOLVER_BUDGET_S,
        "required_outer_hard_timeout_s": optimized.REQUIRED_OUTER_HARD_TIMEOUT_S,
        "outer_watchdog_policy": optimized.OUTER_WATCHDOG_POLICY,
        "outer_watchdog_internally_enforced": False,
        "checkpoint_path": str(evidence_path),
        "progress_path": str(progress_path),
        "solver_callback_injected": solver_callback_injected,
        "production_cli_requested": production_cli_requested,
        "resource_gate_enforced": resource_gate_enforced,
        "production_context_sha256": production_context["context_sha256"],
    }, "binding_sha256")


def _build_checkpoint_identity(
    sources: Mapping[str, Any], instance: optimized.OptimizedInstance,
    campaign_binding: Mapping[str, Any], dimacs_path: Path,
    evidence_path: Path, progress_path: Path,
) -> dict[str, Any]:
    return optimized.seal({
        "schema_version": SCHEMA_VERSION,
        "campaign_binding_sha256": campaign_binding["binding_sha256"],
        "source_bundle_sha256": sources["source_bundle_sha256"],
        "optimized_report_sha256": instance.report["report_sha256"],
        "cnf_sha256": instance.cnf["cnf_sha256"],
        "dimacs_file_sha256": optimized.file_sha256(dimacs_path),
        "checkpoint_path": str(evidence_path),
        "progress_path": str(progress_path),
        "resume": False,
        "workers": 1,
        "execution_mode": "single-process-in-process-v1",
    }, "identity_sha256")


def _build_manifest(
    sources: Mapping[str, Any], resource: Mapping[str, Any],
    production_context: Mapping[str, Any], instance: optimized.OptimizedInstance,
    campaign_binding: Mapping[str, Any], identity: Mapping[str, Any],
    *, production_intent: bool,
) -> dict[str, Any]:
    return optimized.seal({
        "schema_version": SCHEMA_VERSION,
        "gate": GATE,
        "status": "SEALED_NOT_RUN",
        "solver_invoked": False,
        "source_bundle": sources,
        "resource_gate": resource,
        "production_context": production_context,
        "production_intent": production_intent,
        "optimized_report": instance.report,
        "campaign_binding": campaign_binding,
        "checkpoint_identity": identity,
        "authority": _authority(),
    }, "manifest_sha256")


def _build_terminal_payload(
    output_root: Path, manifest_path: Path, evidence_path: Path, record_path: Path,
    sources: Mapping[str, Any], instance: optimized.OptimizedInstance,
    campaign_binding: Mapping[str, Any], identity: Mapping[str, Any],
    production_context: Mapping[str, Any], record: Mapping[str, Any],
    evidence: Mapping[str, Any], *, production_intent: bool,
) -> dict[str, Any]:
    strict_decision = bool(
        record["strict_verified_sat_rejection"] is True
        or record["strict_current_source_unsat"] is True
    )
    if not strict_decision:
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            "nonterminal/UNKNOWN evidence cannot produce terminal"
        )
    production_eligible = bool(production_intent and strict_decision)
    return optimized.seal({
        "schema_version": SCHEMA_VERSION,
        "gate": GATE,
        "status": (
            record["status"] if production_eligible else "TEST_ONLY_UNRESOLVED"
        ),
        "scientific_record_status": record["status"],
        "distance_lower_bound": (
            record["distance_lower_bound"] if production_eligible else None
        ),
        "root": str(output_root),
        "manifest_path": str(manifest_path),
        "manifest_file_sha256": optimized.file_sha256(manifest_path),
        "manifest_sha256": _strict_json(manifest_path)["manifest_sha256"],
        "evidence_path": str(evidence_path),
        "evidence_file_sha256": optimized.file_sha256(evidence_path),
        "evidence_sha256": evidence["evidence_sha256"],
        "record_path": str(record_path),
        "record_file_sha256": optimized.file_sha256(record_path),
        "record_sha256": record["record_sha256"],
        "source_bundle_sha256": sources["source_bundle_sha256"],
        "runtime_sha256": sources["deterministic_runtime_seal"]["runtime_sha256"],
        "optimized_report_sha256": instance.report["report_sha256"],
        "campaign_binding_sha256": campaign_binding["binding_sha256"],
        "checkpoint_identity_sha256": identity["identity_sha256"],
        "production_context": production_context,
        "solver_invocations": 1,
        "execution_mode": "single-process-in-process-v1",
        "solver_budget_s": optimized.SOLVER_BUDGET_S,
        "required_outer_hard_timeout_s": optimized.REQUIRED_OUTER_HARD_TIMEOUT_S,
        "outer_watchdog_policy": optimized.OUTER_WATCHDOG_POLICY,
        "outer_watchdog_internally_enforced": False,
        "resume": False,
        "workers": 1,
        "production_eligible": production_eligible,
        "test_only": not production_eligible,
        "strict_verified_sat_rejection": (
            record["strict_verified_sat_rejection"] if production_eligible else False
        ),
        "strict_current_source_unsat": (
            record["strict_current_source_unsat"] if production_eligible else False
        ),
        "official_full_matrix_witness_failures": record[
            "official_full_matrix_witness_failures"
        ],
        "publication_certificate": False,
        "upload_authorized": False,
        "publication_blocker": (
            "durable independently checked DRAT/LRAT proof is absent"
            if production_eligible and record["strict_current_source_unsat"] is True
            else None
        ),
    }, "terminal_sha256")


def _production_context_is_valid(
    context: Any, output_root: Path, sources: Mapping[str, Any],
) -> bool:
    if type(context) is not dict:
        return False
    runner_path = (PROJECT / sources["runner_relative_path"]).resolve()
    expected_checks = {
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
        "normalized_invocation": ["run", "--root", str(output_root)],
        "checks": expected_checks,
        "passed": True,
    }, "context_sha256")
    expected = optimized.seal({
        **{key: value for key, value in early.items() if key != "context_sha256"},
        "early_context_sha256": early["context_sha256"],
        "command_path_hash_matches_source_closure": True,
        "passed": True,
    }, "context_sha256")
    return optimized.json_type_equal(context, expected)


def _resource_gate_is_valid(resource: Any, *, enforced: bool) -> bool:
    if type(enforced) is not bool or type(resource) is not dict:
        return False
    if enforced is False:
        return optimized.json_type_equal(
            resource, {"passed": False, "test_override": True}
        )
    try:
        expected = _FROZEN_CALLABLES["baseline_resource_evaluator"](
            cpu=resource["cpu"],
            busy_percent=resource["busy_percent"],
            niceness=resource["niceness"],
            affinity=resource["affinity"],
            memory_current=resource["memory_current"],
            memory_max=resource["memory_max"],
            memory_stat=resource["memory_stat"],
            memory_events=resource["memory_events"],
            memory_pressure=resource["memory_pressure"],
            thread_environment=resource["thread_environment"],
        )
    except (KeyError, TypeError, ValueError, RuntimeError):
        return False
    return bool(
        optimized.json_type_equal(resource, expected)
        and resource.get("passed") is True
    )


def _closed_tree_failures(
    root: Path, *, authoritative_terminal_present: bool,
) -> list[str]:
    failures: list[str] = []
    expected_directories = {"input", "state", "sectors"}
    expected_files = {
        "input/optimized.cnf", "input/manifest.json",
        "state/evidence.json", "sectors/Z.json",
    }
    if authoritative_terminal_present:
        expected_files.add("terminal.json")
    if not root.is_dir() or root.is_symlink() or root.resolve(strict=True) != root:
        return ["result root is not a canonical real directory"]
    actual_directories: set[str] = set()
    actual_files: set[str] = set()
    try:
        for entry in root.rglob("*"):
            relative = entry.relative_to(root).as_posix()
            if entry.is_symlink():
                failures.append(f"symlink in result tree: {relative}")
            elif entry.is_dir():
                actual_directories.add(relative)
            elif entry.is_file():
                actual_files.add(relative)
            else:
                failures.append(f"non-regular result entry: {relative}")
    except OSError as exc:
        failures.append(f"result tree walk failed: {exc}")
    if actual_directories != expected_directories:
        failures.append("result directory set mismatch")
    if actual_files != expected_files:
        failures.append("result file set mismatch")
    return failures


def _terminal_payload_failures(
    terminal: Any, terminal_path: Path, *, authoritative_terminal_present: bool,
) -> list[str]:
    failures: list[str] = []
    if type(terminal) is not dict:
        return ["terminal payload must be exact object"]
    if set(terminal) != TERMINAL_FIELDS:
        failures.append("terminal field set mismatch")
    if not _selfhash_valid(terminal, "terminal_sha256"):
        failures.append("terminal self-hash mismatch")
    root_value = terminal.get("root")
    if type(root_value) is not str:
        return failures + ["terminal root type mismatch"]
    root = Path(root_value)
    expected_paths = {
        "dimacs": root / "input" / "optimized.cnf",
        "manifest": root / "input" / "manifest.json",
        "evidence": root / "state" / "evidence.json",
        "progress": root / "state" / "progress.json",
        "record": root / "sectors" / "Z.json",
        "terminal": root / "terminal.json",
    }
    if (
        not root.is_absolute()
        or terminal_path != expected_paths["terminal"]
        or terminal_path.parent != root
    ):
        failures.append("terminal/root path mismatch")
    failures.extend(_closed_tree_failures(
        root, authoritative_terminal_present=authoritative_terminal_present
    ))
    try:
        manifest = _strict_json(expected_paths["manifest"])
        evidence = _strict_json(expected_paths["evidence"])
        record = _strict_json(expected_paths["record"])
        for role, value, self_field in (
            ("manifest", manifest, "manifest_sha256"),
            ("evidence", evidence, "evidence_sha256"),
            ("record", record, "record_sha256"),
        ):
            if not _selfhash_valid(value, self_field):
                failures.append(f"{role} self-hash mismatch")
            if type(terminal.get(f"{role}_path")) is not str or Path(
                terminal[f"{role}_path"]
            ) != expected_paths[role]:
                failures.append(f"{role} path mismatch")
            if terminal.get(f"{role}_file_sha256") != optimized.file_sha256(
                expected_paths[role]
            ):
                failures.append(f"{role} physical hash mismatch")
            if terminal.get(self_field) != value.get(self_field):
                failures.append(f"{role} internal hash mismatch")
        sources = source_bundle()
        instance = _FROZEN_CALLABLES["optimized_builder"]()
        dimacs_path = expected_paths["dimacs"]
        if (
            dimacs_path.is_symlink() or not dimacs_path.is_file()
            or dimacs_path.read_bytes() != instance.dimacs
            or optimized.file_sha256(dimacs_path)
            != optimized.EXPECTED_OPTIMIZED_DIMACS_SHA256
        ):
            failures.append("physical DIMACS replay mismatch")
        campaign = manifest.get("campaign_binding")
        if type(campaign) is not dict:
            failures.append("campaign binding type mismatch")
            campaign = {}
        injected = campaign.get("solver_callback_injected")
        production_requested = campaign.get("production_cli_requested")
        resource_enforced = campaign.get("resource_gate_enforced")
        if type(injected) is not bool:
            failures.append("solver callback binding type mismatch")
        if type(production_requested) is not bool:
            failures.append("production CLI binding type mismatch")
        if type(resource_enforced) is not bool:
            failures.append("resource gate enforcement type mismatch")
        context = manifest.get("production_context")
        context_valid = _production_context_is_valid(context, root, sources)
        resource = manifest.get("resource_gate")
        resource_valid = (
            _resource_gate_is_valid(resource, enforced=resource_enforced)
            if type(resource_enforced) is bool else False
        )
        if not resource_valid:
            failures.append("resource gate replay mismatch")
        production_intent = bool(
            production_requested is True
            and injected is False
            and resource_enforced is True
            and resource_valid
            and context_valid
            and sources["frozen_callable_seal"]["passed"] is True
        )
        if production_requested is True and not context_valid:
            failures.append("production CLI context replay mismatch")
        expected_campaign = _build_campaign_binding(
            root, sources, instance, dimacs_path, expected_paths["evidence"],
            expected_paths["progress"], context,
            solver_callback_injected=(
                injected if type(injected) is bool else False
            ),
            production_cli_requested=(
                production_requested if type(production_requested) is bool else False
            ),
            resource_gate_enforced=(
                resource_enforced if type(resource_enforced) is bool else False
            ),
        )
        if not optimized.json_type_equal(campaign, expected_campaign):
            failures.append("fresh campaign binding mismatch")
        expected_identity = _build_checkpoint_identity(
            sources, instance, expected_campaign, dimacs_path,
            expected_paths["evidence"], expected_paths["progress"],
        )
        if not optimized.json_type_equal(
            manifest.get("checkpoint_identity"), expected_identity
        ):
            failures.append("fresh checkpoint identity mismatch")
        expected_manifest = _build_manifest(
            sources, resource, context, instance, expected_campaign,
            expected_identity, production_intent=production_intent,
        )
        if not optimized.json_type_equal(manifest, expected_manifest):
            failures.append("fresh manifest replay mismatch")
        fresh_record = optimized.classify_evidence(
            evidence, instance, expected_identity
        )
        if not optimized.json_type_equal(record, fresh_record):
            failures.append("fresh evidence/record replay mismatch")
        strict_decision = bool(
            fresh_record["strict_verified_sat_rejection"] is True
            or fresh_record["strict_current_source_unsat"] is True
        )
        if not strict_decision:
            failures.append("nonterminal evidence cannot authorize terminal")
        expected_terminal = (
            _build_terminal_payload(
                root, expected_paths["manifest"], expected_paths["evidence"],
                expected_paths["record"], sources, instance, expected_campaign,
                expected_identity, context, fresh_record, evidence,
                production_intent=production_intent,
            )
            if strict_decision else None
        )
        if expected_terminal is not None and not optimized.json_type_equal(
            terminal, expected_terminal
        ):
            failures.append("fresh terminal replay mismatch")
    except (OSError, KeyError, TypeError, ValueError, RuntimeError) as exc:
        failures.append(
            f"physical terminal replay failed: {type(exc).__name__}: {exc}"
        )
    return failures


def run_campaign(
    root: Path, *, solver_callback: SolverCallback | None = None,
    enforce_resource_gate: bool = True,
    _production_cli_nonce: object | None = None,
) -> dict[str, Any]:
    requested_root = Path(root)
    early_context = _early_direct_cli_context(requested_root)
    production_requested = _production_cli_nonce is _PRODUCTION_CLI_NONCE
    if _production_cli_nonce is not None and not production_requested:
        raise optimized.Dic5OptimizedCnfFinalV13Error("invalid production CLI nonce")
    if production_requested and early_context["passed"] is not True:
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            "production requires direct python -I -B runner invocation"
        )

    # This gate is the first stateful/scientific action: no source/build/root yet.
    resource = (
        _FROZEN_CALLABLES["baseline_resource_gate"]()
        if enforce_resource_gate else {"passed": False, "test_override": True}
    )
    sources_before = source_bundle()
    instance = _FROZEN_CALLABLES["optimized_builder"]()
    sources_after_build = source_bundle()
    if not optimized.json_type_equal(sources_after_build, sources_before):
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            "source/runtime closure changed while building optimized instance"
        )
    command_hash_matches = bool(
        early_context["runner_realpath"]
        == str((PROJECT / sources_before["runner_relative_path"]).resolve())
        and optimized.file_sha256(Path(early_context["runner_realpath"]))
        == sources_before["runner_file_sha256"]
    )
    production_context = optimized.seal({
        **{key: value for key, value in early_context.items() if key != "context_sha256"},
        "early_context_sha256": early_context["context_sha256"],
        "command_path_hash_matches_source_closure": command_hash_matches,
        "passed": bool(early_context["passed"] is True and command_hash_matches),
    }, "context_sha256")
    if production_requested and production_context["passed"] is not True:
        raise optimized.Dic5OptimizedCnfFinalV13Error(
            "production command path/source hash binding failed"
        )
    output_root = _FROZEN_CALLABLES["baseline_root_builder"](requested_root)
    dimacs_path = output_root / "input" / "optimized.cnf"
    manifest_path = output_root / "input" / "manifest.json"
    evidence_path = output_root / "state" / "evidence.json"
    progress_path = output_root / "state" / "progress.json"
    record_path = output_root / "sectors" / "Z.json"
    terminal_path = output_root / "terminal.json"
    _write_new_bytes(dimacs_path, instance.dimacs)
    if optimized.file_sha256(dimacs_path) != optimized.EXPECTED_OPTIMIZED_DIMACS_SHA256:
        raise optimized.Dic5OptimizedCnfFinalV13Error("written DIMACS hash mismatch")
    injected_solver = solver_callback is not None
    callback = (
        _FROZEN_CALLABLES["optimized_solver"]
        if solver_callback is None else solver_callback
    )
    context_valid = _production_context_is_valid(
        production_context, output_root, sources_before
    )
    resource_valid = _resource_gate_is_valid(
        resource, enforced=enforce_resource_gate
    )
    production_intent = bool(
        production_requested
        and not injected_solver
        and enforce_resource_gate
        and resource_valid
        and context_valid
        and sources_before["frozen_callable_seal"]["passed"] is True
    )
    campaign_binding = _build_campaign_binding(
        output_root, sources_before, instance, dimacs_path, evidence_path,
        progress_path, production_context,
        solver_callback_injected=injected_solver,
        production_cli_requested=production_requested,
        resource_gate_enforced=enforce_resource_gate,
    )
    identity = _build_checkpoint_identity(
        sources_before, instance, campaign_binding, dimacs_path,
        evidence_path, progress_path,
    )
    manifest = _build_manifest(
        sources_before, resource, production_context, instance,
        campaign_binding, identity, production_intent=production_intent,
    )
    _write_new_json(manifest_path, manifest)
    calls = 0

    def call_solver() -> Mapping[str, Any]:
        nonlocal calls
        calls += 1
        return callback(instance, identity)

    try:
        raw_evidence = call_solver()
        if type(raw_evidence) is not dict:
            raise optimized.Dic5OptimizedCnfFinalV13Error(
                "solver evidence must be an exact dict"
            )
        evidence = dict(raw_evidence)
        if calls != 1:
            raise optimized.Dic5OptimizedCnfFinalV13Error(
                "solver callback was not invoked exactly once"
            )
        _write_new_json(evidence_path, evidence)
        record = optimized.classify_evidence(evidence, instance, identity)
        _write_new_json(record_path, record)
        sources_after_solver = source_bundle()
        if not optimized.json_type_equal(sources_after_solver, sources_before):
            raise optimized.Dic5OptimizedCnfFinalV13Error(
                "source/runtime closure changed during solver execution"
            )
        strict_decision = bool(
            record["strict_verified_sat_rejection"] is True
            or record["strict_current_source_unsat"] is True
        )
        if not strict_decision:
            raise optimized.Dic5OptimizedCnfFinalV13Error(
                "UNKNOWN/malformed evidence cannot produce terminal"
            )
        terminal = _build_terminal_payload(
            output_root, manifest_path, evidence_path, record_path,
            sources_before, instance, campaign_binding, identity,
            production_context, record, evidence,
            production_intent=production_intent,
        )
        precommit_failures = _terminal_payload_failures(
            terminal, terminal_path, authoritative_terminal_present=False,
        )
        if precommit_failures:
            raise optimized.Dic5OptimizedCnfFinalV13Error(
                f"precommit authoritative replay failed: {precommit_failures}"
            )
    except BaseException as exc:
        _write_wrapper_error(output_root, manifest["manifest_sha256"], calls, exc)
        raise
    # This atomic no-replace commit is the final action of a successful run.
    _commit_new_json(terminal_path, terminal)
    return terminal


def validate_authoritative_terminal(terminal_path: Path) -> dict[str, Any]:
    """Zero-solver replay of the committed terminal and every physical source."""

    terminal_file = Path(terminal_path)
    failures: list[str] = []
    terminal: dict[str, Any] = {}
    try:
        terminal = _strict_json(terminal_file)
        failures.extend(_terminal_payload_failures(
            terminal, terminal_file, authoritative_terminal_present=True,
        ))
    except (OSError, KeyError, TypeError, ValueError, RuntimeError) as exc:
        failures.append(
            f"physical terminal replay failed: {type(exc).__name__}: {exc}"
        )
    authoritative_lower = bool(
        not failures
        and terminal.get("production_eligible") is True
        and type(terminal.get("distance_lower_bound")) is int
        and terminal.get("distance_lower_bound") == 20
        and terminal.get("status") == "CURRENT_SOURCE_LOWER_20"
    )
    return optimized.seal({
        "schema_version": 2,
        "gate": "qcode-paper400-dic5-authoritative-terminal-validator-v2",
        "terminal_path": str(terminal_file),
        "terminal_sha256": terminal.get("terminal_sha256"),
        "valid": not failures,
        "authoritative_current_source_lower": authoritative_lower,
        "publication_certificate": False,
        "upload_authorized": False,
        "failures": failures,
        "solver_invoked": False,
    }, "validation_sha256")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="action", required=True)
    subparsers.add_parser("preflight", help="zero-solver deterministic rebuild")
    run = subparsers.add_parser("run", help="one new in-process optimized lane")
    run.add_argument("--root", required=True, type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.action == "preflight":
        result = build_preflight()
    else:
        result = run_campaign(
            args.root,
            solver_callback=None,
            enforce_resource_gate=True,
            _production_cli_nonce=_PRODUCTION_CLI_NONCE,
        )
    print(optimized.canonical_bytes(result).decode("utf-8"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
