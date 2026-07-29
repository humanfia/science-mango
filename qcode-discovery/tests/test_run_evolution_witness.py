from __future__ import annotations

import asyncio
import concurrent.futures
import fcntl
import json
import os
import threading
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

import evolve.run_evolution as launcher


@dataclass
class FakeResult:
    child_program_dict: dict[str, Any] | None = None
    iteration: int = 0
    error: str | None = None


class FakeFuture:
    def __init__(self, value: Any):
        self.value = value
        self.was_cancelled = False

    def done(self) -> bool:
        return True

    def result(self, *_args: Any, **_kwargs: Any) -> Any:
        if isinstance(self.value, BaseException):
            raise self.value
        return self.value

    def cancel(self) -> bool:
        self.was_cancelled = True
        return True

    def cancelled(self) -> bool:
        return self.was_cancelled


def _child(iteration: int, program_id: str | None = None) -> FakeResult:
    return FakeResult(
        child_program_dict={
            "id": program_id or f"program-{iteration}",
            "code": f"code-{iteration}",
            "metrics": {"combined_score": float(iteration)},
            "iteration_found": iteration,
        },
        iteration=iteration,
    )


def _observer_controller(
    programs: dict[str, Any],
    *,
    shutdown: bool = False,
    early_stop: bool = False,
) -> Any:
    event = threading.Event()
    if shutdown:
        event.set()
    return SimpleNamespace(
        shutdown_event=event,
        early_stopping_triggered=early_stop,
        database=SimpleNamespace(programs=programs),
    )


def test_observer_accepts_out_of_order_results_and_worker_error():
    observer = launcher._SliceObserver(10, 3, FakeResult)
    observer.begin(11, 3, None)
    futures = {
        iteration: observer.record_submission(
            iteration,
            iteration % 2,
            FakeFuture(
                FakeResult(iteration=iteration, error="worker failed")
                if iteration == 12
                else _child(iteration)
            ),
        )
        for iteration in (11, 12, 13)
    }
    programs: dict[str, Any] = {}
    for iteration in (13, 11, 12):
        result = futures[iteration].result()
        if result.child_program_dict is not None:
            program_id = result.child_program_dict["id"]
            programs[program_id] = SimpleNamespace(**result.child_program_dict)
            observer.record_program_add(iteration, programs[program_id])
    programs.clear()

    observer.verify(_observer_controller(programs))

    assert observer.accounting_complete is True
    assert sorted(observer.outcomes) == [11, 12, 13]
    assert observer.outcomes[12]["status"] == "worker_error"


@pytest.mark.parametrize(
    "case",
    (
        "submit_none",
        "future_exception",
        "future_cancelled",
        "result_iteration_mismatch",
        "child_iteration_mismatch",
        "program_id_reused",
        "add_missing",
        "early_stop",
        "shutdown",
    ),
)
def test_observer_rejects_incomplete_or_ambiguous_accounting(case: str):
    observer = launcher._SliceObserver(0, 2, FakeResult)
    observer.begin(1, 2, None)
    first = _child(1, "same-id" if case == "program_id_reused" else None)
    second: Any = _child(
        2, "same-id" if case == "program_id_reused" else None
    )
    if case == "future_exception":
        second = RuntimeError("future exploded")
    elif case == "future_cancelled":
        second = concurrent.futures.CancelledError()
    elif case == "result_iteration_mismatch":
        second = _child(1, "wrong-result-iteration")
    elif case == "child_iteration_mismatch":
        second = FakeResult(
            child_program_dict={"id": "wrong-child-iteration", "iteration_found": 1},
            iteration=2,
        )

    observed = {
        1: observer.record_submission(1, 0, FakeFuture(first)),
        2: observer.record_submission(
            2, 0, None if case == "submit_none" else FakeFuture(second)
        ),
    }
    programs: dict[str, Any] = {}
    for iteration in (1, 2):
        future = observed[iteration]
        if future is None:
            continue
        try:
            result = future.result()
        except BaseException:
            continue
        if result.child_program_dict is None:
            continue
        program_id = result.child_program_dict["id"]
        programs[program_id] = SimpleNamespace(**result.child_program_dict)
        if not (case == "add_missing" and iteration == 2):
            observer.record_program_add(iteration, programs[program_id])

    controller = _observer_controller(
        programs,
        shutdown=case == "shutdown",
        early_stop=case == "early_stop",
    )
    with pytest.raises(RuntimeError, match="incomplete OpenEvolve slice"):
        observer.verify(controller)
    assert observer.accounting_complete is False


def test_observer_rejects_non_integer_submission_and_island():
    observer = launcher._SliceObserver(0, 1, FakeResult)
    observer.begin(1, 1, None)
    future = observer.record_submission(True, False, FakeFuture(_child(1)))
    result = future.result()
    program_id = result.child_program_dict["id"]
    programs = {program_id: SimpleNamespace(**result.child_program_dict)}
    observer.record_program_add(1, programs[program_id])
    with pytest.raises(RuntimeError, match="submission iteration"):
        observer.verify(_observer_controller(programs))


class FakeDatabase:
    def __init__(
        self,
        *,
        fail_add_at: int | None = None,
        mutate_at: int | None = None,
    ):
        self.programs: dict[str, Any] = {}
        self.fail_add_at = fail_add_at
        self.mutate_at = mutate_at

    def add(
        self,
        program: Any,
        iteration: int | None = None,
        target_island: int | None = None,
    ) -> str:
        del target_island
        if self.fail_add_at is not None and iteration == self.fail_add_at:
            raise RuntimeError("database add failed")
        if iteration is not None:
            program.iteration_found = iteration
        if self.mutate_at is not None and iteration == self.mutate_at:
            program.code = "content-replaced-after-future"
        self.programs[program.id] = program
        return program.id


class FakeOpenEvolve:
    def __init__(self):
        self.output_dir = "/fake-output"
        self.saved: list[int] = []

    def _save_checkpoint(self, iteration: int) -> None:
        self.saved.append(iteration)


class FakeParallelController:
    scenario = "normal"

    def __init__(self, database: FakeDatabase):
        self.database = database
        self.shutdown_event = threading.Event()
        self.early_stopping_triggered = False
        self.num_islands = 2

    def request_shutdown(self) -> None:
        self.shutdown_event.set()

    def _submit_iteration(
        self, iteration: int, island_id: int | None = None
    ) -> FakeFuture | None:
        del island_id
        if self.scenario == "submit_none" and iteration == 2:
            return None
        if self.scenario == "future_exception" and iteration == 2:
            return FakeFuture(RuntimeError("future failed"))
        if self.scenario == "future_cancelled" and iteration == 2:
            return FakeFuture(concurrent.futures.CancelledError())
        if self.scenario == "all_worker_error":
            return FakeFuture(
                FakeResult(iteration=iteration, error="worker failed")
            )
        if self.scenario == "id_wrong" and iteration == 2:
            return FakeFuture(
                FakeResult(
                    child_program_dict={
                        "id": "bad-iteration",
                        "iteration_found": 1,
                    },
                    iteration=2,
                )
            )
        return FakeFuture(_child(iteration))

    async def run_evolution(
        self,
        start_iteration: int,
        max_iterations: int,
        target_score: float | None = None,
        checkpoint_callback: Any = None,
    ) -> Any:
        del target_score
        end = start_iteration + max_iterations - 1
        iterations = list(range(start_iteration, end + 1))
        if self.scenario == "early_return":
            iterations = iterations[:1]
        futures = [
            (iteration, self._submit_iteration(iteration, iteration % 2))
            for iteration in iterations
        ]
        checkpoint_callback(start_iteration)
        for iteration, future in reversed(futures):
            if future is None:
                continue
            try:
                result = future.result()
                if result.error:
                    continue
                child = SimpleNamespace(**result.child_program_dict)
                self.database.add(child, iteration=iteration)
                if self.scenario == "migration" and iteration == end:
                    self.database.add(
                        SimpleNamespace(
                            id=f"migrant-{iteration}",
                            code=child.code,
                            metrics=dict(child.metrics),
                            iteration_found=0,
                            parent_id=child.id,
                            metadata={"migrant": True, "island": 1},
                        ),
                        target_island=1,
                    )
            except Exception:
                continue
        if self.scenario == "request_shutdown":
            self.request_shutdown()
        if self.scenario == "early_stop":
            self.early_stopping_triggered = True
        if self.scenario == "system_exit_zero":
            raise SystemExit(0)
        checkpoint_callback(end)
        return None


def _fake_source_modules(monkeypatch: pytest.MonkeyPatch):
    controller_module = SimpleNamespace(
        ProcessParallelController=FakeParallelController,
        OpenEvolve=FakeOpenEvolve,
    )
    process_module = SimpleNamespace(SerializableResult=FakeResult)
    binding = {"controller": {"path": "/fake", "sha256": "a" * 64, "bytes": 1}}
    monkeypatch.setattr(
        launcher,
        "_openevolve_source_binding",
        lambda: (binding, controller_module, process_module),
    )
    monkeypatch.setattr(
        launcher,
        "_strong_checkpoint_descriptor",
        lambda _output, _checkpoint, expected_iteration=None: {
            "path": f"/fake-output/checkpoints/checkpoint_{expected_iteration}",
            "last_iteration": expected_iteration,
            "sha256": f"{expected_iteration:064x}",
            "programs": expected_iteration + 1,
        },
    )
    return binding, controller_module


def test_verified_controller_suppresses_early_end_save_and_saves_after_accounting(
    monkeypatch,
):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = "normal"
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with launcher._verified_slice_controller(0, 2) as (observer, _sources):
        parallel = controller_module.ProcessParallelController(database)
        asyncio.run(
            parallel.run_evolution(
                1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
            )
        )
        assert open_evolve.saved == []
        assert observer.accounting_complete is True

    assert open_evolve.saved == [2]
    assert [
        (save["iteration"], save["accounting_complete"])
        for save in observer.checkpoint_saves
    ] == [(1, False), (2, False), (2, True)]
    assert all(
        save["suppressed"] is True
        for save in observer.checkpoint_saves[:2]
    )
    assert observer.checkpoint_saves[-1]["accounting_complete"] is True


def test_verified_controller_accounts_for_database_migration_adds(monkeypatch):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = "migration"
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with launcher._verified_slice_controller(0, 2) as (observer, _sources):
        parallel = controller_module.ProcessParallelController(database)
        asyncio.run(
            parallel.run_evolution(
                1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
            )
        )
        assert observer.accounting_complete is True
        assert observer.auxiliary_programs == [
            {
                "program_id": "migrant-2",
                "parent_id": "program-2",
                "target_island": 1,
                "program_sha256": observer.auxiliary_programs[0][
                    "program_sha256"
                ],
                "program_bytes": observer.auxiliary_programs[0][
                    "program_bytes"
                ],
            }
        ]

    assert open_evolve.saved == [2]


def test_observer_rejects_unclassified_iterationless_database_add():
    observer = launcher._SliceObserver(0, 1, FakeResult)
    observer.begin(1, 1, None)
    observer.record_auxiliary_program_add(
        program=SimpleNamespace(
            id="not-a-migrant",
            parent_id="parent",
            code="code",
            metrics={},
            metadata={},
            iteration_found=0,
        ),
        stored=SimpleNamespace(id="not-a-migrant", iteration_found=0),
        parent=SimpleNamespace(id="parent", code="code", metrics={}),
        target_island=0,
        num_islands=2,
    )

    with pytest.raises(RuntimeError, match="valid migration"):
        observer.verify(_observer_controller({}))


@pytest.mark.parametrize(
    "scenario",
    (
        "submit_none",
        "future_exception",
        "future_cancelled",
        "id_wrong",
        "add_fail",
        "content_replaced",
        "all_worker_error",
        "early_return",
        "early_stop",
        "request_shutdown",
    ),
)
def test_verified_controller_refuses_incomplete_scenarios(monkeypatch, scenario):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = scenario
    database = FakeDatabase(
        fail_add_at=2 if scenario == "add_fail" else None,
        mutate_at=2 if scenario == "content_replaced" else None,
    )
    open_evolve = controller_module.OpenEvolve()

    with pytest.raises(RuntimeError, match="incomplete OpenEvolve slice"):
        with launcher._verified_slice_controller(0, 2):
            parallel = controller_module.ProcessParallelController(database)
            asyncio.run(
                parallel.run_evolution(
                    1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
                )
            )
    assert open_evolve.saved == []


def test_verified_controller_system_exit_zero_never_completes(monkeypatch):
    _binding, controller_module = _fake_source_modules(monkeypatch)
    FakeParallelController.scenario = "system_exit_zero"
    database = FakeDatabase()
    open_evolve = controller_module.OpenEvolve()

    with pytest.raises(SystemExit) as raised:
        with launcher._verified_slice_controller(0, 2) as (observer, _sources):
            parallel = controller_module.ProcessParallelController(database)
            asyncio.run(
                parallel.run_evolution(
                    1, 2, None, checkpoint_callback=open_evolve._save_checkpoint
                )
            )
    assert raised.value.code == 0
    assert observer.accounting_complete is False
    assert open_evolve.saved == []


def test_openevolve_source_hashes_match_pinned_0_2_26():
    pytest.importorskip("openevolve")
    binding, _controller, _process = launcher._openevolve_source_binding()
    assert set(binding) == {"controller", "process_parallel", "database", "api"}
    assert {
        name: descriptor["sha256"] for name, descriptor in binding.items()
    } == launcher.SUPPORTED_OPENEVOLVE_SHA256


def test_openevolve_source_hash_mismatch_fails_closed(monkeypatch):
    pytest.importorskip("openevolve")
    monkeypatch.setitem(
        launcher.SUPPORTED_OPENEVOLVE_SHA256, "controller", "0" * 64
    )
    with pytest.raises(RuntimeError, match="controller source hash"):
        launcher._openevolve_source_binding()


def test_invocation_binding_requires_exact_fields_and_backend_consistency(
    tmp_path,
):
    invocation = {
        "model_names": ["fake-model"],
        "reasoning_effort": None,
        "codex_cli": True,
        "max_parallel_evaluations": 4,
        "api_base": "http://localhost:4000/v1",
        "temperature_disabled": True,
        "codex_version": "codex-cli 1.2.3",
        "codex_cwd": str(Path(launcher.PROJECT_ROOT).resolve()),
        "codex_executable_mode": 0o700,
    }
    backend = tmp_path / "codex_cli_llm.py"
    backend.write_text("backend\n")
    executable = tmp_path / "codex-native"
    executable.write_bytes(b"\x7fELFfake")
    executable.chmod(0o700)
    executable_identity = launcher._file_identity(
        executable, "test Codex executable"
    )
    executable_identity["mode"] = 0o700
    assert launcher._validated_invocation_binding(
        invocation, backend, executable_identity
    ) == invocation
    with pytest.raises(RuntimeError, match="backend binding"):
        launcher._validated_invocation_binding(invocation, None, None)
    with pytest.raises(RuntimeError, match="fields are incomplete"):
        launcher._validated_invocation_binding(
            {**invocation, "schema_version": 99}, backend, executable_identity
        )


def test_managed_codex_resolves_and_pins_native_binary(monkeypatch):
    if launcher.shutil.which("codex") is None:
        pytest.skip("Codex CLI is not installed")
    monkeypatch.delenv("QCODE_CODEX_BIN", raising=False)
    monkeypatch.delenv("QCODE_CODEX_CWD", raising=False)

    identity, version, cwd = launcher._resolve_codex_execution_binding()

    native_path = Path(identity["path"])
    assert native_path.read_bytes()[:4] in (b"\x7fELF", b"MZ\x90\x00")
    assert identity["mode"] == native_path.stat().st_mode & 0o7777
    assert version
    assert cwd == str(Path(launcher.PROJECT_ROOT).resolve())
    assert os.environ["QCODE_CODEX_BIN"] == str(native_path)
    assert os.environ["QCODE_CODEX_CWD"] == cwd


def test_lifecycle_lease_requires_preheld_independent_lock(tmp_path):
    path = (tmp_path / "lifecycle.lock").resolve()
    fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        with pytest.raises(RuntimeError, match="not locked before inheritance"):
            launcher._validate_lifecycle_lease(fd, str(path))
        fcntl.flock(fd, fcntl.LOCK_EX)
        os.set_inheritable(fd, True)
        assert launcher._validate_lifecycle_lease(fd, str(path)) == path
        assert os.get_inheritable(fd) is False
    finally:
        os.close(fd)


def _managed_argv(tmp_path: Path, lease_fd: int, lease_path: Path) -> list[str]:
    context_path = tmp_path / "context.md"
    context_path.write_text("managed context\n")
    return [
        "run_evolution.py",
        "--iterations",
        "1",
        "--output",
        str(tmp_path / "output"),
        "--completion-marker",
        str(tmp_path / "completed.json"),
        "--slice-witness",
        str(tmp_path / "witness.json"),
        "--humanize-context",
        str(context_path),
        "--lifecycle-lease-fd",
        str(lease_fd),
        "--lifecycle-lease-path",
        str(lease_path),
    ]


def test_managed_build_config_system_exit_does_not_reference_unbound_observer(
    tmp_path, monkeypatch
):
    lease_path = (tmp_path / "lease.lock").resolve()
    lease_fd = os.open(lease_path, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(lease_fd, fcntl.LOCK_EX)
    monkeypatch.setattr(
        launcher,
        "_build_config",
        lambda *_args: (_ for _ in ()).throw(SystemExit(1)),
    )
    monkeypatch.setattr(
        launcher.sys, "argv", _managed_argv(tmp_path, lease_fd, lease_path)
    )
    try:
        with pytest.raises(SystemExit) as raised:
            launcher.main()
    finally:
        os.close(lease_fd)
    assert raised.value.code == 1


def test_managed_inner_system_exit_zero_becomes_nonzero(tmp_path, monkeypatch):
    lease_path = (tmp_path / "lease.lock").resolve()
    lease_fd = os.open(lease_path, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(lease_fd, fcntl.LOCK_EX)
    config = SimpleNamespace(
        llm=SimpleNamespace(
            models=[SimpleNamespace(name="fake-model")],
            evaluator_models=[],
        ),
        evaluator=SimpleNamespace(parallel_evaluations=1),
    )

    @contextmanager
    def fake_scope(*_args):
        yield SimpleNamespace(shutdown_requested=False), {}

    monkeypatch.setattr(launcher, "_build_config", lambda *_args: config)
    monkeypatch.setattr(launcher, "_verified_slice_controller", fake_scope)
    monkeypatch.setattr(
        launcher,
        "_run_fresh",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(SystemExit(0)),
    )
    monkeypatch.setattr(
        launcher.sys, "argv", _managed_argv(tmp_path, lease_fd, lease_path)
    )
    try:
        with pytest.raises(SystemExit) as raised:
            launcher.main()
    finally:
        os.close(lease_fd)
    assert raised.value.code == 130
    assert not (tmp_path / "completed.json").exists()
    assert not (tmp_path / "witness.json").exists()


def test_witness_is_written_before_bound_marker(tmp_path, monkeypatch):
    observer = launcher._SliceObserver(0, 1, FakeResult)
    observer.accounting_complete = True
    observer.submission_attempts = [{
        "iteration": 1,
        "island_id": 0,
        "result": "future",
    }]
    observer.outcomes = {
        1: {
            "iteration": 1,
            "status": "worker_error",
            "error_sha256": "a" * 64,
            "error_bytes": 1,
        }
    }
    observer.checkpoint_saves = [{
        "iteration": 1,
        "accounting_complete": True,
        "checkpoint_sha256": "b" * 64,
        "checkpoint_programs": 2,
    }]
    descriptor = {
        "path": str(tmp_path / "output" / "checkpoints" / "checkpoint_1"),
        "last_iteration": 1,
        "sha256": "b" * 64,
        "programs": 2,
    }
    source_binding = {
        name: {"path": f"/fake/{name}.py", "sha256": char * 64, "bytes": 1}
        for name, char in zip(
            ("controller", "process_parallel", "database", "api"), "cdef"
        )
    }
    monkeypatch.setattr(
        launcher,
        "_openevolve_source_binding",
        lambda: (source_binding, None, None),
    )
    monkeypatch.setattr(
        launcher, "_strong_checkpoint_descriptor", lambda *_args, **_kwargs: descriptor
    )
    config = tmp_path / "config.yaml"
    seed = tmp_path / "seed.py"
    evaluator = tmp_path / "evaluator.py"
    context = tmp_path / "context.md"
    for path in (config, seed, evaluator, context):
        path.write_text(path.name)
    invocation = {
        "model_names": ["fake-model"],
        "reasoning_effort": "high",
        "codex_cli": False,
        "max_parallel_evaluations": 2,
        "api_base": "http://localhost:4000/v1",
        "temperature_disabled": True,
        "codex_version": None,
        "codex_cwd": None,
        "codex_executable_mode": None,
    }
    context_identity = launcher._file_identity(context, "test context")
    dependency_identities = launcher._evaluator_dependency_identities()
    witness_path = tmp_path / "slice-witness.json"
    marker_path = tmp_path / "completed.json"

    result, witness = launcher._write_slice_witness(
        witness_path,
        observer=observer,
        source_binding=source_binding,
        output_dir=tmp_path / "output",
        resume_checkpoint=None,
        iterations=1,
        config_path=config,
        seed_path=seed,
        evaluator_path=evaluator,
        context_path=context,
        context_identity=context_identity,
        dependency_identities=dependency_identities,
        backend_path=None,
        codex_executable_identity=None,
        invocation=invocation,
    )
    launcher._write_completion_marker(
        marker_path,
        output_dir=tmp_path / "output",
        resume_checkpoint=None,
        iterations=1,
        config_path=config,
        seed_path=seed,
        evaluator_path=evaluator,
        context_path=context,
        context_identity=context_identity,
        dependency_identities=dependency_identities,
        backend_path=None,
        codex_executable_identity=None,
        invocation=invocation,
        result_checkpoint=result,
        slice_witness=witness,
    )

    witness_payload = json.loads(witness_path.read_text())
    marker_payload = json.loads(marker_path.read_text())
    assert witness_payload["schema_version"] == 2
    assert marker_payload["schema_version"] == 2
    assert marker_payload["slice_witness_sha256"] == witness["sha256"]
    assert marker_payload["result_checkpoint_sha256"] == "b" * 64
    assert marker_payload["context_sha256"] == witness_payload["context_sha256"]
    assert marker_payload["model_names"] == ["fake-model"]
    assert (
        marker_payload["evaluation_distance_milp_sha256"]
        == dependency_identities["evaluation_distance_milp"]["sha256"]
    )
