import fcntl
import hashlib
import json
import os
from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace

import pytest

import humanize.flow as flow_module
from evolve.run_evolution import _cap_parallel_evaluations
from humanize.audit_state import AuditStateError
from humanize.flow import (
    FlowConfig,
    HumanizeFlow,
    _acquire_round_lifecycle_lease,
    _checkpoint_descriptor,
    _completion_marker_expected,
    _evolution_launch_binding,
    _file_descriptor,
    _slice_iterations_sha256,
    _milp_is_fully_exact,
    _stage1_milp_worker_count,
    evaluate_with_milp,
    run_openevolve,
)
from humanize.reviewer import validate_review
from humanize.state import atomic_write_json, code_key


class Reviewer:
    def review(self, _prompt, _round_dir):
        return validate_review({
            "verdict": "continue",
            "summary": "No exact candidate yet.",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        })


def write_launch_inputs(
    repo: Path,
    *,
    config_path: Path | None = None,
    seed_path: Path | None = None,
) -> tuple[Path, Path]:
    evolve = repo / "evolve"
    evolve.mkdir(parents=True, exist_ok=True)
    (evolve / "run_evolution.py").write_text("# launcher\n")
    (evolve / "openevolve_evaluator.py").write_text("# evaluator\n")
    sources = repo / "fake-openevolve"
    sources.mkdir(exist_ok=True)
    for name in ("controller", "process_parallel", "database", "api"):
        (sources / f"{name}.py").write_text(f"# fake {name}\n")
    config_path = config_path or evolve / "config.yaml"
    seed_path = seed_path or evolve / "seed_solution.py"
    if not config_path.exists():
        config_path.write_text("evaluator:\n  parallel_evaluations: 4\n")
    if not seed_path.exists():
        seed_path.write_text("def generate_candidates(): return []\n")
    for relative_path in flow_module.LOCAL_EVOLUTION_DEPENDENCIES.values():
        dependency = repo / relative_path
        dependency.parent.mkdir(parents=True, exist_ok=True)
        dependency.write_text(f"# dependency {relative_path}\n")
    return config_path, seed_path


def write_checkpoint(repo: Path, run_id: str, iteration: int) -> Path:
    checkpoint = (
        repo
        / "results/evolution"
        / f"humanize_{run_id}"
        / "checkpoints"
        / f"checkpoint_{iteration}"
    )
    programs = checkpoint / "programs"
    programs.mkdir(parents=True, exist_ok=True)
    program_id = "program"
    code = "def generate_candidates():\n    return []\n"
    atomic_write_json(checkpoint / "metadata.json", {
        "last_iteration": iteration,
        "archive": [program_id],
        "best_program_id": program_id,
        "islands": [[program_id]],
        "island_best_programs": [program_id],
        "island_feature_maps": [{"cell": program_id}],
    })
    atomic_write_json(checkpoint / "best_program_info.json", {
        "id": program_id,
        "current_iteration": iteration,
    })
    atomic_write_json(programs / f"{program_id}.json", {
        "id": program_id,
        "code": code,
        "metrics": {},
        "iteration_found": iteration,
    })
    (checkpoint / "best_program.py").write_text(code)
    return checkpoint


def complete_fake_evolution(config: FlowConfig, command: list[str]) -> Path:
    resume = None
    if "--resume" in command:
        resume = Path(command[command.index("--resume") + 1])
    output = (
        config.repo_dir / "results/evolution" / f"humanize_{config.run_id}"
    )
    base = None if resume is None else _checkpoint_descriptor(output, resume)
    base_iteration = 0 if base is None else base["last_iteration"]
    iterations = int(command[command.index("--iterations") + 1])
    checkpoint = write_checkpoint(
        config.repo_dir, config.run_id, base_iteration + iterations
    )
    result = _checkpoint_descriptor(output, checkpoint)
    witness_path = Path(command[command.index("--slice-witness") + 1])
    context_path = Path(command[command.index("--humanize-context") + 1])
    launch = _evolution_launch_binding(
        config, context_path=context_path
    )
    invocation = {
        "model_names": [config.model],
        "reasoning_effort": config.reasoning_effort,
        "codex_cli": False,
        "max_parallel_evaluations": int(
            command[command.index("--max-parallel-evaluations") + 1]
        ),
        "api_base": command[command.index("--api-base") + 1],
        "temperature_disabled": "--no-temperature" in command,
        "codex_version": None,
        "codex_cwd": None,
        "codex_executable_mode": None,
    }
    error = b"test worker error"
    start = base_iteration + 1
    program = json.loads(
        (
            Path(result["path"])
            / "programs"
            / "program.json"
        ).read_text()
    )
    program["id"] = "evicted-child"
    program["iteration_found"] = start
    encoded_program = json.dumps(
        program,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode()
    payload = {
        "schema_version": 2,
        "status": "completed",
        "output_dir": str(output.resolve()),
        "resume_checkpoint": None if base is None else base["path"],
        "base_last_iteration": base_iteration,
        "iterations_requested": iterations,
        "slice_start_iteration": base_iteration + 1,
        "slice_end_iteration": base_iteration + iterations,
        "slice_iteration_count": iterations,
        "slice_iterations_sha256": _slice_iterations_sha256(
            base_iteration + 1, iterations
        ),
        "submission_attempts": [
            {"iteration": i, "island_id": 0, "result": "future"}
            for i in range(base_iteration + 1, base_iteration + iterations + 1)
        ],
        "outcomes": [{
            "iteration": start,
            "status": "program_added",
            "program_id": "evicted-child",
            "program_sha256": hashlib.sha256(encoded_program).hexdigest(),
            "program_bytes": len(encoded_program),
        }] + [
            {
                "iteration": i,
                "status": "worker_error",
                "error_sha256": hashlib.sha256(error).hexdigest(),
                "error_bytes": len(error),
            }
            for i in range(start + 1, base_iteration + iterations + 1)
        ],
        "successful_evaluations": 1,
        "worker_errors": iterations - 1,
        "checkpoint_saves": [{
            "iteration": base_iteration + iterations,
            "accounting_complete": True,
            "checkpoint_sha256": result["sha256"],
            "checkpoint_programs": result["programs"],
        }],
        "result_checkpoint": result["path"],
        "result_last_iteration": result["last_iteration"],
        "result_checkpoint_sha256": result["sha256"],
        "result_checkpoint_programs": result["programs"],
        "openevolve_version": "0.2.26",
        "completed_at": "test",
    }
    for name, descriptor in launch.items():
        for field in ("path", "sha256", "bytes"):
            payload[f"{name}_{field}"] = descriptor[field]
    payload.update(invocation)
    sources = config.repo_dir / "fake-openevolve"
    for name in ("controller", "process_parallel", "database", "api"):
        descriptor = _file_descriptor(sources / f"{name}.py", "fake source")
        for field in ("path", "sha256", "bytes"):
            payload[f"openevolve_{name}_{field}"] = descriptor[field]
    atomic_write_json(witness_path, payload)
    witness = _file_descriptor(witness_path, "test witness")
    marker = Path(command[command.index("--completion-marker") + 1])
    marker_payload = _completion_marker_expected(
        config, base, result, launch, invocation, witness
    )
    marker_payload["completed_at"] = "test"
    atomic_write_json(marker, marker_payload)
    return checkpoint


def install_fake_popen(monkeypatch, captured, config):
    class Process:
        pid = 999999

        @staticmethod
        def wait(*_args, **_kwargs):
            return 0

    def fake_popen(command, **kwargs):
        captured["command"] = command
        captured["kwargs"] = kwargs
        complete_fake_evolution(config, command)
        return Process()

    monkeypatch.setattr(flow_module.subprocess, "Popen", fake_popen)
    monkeypatch.setattr(
        flow_module,
        "_wait_for_managed_process",
        lambda process, command: process.wait(),
    )


def frozen_runner_state(
    config: FlowConfig,
    state: dict,
    round_dir: Path,
) -> dict:
    launch, invocation = flow_module._fresh_evolution_bindings(
        config, state, round_dir
    )
    frozen = dict(state)
    frozen["_evolution_launch_binding"] = launch
    frozen["_evolution_invocation_binding"] = invocation
    checkpoint = state.get("last_checkpoint")
    frozen["_evolution_base_checkpoint"] = (
        None
        if checkpoint is None
        else _checkpoint_descriptor(
            config.repo_dir
            / "results/evolution"
            / f"humanize_{config.run_id}",
            Path(checkpoint),
        )
    )
    return frozen


def test_symplectic_d2_rule_is_exact_but_only_at_two():
    row = {"stage": "symplectic_low_d", "d_is_exact": True, "d": 2}
    assert _milp_is_fully_exact(row)
    row["d"] = 3
    assert not _milp_is_fully_exact(row)


def test_resume_rejects_milp_base_budget_drift(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    candidates = repo / "candidates.jsonl"
    candidates.write_text("")
    first = FlowConfig(
        repo_dir=repo,
        run_id="immutable",
        max_rounds=1,
        milp_top=1,
        candidate_file=candidates,
    )
    HumanizeFlow(first, reviewer=Reviewer()).run()

    changed = FlowConfig(
        repo_dir=repo,
        run_id="immutable",
        max_rounds=2,
        milp_top=1,
        milp_timeout_per_logical=301,
        candidate_file=candidates,
    )
    with pytest.raises(ValueError, match="different configuration"):
        HumanizeFlow(changed, reviewer=Reviewer()).run()


def test_openevolve_config_and_seed_are_forwarded(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    repo.mkdir()
    config_path = repo / "server.yaml"
    seed_path = repo / "seed.py"
    config_path.write_text("evaluator:\n  parallel_evaluations: 24\n")
    seed_path.write_text("def generate_candidates(*_args): return []\n")
    write_launch_inputs(repo, config_path=config_path, seed_path=seed_path)
    round_dir = repo / "round"
    round_dir.mkdir()
    captured = {}

    config = FlowConfig(
        repo_dir=repo,
        run_id="server-profile",
        max_rounds=1,
        iterations_per_round=25,
        evolution_config=config_path,
        evolution_seed=seed_path,
        max_total_workers=4,
    )
    install_fake_popen(monkeypatch, captured, config)
    with _acquire_round_lifecycle_lease(round_dir) as lease:
        state = {
            "current_round": 0,
            "last_checkpoint": None,
            "_round_lifecycle_lease_fd": lease.fd,
            "_round_lifecycle_lease_path": str(lease.path),
        }
        run_openevolve(
            config, frozen_runner_state(config, state, round_dir), round_dir
        )

    command = captured["command"]
    assert command[command.index("--iterations") + 1] == "25"
    assert command[command.index("--max-parallel-evaluations") + 1] == "4"
    assert command[command.index("--config") + 1] == str(config_path)
    assert command[command.index("--seed") + 1] == str(seed_path)
    assert captured["kwargs"]["cwd"] == repo


def test_openevolve_resume_runs_one_increment_not_cumulative(tmp_path, monkeypatch):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    round_dir = repo / "round-003"
    round_dir.mkdir()
    checkpoint = write_checkpoint(repo, "incremental", 50)
    captured = {}

    config = FlowConfig(
        repo_dir=repo,
        run_id="incremental",
        max_rounds=3,
        iterations_per_round=25,
        max_total_workers=2,
    )
    install_fake_popen(monkeypatch, captured, config)
    with _acquire_round_lifecycle_lease(round_dir) as lease:
        state = {
            "current_round": 2,
            "last_checkpoint": str(checkpoint),
            "_round_lifecycle_lease_fd": lease.fd,
            "_round_lifecycle_lease_path": str(lease.path),
        }
        run_openevolve(
            config,
            frozen_runner_state(config, state, round_dir),
            round_dir,
        )

    command = captured["command"]
    assert command[command.index("--iterations") + 1] == "25"
    assert command[command.index("--max-parallel-evaluations") + 1] == "2"
    assert command[command.index("--resume") + 1] == str(checkpoint)
    assert captured["kwargs"]["cwd"] == repo


def test_stage1_milp_uses_official_dynamic_fom_target(tmp_path, monkeypatch):
    from evaluation.final_gate import FOM_THRESHOLD

    captured = {}

    def fake_evaluator(*_args, **kwargs):
        captured.update(kwargs)
        return {"d": 16, "d_is_exact": False, "stage": "milp_low_d"}

    monkeypatch.setattr(
        "evaluation.evaluator.evaluate_candidate_milp", fake_evaluator
    )
    monkeypatch.setattr(
        "main.merge_bp_milp_result",
        lambda _candidate, milp_result: dict(milp_result),
    )
    candidate = {
        "ell": 18,
        "m": 10,
        "A_terms": [[0, 0], [1, 0], [0, 1]],
        "B_terms": [[0, 0], [2, 0], [0, 2]],
    }
    config = FlowConfig(repo_dir=tmp_path, run_id="dynamic-cutoff")

    evaluate_with_milp(
        candidate,
        config,
        checkpoint_path=tmp_path / "checkpoint.json",
        resume=True,
        hard_timeout_per_logical=330.0,
    )

    assert captured["milp_target_fom"] == FOM_THRESHOLD
    assert captured["milp_checkpoint_path"] == tmp_path / "checkpoint.json"
    assert captured["milp_resume"] is True
    assert captured["milp_hard_timeout_per_logical"] == 330.0


@pytest.mark.parametrize(
    ("configured", "cap", "effective"),
    ((6, 4, 4), (1, 4, 1), (24, 4, 4), (6, None, 6)),
)
def test_openevolve_parallel_evaluations_are_capped_not_increased(
    configured, cap, effective,
):
    config = SimpleNamespace(
        evaluator=SimpleNamespace(parallel_evaluations=configured)
    )

    observed = _cap_parallel_evaluations(config, cap)

    assert observed == (configured, effective)
    assert config.evaluator.parallel_evaluations == effective


@pytest.mark.parametrize("invalid", (0, -1, True, 1.5, None))
def test_openevolve_rejects_invalid_configured_worker_count(invalid):
    config = SimpleNamespace(
        evaluator=SimpleNamespace(parallel_evaluations=invalid)
    )
    with pytest.raises(ValueError, match="positive integer"):
        _cap_parallel_evaluations(config, 4)


def test_stage1_milp_workers_obey_shared_budget(tmp_path):
    base = dict(repo_dir=tmp_path, run_id="worker-cap")
    assert _stage1_milp_worker_count(FlowConfig(**base), 9) == 3
    assert _stage1_milp_worker_count(
        FlowConfig(**base, max_total_workers=2), 9
    ) == 2
    assert _stage1_milp_worker_count(
        FlowConfig(**base, max_total_workers=8), 2
    ) == 2
    assert _stage1_milp_worker_count(
        FlowConfig(**base, max_total_workers=1), 0
    ) == 0


def test_run_evolution_sigint_exits_nonzero_without_marker(tmp_path, monkeypatch):
    import evolve.run_evolution as run_module

    config = SimpleNamespace(
        llm=SimpleNamespace(
            models=[SimpleNamespace(name="test-model")],
            evaluator_models=[],
        ),
        evaluator=SimpleNamespace(parallel_evaluations=1),
    )

    def interrupted(*_args, **_kwargs):
        raise KeyboardInterrupt

    marker = tmp_path / "completed.json"
    witness = tmp_path / "witness.json"
    context = tmp_path / "context.md"
    context.write_text("managed context\n")
    lease_path = tmp_path / "lease.lock"
    lease_fd = os.open(lease_path, os.O_RDWR | os.O_CREAT, 0o600)
    fcntl.flock(lease_fd, fcntl.LOCK_EX)

    @contextmanager
    def fake_verified_scope(*_args):
        yield SimpleNamespace(shutdown_requested=False), {}

    monkeypatch.setattr(run_module, "_build_config", lambda *_args: config)
    monkeypatch.setattr(run_module, "_run_fresh", interrupted)
    monkeypatch.setattr(
        run_module, "_verified_slice_controller", fake_verified_scope
    )
    monkeypatch.setattr(run_module.sys, "argv", [
        "run_evolution.py",
        "--iterations", "1",
        "--output", str(tmp_path / "output"),
        "--completion-marker", str(marker),
        "--slice-witness", str(witness),
        "--humanize-context", str(context),
        "--lifecycle-lease-fd", str(lease_fd),
        "--lifecycle-lease-path", str(lease_path),
    ])

    try:
        with pytest.raises(SystemExit) as raised:
            run_module.main()
    finally:
        os.close(lease_fd)
    assert raised.value.code == 130
    assert not marker.exists()
    assert not witness.exists()


def test_worker_budget_does_not_break_legacy_checkpoint_identity(tmp_path):
    base = FlowConfig(repo_dir=tmp_path, run_id="resume-compatible")
    capped = FlowConfig(
        repo_dir=tmp_path,
        run_id="resume-compatible",
        max_total_workers=4,
    )
    assert capped.serializable() == base.serializable()


def _audit_candidate() -> dict:
    return {
        "ell": 18,
        "m": 10,
        "A_terms": [[0, 0], [1, 0], [0, 1]],
        "B_terms": [[0, 0], [2, 0], [0, 2]],
        "n": 360,
        "k": 16,
        "d": 18,
        "fom": 13.0,
        "static_eligibility": {"eligible": True},
        "structural_novelty": {
            "novel": True,
            "canonical_digest": "audit-guard-digest",
        },
    }


def _exact_audit_result(candidate: dict) -> dict:
    result = dict(candidate)
    result.update({
        "stage": "milp_exact",
        "d_is_exact": True,
        "milp_details": {
            "exact": True,
            "total_logicals": 16,
            "num_logicals_checked": 16,
            "logicals_optimal": 16,
        },
    })
    return result


def _audit_flow(
    tmp_path,
    evaluator,
    *,
    allow_debug_audit_evaluator=True,
) -> HumanizeFlow:
    repo = tmp_path / "repo"
    repo.mkdir()
    return HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id="audit-hardening",
            max_rounds=1,
            milp_top=1,
            allow_debug_audit_evaluator=allow_debug_audit_evaluator,
        ),
        reviewer=Reviewer(),
        milp_evaluator=evaluator,
    )


def test_malformed_round_evidence_is_archived_before_reconstruction(tmp_path):
    flow = _audit_flow(tmp_path, _exact_audit_result)
    round_dir = flow.store.round_dir(1)
    milp_path = round_dir / "milp.jsonl"
    malformed = b'{"candidate_key":"unterminated"'
    milp_path.write_bytes(malformed)

    assert flow._reconcile_round_evaluations(
        [],
        round_number=1,
        milp_path=milp_path,
        global_rows=[],
    ) == []

    archives = list(round_dir.glob("milp-malformed-*.bin"))
    assert len(archives) == 1
    assert archives[0].read_bytes() == malformed
    assert milp_path.read_bytes() == b""


@pytest.mark.parametrize("failure", ("identity", "nan"))
def test_invalid_evaluator_result_never_pollutes_global_log(tmp_path, failure):
    candidate = _audit_candidate()

    def evaluator(row, _config, **_invocation):
        result = _exact_audit_result(row)
        if failure == "identity":
            result["A_terms"] = [[0, 0], [3, 0], [0, 3]]
        else:
            result["fom"] = float("nan")
        return result

    flow = _audit_flow(tmp_path, evaluator)
    state = flow.store.initialize(flow.config.serializable())
    milp_path = flow.store.round_dir(1) / "milp.jsonl"

    with pytest.raises(AuditStateError):
        flow._audit_selected(
            [candidate],
            state=state,
            milp_path=milp_path,
            round_number=1,
        )

    assert not flow.evaluations_path.exists()


def test_legacy_two_argument_evaluator_requires_explicit_debug_mode(tmp_path):
    candidate = _audit_candidate()
    calls = []

    def legacy_evaluator(row, config):
        calls.append((code_key(row), config.milp_timeout_per_logical))
        return _exact_audit_result(row)

    flow = _audit_flow(tmp_path, legacy_evaluator)
    state = flow.store.initialize(flow.config.serializable())
    audited = flow._audit_selected(
        [candidate],
        state=state,
        milp_path=flow.store.round_dir(1) / "milp.jsonl",
        round_number=1,
    )

    assert calls == [(code_key(candidate), 300)]
    assert len(audited) == 1
    assert flow.evaluations_path.is_file()


def test_legacy_two_argument_evaluator_fails_closed_by_default(tmp_path):
    candidate = _audit_candidate()

    def legacy_evaluator(row, _config):
        return _exact_audit_result(row)

    flow = _audit_flow(
        tmp_path,
        legacy_evaluator,
        allow_debug_audit_evaluator=False,
    )
    state = flow.store.initialize(flow.config.serializable())

    with pytest.raises(AuditStateError, match="explicit debug"):
        flow._audit_selected(
            [candidate],
            state=state,
            milp_path=flow.store.round_dir(1) / "milp.jsonl",
            round_number=1,
        )
    assert not flow.evaluations_path.exists()


def test_checkpoint_path_rejects_escape_and_symlink_root(tmp_path):
    flow = _audit_flow(tmp_path, _exact_audit_result)
    key = code_key(_audit_candidate())
    expected = (
        flow.config.repo_dir
        / "results"
        / "runs"
        / flow.store.run_id
        / "milp-checkpoints"
        / f"{key}.json"
    ).resolve()
    assert flow._milp_checkpoint_path(key) == expected

    outside = tmp_path / "outside-run"
    outside.mkdir()
    flow.run_dir = outside
    with pytest.raises(AuditStateError, match="fixed results/runs root"):
        flow._milp_checkpoint_path(key)

    second = HumanizeFlow(
        FlowConfig(
            repo_dir=flow.config.repo_dir,
            run_id="audit-symlink",
            milp_top=1,
        ),
        reviewer=Reviewer(),
        milp_evaluator=_exact_audit_result,
    )
    target = tmp_path / "outside-checkpoints"
    target.mkdir()
    (second.run_dir / "milp-checkpoints").symlink_to(
        target, target_is_directory=True
    )
    with pytest.raises(AuditStateError, match="may not be a symlink"):
        second._milp_checkpoint_path(key)
