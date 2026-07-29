import hashlib
import json
from pathlib import Path

import pytest

import humanize.flow as flow_module
from humanize.flow import (
    FlowConfig,
    HumanizeFlow,
    RoundTransactionError,
)
from humanize.reviewer import validate_review
from humanize.state import atomic_write_json


def candidate(tag: int) -> dict:
    return {
        "ell": 6 + tag,
        "m": 6,
        "n": 12 * (6 + tag),
        "k": 8,
        "d": 6,
        "fom": float(6 + tag),
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
    }


def jsonl(*rows: dict) -> bytes:
    return b"".join(
        (json.dumps(row) + "\n").encode("utf-8") for row in rows
    )


def write_launch_inputs(repo: Path) -> None:
    evolve = repo / "evolve"
    evolve.mkdir(parents=True, exist_ok=True)
    (evolve / "config.yaml").write_text(
        "evaluator:\n  parallel_evaluations: 1\n"
    )
    (evolve / "seed_solution.py").write_text(
        "def generate_candidates(): return []\n"
    )
    (evolve / "run_evolution.py").write_text("# launcher\n")
    (evolve / "openevolve_evaluator.py").write_text("# evaluator\n")
    (evolve / "codex_cli_llm.py").write_text("# codex backend\n")
    for relative_path in flow_module.LOCAL_EVOLUTION_DEPENDENCIES.values():
        dependency = repo / relative_path
        dependency.parent.mkdir(parents=True, exist_ok=True)
        dependency.write_text(f"# dependency {relative_path}\n")
    sources = repo / "fake-openevolve"
    sources.mkdir(exist_ok=True)
    for name in ("controller", "process_parallel", "database", "api"):
        (sources / f"{name}.py").write_text(f"# fake {name}\n")


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


def write_full_slice_proof(
    flow: HumanizeFlow,
    round_dir: Path,
    checkpoint: Path,
    base: dict | None,
) -> None:
    config = flow.config
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output, checkpoint
    )
    base_iteration = 0 if base is None else base["last_iteration"]
    count = config.iterations_per_round
    error = b"test worker error"
    transaction = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    launch = transaction["launch_binding"]
    invocation = transaction["invocation_binding"]
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
    witness_path = flow_module._slice_witness_path(round_dir)
    witness = {
        "schema_version": 2,
        "status": "completed",
        "output_dir": str(flow.evolution_output.resolve()),
        "resume_checkpoint": None if base is None else base["path"],
        "base_last_iteration": base_iteration,
        "iterations_requested": count,
        "slice_start_iteration": base_iteration + 1,
        "slice_end_iteration": base_iteration + count,
        "slice_iteration_count": count,
        "slice_iterations_sha256": flow_module._slice_iterations_sha256(
            base_iteration + 1, count
        ),
        "submission_attempts": [
            {"iteration": i, "island_id": 0, "result": "future"}
            for i in range(base_iteration + 1, base_iteration + count + 1)
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
            for i in range(start + 1, base_iteration + count + 1)
        ],
        "successful_evaluations": 1,
        "worker_errors": count - 1,
        "checkpoint_saves": [{
            "iteration": base_iteration + count,
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
            witness[f"{name}_{field}"] = descriptor[field]
    witness.update(invocation)
    sources = config.repo_dir / "fake-openevolve"
    for name in ("controller", "process_parallel", "database", "api"):
        descriptor = flow_module._file_descriptor(
            sources / f"{name}.py", "fake OpenEvolve source"
        )
        for field in ("path", "sha256", "bytes"):
            witness[f"openevolve_{name}_{field}"] = descriptor[field]
    atomic_write_json(witness_path, witness)
    witness_descriptor = flow_module._file_descriptor(
        witness_path, "test slice witness"
    )
    marker = flow_module._completion_marker_expected(
        config, base, result, launch, invocation, witness_descriptor
    )
    marker["completed_at"] = "test"
    atomic_write_json(flow_module._completion_marker_path(round_dir), marker)


class Reviewer:
    def review(self, _prompt, _round_dir):
        return validate_review({
            "verdict": "continue",
            "summary": "transaction recovery test",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        })


def test_first_v1_round_archives_legacy_tail_and_partial_line(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-tail",
        max_rounds=2,
        iterations_per_round=25,
        milp_top=0,
    )
    prefix_row = candidate(0)
    abandoned_row = candidate(1)
    retry_row = candidate(2)
    prefix = jsonl(prefix_row)
    abandoned_tail = jsonl(abandoned_row) + b'{"partial":'
    base = write_checkpoint(repo, config.run_id, 25)

    runner_calls = []

    def runner(_config, _state, _round_dir):
        runner_calls.append(True)
        assert candidate_log.read_bytes() == prefix
        with candidate_log.open("ab") as stream:
            stream.write(jsonl(retry_row))
        checkpoint = write_checkpoint(repo, config.run_id, 50)
        base_descriptor = flow_module._checkpoint_descriptor(
            flow.evolution_output, base
        )
        write_full_slice_proof(
            flow, round_two, checkpoint, base_descriptor
        )
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    state.update({
        "current_round": 1,
        "candidate_offset": len(prefix),
        "last_checkpoint": str(base.resolve()),
    })
    flow.store.write_state(state)
    candidate_log = flow.candidate_log
    candidate_log.parent.mkdir(parents=True, exist_ok=True)
    candidate_log.write_bytes(prefix + abandoned_tail)

    round_one = flow.store.round_dir(1)
    (round_one / "candidates.jsonl").write_bytes(prefix)
    flow._materialize_legacy_batch(
        1,
        round_one,
        round_one / "candidates.jsonl",
        binding={"kind": "test-history"},
    )
    round_two = flow.store.round_dir(2)
    rows = flow._capture_round_candidates(state, 2, round_two)

    assert runner_calls == [True]
    assert rows == [retry_row]
    assert candidate_log.read_bytes() == prefix + jsonl(retry_row)
    archive = round_two / "abandoned-candidate-tail-001.bin"
    assert archive.read_bytes() == abandoned_tail
    manifest = json.loads(
        (round_two / "evolution-transaction.json").read_text()
    )
    assert manifest["abandoned_ranges"][0]["partial_bytes"] == 11
    salvaged = round_two / "abandoned-candidate-complete-001.jsonl"
    assert salvaged.read_bytes() == jsonl(abandoned_row)
    assert manifest["abandoned_ranges"][0]["complete_candidate_batch"] == {
        "path": str(salvaged.resolve()),
        "sha256": hashlib.sha256(jsonl(abandoned_row)).hexdigest(),
        "bytes": len(jsonl(abandoned_row)),
        "rows": 1,
    }

    state["current_round"] = 2
    state.pop("pending_round", None)
    state.pop("round_phase", None)
    flow.store.write_state(state)
    inputs = flow.pipeline_candidate_inputs
    assert len(inputs) == 3
    assert inputs[1] == salvaged
    assert inputs[1].read_bytes() == jsonl(abandoned_row)
    assert inputs[2].read_bytes() == jsonl(retry_row)

    salvaged.write_bytes(jsonl(candidate(99)))
    with pytest.raises(
        RoundTransactionError,
        match="abandoned complete candidate batch changed",
    ):
        _ = flow.pipeline_candidate_inputs


def test_first_prepare_rejects_stale_intermediate_checkpoint(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="stale-intermediate",
        iterations_per_round=25,
        milp_top=0,
    )
    calls = []

    def must_not_run(*_args):
        calls.append(True)
        raise AssertionError("stale checkpoint frontier reran evolution")

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=must_not_run
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    stale = write_checkpoint(repo, config.run_id, 10)

    with pytest.raises(RoundTransactionError, match="unbound checkpoint"):
        flow._capture_round_candidates(state, 1, round_dir)

    assert calls == []
    assert stale.is_dir()
    assert not (round_dir / "evolution-transaction.json").exists()


def test_prepared_transaction_adopts_complete_checkpoint_after_crash(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="adopt-checkpoint",
        iterations_per_round=25,
        milp_top=0,
    )
    row = candidate(3)
    calls = []

    def crashes_after_checkpoint(_config, _state, _round_dir):
        calls.append(True)
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(jsonl(row))
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(flow, _round_dir, checkpoint, None)
        raise SystemExit(99)

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=crashes_after_checkpoint
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    with pytest.raises(SystemExit) as raised:
        flow._capture_round_candidates(state, 1, round_dir)
    assert raised.value.code == 99

    def must_not_rerun(*_args):
        raise AssertionError("completed checkpoint was rerun")

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=must_not_rerun
    )
    recovered_state = resumed.store.load_state()
    rows = resumed._capture_round_candidates(
        recovered_state, 1, round_dir
    )
    assert calls == [True]
    assert rows == [row]
    marker = json.loads((round_dir / "openevolve-completed.json").read_text())
    assert marker["schema_version"] == 2
    assert (round_dir / "openevolve-slice-witness.json").is_file()


def test_complete_checkpoint_archives_and_truncates_final_partial_candidate(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="adopt-checkpoint-partial",
        iterations_per_round=25,
        milp_top=0,
    )
    row = candidate(5)
    fragment = b'{"partial":'
    original_tail = jsonl(row) + fragment
    calls = []

    def crashes_after_checkpoint(_config, _state, _round_dir):
        calls.append(True)
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(original_tail)
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(flow, _round_dir, checkpoint, None)
        raise SystemExit(99)

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=crashes_after_checkpoint
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    with pytest.raises(SystemExit):
        flow._capture_round_candidates(state, 1, round_dir)

    def must_not_rerun(*_args):
        raise AssertionError("completed checkpoint was rerun")

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=must_not_rerun
    )
    recovered = resumed.store.load_state()
    rows = resumed._capture_round_candidates(recovered, 1, round_dir)

    assert calls == [True]
    assert rows == [row]
    assert resumed.candidate_log.read_bytes() == jsonl(row)
    archive = round_dir / "candidate-final-partial-001.bin"
    assert archive.read_bytes() == original_tail
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    recovery = manifest["candidate_partial_recoveries"]
    assert len(recovery) == 1
    assert recovery[0]["last_complete_offset"] == len(jsonl(row))
    assert recovery[0]["partial_bytes"] == len(fragment)
    assert recovery[0]["archive_sha256"] == hashlib.sha256(
        original_tail
    ).hexdigest()
    assert manifest["candidate_end_offset"] == len(jsonl(row))


def test_swallowed_interrupt_without_checkpoint_cannot_commit_round(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="swallowed-interrupt",
        iterations_per_round=25,
    )
    calls = []

    def swallows_interrupt(*_args):
        calls.append(True)
        try:
            raise KeyboardInterrupt
        except KeyboardInterrupt:
            return None

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=swallows_interrupt
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)

    with pytest.raises(RoundTransactionError, match="checkpoint is missing"):
        flow._capture_round_candidates(state, 1, round_dir)

    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert calls == [True]
    assert manifest["status"] == "prepared"
    persisted = flow.store.load_state()
    assert persisted.get("pending_round") is None
    assert persisted["current_round"] == 0


def test_markerless_expected_checkpoint_is_quarantined_and_rerun(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="incomplete-checkpoint",
        iterations_per_round=25,
    )
    calls = []

    def runner(_config, _state, runner_round):
        calls.append(True)
        expected = flow.evolution_output / "checkpoints" / "checkpoint_25"
        assert not expected.exists()
        quarantined = runner_round / "abandoned-checkpoint-attempt-001"
        assert (quarantined / "metadata.json").is_file()
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    incomplete = flow.evolution_output / "checkpoints" / "checkpoint_25"
    incomplete.mkdir(parents=True)
    atomic_write_json(incomplete / "metadata.json", {"last_iteration": 25})

    rows = flow._capture_round_candidates(state, 1, round_dir)
    assert rows == []
    assert calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert len(manifest["abandoned_checkpoints"]) == 1
    assert manifest["result_checkpoint"]["last_iteration"] == 25


@pytest.mark.parametrize(
    "crash_after",
    (1, 2, 3),
    ids=("checkpoint", "completion-marker", "slice-witness"),
)
def test_checkpoint_quarantine_write_ahead_replays_each_rename_boundary(
    tmp_path, monkeypatch, crash_after
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"quarantine-crash-{crash_after}",
        iterations_per_round=25,
        milp_top=0,
    )
    initial = HumanizeFlow(config, reviewer=Reviewer())
    state = initial.store.initialize(config.serializable())
    round_dir = initial.store.round_dir(1)
    transaction = initial._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(repo, config.run_id, 25)
    marker = flow_module._completion_marker_path(round_dir)
    witness = flow_module._slice_witness_path(round_dir)
    marker.write_text('{"incomplete": true}\n')
    witness.write_text('{"incomplete": true}\n')

    _sources, destinations = initial._checkpoint_quarantine_paths(
        round_dir, checkpoint, 1
    )
    quarantine_targets = {
        path.absolute() for path in destinations.values()
    }
    original_replace = Path.replace
    renamed = []

    class SimulatedProcessDeath(BaseException):
        pass

    def die_after_selected_rename(source, target):
        result = original_replace(source, target)
        if Path(target).absolute() in quarantine_targets:
            renamed.append(Path(target).name)
            if len(renamed) == crash_after:
                raise SimulatedProcessDeath
        return result

    monkeypatch.setattr(Path, "replace", die_after_selected_rename)
    with pytest.raises(SimulatedProcessDeath):
        initial._quarantine_untrusted_evolution_attempt(
            transaction,
            round_dir,
            checkpoint,
            reason="fault-injected incomplete attempt",
        )

    durable_plan = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["abandoned_checkpoints"]
    assert len(durable_plan) == 1
    plan = durable_plan[0]
    assert plan["attempt"] == 1
    assert plan["status"] == "quarantining"
    assert plan["reason"] == "fault-injected incomplete attempt"
    assert plan["expected_checkpoint"] == str(checkpoint.absolute())
    assert plan["artifact_names"] == [
        "checkpoint", "completion_marker", "slice_witness"
    ]
    assert isinstance(plan["planned_at"], str)
    assert set(plan["artifact_identities"]) == set(plan["artifact_names"])
    for name, identity in plan["artifact_identities"].items():
        assert identity["path"] == str(destinations[name].resolve())
        assert isinstance(identity["sha256"], str)
        assert identity["bytes"] > 0
    assert len(renamed) == crash_after

    monkeypatch.setattr(Path, "replace", original_replace)
    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert not checkpoint.exists()
        assert not marker.exists()
        assert not witness.exists()
        assert all(path.exists() for path in destinations.values())
        result = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(resumed, runner_round, result, None)
        return result

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    rows = resumed._capture_round_candidates(
        resumed.store.load_state(), 1, round_dir
    )

    assert rows == []
    assert runner_calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    quarantined = manifest["abandoned_checkpoints"]
    assert len(quarantined) == 1
    assert quarantined[0]["attempt"] == 1
    assert quarantined[0]["reason"] == "fault-injected incomplete attempt"
    assert set(quarantined[0]["artifacts"]) == {
        "checkpoint", "completion_marker", "slice_witness"
    }
    assert manifest["result_checkpoint"]["last_iteration"] == 25
    assert not any(round_dir.glob("abandoned-*-attempt-002*"))


@pytest.mark.parametrize(
    "tampered_artifact",
    ("checkpoint", "completion_marker", "slice_witness"),
    ids=("checkpoint-destination", "marker-source", "witness-source"),
)
def test_checkpoint_quarantine_rejects_tampered_replay_identity(
    tmp_path, monkeypatch, tampered_artifact
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"quarantine-tamper-{tampered_artifact}",
        iterations_per_round=25,
        milp_top=0,
    )
    initial = HumanizeFlow(config, reviewer=Reviewer())
    state = initial.store.initialize(config.serializable())
    round_dir = initial.store.round_dir(1)
    transaction = initial._prepare_transaction(state, 1, round_dir)
    checkpoint = write_checkpoint(repo, config.run_id, 25)
    marker = flow_module._completion_marker_path(round_dir)
    witness = flow_module._slice_witness_path(round_dir)
    marker.write_text('{"incomplete": true}\n')
    witness.write_text('{"incomplete": true}\n')
    _sources, destinations = initial._checkpoint_quarantine_paths(
        round_dir, checkpoint, 1
    )

    original_replace = Path.replace

    class SimulatedProcessDeath(BaseException):
        pass

    def die_after_checkpoint_rename(source, target):
        result = original_replace(source, target)
        if Path(target).absolute() == destinations["checkpoint"].absolute():
            raise SimulatedProcessDeath
        return result

    monkeypatch.setattr(Path, "replace", die_after_checkpoint_rename)
    with pytest.raises(SimulatedProcessDeath):
        initial._quarantine_untrusted_evolution_attempt(
            transaction,
            round_dir,
            checkpoint,
            reason="fault-injected incomplete attempt",
        )
    monkeypatch.setattr(Path, "replace", original_replace)

    if tampered_artifact == "checkpoint":
        metadata = destinations["checkpoint"] / "metadata.json"
        metadata.write_text(metadata.read_text() + "tampered\n")
    elif tampered_artifact == "completion_marker":
        marker.write_text('{"tampered": true}\n')
    else:
        witness.write_text('{"tampered": true}\n')

    runner_calls = []

    def must_not_run(*_args):
        runner_calls.append(True)
        raise AssertionError("tampered quarantine replay launched evolution")

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=must_not_run
    )
    with pytest.raises(RoundTransactionError, match="identity changed"):
        resumed._capture_round_candidates(
            resumed.store.load_state(), 1, round_dir
        )
    assert runner_calls == []
    durable = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert durable["abandoned_checkpoints"][0]["status"] == "quarantining"
    assert durable["abandoned_checkpoints"][0]["attempt"] == 1


def candidate_file_flow(tmp_path, run_id: str):
    repo = tmp_path / run_id
    repo.mkdir()
    source = repo / "candidates.jsonl"
    source.write_bytes(jsonl(candidate(4)))
    config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        max_rounds=1,
        candidate_file=source,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    return flow, state, flow.store.round_dir(1)


def test_recovers_batch_rename_before_batch_ready_manifest(tmp_path, monkeypatch):
    flow, state, round_dir = candidate_file_flow(tmp_path, "batch-rename")
    original = flow_module.atomic_write_json

    def crash(path, value):
        if (
            path.name == "evolution-transaction.json"
            and value.get("status") == "batch-ready"
        ):
            raise RuntimeError("crash after batch rename")
        return original(path, value)

    monkeypatch.setattr(flow_module, "atomic_write_json", crash)
    with pytest.raises(RuntimeError, match="batch rename"):
        flow._capture_round_candidates(state, 1, round_dir)
    assert (round_dir / "candidate-batch.jsonl").is_file()
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == "source-ready"

    monkeypatch.setattr(flow_module, "atomic_write_json", original)
    resumed = HumanizeFlow(flow.config, reviewer=Reviewer())
    rows = resumed._capture_round_candidates(
        resumed.store.load_state(), 1, round_dir
    )
    assert rows == [candidate(4)]
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == "committed"


def test_recovers_state_commit_before_committed_manifest_and_rejects_redirect(
    tmp_path, monkeypatch
):
    flow, state, round_dir = candidate_file_flow(tmp_path, "state-commit")
    original = flow_module.atomic_write_json

    def crash(path, value):
        if (
            path.name == "evolution-transaction.json"
            and value.get("status") == "committed"
        ):
            raise RuntimeError("crash after state commit")
        return original(path, value)

    monkeypatch.setattr(flow_module, "atomic_write_json", crash)
    with pytest.raises(RuntimeError, match="state commit"):
        flow._capture_round_candidates(state, 1, round_dir)
    persisted = flow.store.load_state()
    assert persisted["pending_round"] == 1
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == "batch-ready"

    monkeypatch.setattr(flow_module, "atomic_write_json", original)
    resumed = HumanizeFlow(flow.config, reviewer=Reviewer())
    recovered = resumed.store.load_state()
    resumed._capture_round_candidates(recovered, 1, round_dir)
    recovered["current_round"] = 1
    recovered.pop("pending_round", None)
    recovered.pop("round_phase", None)
    resumed.store.write_state(recovered)
    assert len(resumed.pipeline_candidate_inputs) == 1

    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    redirected = round_dir / "redirected.jsonl"
    redirected.write_bytes((round_dir / "candidate-batch.jsonl").read_bytes())
    manifest["candidate_batch"] = str(redirected.resolve())
    atomic_write_json(manifest_path, manifest)
    with pytest.raises(RoundTransactionError, match="candidate_batch"):
        _ = resumed.pipeline_candidate_inputs


def test_legacy_pending_checkpoint_25_migrates_without_evolution(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-pending",
        max_rounds=1,
        iterations_per_round=25,
        milp_top=0,
    )
    calls = []

    def runner(*_args):
        calls.append(True)
        raise AssertionError("legacy pending round reran evolution")

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    row = candidate(5)
    flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    flow.candidate_log.write_bytes(jsonl(row))
    checkpoint = write_checkpoint(repo, config.run_id, 25)
    round_dir = flow.store.round_dir(1)
    (round_dir / "candidates.jsonl").write_bytes(jsonl(row))
    (round_dir / "selected.jsonl").write_bytes(b"")
    (round_dir / "milp.jsonl").write_bytes(b"")
    state.update({
        "pending_round": 1,
        "round_phase": "audit",
        "candidate_offset": flow.candidate_log.stat().st_size,
        "last_checkpoint": str(checkpoint.resolve()),
    })
    state.pop("round_transaction_version")
    flow.store.write_state(state)

    completed = flow.run()
    assert calls == []
    assert completed["status"] == "search-complete"
    assert completed["round_transaction_version"] == 2
    assert not (round_dir / "evolution-transaction.json").exists()


def test_prepare_freezes_context_and_api_environment_for_recovery(
    tmp_path, monkeypatch
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    monkeypatch.setenv("OPENAI_API_BASE", "https://frozen.invalid/v1")
    config = FlowConfig(
        repo_dir=repo,
        run_id="frozen-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    flow.store.memory_path.write_text("original bitlesson\n")
    round_dir = flow.store.round_dir(1)

    transaction = flow._prepare_transaction(state, 1, round_dir)

    assert (round_dir / "search-context.md").read_text() == (
        "original bitlesson\n\n"
    )
    assert transaction["launch_binding"]["context"][
        "sha256"
    ] == hashlib.sha256(b"original bitlesson\n\n").hexdigest()
    assert transaction["invocation_binding"]["api_base"] == (
        "https://frozen.invalid/v1"
    )

    flow.store.memory_path.write_text("later bitlesson must not leak\n")
    monkeypatch.setenv("OPENAI_API_BASE", "https://changed.invalid/v1")
    recovered = flow._load_transaction(state, 1, round_dir)

    assert recovered is not None
    assert recovered["invocation_binding"]["api_base"] == (
        "https://frozen.invalid/v1"
    )
    assert (round_dir / "search-context.md").read_text() == (
        "original bitlesson\n\n"
    )


def test_prepare_quarantines_context_orphaned_before_manifest(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="orphan-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    orphan = round_dir / "search-context.md"
    orphan.write_text("context written before process death\n")

    transaction = flow._prepare_transaction(state, 1, round_dir)

    archives = list(round_dir.glob("orphan-search-context-*.md"))
    assert len(archives) == 1
    assert archives[0].read_text() == "context written before process death\n"
    assert transaction["launch_binding"]["context"]["path"] == str(
        (round_dir / "search-context.md").resolve()
    )
    assert (round_dir / "search-context.md").read_text() != archives[
        0
    ].read_text()


def test_prepared_transaction_rejects_worker_budget_tampering(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    (repo / "evolve/config.yaml").write_text(
        "evaluator:\n  parallel_evaluations: 6\n"
    )
    config = FlowConfig(
        repo_dir=repo,
        run_id="worker-binding-tamper",
        iterations_per_round=3,
        milp_top=0,
        max_total_workers=4,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    assert manifest["invocation_binding"]["max_parallel_evaluations"] == 4
    manifest["invocation_binding"]["max_parallel_evaluations"] = 5
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="unified worker budget",
    ):
        flow._load_transaction(state, 1, round_dir)


@pytest.mark.parametrize(
    "tamper",
    ("context", "dependency", "invocation"),
)
def test_prepared_transaction_rejects_frozen_launch_tampering(
    tmp_path, tamper
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"binding-tamper-{tamper}",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"

    if tamper == "context":
        (round_dir / "search-context.md").write_text("tampered context\n")
        expected = "launch inputs changed"
    elif tamper == "dependency":
        (repo / "evaluation/evaluator.py").write_text(
            "# tampered evaluator dependency\n"
        )
        expected = "launch inputs changed"
    else:
        manifest = json.loads(manifest_path.read_text())
        manifest["invocation_binding"]["model_names"] = ["tampered-model"]
        atomic_write_json(manifest_path, manifest)
        expected = "model binding changed"

    with pytest.raises(flow_module.RoundTransactionError, match=expected):
        flow._load_transaction(state, 1, round_dir)


@pytest.mark.parametrize("tamper", ("binary", "version"))
def test_codex_execution_identity_is_frozen_and_revalidated(
    tmp_path, monkeypatch, tamper
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    native = repo / "fake-codex"
    native.write_bytes(b"\x7fELFfake-codex-v1")
    native.chmod(0o755)
    version = {"value": "codex-test 1.0"}
    monkeypatch.setattr(
        flow_module, "_resolve_native_codex_path", lambda _requested: native
    )
    monkeypatch.setattr(
        flow_module, "_codex_version", lambda _executable: version["value"]
    )
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"codex-binding-{tamper}",
        iterations_per_round=3,
        milp_top=0,
        codex_cli=True,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)

    transaction = flow._prepare_transaction(state, 1, round_dir)

    executable = transaction["launch_binding"]["codex_executable"]
    invocation = transaction["invocation_binding"]
    assert executable["path"] == str(native.resolve())
    assert executable["mode"] == 0o755
    assert invocation["codex_version"] == "codex-test 1.0"
    assert invocation["codex_cwd"] == str(repo.resolve())

    if tamper == "binary":
        native.write_bytes(b"\x7fELFfake-codex-v2")
    else:
        version["value"] = "codex-test 2.0"

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="Codex CLI native executable changed|Codex execution identity changed",
    ):
        flow._load_transaction(state, 1, round_dir)


@pytest.mark.parametrize(
    ("tamper", "message"),
    (
        ("invocation", "witness mismatch for model_names"),
        ("no-success", "no successful program"),
        ("program-identity", "program identity is invalid"),
    ),
)
def test_completed_transaction_replays_exact_witness_binding(
    tmp_path, tamper, message
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"witness-binding-{tamper}",
        iterations_per_round=3,
        milp_top=0,
    )

    def runner(_config, _state, runner_round):
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._capture_round_candidates(state, 1, round_dir)

    witness_path = flow_module._slice_witness_path(round_dir)
    marker_path = flow_module._completion_marker_path(round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    witness = json.loads(witness_path.read_text())
    if tamper == "invocation":
        witness["model_names"] = ["tampered-model"]
    elif tamper == "no-success":
        witness["outcomes"][0] = {
            "iteration": 1,
            "status": "worker_error",
            "error_sha256": hashlib.sha256(b"tampered error").hexdigest(),
            "error_bytes": len(b"tampered error"),
        }
        witness["successful_evaluations"] = 0
        witness["worker_errors"] = 3
    else:
        witness["outcomes"][0]["program_sha256"] = "not-a-digest"
    atomic_write_json(witness_path, witness)

    witness_identity = flow_module._file_descriptor(
        witness_path, "tampered witness"
    )
    marker = json.loads(marker_path.read_text())
    marker["slice_witness_sha256"] = witness_identity["sha256"]
    marker["slice_witness_bytes"] = witness_identity["bytes"]
    if tamper == "invocation":
        marker["model_names"] = ["tampered-model"]
    atomic_write_json(marker_path, marker)

    manifest = json.loads(manifest_path.read_text())
    manifest["completion_witness_sha256"] = witness_identity["sha256"]
    manifest["completion_marker_sha256"] = flow_module._file_sha256(marker_path)
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(flow_module.RoundTransactionError, match=message):
        flow._validate_completed_transaction(1, round_dir)
