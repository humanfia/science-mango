import copy
import hashlib
import json
from pathlib import Path

import pytest

import evolve.run_evolution as evolution_launcher
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


def write_launch_inputs(repo: Path, *, portfolio: bool = False) -> None:
    evolve = repo / "evolve"
    evolve.mkdir(parents=True, exist_ok=True)
    config_text = "evaluator:\n  parallel_evaluations: 1\n"
    if portfolio:
        config_text += (
            "database:\n"
            "  num_islands: 5\n"
            "  feature_dimensions:\n"
            "    - pattern_type\n"
            "    - support_split_type\n"
            "    - search_structural_entropy\n"
            "  feature_bins:\n"
            "    pattern_type: 6\n"
            "    support_split_type: 6\n"
            "    search_structural_entropy: 5\n"
            "qcode_search_portfolio:\n"
            "  enabled: true\n"
            "  schema_version: 1\n"
        )
    (evolve / "config.yaml").write_text(config_text)
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
    *,
    schema_version: int = (
        flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
    ),
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
    candidate_source = (
        flow_module._candidate_log_range_identity(
            flow.candidate_log,
            start_offset=int(transaction["candidate_start_offset"]),
        )
        if schema_version in {
            flow_module.EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION,
            flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
        }
        else None
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
    portfolio_enabled = flow_module._search_portfolio_enabled_from_config(
        Path(launch["config"]["path"])
    )
    attempts = [
        {"iteration": i, "island_id": 0, "result": "future"}
        for i in range(base_iteration + 1, base_iteration + count + 1)
    ]
    search_portfolio = None
    if (
        schema_version
        == flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION
        and portfolio_enabled
    ):
        policy = flow_module._adaptive_mutation_policy_from_context(
            Path(launch["context"]["path"])
        )
        policy_sha256 = (
            flow_module._adaptive_mutation_policy_sha256(policy)
        )
        parent_code = json.loads(
            (
                Path(result["path"])
                / "programs"
                / "program.json"
            ).read_text()
        )["code"]
        parent_code_sha256 = hashlib.sha256(
            parent_code.encode()
        ).hexdigest()
        role_counts = {
            role: sum(
                (iteration - start)
                % flow_module.SEARCH_PORTFOLIO_ISLAND_COUNT
                == island
                for iteration in range(start, start + count)
            )
            for island, role in enumerate(
                flow_module.SEARCH_PORTFOLIO_ROLES
            )
        }
        attempts = []
        for iteration in range(start, start + count):
            island = (
                iteration - start
            ) % flow_module.SEARCH_PORTFOLIO_ISLAND_COUNT
            attempts.append({
                "iteration": iteration,
                "island_id": island,
                "result": "future",
                "search_portfolio_schema_version": 1,
                "search_policy_sha256": policy_sha256,
                "search_role":
                    flow_module.SEARCH_PORTFOLIO_ROLES[island],
                "search_tactic":
                    flow_module._adaptive_mutation_tactic_from_parent_hash(
                        policy,
                        parent_code_sha256=parent_code_sha256,
                        iteration=iteration,
                    ),
                "search_parent_program_id": "program",
                "search_parent_code_sha256": parent_code_sha256,
                "search_role_submission_counts": role_counts,
            })
        search_portfolio = {
            "schema_version": 1,
            "island_count": flow_module.SEARCH_PORTFOLIO_ISLAND_COUNT,
            "roles": list(flow_module.SEARCH_PORTFOLIO_ROLES),
            "policy_sha256": policy_sha256,
            "role_submission_counts": role_counts,
        }
    witness = {
        "schema_version": schema_version,
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
        "submission_attempts": attempts,
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
    if schema_version == flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION:
        witness["search_portfolio"] = search_portfolio
    if candidate_source is not None:
        witness.update({
            "candidate_log_path": candidate_source["path"],
            "candidate_log_device": candidate_source["device"],
            "candidate_log_inode": candidate_source["inode"],
            "candidate_start_offset": candidate_source["start_offset"],
            "candidate_end_offset": candidate_source["end_offset"],
            "candidate_range_sha256": candidate_source["sha256"],
            "candidate_range_bytes": candidate_source["bytes"],
            "candidate_wal_clean": candidate_source["wal_clean"],
        })
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
    witness_descriptor["schema_version"] = witness["schema_version"]
    if schema_version in {
        flow_module.EVOLUTION_SLICE_WITNESS_PREVIOUS_SCHEMA_VERSION,
        flow_module.EVOLUTION_SLICE_WITNESS_SCHEMA_VERSION,
    }:
        witness_descriptor.update({
            field: witness[field]
            for field in flow_module.CANDIDATE_WITNESS_FIELDS
        })
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
    assert marker["schema_version"] == 4
    assert (round_dir / "openevolve-slice-witness.json").is_file()


def test_prepared_legacy_proof_with_partial_tail_is_quarantined_and_rerun(
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
        write_full_slice_proof(
            flow,
            _round_dir,
            checkpoint,
            None,
            schema_version=2,
        )
        raise SystemExit(99)

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=crashes_after_checkpoint
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    with pytest.raises(SystemExit):
        flow._capture_round_candidates(state, 1, round_dir)

    def rerun_without_unbound_tail(_config, _state, runner_round):
        calls.append("replayed")
        assert flow.candidate_log.read_bytes() == b""
        checkpoint = write_checkpoint(repo, config.run_id, 25)
        write_full_slice_proof(resumed, runner_round, checkpoint, None)
        return checkpoint

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=rerun_without_unbound_tail
    )
    recovered = resumed.store.load_state()
    rows = resumed._capture_round_candidates(recovered, 1, round_dir)

    assert calls == [True, "replayed"]
    assert rows == []
    assert resumed.candidate_log.read_bytes() == b""
    archive = round_dir / "abandoned-candidate-tail-001.bin"
    assert archive.read_bytes() == original_tail
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    recovery = manifest["abandoned_ranges"]
    assert len(recovery) == 1
    assert recovery[0]["last_complete_offset"] == len(jsonl(row))
    assert recovery[0]["partial_bytes"] == len(fragment)
    assert recovery[0]["archive_sha256"] == hashlib.sha256(
        original_tail
    ).hexdigest()
    assert recovery[0]["complete_candidate_batch"]["rows"] == 1
    assert manifest["candidate_end_offset"] == 0
    assert (
        round_dir / "abandoned-checkpoint-attempt-001"
    ).is_dir()


def test_flow_recovers_orphan_candidate_wal_before_tail_inspection(
    tmp_path,
):
    import evolve.openevolve_evaluator as evaluator

    repo = tmp_path / "repo"
    repo.mkdir()
    config = FlowConfig(
        repo_dir=repo,
        run_id="flow-wal-recovery",
        iterations_per_round=1,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    path = flow.candidate_log.resolve()
    path.parent.mkdir(parents=True)
    path.touch()
    payload = jsonl(candidate(51))
    evaluator._install_candidate_log_wal(
        path,
        start_offset=0,
        payload=payload,
    )
    path.write_bytes(payload[:19])
    wal_file, temporary = evaluator._candidate_log_wal_paths(path)

    assert flow._candidate_log_size(start_offset=0) == len(payload)
    assert path.read_bytes() == payload
    assert not wal_file.exists()
    assert not temporary.exists()


@pytest.mark.parametrize(
    "mutation",
    ("delete-empty", "replace-empty", "truncate", "tamper"),
)
def test_candidate_range_witness_rejects_log_replacement_or_change(
    tmp_path,
    mutation,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"candidate-range-{mutation}",
        iterations_per_round=1,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    original = (
        b""
        if mutation in {"delete-empty", "replace-empty"}
        else jsonl(candidate(52))
    )
    flow.candidate_log.write_bytes(original)
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(flow, round_dir, checkpoint, None)

    if mutation == "delete-empty":
        flow.candidate_log.unlink()
    elif mutation == "replace-empty":
        flow_module.atomic_write_bytes(flow.candidate_log, b"")
    elif mutation == "truncate":
        flow.candidate_log.write_bytes(original[:-1])
    else:
        changed = bytearray(original)
        changed[0] = ord("[")
        flow.candidate_log.write_bytes(changed)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="candidate",
    ):
        flow._capture_round_candidates(state, 1, round_dir)


def test_candidate_range_witness_accepts_unchanged_log(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="candidate-range-valid",
        iterations_per_round=1,
        milp_top=0,
    )
    row = candidate(53)
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    flow.candidate_log.write_bytes(jsonl(row))
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(flow, round_dir, checkpoint, None)

    assert flow._capture_round_candidates(state, 1, round_dir) == [row]


def test_portfolio_witness_v4_replays_policy_roles_tactics_and_quota(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo, portfolio=True)
    config = FlowConfig(
        repo_dir=repo,
        run_id="portfolio-witness-v4",
        iterations_per_round=7,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    flow.candidate_log.write_bytes(jsonl(candidate(55)))
    checkpoint = write_checkpoint(repo, config.run_id, 7)
    write_full_slice_proof(flow, round_dir, checkpoint, None)
    witness_path = flow_module._slice_witness_path(round_dir)
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output, checkpoint
    )

    def validate() -> dict:
        return flow_module._validate_slice_witness(
            witness_path,
            config,
            None,
            result,
            transaction["launch_binding"],
            transaction["invocation_binding"],
            flow.candidate_log,
            int(transaction["candidate_start_offset"]),
        )

    accepted = validate()
    assert accepted["search_portfolio"]["role_submission_counts"] == {
        "compact_mixed_2_2": 2,
        "hybrid_2_3_3_2": 2,
        "balanced_3_3": 1,
        "asymmetric_2_4_4_2": 1,
        "failure_repair_novelty": 1,
    }
    original = json.loads(witness_path.read_text())

    mutations = []

    def mutate_policy(row):
        row["search_portfolio"]["policy_sha256"] = "0" * 64

    mutations.append(mutate_policy)

    def mutate_island(row):
        row["submission_attempts"][0]["island_id"] = 4

    mutations.append(mutate_island)

    def mutate_role(row):
        row["submission_attempts"][0]["search_role"] = (
            "failure_repair_novelty"
        )

    mutations.append(mutate_role)

    def mutate_tactic(row):
        row["submission_attempts"][0]["search_tactic"] = (
            "repair_x_low_weight"
        )

    mutations.append(mutate_tactic)

    def mutate_parent_hash(row):
        row["submission_attempts"][0][
            "search_parent_code_sha256"
        ] = "1" * 64

    mutations.append(mutate_parent_hash)

    def mutate_bool_quota(row):
        row["search_portfolio"]["role_submission_counts"][
            "balanced_3_3"
        ] = True

    mutations.append(mutate_bool_quota)

    def mutate_extra_field(row):
        row["submission_attempts"][0]["unbound"] = "forbidden"

    mutations.append(mutate_extra_field)

    for mutate in mutations:
        changed = copy.deepcopy(original)
        mutate(changed)
        atomic_write_json(witness_path, changed)
        with pytest.raises(RoundTransactionError):
            validate()


def test_legacy_source_ready_candidate_binding_remains_resumable(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-source-ready",
        iterations_per_round=1,
        milp_top=0,
    )
    row = candidate(54)
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    encoded = jsonl(row)
    flow.candidate_log.write_bytes(encoded)
    checkpoint = write_checkpoint(repo, config.run_id, 1)
    write_full_slice_proof(
        flow,
        round_dir,
        checkpoint,
        None,
        schema_version=2,
    )
    result = flow_module._checkpoint_descriptor(
        flow.evolution_output,
        checkpoint,
    )
    transaction.update({
        "status": "source-ready",
        "result_checkpoint": result,
        "completion_witness_sha256": flow_module._file_sha256(
            flow_module._slice_witness_path(round_dir)
        ),
        "completion_marker_sha256": flow_module._file_sha256(
            flow_module._completion_marker_path(round_dir)
        ),
        "candidate_end_offset": len(encoded),
        "candidate_source_sha256": hashlib.sha256(encoded).hexdigest(),
        "candidate_source_rows": 1,
        "source_ready_at": "legacy",
    })
    atomic_write_json(
        round_dir / "evolution-transaction.json",
        transaction,
    )

    resumed = HumanizeFlow(
        config,
        reviewer=Reviewer(),
        evolution_runner=lambda *_args: (_ for _ in ()).throw(
            AssertionError("source-ready legacy slice must not rerun")
        ),
    )
    assert resumed._capture_round_candidates(
        resumed.store.load_state(),
        1,
        round_dir,
    ) == [row]


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


def test_round_finalize_event_failure_keeps_resumable_atomic_state(
    tmp_path, monkeypatch
):
    flow, _state, _round_dir = candidate_file_flow(
        tmp_path, "finalize-event-failure"
    )
    original_event = flow.store.event

    def fail_completed_event(event_name, **fields):
        if event_name == "round_completed":
            raise RuntimeError("injected round completion event failure")
        return original_event(event_name, **fields)

    monkeypatch.setattr(flow.store, "event", fail_completed_event)
    with pytest.raises(RuntimeError, match="injected round completion"):
        flow.run()

    failed = flow.store.load_state()
    assert failed["current_round"] == 0
    assert failed["pending_round"] == 1
    assert failed["round_phase"] == "finalize"
    assert failed["rounds"] == []

    resumed = HumanizeFlow(flow.config, reviewer=Reviewer())
    completed = resumed.run()
    assert completed["current_round"] == 1
    assert "pending_round" not in completed
    assert "round_phase" not in completed
    assert len(completed["rounds"]) == 1


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


def test_completed_round_records_transaction_bound_candidate_diversity(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    source = repo / "candidates.jsonl"
    mixed = candidate(60)
    mixed.update({
        "A_terms": [[0, 0], [1, 1]],
        "B_terms": [[0, 1], [1, 0]],
        # These self-reported labels deliberately contradict the terms.
        "pattern_type": "reported-nonmixed",
    })
    duplicate = dict(mixed)
    duplicate.update({
        "d": 5,
        "fom": 999.0,
        "pattern_type": "another-untrusted-label",
    })
    nonmixed = candidate(61)
    nonmixed.update({
        "A_terms": [[0, 0], [1, 0]],
        "B_terms": [[0, 0], [0, 1], [2, 0]],
        "pattern_type": "reported-mixed",
    })
    source.write_bytes(jsonl(mixed, duplicate, nonmixed))
    config = FlowConfig(
        repo_dir=repo,
        run_id="candidate-diversity-summary",
        max_rounds=1,
        candidate_file=source,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)

    batch = flow._capture_round_candidates(state, 1, round_dir)
    review = Reviewer().review("", round_dir)
    flow._finish_round(state, 1, batch, [], review, round_dir)
    flow.store.write_state(state)

    persisted = flow.store.load_state()
    assert persisted is not None
    diversity = persisted["rounds"][0]["candidate_diversity"]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert diversity == {
        "schema_version": 1,
        "basis": "transaction-bound-source-and-canonical-batch",
        "raw_candidate_source_rows": 3,
        "canonical_unique_batch_rows": 2,
        "duplicate_count": 1,
        "duplicate_rate": pytest.approx(1 / 3),
        "candidate_source_sha256": manifest["candidate_source_sha256"],
        "candidate_batch_sha256": manifest[
            "candidate_batch_identity"
        ]["sha256"],
        "support_split_counts": {"2+2": 1, "2+3": 1},
        "mixed_vs_nonmixed_counts": {
            "mixed": 1,
            "nonmixed": 1,
            "unclassified": 0,
        },
    }


def test_next_round_freezes_machine_diversity_advisory(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="machine-diversity-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    state["current_round"] = 1
    state["rounds"] = [{
        "round": 1,
        "candidate_diversity": {
            "schema_version": 1,
            "basis": "transaction-bound-source-and-canonical-batch",
            "raw_candidate_source_rows": 10,
            "canonical_unique_batch_rows": 4,
            "duplicate_count": 6,
            "duplicate_rate": 0.6,
            "candidate_source_sha256": "a" * 64,
            "candidate_batch_sha256": "b" * 64,
            "support_split_counts": {"2+2": 3, "3+3": 1},
            "mixed_vs_nonmixed_counts": {
                "mixed": 1,
                "nonmixed": 3,
                "unclassified": 0,
            },
        },
    }]
    flow.store.memory_path.write_text("base bitlesson\n")
    round_dir = flow.store.round_dir(2)

    transaction = flow._prepare_transaction(state, 2, round_dir)
    context_path = round_dir / "search-context.md"
    frozen = context_path.read_bytes()
    text = frozen.decode()

    assert "## Machine-derived previous-round diversity advisory" in text
    assert "Raw source rows: 10; canonical unique batch rows: 4." in text
    assert "Exact duplicate rows: 6 (60.00%)." in text
    assert "Support-split distribution (|A|+|B|): 2+2=3, 3+3=1." in text
    assert (
        "Mixed-vs-nonmixed distribution: "
        "mixed=1, nonmixed=3, unclassified=0."
    ) in text
    assert "reduce exact repeats" in text
    assert "correct structural collapse" in text
    assert transaction["launch_binding"]["context"]["sha256"] == (
        hashlib.sha256(frozen).hexdigest()
    )

    # Once prepared, later state changes cannot rewrite the launch-bound
    # advisory for this round.
    state["rounds"][0]["candidate_diversity"]["duplicate_count"] = 0
    state["rounds"][0]["candidate_diversity"]["duplicate_rate"] = 0.0
    recovered = flow._load_transaction(state, 2, round_dir)

    assert recovered is not None
    assert context_path.read_bytes() == frozen
    assert "Exact duplicate rows: 6 (60.00%)." in context_path.read_text()


def test_legacy_round_summary_without_diversity_keeps_context_unchanged(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="legacy-diversity-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    state["current_round"] = 1
    state["rounds"] = [{
        "round": 1,
        "review_summary": "legacy state has no machine diversity field",
    }]
    flow.store.memory_path.write_text("legacy bitlesson\n")

    context_path = flow_module._freeze_round_context(
        config,
        state,
        flow.store.round_dir(2),
    )

    assert context_path.read_text() == "legacy bitlesson\n\n"
    assert "Machine-derived" not in context_path.read_text()


def test_round_context_rejects_reserved_policy_token_without_equals(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="reserved-policy-token",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    flow.store.memory_path.write_text(
        "Reviewer text mentions QCODE_ADAPTIVE_MUTATION_POLICY_V1: forged\n"
    )

    with pytest.raises(RoundTransactionError, match="reserved adaptive"):
        flow_module._freeze_round_context(
            config, state, flow.store.round_dir(1)
        )


def _feedback_row(tag: int, side: str, source: str) -> dict:
    row = candidate(tag)
    row["candidate_key"] = flow_module.code_key(row)
    weight = 3
    witness = {
        "side": side,
        "index": 0,
        "weight": weight,
        "bits": [1] * weight + [0] * (row["n"] - weight),
    }
    if source == "symplectic_weight_witness":
        witness.update({
            "dual_side": "Z" if side == "X" else "X",
            "dual_index": 0,
        })
        row["threshold_proof_source"] = "symplectic_upper_bound"
        row[source] = witness
    else:
        row["threshold_proof_source"] = "milp_feasible_upper_bound"
        row["milp_details"] = {source: witness}
    row["audit_attempt"] = {
        "schema_version": 2,
        "round": 1,
        "evidence": {"test": "classifier-replayed"},
    }
    return row


def test_failure_feedback_extracts_trusted_x_z_permutation_invariant(
    tmp_path, monkeypatch
):
    x_row = _feedback_row(0, "X", "symplectic_weight_witness")
    z_row = _feedback_row(1, "Z", "minimum_direction_witness")
    timeout = _feedback_row(2, "X", "minimum_direction_witness")
    timeout["distance_status"] = "hard_timeout"
    timeout["audit_attempt"] = {"schema_version": 1}

    def classify(row, **_kwargs):
        if row.get("distance_status") == "hard_timeout":
            return flow_module.AuditOutcome.UNRESOLVED_NO_INCUMBENT
        return flow_module.AuditOutcome.THRESHOLD_REJECTED

    monkeypatch.setattr(flow_module, "classify_evaluation", classify)
    source = {
        "path": "milp.jsonl",
        "sha256": "a" * 64,
        "bytes": 123,
        "rows": 3,
    }
    first = flow_module._build_failure_direction_feedback(
        round_number=1,
        source_milp=source,
        audited_rows=[x_row, timeout, z_row],
    )
    second = flow_module._build_failure_direction_feedback(
        round_number=1,
        source_milp=source,
        audited_rows=[z_row, x_row, timeout],
    )

    assert first == second
    assert sorted(item["side"] for item in first["observations"]) == ["X", "Z"]
    assert {
        item["source"] for item in first["observations"]
    } == {"symplectic_weight_witness", "minimum_direction_witness"}
    tactics = first["mutation_policy"]["tactics"]
    assert [item["tactic"] for item in tactics] == list(
        flow_module.ADAPTIVE_MUTATION_TACTICS
    )
    assert all(type(item["weight"]) is int for item in tactics)
    assert sum(item["weight"] for item in tactics) == 1000
    assert tactics[0]["weight"] >= 250
    assert all(item["weight"] > 0 for item in tactics[1:])


def test_untrusted_timeout_does_not_vote_in_failure_policy(
    monkeypatch,
):
    timeout = _feedback_row(3, "X", "minimum_direction_witness")
    timeout["audit_attempt"] = {"schema_version": 1}
    monkeypatch.setattr(
        flow_module,
        "classify_evaluation",
        lambda _row, **_kwargs: (
            flow_module.AuditOutcome.UNRESOLVED_NO_INCUMBENT
        ),
    )
    feedback = flow_module._build_failure_direction_feedback(
        round_number=1,
        source_milp={
            "path": "milp.jsonl",
            "sha256": "b" * 64,
            "bytes": 1,
            "rows": 1,
        },
        audited_rows=[timeout],
    )

    assert feedback["observations"] == []
    assert [item["weight"] for item in feedback["mutation_policy"]["tactics"]] == [
        1000,
        0,
        0,
        0,
    ]


def test_failure_feedback_context_is_deterministic_and_tamper_fails(
    tmp_path, monkeypatch
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="failure-feedback-context",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    x_row = _feedback_row(0, "X", "symplectic_weight_witness")
    z_row = _feedback_row(1, "Z", "minimum_direction_witness")
    monkeypatch.setattr(
        flow_module,
        "classify_evaluation",
        lambda _row, **_kwargs: flow_module.AuditOutcome.THRESHOLD_REJECTED,
    )
    previous_dir = flow.store.round_dir(1)
    (previous_dir / "milp.jsonl").write_bytes(jsonl(z_row, x_row))
    feedback_summary = (
        flow_module._write_round_failure_direction_feedback(
            round_number=1,
            round_dir=previous_dir,
            audited_rows=[x_row, z_row],
        )
    )
    state["current_round"] = 1
    state["rounds"] = [{
        "round": 1,
        "failure_direction_feedback": feedback_summary,
    }]
    current_dir = flow.store.round_dir(2)

    context = flow_module._freeze_round_context(
        config, state, current_dir
    )
    frozen = context.read_bytes()
    policy_lines = [
        line for line in context.read_text().splitlines()
        if line.startswith("QCODE_ADAPTIVE_MUTATION_POLICY_V1=")
    ]
    assert len(policy_lines) == 1
    policy_mapping = json.loads(policy_lines[0].split("=", 1)[1])
    assert set(policy_mapping) == set(flow_module.ADAPTIVE_MUTATION_TACTICS)
    assert policy_mapping == {
        item["tactic"]: item["weight"]
        for item in json.loads(
            (
                previous_dir / "failure-direction-feedback.json"
            ).read_text()
        )["mutation_policy"]["tactics"]
    }
    assert evolution_launcher._validated_adaptive_mutation_policy(
        context.read_text()
    ) == policy_mapping
    assert "trusted sealed low-weight logical witnesses: 2 (X=1, Z=1)" in (
        context.read_text()
    )
    context.unlink()
    assert flow_module._freeze_round_context(
        config, state, current_dir
    ).read_bytes() == frozen

    artifact_path = previous_dir / "failure-direction-feedback.json"
    artifact = json.loads(artifact_path.read_text())
    artifact["mutation_policy"]["total_weight"] = 999
    artifact_path.write_text(
        flow_module._canonical_compact_json(artifact) + "\n"
    )
    context.unlink()
    with pytest.raises(RoundTransactionError, match="self-hash"):
        flow_module._freeze_round_context(config, state, current_dir)


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


def test_prepared_transaction_rebinds_changed_sources_and_archives_old_attempt(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-source-rebind",
        iterations_per_round=3,
        milp_top=0,
    )
    old_row = candidate(31)
    new_row = candidate(32)
    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert flow.candidate_log.read_bytes() == b""
        assert (
            runner_round / "abandoned-checkpoint-attempt-001"
        ).is_dir()
        assert (
            runner_round
            / "abandoned-completion-marker-attempt-001.json"
        ).is_file()
        assert (
            runner_round / "abandoned-slice-witness-attempt-001.json"
        ).is_file()
        flow.candidate_log.write_bytes(jsonl(new_row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    old_evaluator = transaction["launch_binding"]["evaluation_evaluator"]
    flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    flow.candidate_log.write_bytes(jsonl(old_row))
    old_checkpoint = write_checkpoint(repo, config.run_id, 3)
    write_full_slice_proof(flow, round_dir, old_checkpoint, None)

    evaluator = repo / "evaluation/evaluator.py"
    evaluator.write_text("# upgraded evaluator source\n")
    rows = flow._capture_round_candidates(state, 1, round_dir)

    assert rows == [new_row]
    assert runner_calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["status"] == "committed"
    assert len(manifest["evolution_binding_rebinds"]) == 1
    rebind = manifest["evolution_binding_rebinds"][0]
    assert rebind["status"] == "rebound"
    assert "launch:evaluation_evaluator" in rebind["reason"]
    assert (
        rebind["old_launch_binding"]["evaluation_evaluator"]
        == old_evaluator
    )
    assert (
        rebind["new_launch_binding"]["evaluation_evaluator"]
        == flow_module._file_descriptor(evaluator, "current evaluator")
    )
    assert rebind["old_binding_sha256"] != rebind["new_binding_sha256"]
    assert rebind["abandoned_ranges_after"] == 1
    assert rebind["abandoned_checkpoints_after"] == 1
    assert (
        round_dir / "abandoned-candidate-tail-001.bin"
    ).read_bytes() == jsonl(old_row)
    assert (
        round_dir / "abandoned-candidate-complete-001.jsonl"
    ).read_bytes() == jsonl(old_row)
    assert manifest["abandoned_checkpoints"][0]["attempt"] == 1


def test_unbound_prepared_transaction_migrates_allowlisted_legacy_binding(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-legacy-binding",
        iterations_per_round=3,
        milp_top=0,
    )
    old_row = candidate(33)
    new_row = candidate(34)
    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert flow.candidate_log.read_bytes() == b""
        flow.candidate_log.write_bytes(jsonl(new_row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    oldest_launch = dict(manifest["launch_binding"])
    for field in (
        "evaluation_final_gate",
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        oldest_launch.pop(field)
    previous_launch = dict(manifest["launch_binding"])
    for field in (
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        previous_launch.pop(field)
    invocation = manifest["invocation_binding"]
    oldest_sha256 = flow_module._binding_identity_sha256(
        oldest_launch, invocation
    )
    previous_sha256 = flow_module._binding_identity_sha256(
        previous_launch, invocation
    )

    def historical_rebind(
        attempt, old_launch, old_sha256, new_launch, new_sha256
    ):
        return {
            "attempt": attempt,
            "status": "rebound",
            "reason": "historical launch binding schema",
            "old_launch_binding": old_launch,
            "old_invocation_binding": invocation,
            "old_binding_sha256": old_sha256,
            "candidate_start_offset": manifest["candidate_start_offset"],
            "evolution_attempts_before": 0,
            "abandoned_ranges_before": 0,
            "abandoned_checkpoints_before": 0,
            "planned_at": "legacy",
            "new_launch_binding": new_launch,
            "new_invocation_binding": invocation,
            "new_binding_sha256": new_sha256,
            "evolution_attempts_after": 0,
            "abandoned_ranges_after": 0,
            "abandoned_checkpoints_after": 0,
            "rebound_at": "legacy",
        }

    manifest["launch_binding"] = previous_launch
    manifest["evolution_binding_rebinds"] = [
        historical_rebind(
            1,
            oldest_launch,
            oldest_sha256,
            oldest_launch,
            oldest_sha256,
        ),
        historical_rebind(
            2,
            oldest_launch,
            oldest_sha256,
            previous_launch,
            previous_sha256,
        ),
    ]
    atomic_write_json(manifest_path, manifest)
    flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    flow.candidate_log.write_bytes(jsonl(old_row))

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow._load_transaction(state, 1, round_dir)
    assert flow.candidate_log.read_bytes() == jsonl(old_row)

    rows = flow._capture_round_candidates(state, 1, round_dir)

    assert rows == [new_row]
    assert runner_calls == [True]
    durable = json.loads(manifest_path.read_text())
    assert durable["status"] == "committed"
    assert len(durable["evolution_binding_rebinds"]) == 3
    migration = durable["evolution_binding_rebinds"][2]
    assert migration["status"] == "rebound"
    assert "launch:evaluation_search_contract" in migration["reason"]
    assert (
        "evaluation_search_contract"
        not in migration["old_launch_binding"]
    )
    assert (
        "evaluation_search_contract"
        in migration["new_launch_binding"]
    )
    assert (
        round_dir / "abandoned-candidate-complete-001.jsonl"
    ).read_bytes() == jsonl(old_row)
    flow._validate_completed_transaction(1, round_dir)


def test_completed_round_accepts_only_immediately_previous_dependency_shape(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="completed-previous-dependency-shape",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    transaction = flow._prepare_transaction(state, 1, round_dir)
    current_launch = transaction["launch_binding"]
    previous_launch = dict(current_launch)
    previous_launch.pop("evaluation_structural_features")

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow_module._validate_stored_binding_shape(
            config,
            previous_launch,
            transaction["invocation_binding"],
            round_dir,
            current_launch,
        )

    validated, _invocation = flow_module._validate_stored_binding_shape(
        config,
        previous_launch,
        transaction["invocation_binding"],
        round_dir,
        current_launch,
        allow_previous_committed=True,
    )
    assert validated == previous_launch

    older_launch = dict(previous_launch)
    older_launch.pop("evaluation_search_contract")
    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow_module._validate_stored_binding_shape(
            config,
            older_launch,
            transaction["invocation_binding"],
            round_dir,
            current_launch,
            allow_previous_committed=True,
        )


def test_prepared_binding_history_rejects_legacy_schema_downgrade(
    tmp_path,
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-legacy-schema-downgrade",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    invocation = manifest["invocation_binding"]
    previous_launch = dict(manifest["launch_binding"])
    for field in (
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        previous_launch.pop(field)
    oldest_launch = dict(previous_launch)
    oldest_launch.pop("evaluation_final_gate")
    previous_sha256 = flow_module._binding_identity_sha256(
        previous_launch, invocation
    )
    oldest_sha256 = flow_module._binding_identity_sha256(
        oldest_launch, invocation
    )
    manifest["launch_binding"] = oldest_launch
    manifest["evolution_binding_rebinds"] = [{
        "attempt": 1,
        "status": "rebound",
        "reason": "tampered schema downgrade",
        "old_launch_binding": previous_launch,
        "old_invocation_binding": invocation,
        "old_binding_sha256": previous_sha256,
        "candidate_start_offset": manifest["candidate_start_offset"],
        "evolution_attempts_before": 0,
        "abandoned_ranges_before": 0,
        "abandoned_checkpoints_before": 0,
        "planned_at": "legacy",
        "new_launch_binding": oldest_launch,
        "new_invocation_binding": invocation,
        "new_binding_sha256": oldest_sha256,
        "evolution_attempts_after": 0,
        "abandoned_ranges_after": 0,
        "abandoned_checkpoints_after": 0,
        "rebound_at": "legacy",
    }]
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="downgrades its schema",
    ):
        flow._load_transaction(
            state, 1, round_dir, allow_prepared_rebind=True
        )


@pytest.mark.parametrize(
    "missing_field",
    ("evaluation_evaluator", "evaluation_results"),
)
def test_prepared_transaction_rejects_unallowlisted_legacy_shape(
    tmp_path, missing_field
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"prepared-bad-legacy-{missing_field}",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["launch_binding"].pop(missing_field)
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow._capture_round_candidates(state, 1, round_dir)
    assert json.loads(manifest_path.read_text())[
        "evolution_binding_rebinds"
    ] == []


@pytest.mark.parametrize(
    ("status", "bind_source"),
    (
        ("prepared", True),
        ("source-ready", False),
        ("batch-ready", False),
        ("committed", False),
    ),
)
def test_legacy_binding_is_not_migrated_after_source_binding(
    tmp_path, status, bind_source
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"bound-legacy-{status}",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    for field in (
        "evaluation_proof_runtime",
        "evaluation_search_contract",
        "evaluation_structural_features",
        "evolution_dependency_contract",
    ):
        manifest["launch_binding"].pop(field)
    manifest["status"] = status
    if bind_source:
        manifest["candidate_end_offset"] = manifest[
            "candidate_start_offset"
        ]
    atomic_write_json(manifest_path, manifest)
    before = manifest_path.read_bytes()

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="binding fields are incomplete",
    ):
        flow._load_transaction(
            state, 1, round_dir, allow_prepared_rebind=True
        )
    assert manifest_path.read_bytes() == before


def test_interrupted_prepared_binding_rebind_resumes_from_its_wal(
    tmp_path, monkeypatch
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="prepared-rebind-crash",
        iterations_per_round=3,
        milp_top=0,
    )
    old_row = candidate(41)
    new_row = candidate(42)
    initial = HumanizeFlow(config, reviewer=Reviewer())
    state = initial.store.initialize(config.serializable())
    round_dir = initial.store.round_dir(1)
    initial._prepare_transaction(state, 1, round_dir)
    initial.candidate_log.parent.mkdir(parents=True, exist_ok=True)
    initial.candidate_log.write_bytes(jsonl(old_row))
    write_checkpoint(repo, config.run_id, 3)
    flow_module._completion_marker_path(round_dir).write_text(
        '{"old": "marker"}\n'
    )
    flow_module._slice_witness_path(round_dir).write_text(
        '{"old": "witness"}\n'
    )
    (repo / "evaluation/evaluator.py").write_text(
        "# upgraded evaluator source\n"
    )

    original_quarantine = (
        initial._quarantine_untrusted_evolution_attempt
    )

    class SimulatedProcessDeath(BaseException):
        pass

    def crash_after_quarantine(
        transaction, target_round, checkpoint, *, reason
    ):
        original_quarantine(
            transaction,
            target_round,
            checkpoint,
            reason=reason,
        )
        raise SimulatedProcessDeath

    monkeypatch.setattr(
        initial,
        "_quarantine_untrusted_evolution_attempt",
        crash_after_quarantine,
    )
    with pytest.raises(SimulatedProcessDeath):
        initial._capture_round_candidates(state, 1, round_dir)

    durable = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert durable["evolution_binding_rebinds"][0]["status"] == "rebinding"
    assert len(durable["abandoned_ranges"]) == 1
    assert len(durable["abandoned_checkpoints"]) == 1
    assert initial.candidate_log.read_bytes() == b""

    runner_calls = []

    def runner(_config, _state, runner_round):
        runner_calls.append(True)
        assert initial.candidate_log.read_bytes() == b""
        initial.candidate_log.write_bytes(jsonl(new_row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(resumed, runner_round, checkpoint, None)
        return checkpoint

    resumed = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    rows = resumed._capture_round_candidates(
        resumed.store.load_state(), 1, round_dir
    )

    assert rows == [new_row]
    assert runner_calls == [True]
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["evolution_binding_rebinds"][0]["status"] == "rebound"
    assert len(manifest["evolution_binding_rebinds"]) == 1
    assert len(manifest["abandoned_ranges"]) == 1
    assert len(manifest["abandoned_checkpoints"]) == 1
    assert len(list(round_dir.glob("abandoned-candidate-tail-*.bin"))) == 1
    assert len(list(round_dir.glob("abandoned-checkpoint-attempt-*"))) == 1


def test_completed_transaction_preserves_historical_source_binding(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="completed-source-change",
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
    (repo / "evaluation/evaluator.py").write_text(
        "# source changed after commit\n"
    )

    rows = flow._capture_round_candidates(
        flow.store.load_state(), 1, round_dir
    )
    assert rows == []
    flow._validate_completed_transaction(1, round_dir)
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["status"] == "committed"
    assert manifest["evolution_binding_rebinds"] == []
    assert (
        manifest["launch_binding"]["evaluation_evaluator"]["sha256"]
        != flow_module._file_sha256(repo / "evaluation/evaluator.py")
    )

    # Finishing the historical round must not weaken the next launch: the
    # following prepared transaction freezes the new evaluator bytes.
    next_state = flow.store.load_state()
    next_state["current_round"] = 1
    next_state["pending_round"] = None
    next_state["round_phase"] = None
    next_state.pop("round_transaction_version", None)
    flow.store.write_state(next_state)
    next_round = flow.store.round_dir(2)
    next_transaction = flow._prepare_transaction(
        next_state, 2, next_round
    )
    assert (
        next_transaction["launch_binding"]["evaluation_evaluator"]["sha256"]
        == flow_module._file_sha256(repo / "evaluation/evaluator.py")
    )


@pytest.mark.parametrize("durable_status", ("source-ready", "batch-ready"))
def test_bound_transaction_rejects_source_rebinding(
    tmp_path, monkeypatch, durable_status
):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id=f"{durable_status}-source-change",
        iterations_per_round=3,
        milp_top=0,
    )
    row = candidate(51)

    def runner(_config, _state, runner_round):
        flow.candidate_log.parent.mkdir(parents=True, exist_ok=True)
        flow.candidate_log.write_bytes(jsonl(row))
        checkpoint = write_checkpoint(repo, config.run_id, 3)
        write_full_slice_proof(flow, runner_round, checkpoint, None)
        return checkpoint

    flow = HumanizeFlow(
        config, reviewer=Reviewer(), evolution_runner=runner
    )
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    original_write = flow_module.atomic_write_json

    class SimulatedProcessDeath(BaseException):
        pass

    def crash_after_bound_manifest(path, value):
        result = original_write(path, value)
        if (
            path.name == "evolution-transaction.json"
            and value.get("status") == durable_status
        ):
            raise SimulatedProcessDeath
        return result

    monkeypatch.setattr(
        flow_module, "atomic_write_json", crash_after_bound_manifest
    )
    with pytest.raises(SimulatedProcessDeath):
        flow._capture_round_candidates(state, 1, round_dir)
    monkeypatch.setattr(flow_module, "atomic_write_json", original_write)
    assert json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )["status"] == durable_status

    (repo / "evaluation/evaluator.py").write_text(
        "# source changed after source binding\n"
    )
    resumed = HumanizeFlow(config, reviewer=Reviewer())
    with pytest.raises(
        flow_module.RoundTransactionError,
        match="launch inputs changed",
    ):
        resumed._capture_round_candidates(
            resumed.store.load_state(), 1, round_dir
        )
    manifest = json.loads(
        (round_dir / "evolution-transaction.json").read_text()
    )
    assert manifest["status"] == durable_status
    assert manifest["evolution_binding_rebinds"] == []


def test_prepared_rebind_rejects_malformed_frozen_identity(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    write_launch_inputs(repo)
    config = FlowConfig(
        repo_dir=repo,
        run_id="malformed-rebind-identity",
        iterations_per_round=3,
        milp_top=0,
    )
    flow = HumanizeFlow(config, reviewer=Reviewer())
    state = flow.store.initialize(config.serializable())
    round_dir = flow.store.round_dir(1)
    flow._prepare_transaction(state, 1, round_dir)
    manifest_path = round_dir / "evolution-transaction.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["launch_binding"]["evaluation_evaluator"]["sha256"] = (
        "not-a-sha256"
    )
    atomic_write_json(manifest_path, manifest)

    with pytest.raises(
        flow_module.RoundTransactionError,
        match="malformed or redirected",
    ):
        flow._capture_round_candidates(state, 1, round_dir)
    assert json.loads(manifest_path.read_text())[
        "evolution_binding_rebinds"
    ] == []


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
