"""Regression tests for verified coset negative-mechanism memory."""

from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest

import humanize.pipeline as pipeline_module
from evaluation.construction import build_css_code_from_claim
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import solve_css_sector_sat
from evaluation.final_gate import minimum_winning_distance
from evaluation.low_weight_oracle import evaluate_css_low_weight_oracle
from evaluation.proof_runtime import proof_runtime_fingerprint
from evaluation.selection_ledger import (
    acknowledge_selection_page,
    install_pending_page,
    make_scan_evidence,
    make_selection_page,
    new_selection_ledger,
    seal_selection_ledger,
)
from evaluation.two_block_sparse_kernel_oracle import (
    evaluate_two_block_sparse_kernel_oracle,
)
from evolve import coset_negative_archive as archive
from evolve import coset_openevolve_evaluator as evaluator
from evolve import coset_policy_dsl as policy_dsl
from evolve import run_evolution as evolution_launcher
from evolve.coset_search_contract import (
    COSET_CANDIDATE_SCHEMA_VERSION_V3,
    COSET_RENDERER_V3_ID,
    COSET_REPRESENTATION_ID_V3,
    action_search_view,
    coset_candidate_digest,
)
from humanize.pipeline import (
    FiveStagePipeline,
    PipelineConfig,
    PipelineError,
)
from humanize import flow as flow_module
from humanize.flow import FlowConfig
from humanize.state import RunStore
from scripts.audit_candidate_pool import (
    _compact_low_weight_cache_binding,
    _construction_candidate,
    _seal_compact_low_weight_cache,
)
from tests.test_humanize_pipeline import ScenarioRunner, _plan, _repo


def _sha256(value) -> str:
    return hashlib.sha256(json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()).hexdigest()


@pytest.fixture(scope="module")
def stable_pipeline_runtime():
    return proof_runtime_fingerprint()


@pytest.fixture(scope="module")
def rendered_candidates():
    return policy_dsl.render_candidates(policy_dsl.default_policy())


@pytest.fixture(scope="module")
def stage1_negative_row():
    document = policy_dsl.policy_document(policy_dsl.default_policy())
    for action in document["actions"]:
        view = action_search_view(action["action_id"])
        if not action["include_published"]:
            left = [
                item for item in view.left_element_ids
                if item != view.left_identity_id
            ]
            right = [
                item for item in view.right_element_ids
                if item != view.right_identity_id
            ]
            action["supports"] = [{
                "left": [0, len(left) - 1],
                "right": [0, len(right) - 1],
            }]
    policy = policy_dsl.parse_policy(json.dumps(document))
    candidate = next(
        item for item in policy_dsl.render_candidates(policy)
        if action_search_view(item["action_id"]).subgroup_normal
    )
    row = evaluator._static_candidate(candidate)
    evaluator._run_oracle(row)
    assert row["oracle_outcome"] == "SAT"
    assert row["threshold_rejected"] is True
    return row


def _sparse_negative(candidate: dict) -> tuple[dict, dict]:
    row = evaluator._static_candidate(candidate)
    code = build_css_code_from_claim({"construction": row["construction"]})
    matrices = tuple(
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    evidence = evaluate_two_block_sparse_kernel_oracle(
        *matrices,
        max_weight=4,
        hard_timeout_s=20,
    )
    assert evidence["outcome"] == "SAT"
    return row, evidence


@pytest.fixture(scope="module")
def two_sparse_negatives(rendered_candidates):
    # Both independently replay to X/A-only weight-four witnesses, but their
    # actions and exact construction supports differ.
    first = _sparse_negative(rendered_candidates[303])
    second = _sparse_negative(rendered_candidates[353])
    for _row, evidence in (first, second):
        assert evidence["witness"]["side"] == "X"
        assert evidence["witness"]["block"] == "A"
        assert evidence["witness"]["weight"] == 4
    return first, second


def _stage2_files(
    root: Path,
    negatives: list[tuple[dict, dict]],
) -> tuple[Path, Path]:
    ranked = root / "stage2-ranked.jsonl"
    summary_path = root / "stage2-summary.json"
    rows = []
    results = []
    for index, (row, evidence) in enumerate(negatives, start=1):
        digest = f"{index:064x}"
        required = minimum_winning_distance(row["n"], row["k"])
        rows.append({
            "canonical_digest": digest,
            "construction": row["construction"],
            "n": row["n"],
            "k": row["k"],
            "required_distance": required,
        })
        results.append({
            "canonical_digest": digest,
            "status": "REJECTED",
            "retry_required": False,
            "threshold_proof_source": "two-block-sparse-kernel-oracle",
            "two_block_sparse_kernel_oracle": evidence,
        })
    ranked.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )
    summary_path.write_text(json.dumps({
        "schema_version": 1,
        "gate": "qldpc-proof-oriented-candidate-pool",
        "ranked_output": str(ranked.resolve()),
        "results": results,
    }, sort_keys=True), encoding="utf-8")
    return summary_path, ranked


def _stage2_global_files(
    root: Path,
    row: dict,
    evidence: dict,
) -> tuple[Path, Path, Path]:
    digest = "a" * 64
    required = minimum_winning_distance(row["n"], row["k"])
    ranked_row = {
        "canonical_digest": digest,
        "construction": row["construction"],
        "n": row["n"],
        "k": row["k"],
        "required_distance": required,
    }
    code = build_css_code_from_claim({"construction": row["construction"]})
    matrices = tuple(
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    producer_candidate = _construction_candidate(ranked_row, digest)
    binding = _compact_low_weight_cache_binding(
        producer_candidate,
        matrices,
        max_weight=int(evidence["max_weight"]),
    )
    cache_path = (root / "global-low-weight-cache.json").resolve()
    cache_path.write_text(json.dumps(
        _seal_compact_low_weight_cache(binding, evidence),
        sort_keys=True,
    ), encoding="utf-8")
    ladder = {
        "schema_version": 1,
        "gate": "qldpc-stage2-compact-low-weight-gate",
        "outcome": "SAT",
        "max_weight": evidence["max_weight"],
        "distance_lower_bound": evidence.get("distance_lower_bound"),
        "witness": evidence["witness"],
        "evidence_sha256": evidence["evidence_sha256"],
        "cache_path": str(cache_path),
        "cache_hit": False,
        "resumed_sectors": 0,
        "decision_complete": True,
        "retryable": False,
    }
    result = {
        "canonical_digest": digest,
        "status": "REJECTED",
        "retry_required": False,
        "distance_upper_bound": evidence["witness"]["weight"],
        "threshold_rejection_proven": True,
        "threshold_proof_source": "compact-low-weight-sat",
        "compact_low_weight_sat_ladder": ladder,
    }
    ranked = (root / "stage2-global-ranked.jsonl").resolve()
    ranked.write_text(json.dumps(ranked_row, sort_keys=True) + "\n", encoding="utf-8")
    summary_path = (root / "stage2-global-summary.json").resolve()
    summary_path.write_text(json.dumps({
        "schema_version": 1,
        "gate": "qldpc-proof-oriented-candidate-pool",
        "ranked_output": str(ranked),
        "results": [result],
    }, sort_keys=True), encoding="utf-8")
    return summary_path, ranked, cache_path


def test_stage1_ingest_is_verified_deduplicated_and_v3_compatible(
    tmp_path,
    stage1_negative_row,
):
    path = tmp_path / "negative.json"
    first = archive.ingest_stage1_rows(path, [stage1_negative_row])
    second = archive.ingest_stage1_rows(path, [stage1_negative_row])
    assert first["events_added"] == 1
    assert second["events_added"] == 0
    stored = archive.load_archive(path)
    assert len(stored["events"]) == 1
    motif = next(iter(stored["motifs"].values()))["motif"]
    witness = motif["witness"]
    assert witness["block_layout"] in {"A-only", "B-only", "cross"}
    assert set(motif["coordinates"]) >= {"block", "action", "support"}
    assert motif["coordinates"]["block"]["kind"] == "witness-block-layout"
    assert "block_size" not in motif["coordinates"]["block"]

    # Renderer v3 changes genotype identity but compiles to the same trusted
    # construction.  Its negative witness must remain replayable.
    v3 = {
        "schema_version": COSET_CANDIDATE_SCHEMA_VERSION_V3,
        "representation_id": COSET_REPRESENTATION_ID_V3,
        "renderer_descriptor_id": COSET_RENDERER_V3_ID,
        "action_id": stage1_negative_row["candidate"]["action_id"],
        "support_split": [3, 3],
        "left_support": stage1_negative_row["candidate"]["left_support"],
        "right_support": stage1_negative_row["candidate"]["right_support"],
    }
    v3_row = copy.deepcopy(stage1_negative_row)
    v3_row["candidate"] = v3
    v3_row["candidate_sha256"] = coset_candidate_digest(v3)
    v3_result = archive.ingest_stage1_rows(path, [v3_row])
    assert v3_result["events_added"] == 0  # same proof/mechanism, not duplicated


def test_negative_feedback_epoch_is_immutable_and_visible_next_round_only(
    tmp_path,
    stage1_negative_row,
):
    live = (tmp_path / "live.json").resolve()
    round_one = tmp_path / "round-001"
    round_one.mkdir()
    snapshot_one = (round_one / "negative-feedback-snapshot.json").resolve()
    manifest_one = (
        round_one / "negative-feedback-snapshot-manifest.json"
    ).resolve()
    epoch_one = archive.materialize_feedback_snapshot(
        live,
        snapshot_one,
        manifest_one,
        run_id="feedback-epoch-test",
        round_number=1,
        feedback_epoch=1,
    )
    snapshot_one_bytes = snapshot_one.read_bytes()
    row_before = copy.deepcopy(stage1_negative_row)
    archive.annotate_rows(snapshot_one, [row_before])
    assert row_before["negative_archive_penalty"] == 0

    archive.ingest_stage1_rows(live, [stage1_negative_row])
    # Re-entering the same round adopts its sealed snapshot instead of taking
    # a newer view of the live append target.
    replayed = archive.materialize_feedback_snapshot(
        live,
        snapshot_one,
        manifest_one,
        run_id="feedback-epoch-test",
        round_number=1,
        feedback_epoch=1,
    )
    assert replayed["snapshot_sha256"] == epoch_one["snapshot_sha256"]
    assert snapshot_one.read_bytes() == snapshot_one_bytes
    assert snapshot_one.stat().st_mode & 0o222 == 0

    round_two = tmp_path / "round-002"
    round_two.mkdir()
    snapshot_two = (round_two / "negative-feedback-snapshot.json").resolve()
    manifest_two = (
        round_two / "negative-feedback-snapshot-manifest.json"
    ).resolve()
    epoch_two = archive.materialize_feedback_snapshot(
        live,
        snapshot_two,
        manifest_two,
        run_id="feedback-epoch-test",
        round_number=2,
        feedback_epoch=2,
        parent_snapshot_sha256=epoch_one["snapshot_sha256"],
    )
    assert epoch_two["archive_sha256"] != epoch_one["archive_sha256"]
    row_after = copy.deepcopy(stage1_negative_row)
    archive.annotate_rows(snapshot_two, [row_after])
    assert row_after["negative_archive_penalty"] > 0


def test_orphan_snapshot_is_adopted_and_partial_publish_is_not_visible(
    tmp_path,
    monkeypatch,
    stage1_negative_row,
):
    live = (tmp_path / "live.json").resolve()
    snapshot = (tmp_path / "round-001-snapshot.json").resolve()
    manifest = (tmp_path / "round-001-manifest.json").resolve()
    original = archive.materialize_feedback_snapshot(
        live,
        snapshot,
        manifest,
        run_id="orphan-test",
        round_number=1,
        feedback_epoch=1,
    )
    manifest.unlink()
    archive.ingest_stage1_rows(live, [stage1_negative_row])
    recovered = archive.materialize_feedback_snapshot(
        live,
        snapshot,
        manifest,
        run_id="orphan-test",
        round_number=1,
        feedback_epoch=1,
    )
    assert recovered["archive_sha256"] == original["archive_sha256"]
    assert recovered["archive_sha256"] != archive.load_archive(live)[
        "archive_sha256"
    ]
    with pytest.raises(archive.NegativeArchiveError, match="round changed"):
        archive.load_feedback_snapshot_manifest(
            manifest,
            expected_round_number=2,
        )

    interrupted = (tmp_path / "interrupted.json").resolve()
    real_write = archive.os.write
    attempted = False

    def interrupt_after_partial_write(descriptor, payload):
        nonlocal attempted
        if not attempted:
            attempted = True
            real_write(descriptor, payload[: max(1, len(payload) // 2)])
            raise OSError("simulated crash")
        return real_write(descriptor, payload)

    monkeypatch.setattr(archive.os, "write", interrupt_after_partial_write)
    with pytest.raises(OSError, match="simulated crash"):
        archive._write_immutable_json(interrupted, archive._empty_archive())
    assert not interrupted.exists()
    assert list(tmp_path.glob(f".{interrupted.name}.*.tmp")) == []


def test_managed_snapshot_binding_crosses_flow_launcher_and_evaluator(
    tmp_path,
    monkeypatch,
):
    project = Path(flow_module.__file__).resolve().parents[1]
    live = (tmp_path / "shared-live.json").resolve()
    monkeypatch.setenv(archive.NEGATIVE_ARCHIVE_PATH_ENV, str(live))
    round_dir = tmp_path / "round-001"
    round_dir.mkdir()
    context = round_dir / "search-context.md"
    context.write_text("snapshot binding test\n", encoding="utf-8")
    config = FlowConfig(
        repo_dir=project,
        run_id="snapshot-binding-test",
        evolution_config=project / "evolve/coset_config_v2.yaml",
        evolution_seed=project / "evolve/coset_seed_solution_v2.py",
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    launch = flow_module._evolution_launch_binding(
        config, context_path=context
    )
    invocation = flow_module._fresh_invocation_binding(
        config,
        codex_identity=None,
        codex_version=None,
        codex_cwd=None,
        launch_binding=launch,
    )
    assert flow_module._validate_invocation_binding(
        config, invocation, launch
    ) == invocation
    replayed = evolution_launcher._validated_negative_feedback_binding(
        live_archive_path=invocation[
            "qcode_negative_feedback_live_archive_path"
        ],
        snapshot_path=invocation["qcode_negative_feedback_snapshot_path"],
        snapshot_sha256=invocation[
            "qcode_negative_feedback_snapshot_sha256"
        ],
        archive_sha256=invocation[
            "qcode_negative_feedback_archive_sha256"
        ],
        manifest_path=invocation["qcode_negative_feedback_manifest_path"],
        manifest_sha256=invocation[
            "qcode_negative_feedback_manifest_sha256"
        ],
        feedback_epoch=invocation["qcode_negative_feedback_epoch"],
        required=True,
        expected_run_id=config.run_id,
    )
    assert replayed is not None and replayed[0] == {
        name: invocation[name]
        for name in flow_module.COSET_NEGATIVE_FEEDBACK_INVOCATION_FIELDS
    }
    # Mutable live bytes are intentionally absent from launch dependencies.
    assert all(
        descriptor.get("path") != str(live)
        for descriptor in launch.values()
    )

    observed: dict[str, Path] = {}
    monkeypatch.setenv(
        archive.NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV,
        invocation["qcode_negative_feedback_snapshot_path"],
    )
    monkeypatch.setattr(evaluator, "_configured_stage2_negative_paths", lambda: ())
    monkeypatch.setattr(evaluator, "_configured_stage3_negative_paths", lambda: ())
    def fake_archive(path, _rows):
        observed["write"] = path
        return {"events_added": 1}

    def fake_annotate(path, _rows):
        observed["read"] = path
        return {
            "event_count": 0,
            "penalized_candidates": 0,
            "maximum_penalty": 0.0,
        }

    monkeypatch.setattr(evaluator, "_archive_stage1_negative_rows", fake_archive)
    monkeypatch.setattr(
        evaluator, "_annotate_negative_archive_rows", fake_annotate
    )
    summary = evaluator._archive_and_annotate_negative_rows([{
        "oracle_outcome": "SAT",
        "threshold_rejected": True,
        "low_weight_oracle": {},
    }])
    assert observed["write"] == live
    assert observed["read"] == Path(
        invocation["qcode_negative_feedback_snapshot_path"]
    )
    assert summary["events_added"] == 1


def test_pipeline_feedback_epoch_is_deferred_immutable_and_keeps_one_live_archive(
    tmp_path,
    monkeypatch,
    stage1_negative_row,
    two_sparse_negatives,
):
    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    candidate_output = repo / "candidate-output.jsonl"
    candidate_output.write_text("{}\n", encoding="utf-8")
    run_id = "pipeline-feedback-epoch"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidate_output,
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
    )
    config.root.mkdir(parents=True)
    flow_run_ids: list[str] = []
    flow_lease_paths: list[Path] = []

    class SearchFlow:
        def __init__(self, selected: FlowConfig):
            self.config = selected
            self.store = RunStore.create(
                selected.repo_dir / "results",
                selected.run_id,
            )
            self.pipeline_candidate_inputs = (candidate_output,)

        def run(self, *, inherited_run_lease):
            flow_module._validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            flow_run_ids.append(self.config.run_id)
            flow_lease_paths.append(inherited_run_lease.path)
            # A verified negative appended by Stage 1 is allowed to change the
            # mutable live side. The startup snapshot remains an input and must
            # remain unchanged throughout the machine transaction.
            if len(flow_run_ids) == 2:
                archive.ingest_stage1_rows(
                    Path(os.environ[archive.NEGATIVE_ARCHIVE_PATH_ENV]),
                    [stage1_negative_row],
                )
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidate_output)],
            }

    pipeline = FiveStagePipeline(
        config,
        flow_factory=SearchFlow,
        reviewer=None,
    )
    monkeypatch.setattr(pipeline, "_stage1_source_provenance", lambda: {})
    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()

        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        stage1 = pipeline.state["stages"]["stage1_search"]
        startup_one = stage1["negative_feedback_startup"]
        consumed_one = stage1["negative_feedback_consumed"]
        base_live = Path(consumed_one["live_archive_path"])
        assert startup_one["feedback_epoch"] == 1
        assert flow_run_ids == [run_id]
        assert flow_lease_paths == [
            pipeline._humanize_run_lease.path,
        ]
        assert "negative_feedback_pending" not in pipeline.state

        # An unchanged immutable startup view is a real cache hit.
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert flow_run_ids == [run_id]
        assert pipeline.state["stages"]["stage1_search"]["attempt"] == 1

        stage2_root = pipeline.paths.artifacts
        _stage2_files(stage2_root, [two_sparse_negatives[0]])
        first_stage2 = pipeline._archive_stage2_coset_negatives(
            [candidate_output]
        )
        assert first_stage2["events_added"] == 1
        pending = pipeline._validate_pending_feedback_state(
            pipeline.state["negative_feedback_pending"]
        )
        assert pending["record"]["pending_epoch"] == 2
        assert pending["record"]["source_stage"] == "stage2-sector-audit"
        # This Stage 2 archive operation only records a pending epoch; the
        # outer pipeline scheduler decides when the next proof pass begins.
        assert flow_run_ids == [run_id]

    with pipeline._exclusive_lock():
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert len(flow_run_ids) == 2
        assert flow_run_ids[1] != flow_run_ids[0]
        stage1 = pipeline.state["stages"]["stage1_search"]
        assert stage1["attempt"] == 2
        assert stage1["negative_feedback_startup"]["feedback_epoch"] == 2
        assert stage1["negative_feedback_consumed"][
            "live_archive_path"
        ] == str(base_live)
        assert pipeline.state["negative_feedback_pending"]["record"][
            "source_stage"
        ] == "stage1-search"
        derived_store = RunStore.create(
            repo / "results",
            flow_run_ids[1],
        )
        assert flow_lease_paths[1] == derived_store.lock_path.absolute()
        # The derived lease remains held through the downstream proof stages.
        with pytest.raises(flow_module.HumanizeRunAlreadyActiveError):
            with flow_module._acquire_humanize_run_lease(derived_store):
                pass

        # A Stage 2 witness produced after the derived epoch must still land in
        # the original base live archive, never a run-id-derived side archive.
        _stage2_files(stage2_root, [two_sparse_negatives[1]])
        second_stage2 = pipeline._archive_stage2_coset_negatives(
            [candidate_output]
        )
        assert second_stage2["events_added"] == 1
        assert len(archive.load_archive(base_live)["events"]) == 3
        assert (
            pipeline._coset_negative_archive_path([candidate_output])
            == base_live
        )

    with flow_module._acquire_humanize_run_lease(derived_store):
        pass


def test_pipeline_feedback_waits_for_bound_stage2_snapshot_exhaustion(
    tmp_path,
    monkeypatch,
    two_sparse_negatives,
):
    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    candidate_output = repo / "candidate-output.jsonl"
    candidate_output.write_text("{}\n", encoding="utf-8")
    run_id = "pipeline-feedback-stage2-fence"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidate_output,
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
    )
    config.root.mkdir(parents=True)
    flow_run_ids: list[str] = []

    class SearchFlow:
        def __init__(self, selected: FlowConfig):
            self.config = selected
            self.store = RunStore.create(
                selected.repo_dir / "results",
                selected.run_id,
            )
            self.pipeline_candidate_inputs = (candidate_output,)

        def run(self, *, inherited_run_lease):
            flow_module._validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            flow_run_ids.append(self.config.run_id)
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidate_output)],
            }

    pipeline = FiveStagePipeline(
        config,
        flow_factory=SearchFlow,
        reviewer=None,
    )
    monkeypatch.setattr(pipeline, "_stage1_source_provenance", lambda: {})
    binding = "a" * 64
    snapshot_identity = "b" * 64

    def write_ledger(value):
        pipeline.paths.stage2_selection_ledger.parent.mkdir(
            parents=True,
            exist_ok=True,
        )
        pipeline.paths.stage2_selection_ledger.write_text(
            json.dumps(value, indent=2) + "\n",
            encoding="utf-8",
        )

    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert flow_run_ids == [run_id]

        _stage2_files(
            pipeline.paths.artifacts,
            [two_sparse_negatives[0]],
        )
        archived = pipeline._archive_stage2_coset_negatives(
            [candidate_output]
        )
        assert archived["events_added"] == 1
        assert pipeline.state["negative_feedback_pending"]["record"][
            "pending_epoch"
        ] == 2
        consumed_binding = pipeline.state["stages"]["stage1_search"][
            "negative_feedback_consumed"
        ]["binding_sha256"]
        pipeline.state["stages"]["stage2_sector_audit"]["stage_config"] = {
            "stage1_feedback_binding_sha256": consumed_binding,
        }
        pipeline._write_state()

        ledger = new_selection_ledger(
            binding_sha256=binding,
            snapshot_identity_sha256_value=snapshot_identity,
            snapshot_rows=2,
            eligible_rows=2,
        )
        first_scan = make_scan_evidence(
            snapshot_identity_sha256_value=snapshot_identity,
            start_index=0,
            next_index=1,
            snapshot_rows=2,
            eligible_rows=2,
            selection_exhausted=False,
        )
        first_page = make_selection_page(
            binding_sha256=binding,
            snapshot_identity_sha256_value=snapshot_identity,
            page_sequence=0,
            previous_ack_sha256=ledger["last_ack_sha256"],
            start_index=0,
            next_index=1,
            selected_digests=["page-one"],
            scan_evidence=first_scan,
        )
        ledger = install_pending_page(ledger, first_page)
        write_ledger(ledger)
        first_summary = {
            "selection_exhausted": False,
            "selection_page": first_page,
        }
        pipeline.paths.stage2_summary.write_text(
            json.dumps(first_summary) + "\n",
            encoding="utf-8",
        )
        pipeline.state["stages"]["stage2_sector_audit"][
            "machine_status"
        ] = "COMPLETED"
        pipeline._write_state()

        # A proof-retry or crash may revisit Stage 1 while the current page is
        # still pending. It must reuse the same immutable feedback epoch.
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert flow_run_ids == [run_id]
        assert pipeline.state["stages"]["stage1_search"]["attempt"] == 1

        ledger = acknowledge_selection_page(
            ledger,
            first_page,
            disposition="COMPLETED",
        )
        ledger["last_acknowledged_page_sha256"] = first_page[
            "page_sha256"
        ]
        ledger["last_acknowledged_at"] = "2026-08-07T00:00:00+00:00"
        ledger = seal_selection_ledger(ledger)
        write_ledger(ledger)
        pipeline.state["stage2_pagination"] = {
            "binding_sha256": binding,
            "cursor": 0,
            "completed_pages": 0,
            "selection_exhausted": False,
            "paginated_persistent_incompleteness": [{
                "code": "STAGE2_STRUCTURAL_SCREEN_UNRESOLVED",
            }],
        }
        pipeline._write_state()

        # The ledger acknowledgement is authoritative if the process dies
        # before the monitoring state advances; recovery must retain the same
        # epoch and repair cursor 0 -> 1 rather than fail permanently.
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert flow_run_ids == [run_id]
        assert pipeline.state["stages"]["stage1_search"]["attempt"] == 1
        assert pipeline.state["stage2_pagination"]["cursor"] == 1
        assert pipeline.state["stage2_pagination"]["completed_pages"] == 1
        assert pipeline.state["stage2_pagination"][
            "paginated_persistent_incompleteness"
        ] == [{"code": "STAGE2_STRUCTURAL_SCREEN_UNRESOLVED"}]

        terminal_scan = make_scan_evidence(
            snapshot_identity_sha256_value=snapshot_identity,
            start_index=1,
            next_index=2,
            snapshot_rows=2,
            eligible_rows=2,
            selection_exhausted=True,
        )
        terminal_page = make_selection_page(
            binding_sha256=binding,
            snapshot_identity_sha256_value=snapshot_identity,
            page_sequence=ledger["completed_pages"],
            previous_ack_sha256=ledger["last_ack_sha256"],
            start_index=1,
            next_index=2,
            selected_digests=["page-two"],
            scan_evidence=terminal_scan,
        )
        ledger = install_pending_page(ledger, terminal_page)
        write_ledger(ledger)
        terminal_summary = {
            "selection_exhausted": True,
            "selection_page": terminal_page,
        }
        pipeline.paths.stage2_summary.write_text(
            json.dumps(terminal_summary) + "\n",
            encoding="utf-8",
        )
        release_marker = pipeline._stage2_feedback_release_marker(
            terminal_summary
        )

        # _run_locked archives the terminal result before asking for the next
        # Stage-1 inputs. Model that restart boundary explicitly.
        pipeline.state["status"] = "RUNNING"
        pipeline.state.setdefault("result_history", []).append({
            "status": "COMPLETED_NO_WIN",
            "result": {"stage2_feedback_release": release_marker},
        })
        pipeline.state["stages"]["stage2_sector_audit"]["stage_config"][
            "stage1_feedback_binding_sha256"
        ] = "c" * 64
        pipeline._write_state()

        # A terminal ledger from an older feedback epoch cannot authorize
        # skipping the current Stage 1 after a crash before its first page.
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert flow_run_ids == [run_id]

        pipeline.state["stages"]["stage2_sector_audit"]["stage_config"][
            "stage1_feedback_binding_sha256"
        ] = consumed_binding
        stale_marker = dict(release_marker)
        stale_marker["stage1_feedback_binding_sha256"] = "c" * 64
        stale_unsigned = dict(stale_marker)
        stale_unsigned.pop("marker_sha256")
        stale_marker["marker_sha256"] = _sha256(stale_unsigned)
        pipeline.state["result_history"][-1]["result"] = {
            "stage2_feedback_release": stale_marker,
        }
        pipeline._write_state()

        # A sealed NO_WIN marker from an older feedback epoch also cannot
        # release the current terminal page merely because it is last in
        # result_history.
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert flow_run_ids == [run_id]

        pipeline.state["result_history"][-1]["result"] = {
            "stage2_feedback_release": release_marker,
        }
        pipeline._write_state()
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        assert len(flow_run_ids) == 2
        assert flow_run_ids[1] != flow_run_ids[0]
        stage1 = pipeline.state["stages"]["stage1_search"]
        assert stage1["attempt"] == 2
        assert stage1["negative_feedback_startup"]["feedback_epoch"] == 2


@pytest.mark.parametrize("proof_retry_max_attempts", [1, 2])
def test_pipeline_run_drains_feedback_bound_snapshot_before_next_epoch(
    tmp_path,
    monkeypatch,
    stage1_negative_row,
    stable_pipeline_runtime,
    proof_retry_max_attempts,
):
    runtime = json.loads(json.dumps(stable_pipeline_runtime))
    provenance = {
        "runtime": runtime,
        "interpreter": runtime["interpreter"],
    }
    monkeypatch.setattr(
        pipeline_module,
        "proof_runtime_fingerprint",
        lambda: runtime,
    )
    monkeypatch.setattr(
        pipeline_module,
        "probe_python_runtime",
        lambda *_args, **_kwargs: provenance,
    )
    repo, _unused_candidates = _repo(tmp_path)
    candidate_output = repo / "coset-candidates.jsonl"
    candidate_output.write_text("{}\n", encoding="utf-8")
    run_id = f"feedback-pagination-run-{proof_retry_max_attempts}"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidate_output,
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
        proof_retry_max_attempts=proof_retry_max_attempts,
        proof_retry_backoff_seconds=0,
    )
    flow_run_ids: list[str] = []

    class SearchFlow:
        def __init__(self, selected: FlowConfig):
            self.config = selected
            self.store = RunStore.create(
                selected.repo_dir / "results",
                selected.run_id,
            )
            self.pipeline_candidate_inputs = (candidate_output,)

        def run(self, *, inherited_run_lease):
            flow_module._validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            flow_run_ids.append(self.config.run_id)
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidate_output)],
            }

    runner = ScenarioRunner(stage2=[
        _plan(
            [{"canonical_digest": "page-one", "status": "REJECTED"}],
            selection_exhausted=False,
            selection_page=(0, 1),
            snapshot_rows=2,
        ),
        _plan(
            [{"canonical_digest": "page-two", "status": "REJECTED"}],
            selection_exhausted=True,
            selection_page=(1, 2),
            snapshot_rows=2,
        ),
    ])
    pipeline = FiveStagePipeline(
        config,
        command_runner=runner,
        flow_factory=SearchFlow,
        reviewer=None,
        sleeper=lambda _seconds: None,
    )
    monkeypatch.setattr(pipeline, "_stage1_source_provenance", lambda: {})
    archive_events_added: list[int] = []

    def archive_stage2(candidates):
        live = pipeline._coset_negative_archive_path(candidates)
        summary = archive.ingest_stage1_rows(
            live,
            [stage1_negative_row],
        )
        events_added = int(summary["events_added"])
        archive_events_added.append(events_added)
        pipeline.state["negative_mechanism_archive"] = summary
        pipeline._write_state()
        pipeline._record_coset_feedback_pending(
            candidates,
            source_stage="stage2-sector-audit",
            events_added=events_added,
        )
        return summary

    monkeypatch.setattr(
        pipeline,
        "_archive_stage2_coset_negatives",
        archive_stage2,
    )
    state = pipeline.run()

    assert state["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": 2}
    assert flow_run_ids == [run_id]
    assert archive_events_added == [1, 0]
    assert state["stages"]["stage1_search"]["attempt"] == 1
    ledger = json.loads(
        pipeline.paths.stage2_selection_ledger.read_text()
    )
    assert ledger["cursor"] == 1
    assert ledger["completed_pages"] == 1
    assert ledger["pending"]["start_index"] == 1
    assert ledger["pending"]["next_index"] == 2
    assert ledger["pending"]["scan_evidence"][
        "selection_exhausted"
    ] is True
    assert state["result"]["stage2_feedback_release"][
        "page_sha256"
    ] == ledger["pending"]["page_sha256"]

    # A new process invocation may now consume the accumulated feedback.  It
    # must not have been consumed between the two proof pages above.
    resumed = FiveStagePipeline(
        config,
        command_runner=runner,
        flow_factory=SearchFlow,
        reviewer=None,
        sleeper=lambda _seconds: None,
    )
    monkeypatch.setattr(resumed, "_stage1_source_provenance", lambda: {})
    with resumed._exclusive_lock():
        resumed._load_or_initialize_state()
        assert resumed._stage1_inputs() == [candidate_output.resolve()]
    assert len(flow_run_ids) == 2
    assert flow_run_ids[1] != flow_run_ids[0]
    assert resumed.state["stages"]["stage1_search"][
        "negative_feedback_startup"
    ]["feedback_epoch"] == 2


def test_pipeline_feedback_cache_hit_reacquires_derived_run_lease(
    tmp_path,
    monkeypatch,
):
    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    candidate_output = repo / "candidate-output.jsonl"
    candidate_output.write_text("{}\n", encoding="utf-8")
    run_id = "pipeline-feedback-cache-lease"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidate_output,
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
    )
    config.root.mkdir(parents=True)
    base_store = RunStore.create(repo / "results", run_id)
    base_state = base_store.initialize(flow_config.serializable())
    base_state["status"] = "search-complete"
    base_store.write_state(base_state)
    flow_calls: list[str] = []

    class SearchFlow:
        def __init__(self, selected: FlowConfig):
            self.config = selected
            self.store = RunStore.create(
                selected.repo_dir / "results",
                selected.run_id,
            )
            self.pipeline_candidate_inputs = (candidate_output,)

        def run(self, *, inherited_run_lease):
            flow_module._validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            flow_calls.append(self.config.run_id)
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidate_output)],
            }

    first = FiveStagePipeline(
        config,
        flow_factory=SearchFlow,
        reviewer=None,
    )
    monkeypatch.setattr(first, "_stage1_source_provenance", lambda: {})
    with first._exclusive_lock():
        first._load_or_initialize_state()
        assert first._stage1_inputs() == [candidate_output.resolve()]
        startup = first.state["stages"]["stage1_search"][
            "negative_feedback_startup"
        ]
        derived_id = startup["flow_run_id"]
        assert derived_id != run_id
        assert flow_calls == [derived_id]

    resumed = FiveStagePipeline(
        config,
        flow_factory=SearchFlow,
        reviewer=None,
    )
    monkeypatch.setattr(resumed, "_stage1_source_provenance", lambda: {})
    with resumed._exclusive_lock():
        resumed._load_or_initialize_state()
        assert resumed._stage1_inputs() == [candidate_output.resolve()]
        # Machine cache hit: SearchFlow.run() is not called a second time.
        assert flow_calls == [derived_id]
        derived_store = RunStore.create(repo / "results", derived_id)
        with pytest.raises(flow_module.HumanizeRunAlreadyActiveError):
            with flow_module._acquire_humanize_run_lease(derived_store):
                pass

    with flow_module._acquire_humanize_run_lease(derived_store):
        pass


def test_pipeline_feedback_output_discovery_keeps_sealed_archive_binding(
    tmp_path,
    monkeypatch,
):
    """Replay derived outputs before restoring the process archive environment."""

    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    candidate_output = repo / "candidate-output.jsonl"
    candidate_output.write_text("{}\n", encoding="utf-8")
    run_id = "pipeline-feedback-output-discovery"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidate_output,
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
    )
    config.root.mkdir(parents=True)
    # A terminal base Humanize identity forces the pipeline to create a
    # feedback-derived run whose candidate-log default archive differs from
    # the sealed base live archive.
    base_store = RunStore.create(repo / "results", run_id)
    base_state = base_store.initialize(flow_config.serializable())
    base_state["status"] = "search-complete"
    base_store.write_state(base_state)
    observed: dict[str, str | int | None] = {"replays": 0}

    class SearchFlow:
        def __init__(self, selected: FlowConfig):
            self.config = selected
            self.store = RunStore.create(
                selected.repo_dir / "results",
                selected.run_id,
            )

        @property
        def pipeline_candidate_inputs(self):
            observed["replays"] = int(observed["replays"]) + 1
            round_dir = (
                repo
                / "results"
                / "humanize"
                / self.config.run_id
                / "rounds"
                / "round-001"
            )
            manifest, _snapshot, _manifest = (
                flow_module._negative_feedback_epoch_binding(
                    self.config,
                    round_dir,
                )
            )
            observed["environment"] = os.environ.get(
                archive.NEGATIVE_ARCHIVE_PATH_ENV
            )
            observed["manifest"] = manifest["live_archive_path"]
            return (candidate_output,)

        def run(self, *, inherited_run_lease):
            flow_module._validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            # Force output discovery to use the property above. This matches
            # HumanizeFlow, whose property replays committed round bindings.
            return {"status": "search-complete"}

    pipeline = FiveStagePipeline(
        config,
        flow_factory=SearchFlow,
        reviewer=None,
    )
    monkeypatch.setattr(pipeline, "_stage1_source_provenance", lambda: {})
    monkeypatch.delenv(archive.NEGATIVE_ARCHIVE_PATH_ENV, raising=False)
    monkeypatch.delenv(
        archive.NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV,
        raising=False,
    )

    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        startup = pipeline.state["stages"]["stage1_search"][
            "negative_feedback_startup"
        ]
        assert startup["flow_run_id"] != run_id
        assert observed == {
            "replays": 1,
            "environment": startup["live_archive_path"],
            "manifest": startup["live_archive_path"],
        }

    assert archive.NEGATIVE_ARCHIVE_PATH_ENV not in os.environ
    assert archive.NEGATIVE_ARCHIVE_SNAPSHOT_PATH_ENV not in os.environ


def test_pipeline_prepared_feedback_survives_live_advance_and_recovers_terminal_orphan(
    tmp_path,
    monkeypatch,
    stage1_negative_row,
    two_sparse_negatives,
):
    """A post-run archive hash must not replace an unconsumed epoch input."""

    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    candidate_output = repo / "candidate-output.jsonl"
    candidate_output.write_text("{}\n", encoding="utf-8")
    run_id = "pipeline-feedback-prepared-recovery"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidate_output,
        evolution_evaluator="coset-two-block",
        search_representation_id="css-coset-two-block-actions-v2",
        milp_top=0,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
    )
    config.root.mkdir(parents=True)

    class SearchFlow:
        def __init__(self, selected: FlowConfig):
            self.config = selected
            self.store = RunStore.create(
                selected.repo_dir / "results",
                selected.run_id,
            )
            self.pipeline_candidate_inputs = (candidate_output,)

        def run(self, *, inherited_run_lease):
            flow_module._validate_inherited_humanize_run_lease(
                self.store,
                inherited_run_lease,
            )
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidate_output)],
            }

    pipeline = FiveStagePipeline(
        config,
        flow_factory=SearchFlow,
        reviewer=None,
    )
    monkeypatch.setattr(pipeline, "_stage1_source_provenance", lambda: {})
    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()
        assert pipeline._stage1_inputs() == [candidate_output.resolve()]
        consumed = pipeline.state["stages"]["stage1_search"][
            "negative_feedback_consumed"
        ]
        live = Path(consumed["live_archive_path"])

        # H2 is the exact input frozen for derived feedback epoch 2.
        archive.ingest_stage1_rows(live, [stage1_negative_row])
        derived_config, startup_h2 = pipeline._prepare_stage1_feedback_epoch(
            flow_config
        )
        assert startup_h2["feedback_epoch"] == 2
        assert startup_h2["flow_run_id"] == derived_config.run_id
        assert "negative_feedback_prepared" in pipeline.state

        # The running epoch appends a different verified mechanism, advancing
        # mutable live state to H3. Recovery must remain pinned to H2.
        stage2_root = tmp_path / "prepared-stage2"
        stage2_root.mkdir()
        summary, _ranked = _stage2_files(
            stage2_root,
            [two_sparse_negatives[0]],
        )
        archive.ingest_stage2_paths(live, [summary])
        h3 = archive.load_archive(live)["archive_sha256"]
        assert h3 != startup_h2["archive_sha256"]
        resumed_config, resumed_startup = (
            pipeline._prepare_stage1_feedback_epoch(flow_config)
        )
        assert resumed_config.run_id == derived_config.run_id
        assert resumed_startup == startup_h2

        # Simulate an older controller that lost the prepared state after
        # Humanize reached a terminal checkpoint but before pipeline adoption.
        terminal_store = RunStore.create(
            repo / "results",
            derived_config.run_id,
        )
        terminal = terminal_store.initialize(derived_config.serializable())
        terminal["status"] = "search-complete"
        terminal["pending_round"] = None
        terminal_store.write_state(terminal)
        pipeline.state.pop("negative_feedback_prepared")
        pipeline._write_state()

        recovered_config, recovered_startup = (
            pipeline._prepare_stage1_feedback_epoch(flow_config)
        )
        assert recovered_config.run_id == derived_config.run_id
        assert recovered_startup == startup_h2
        assert pipeline.state["negative_feedback_prepared"]["startup"] == (
            startup_h2
        )
        wrong_h3_run = pipeline._feedback_epoch_run_id(
            run_id,
            feedback_epoch=2,
            archive_sha256=h3,
            initial=False,
        )
        assert wrong_h3_run != derived_config.run_id
        assert not (repo / "results" / "humanize" / wrong_h3_run).exists()

        # Preparing the adoption delta may publish an immutable epoch-3 WAL
        # artifact, but it must not mutate or persist any pipeline pointer.
        # The caller commits this delta together with machine_status and output
        # hashes in one completed-state write.
        before_adoption = copy.deepcopy(pipeline.state)
        transition = pipeline._record_stage1_feedback_consumption(
            startup_h2,
            terminal,
        )
        assert pipeline.state == before_adoption
        assert transition["consumed"]["feedback_epoch"] == 2
        assert transition["next_pending"]["record"]["pending_epoch"] == 3
        assert transition["next_pending"]["record"]["archive_sha256"] == h3


def test_pipeline_feedback_snapshot_and_pending_state_tampering_fail_closed(
    tmp_path,
    monkeypatch,
):
    repo = tmp_path / "repo"
    (repo / "humanize").mkdir(parents=True)
    candidate_output = repo / "candidate-output.jsonl"
    candidate_output.write_text("{}\n", encoding="utf-8")
    run_id = "pipeline-feedback-tamper"
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=FlowConfig(
            repo_dir=repo,
            run_id=run_id,
            candidate_file=candidate_output,
            evolution_evaluator="coset-two-block",
            search_representation_id="css-coset-two-block-actions-v2",
            milp_top=0,
        ),
        stage_review=False,
    )
    config.root.mkdir(parents=True)

    class TamperingFlow:
        pipeline_candidate_inputs = (candidate_output,)

        def __init__(self, selected: FlowConfig):
            self.config = selected

        def run(self):
            snapshot = (
                repo
                / "results"
                / "humanize"
                / self.config.run_id
                / "rounds"
                / "round-001"
                / "negative-feedback-snapshot.json"
            )
            snapshot.chmod(0o600)
            snapshot.write_text("{}\n", encoding="utf-8")
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidate_output)],
            }

    pipeline = FiveStagePipeline(
        config,
        flow_factory=TamperingFlow,
        reviewer=None,
    )
    monkeypatch.setattr(pipeline, "_stage1_source_provenance", lambda: {})
    monkeypatch.setattr(
        pipeline,
        "_run_stage1_flow",
        lambda flow, **_kwargs: flow.run(),
    )
    pipeline._load_or_initialize_state()
    with pytest.raises(PipelineError, match="inputs changed") as captured:
        pipeline._stage1_inputs()
    assert captured.value.classification == "INPUT_CHANGED_DURING_STAGE"

    # The pending record is independently self-hashed and its exact artifact
    # bytes are replayed; changing only state cannot inject a larger epoch.
    clean = copy.deepcopy(pipeline.state)
    empty = archive.load_archive(None)
    pipeline._write_pending_feedback_record(
        live_archive_path=(repo / "live.json").resolve(),
        archive=empty,
        pending_epoch=2,
        source_stage="stage1-cache-recovery",
        events_added=0,
    )
    pipeline.state["negative_feedback_pending"]["record"]["pending_epoch"] = 99
    with pytest.raises(PipelineError, match="binding is invalid"):
        pipeline._validate_pending_feedback_state(
            pipeline.state["negative_feedback_pending"]
        )
    pipeline.state = clean


def test_tampered_stage1_evidence_and_archive_fail_closed(
    tmp_path,
    stage1_negative_row,
):
    path = tmp_path / "negative.json"
    archive.ingest_stage1_rows(path, [stage1_negative_row])
    before = path.read_bytes()
    tampered = copy.deepcopy(stage1_negative_row)
    tampered["low_weight_oracle"]["witness"]["bits"][0] ^= 1
    with pytest.raises(archive.NegativeArchiveError, match="replay failed"):
        archive.ingest_stage1_rows(path, [tampered])
    assert path.read_bytes() == before

    document = json.loads(before)
    document["binding"]["renderer_registry"]["kind"] = "tampered"
    unsigned = dict(document)
    unsigned.pop("archive_sha256")
    document["archive_sha256"] = _sha256(unsigned)
    path.write_text(json.dumps(document, sort_keys=True), encoding="utf-8")
    with pytest.raises(archive.NegativeArchiveError, match="binding mismatch"):
        archive.load_archive(path)


def test_stage2_sparse_witnesses_aggregate_across_mutations(
    tmp_path,
    two_sparse_negatives,
):
    summary, _ranked = _stage2_files(tmp_path, list(two_sparse_negatives))
    path = tmp_path / "negative.json"
    result = archive.ingest_stage2_paths(path, [summary])
    assert result["events_added"] == 2
    assert result["source_counts"] == {
        "stage2-two-block-sparse-kernel": 2,
    }
    stored = archive.load_archive(path)
    block_aggregates = [
        item for item in stored["coordinate_aggregates"].values()
        if item["coordinate"]["kind"] == "witness-block-layout"
        and item["coordinate"]["layout"] == "A-only"
        and item["coordinate"]["block_weight_profile"] == [4, 0]
    ]
    assert len(block_aggregates) == 1
    assert block_aggregates[0]["motif_count"] == 2
    assert block_aggregates[0]["event_count"] == 2
    feedback = archive.feedback_lines(stored)
    assert any("distinct_motifs=2" in line for line in feedback)

    # Replaying the summary is idempotent; corrupting a proof cannot append.
    assert archive.ingest_stage2_paths(path, [summary])["events_added"] == 0
    before = path.read_bytes()
    value = json.loads(summary.read_text())
    value["results"][0]["two_block_sparse_kernel_oracle"]["witness"][
        "support"
    ] = [1]
    summary.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
    with pytest.raises(archive.NegativeArchiveError, match="replay failed"):
        archive.ingest_stage2_paths(path, [summary])
    assert path.read_bytes() == before


def test_stage2_global_cross_block_cache_is_replayed_and_tamper_closed(
    tmp_path,
    rendered_candidates,
):
    # This registered construction has a real unrestricted X logical of
    # weight four spanning A and B.  It exercises the path that the restricted
    # single-block oracle cannot represent.
    row = evaluator._static_candidate(rendered_candidates[7])
    code = build_css_code_from_claim({"construction": row["construction"]})
    matrices = tuple(
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    evidence = evaluate_css_low_weight_oracle(
        *matrices,
        max_weight=4,
        hard_timeout_s=20,
    )
    assert evidence["outcome"] == "SAT"
    witness = evidence["witness"]
    block_size = row["n"] // 2
    assert any(index < block_size for index in witness["support"])
    assert any(index >= block_size for index in witness["support"])

    summary, _ranked, cache = _stage2_global_files(
        tmp_path,
        row,
        evidence,
    )
    archive_path = tmp_path / "negative-global.json"
    result = archive.ingest_stage2_paths(archive_path, [summary])
    assert result["events_added"] == 1
    assert result["source_counts"] == {"stage2-global-low-weight": 1}
    stored = archive.load_archive(archive_path)
    event = next(iter(stored["events"].values()))
    assert event["motif"]["witness"]["block_layout"] == "cross"
    assert set(event["motif"]["coordinates"]) >= {
        "block", "action", "support",
    }
    assert archive.ingest_stage2_paths(archive_path, [summary])[
        "events_added"
    ] == 0

    # The ladder still contains the original plausible synopsis, but changing
    # the authoritative cache without resealing it must fail before mutation
    # feedback can change.
    before = archive_path.read_bytes()
    forged_cache = json.loads(cache.read_text())
    forged_cache["evidence"]["witness"]["support"] = [0]
    cache.write_text(json.dumps(forged_cache, sort_keys=True), encoding="utf-8")
    with pytest.raises(archive.NegativeArchiveError, match="self-hash mismatch"):
        archive.ingest_stage2_paths(archive_path, [summary])
    assert archive_path.read_bytes() == before


def test_stage2_compact_stage3_advance_requires_complete_global_unsat(tmp_path):
    digest = "compact-stage3-prerequisite"
    ranked = tmp_path / "compact-ranked.jsonl"
    summary_path = tmp_path / "compact-summary.json"

    def write(result: dict) -> None:
        ranked.write_text(json.dumps({
            "triage_identity": {"canonical_digest": digest},
            "construction": {"kind": "compact-test-construction"},
            "campaign_selected": True,
            "campaign_audit": result,
        }, sort_keys=True) + "\n", encoding="utf-8")
        summary_path.write_text(json.dumps({
            "schema_version": 1,
            "gate": "qldpc-proof-oriented-candidate-pool",
            "results": [result],
            "status_counts": {"UNRESOLVED": 1},
            "selected_candidates": 1,
            "selection_exhausted": True,
            "retry_required": False,
        }, sort_keys=True), encoding="utf-8")

    missing = {
        "canonical_digest": digest,
        "status": "UNRESOLVED",
        "retry_required": False,
    }
    write(missing)
    with pytest.raises(PipelineError, match="unrestricted UNSAT prerequisite"):
        FiveStagePipeline._validate_pool_summary(
            summary_path,
            ranked,
            "qldpc-proof-oriented-candidate-pool",
        )

    complete = {
        **missing,
        "distance_lower_bound": 5,
        "deferred_backend": "generic-global-sat",
        "compact_low_weight_sat_ladder": {
            "schema_version": 1,
            "gate": "qldpc-stage2-compact-low-weight-gate",
            "outcome": "UNSAT",
            "max_weight": 4,
            "distance_lower_bound": 5,
            "decision_complete": True,
            "retryable": False,
        },
    }
    write(complete)
    validated = FiveStagePipeline._validate_pool_summary(
        summary_path,
        ranked,
        "qldpc-proof-oriented-candidate-pool",
    )
    assert validated["results"] == [complete]

    tampered = copy.deepcopy(complete)
    tampered["compact_low_weight_sat_ladder"]["decision_complete"] = False
    write(tampered)
    with pytest.raises(PipelineError, match="unrestricted UNSAT prerequisite"):
        FiveStagePipeline._validate_pool_summary(
            summary_path,
            ranked,
            "qldpc-proof-oriented-candidate-pool",
        )


def _stage3_artifact(row: dict, sparse_evidence: dict) -> dict:
    code = build_css_code_from_claim({"construction": row["construction"]})
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1
        for value in get_code_matrices(code)
    )
    sector = str(sparse_evidence["witness"]["side"])
    checks, logicals = (hz, lz) if sector == "X" else (hx, lx)
    required = minimum_winning_distance(row["n"], row["k"])
    canonical_digest = "d" * 64
    evidence = solve_css_sector_sat(
        checks,
        logicals,
        max_weight=required,
        timeout=30,
        sector=sector,
        checkpoint_identity={
            "stage3_gate": archive.STAGE3_GATE,
            "candidate_digest": canonical_digest,
        },
    )
    assert evidence["outcome"] == "sat"
    assert evidence["objective"] < required
    wrapper = {
        "sector": sector,
        "partition_index": None,
        "anchor_cube": None,
        "solver_evidence": evidence,
    }
    unit = {
        "unit_id": f"upper-{sector}-global",
        "phase": "upper",
        **wrapper,
    }
    candidate = {
        "canonical_digest": canonical_digest,
        "construction": row["construction"],
        "n": row["n"],
        "k": row["k"],
        "required_distance": required,
    }
    artifact = {
        "schema_version": archive.STAGE3_SCHEMA_VERSION,
        "gate": archive.STAGE3_GATE,
        "status": "REJECTED",
        "candidate": candidate,
        "required_distance": required,
        "low_witnesses": [wrapper],
        "units": [unit],
    }
    artifact["artifact_sha256"] = _sha256(artifact)
    return artifact


def test_stage3_witness_changes_next_parent_fitness_and_feedback(
    tmp_path,
    two_sparse_negatives,
):
    row, sparse = two_sparse_negatives[0]
    artifact = _stage3_artifact(row, sparse)
    artifact_path = tmp_path / "stage3.json"
    artifact_path.write_text(json.dumps(artifact, sort_keys=True), encoding="utf-8")
    path = tmp_path / "negative.json"
    assert archive.ingest_stage3_paths(path, [artifact_path])["events_added"] == 1

    next_round = evaluator._static_candidate(row["candidate"])
    base = evaluator._fitness(next_round)
    summary = archive.annotate_rows(path, [next_round])
    penalized = evaluator._fitness(next_round)
    assert summary["penalized_candidates"] == 1
    assert next_round["negative_archive_match_counts"]["exact_construction"] >= 1
    assert 0 < next_round["negative_archive_penalty"] <= 0.40
    assert penalized < base
    assert archive.feedback_lines(archive.load_archive(path))

    tampered = copy.deepcopy(artifact)
    tampered["low_witnesses"][0]["solver_evidence"]["operator"][
        "packed_hex"
    ] = "00"
    tampered_path = tmp_path / "stage3-tampered.json"
    tampered_path.write_text(json.dumps(tampered, sort_keys=True), encoding="utf-8")
    before = path.read_bytes()
    with pytest.raises(archive.NegativeArchiveError, match="self-hash mismatch"):
        archive.ingest_stage3_paths(path, [tampered_path])
    assert path.read_bytes() == before


def test_pipeline_automatically_archives_stage2_and_stage3_without_env(
    tmp_path,
    monkeypatch,
    two_sparse_negatives,
):
    monkeypatch.delenv(archive.NEGATIVE_ARCHIVE_PATH_ENV, raising=False)
    monkeypatch.delenv(archive.STAGE2_NEGATIVE_INPUTS_ENV, raising=False)
    monkeypatch.delenv(archive.STAGE3_NEGATIVE_INPUTS_ENV, raising=False)
    summary_path, candidate_input = _stage2_files(
        tmp_path,
        [two_sparse_negatives[0]],
    )
    stage3 = _stage3_artifact(*two_sparse_negatives[0])
    stage3_path = tmp_path / "stage3-auto.json"
    stage3_path.write_text(json.dumps(stage3, sort_keys=True), encoding="utf-8")

    pipeline = object.__new__(FiveStagePipeline)
    pipeline.config = SimpleNamespace(
        candidate_inputs=(candidate_input,),
        repo_dir=tmp_path,
        run_id="archive-auto-test",
    )
    pipeline.paths = SimpleNamespace(stage2_summary=summary_path)
    pipeline.state = {}
    pipeline._write_state = lambda: None

    stage2_result = pipeline._archive_stage2_coset_negatives([candidate_input])
    stage3_result = pipeline._archive_stage3_coset_negatives(
        [candidate_input],
        {"results": [{
            "backend": "sat-sectors",
            "status": "REJECTED",
            "artifact_path": str(stage3_path.resolve()),
        }]},
    )
    assert stage2_result["events_added"] == 1
    assert stage3_result["events_added"] == 1
    archive_path = archive.resolve_archive_path(candidate_input)
    assert archive_path is not None
    stored = archive.load_archive(archive_path)
    assert stored["events"]
    assert {
        event["proof"]["source"] for event in stored["events"].values()
    } == {
        "stage2-two-block-sparse-kernel",
        "stage3-threshold-sat",
    }

    next_round = evaluator._static_candidate(two_sparse_negatives[0][0]["candidate"])
    baseline = evaluator._fitness(next_round)
    archive.annotate_rows(archive_path, [next_round])
    assert evaluator._fitness(next_round) < baseline
    assert archive.feedback_lines(stored)


def test_orbit_cap_degrades_without_partial_orbit(monkeypatch):
    construction = {
        "kind": "coset-two-block-v2",
        "representation_id": "css-coset-two-block-actions-v2",
        "action_id": "synthetic",
        "action_catalog_id": "catalog",
        "action_catalog_sha256": "a" * 64,
        "left_support": ["L"],
        "right_support": ["R"],
    }
    generators = [{
        "qubit_permutation": [1, 2, 3, 0],
    }]
    monkeypatch.setattr(archive, "_MAX_WITNESS_ORBIT_STATES", 2)
    monkeypatch.setattr(
        archive,
        "verify_construction_symmetry",
        lambda *_args: {
            "verified": True,
            "verified_generators": generators,
            "report_sha256": "b" * 64,
        },
    )
    result = archive._verified_witness_orbit(
        construction,
        hx=np.zeros((1, 4), dtype=np.uint8),
        hz=np.zeros((1, 4), dtype=np.uint8),
        support=[0],
    )
    assert result["available"] is False
    assert result["reason"] == "verified-orbit-exceeds-safe-state-cap"
    assert "canonical_support" not in result
