from __future__ import annotations

import os
from pathlib import Path

import pytest

from scripts import run_paper400_dic5_nested_width10_child_resume_proof_v1 as runner
from scripts import run_paper400_dic5_nested_width10_four_lane_v1 as coordinator


def _root(tmp_path: Path) -> Path:
    root = (tmp_path / "leaf").resolve()
    root.mkdir(mode=0o700)
    (root / "runtime").mkdir(mode=0o700)
    runtime = root / runner.RUNTIME_ROOT
    runtime.mkdir(mode=0o700)
    generations = runtime / "generations"
    generations.mkdir(mode=0o700)
    generation = generations / "000000"
    generation.mkdir(mode=0o700)
    images = generation / "images"
    images.mkdir(mode=0o700)
    temporary = generation / "tmp"
    temporary.mkdir(mode=0o700)
    (runtime / "proof.drat").write_bytes(b"transport proof")
    (runtime / "proof.drat").chmod(0o600)
    image = images / "ckpt_solver.dmtcp"
    image.write_bytes(b"DMTCP_CHECKPOINT_IMAGE")
    image.chmod(0o600)
    (generation / "coordinator.log").write_text("stopped\n", encoding="ascii")
    (generation / "coordinator.log").chmod(0o600)
    alias = images / runner.RESTART_ALIAS_NAME
    alias.symlink_to("dmtcp_restart_script_deadbeef-40000-cafebabe.sh")
    target = images / os.readlink(alias)
    target.write_text("#!/bin/sh\n", encoding="ascii")
    target.chmod(0o744)
    (root / "static").mkdir(mode=0o700)
    (root / "artifacts").mkdir(mode=0o700)
    for relative, payload in (
        (runner.STATIC_DIMACS, b"p cnf 1 1\n1 0\n"),
        (runner.DRAT_ARTIFACT, b"durable drat"),
        (runner.LRAT_ARTIFACT, b"durable lrat"),
    ):
        path = root / relative
        path.write_bytes(payload)
        path.chmod(0o600)
    return root


def _attestation(root: Path) -> dict:
    values = {
        key: None
        for key in runner.FINAL_ROOT_ATTESTATION_FIELDS
        if key != "record_sha256"
    }
    values.update({
        "schema_version": runner.FINAL_ROOT_ATTESTATION_SCHEMA_VERSION,
        "kind": runner.FINAL_ROOT_ATTESTATION_KIND,
        "gate": runner.proof_v1.RUNNER_GATE,
        "root": str(root),
        "root_identity": runner._root_identity(root),
        "cnf_artifact": runner.v2._physical_record(
            root / runner.STATIC_DIMACS, root,
            "exact-hierarchical-child-cnf", cap=1 << 20,
        ),
        "drat_artifact": runner.v2._physical_record(
            root / runner.DRAT_ARTIFACT, root,
            "raw-binary-drat", cap=1 << 20,
        ),
        "lrat_artifact": runner.v2._physical_record(
            root / runner.LRAT_ARTIFACT, root,
            "converted-lrat", cap=1 << 20,
        ),
        "proof_replay_decision_complete": True,
        "strict_proof_unsat": True,
        "valid": True,
        "failures": [],
    })
    return runner.seal(values)


def test_transport_manifest_is_exact_and_excludes_scientific_artifacts(
    tmp_path: Path,
):
    root = _root(tmp_path)
    manifest = runner._transport_manifest(root)
    paths = {item["relative_path"] for item in manifest["entries"]}
    assert runner.RUNTIME_ROOT.as_posix() in paths
    assert (runner.RUNTIME_ROOT / "proof.drat").as_posix() in paths
    assert runner.STATIC_DIMACS.as_posix() not in paths
    assert runner.DRAT_ARTIFACT.as_posix() not in paths
    assert runner.LRAT_ARTIFACT.as_posix() not in paths
    assert manifest["entry_count"] == len(paths)
    assert manifest["regular_file_bytes"] > 0


def test_delete_claimed_transport_preserves_scientific_artifacts(
    tmp_path: Path,
):
    root = _root(tmp_path)
    manifest = runner._transport_manifest(root)
    claim = {"transport_entries": manifest["entries"]}
    expected = {
        relative: (root / relative).read_bytes()
        for relative in (
            runner.STATIC_DIMACS, runner.DRAT_ARTIFACT,
            runner.LRAT_ARTIFACT,
        )
    }
    runner._delete_claimed_transport(root, claim)
    assert not os.path.lexists(root / runner.RUNTIME_ROOT)
    assert {
        relative: (root / relative).read_bytes() for relative in expected
    } == expected


def test_delete_claimed_transport_rejects_new_or_changed_entry(
    tmp_path: Path,
):
    root = _root(tmp_path)
    manifest = runner._transport_manifest(root)
    claim = {"transport_entries": manifest["entries"]}
    unexpected = root / runner.RUNTIME_ROOT / "unexpected"
    unexpected.write_bytes(b"do not delete")
    with pytest.raises(
        runner.HierarchicalResumeRunnerError,
        match="changed after prune authorization",
    ):
        runner._delete_claimed_transport(root, claim)
    assert unexpected.read_bytes() == b"do not delete"


def test_delete_claimed_transport_resumes_after_partial_deletion(
    tmp_path: Path,
):
    root = _root(tmp_path)
    manifest = runner._transport_manifest(root)
    claim = {"transport_entries": manifest["entries"]}
    already_removed = root / runner.RUNTIME_ROOT / "proof.drat"
    already_removed.unlink()
    runner._delete_claimed_transport(root, claim)
    assert not os.path.lexists(root / runner.RUNTIME_ROOT)


def test_transport_manifest_rejects_hardlinked_file(tmp_path: Path):
    root = _root(tmp_path)
    proof = root / runner.RUNTIME_ROOT / "proof.drat"
    os.link(proof, root / runner.RUNTIME_ROOT / "proof-hardlink")
    with pytest.raises(
        runner.HierarchicalResumeRunnerError,
        match="multiply-linked",
    ):
        runner._transport_manifest(root)


def test_transport_manifest_rejects_fifo(tmp_path: Path):
    root = _root(tmp_path)
    os.mkfifo(root / runner.RUNTIME_ROOT / "unexpected-fifo", mode=0o600)
    with pytest.raises(
        runner.HierarchicalResumeRunnerError,
        match="non-plain",
    ):
        runner._transport_manifest(root)


def test_transport_manifest_does_not_follow_symlink_escape(tmp_path: Path):
    root = _root(tmp_path)
    outside = tmp_path / "outside"
    outside.write_bytes(b"must survive")
    link = root / runner.RUNTIME_ROOT / "outside-link"
    link.symlink_to(outside)
    manifest = runner._transport_manifest(root)
    by_path = {
        item["relative_path"]: item for item in manifest["entries"]
    }
    assert by_path[link.relative_to(root).as_posix()]["entry_type"] == "symlink"
    runner._delete_claimed_transport(
        root, {"transport_entries": manifest["entries"]},
    )
    assert outside.read_bytes() == b"must survive"


def test_prune_transport_root_writes_auditable_commit_and_is_idempotent(
    monkeypatch, tmp_path: Path,
):
    root = _root(tmp_path)
    (root / "state").mkdir(mode=0o700)
    runner._initialize_root_lock(root)
    (root / runner.FINAL_COMMIT).write_bytes(b"synthetic-final-marker\n")
    attestation = _attestation(root)
    monkeypatch.setattr(
        runner, "_action_static_kwargs", lambda _root, kwargs: dict(kwargs),
    )
    monkeypatch.setattr(
        runner, "_verify_final_root_locked",
        lambda *_args, **_kwargs: attestation,
    )
    monkeypatch.setattr(
        runner, "_load_session",
        lambda *_args, **_kwargs: (
            {"record": {"resource_policy": {}}}, {},
        ),
    )
    monkeypatch.setattr(
        runner, "validate_transport_chain",
        lambda *_args, **_kwargs: {"generations": []},
    )
    monkeypatch.setattr(
        runner, "_quiesce_transport_coordinators",
        lambda *_args, **_kwargs: None,
    )
    replayed = []
    monkeypatch.setattr(
        runner, "_validate_pruned_scientific_evidence_locked",
        lambda *_args, **_kwargs: replayed.append(True) or attestation,
    )

    first = runner.prune_transport_root(root)
    assert first["kind"] == runner.TRANSPORT_PRUNE_COMMIT_KIND
    assert first["runtime_absent"] is True
    assert first["scientific_artifacts_preserved"] is True
    assert first["removed_regular_file_bytes"] > 0
    assert not os.path.lexists(root / runner.RUNTIME_ROOT)
    assert (root / runner.STATIC_DIMACS).is_file()
    assert (root / runner.DRAT_ARTIFACT).is_file()
    assert (root / runner.LRAT_ARTIFACT).is_file()

    second = runner.prune_transport_root(root)
    assert second == first
    assert replayed == [True]


def test_prune_transport_root_resumes_a_durable_partial_claim(
    monkeypatch, tmp_path: Path,
):
    root = _root(tmp_path)
    (root / "state").mkdir(mode=0o700)
    runner._initialize_root_lock(root)
    attestation = _attestation(root)
    manifest = runner._transport_manifest(root)
    claim = runner._transport_prune_claim_value(root, attestation, manifest)
    runner._publish_json(root / runner.TRANSPORT_PRUNE_CLAIM, claim)
    (root / runner.RUNTIME_ROOT / "proof.drat").unlink()
    monkeypatch.setattr(
        runner, "_action_static_kwargs", lambda _root, kwargs: dict(kwargs),
    )
    monkeypatch.setattr(
        runner, "_validate_pruned_scientific_evidence_locked",
        lambda *_args, **_kwargs: attestation,
    )

    commit = runner.prune_transport_root(root)
    assert commit["claim_sha256"] == claim["record_sha256"]
    assert not os.path.lexists(root / runner.RUNTIME_ROOT)


def test_prune_transport_root_refuses_before_final_commit(
    monkeypatch, tmp_path: Path,
):
    root = _root(tmp_path)
    (root / "state").mkdir(mode=0o700)
    runner._initialize_root_lock(root)
    monkeypatch.setattr(
        runner, "_action_static_kwargs", lambda _root, kwargs: dict(kwargs),
    )
    with pytest.raises(
        runner.HierarchicalResumeRunnerError,
        match="requires a final child commit",
    ):
        runner.prune_transport_root(root)
    assert os.path.lexists(root / runner.RUNTIME_ROOT)
    assert not (root / runner.TRANSPORT_PRUNE_CLAIM).exists()


def test_quiesce_transport_coordinators_requires_shutdown(
    monkeypatch, tmp_path: Path,
):
    root = _root(tmp_path)
    calls = []
    monkeypatch.setattr(
        runner.controller, "_quit_coordinator_if_present",
        lambda command, port_file: calls.append((command, port_file)),
    )
    attempts = {41000: 0, 41001: 0}

    def query(_command, port, *, timeout):
        attempts[port] += 1
        if attempts[port] == 1:
            return 0, False
        raise runner.controller.ResumeControllerError("gone")

    monkeypatch.setattr(runner.controller, "_query_status", query)
    chain = {
        "generations": [
            {"generation": 0, "coordinator_port": 41000},
            {"generation": 1, "coordinator_port": 41001},
        ]
    }
    runner._quiesce_transport_coordinators(root, chain)
    assert len(calls) == 2
    assert attempts == {41000: 2, 41001: 2}


def test_quiesce_transport_coordinator_fails_if_still_reachable(
    monkeypatch, tmp_path: Path,
):
    root = _root(tmp_path)
    monkeypatch.setattr(
        runner.controller, "_quit_coordinator_if_present",
        lambda *_args: None,
    )
    monkeypatch.setattr(
        runner.controller, "_query_status", lambda *_args, **_kwargs: (0, False),
    )
    with pytest.raises(
        runner.HierarchicalResumeRunnerError,
        match="remained reachable",
    ):
        runner._quiesce_transport_coordinators(
            root,
            {"generations": [{"generation": 0, "coordinator_port": 41000}]},
        )


def test_child_and_batch_cli_expose_prune_transport():
    child = runner.build_parser().parse_args([
        "prune-transport", "--root", "/tmp/leaf",
    ])
    batch = coordinator.build_parser().parse_args([
        "prune-transport", "--root", "/tmp/batch",
    ])
    assert child.action == batch.action == "prune-transport"
    assert coordinator._action_callable("prune-transport") is (
        runner.prune_transport_root
    )


def test_batch_prune_waits_for_final_proof(monkeypatch, tmp_path: Path):
    lane_root = tmp_path / "lane"
    lane_root.mkdir()
    status = {
        "value": {"kind": "status"},
        "state": "CHECKPOINTED",
        "terminal_claimed": False,
        "terminal_committed": False,
    }
    monkeypatch.setattr(coordinator, "_lane_status", lambda *_args: status)
    lane = {
        "lane_index": 0, "global_leaf_index": 12,
        "cpu": 3, "child_root": str(lane_root),
    }
    result = coordinator._dispatch_lane_action(
        lane=lane, action="prune-transport", sequence=1,
        claim_sha256="a" * 64,
        action_function=lambda *_args, **_kwargs: pytest.fail(
            "prune ran before final proof"
        ),
        static_kwargs={},
    )
    assert result["disposition"] == "PENDING"
    assert result["disposition_reason"] == "WAITING_FOR_FINAL_PROOF"
    assert result["goal_satisfied"] is False


def test_batch_prune_applies_only_after_final_proof(monkeypatch, tmp_path: Path):
    lane_root = tmp_path / "lane"
    lane_root.mkdir()
    statuses = iter([
        {
            "value": {"kind": "status-before"},
            "state": "CHECKPOINTED",
            "terminal_claimed": True,
            "terminal_committed": True,
        },
        {
            "value": {"kind": "status-after"},
            "state": "PRUNED",
            "terminal_claimed": True,
            "terminal_committed": True,
        },
    ])
    monkeypatch.setattr(coordinator, "_lane_status", lambda *_args: next(statuses))
    lane = {
        "lane_index": 0, "global_leaf_index": 12,
        "cpu": 3, "child_root": str(lane_root),
    }
    result = coordinator._dispatch_lane_action(
        lane=lane, action="prune-transport", sequence=1,
        claim_sha256="a" * 64,
        action_function=lambda *_args, **_kwargs: {
            "kind": runner.TRANSPORT_PRUNE_COMMIT_KIND,
        },
        static_kwargs={},
    )
    assert result["disposition"] == "APPLIED"
    assert result["goal_satisfied"] is True
    assert result["transport_state_after"] == "PRUNED"
