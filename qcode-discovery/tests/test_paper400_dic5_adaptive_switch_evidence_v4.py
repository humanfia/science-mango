from __future__ import annotations

import builtins
import copy
import fcntl
import hashlib
import importlib.util
import inspect
import json
import os
import subprocess
import stat
from pathlib import Path

import pytest


PROJECT = Path(__file__).resolve().parent.parent
SOURCE = PROJECT / "scripts/paper400_dic5_adaptive_switch_evidence_v4.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("adaptive_switch_v4_test", SOURCE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def v4():
    return _load_module()


def _mkdir(path: Path) -> None:
    path.mkdir(mode=0o700)
    path.chmod(0o700)


def _write(path: Path, payload: bytes) -> None:
    path.write_bytes(payload)
    path.chmod(0o600)


def _flat_material(path: Path, root: Path, role: str) -> dict:
    payload = path.read_bytes()
    info = path.lstat()
    return {
        "role": role,
        "relative_path": path.relative_to(root).as_posix(),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
        "device": info.st_dev,
        "inode": info.st_ino,
        "uid": info.st_uid,
        "mode": stat.S_IMODE(info.st_mode),
        "links": info.st_nlink,
    }


def _sha(label: str) -> str:
    return hashlib.sha256(label.encode("ascii")).hexdigest()


def _reseal(v4, record: dict) -> dict:
    return v4.seal({
        key: copy.deepcopy(value)
        for key, value in record.items()
        if key != "record_sha256"
    })


def _rewrite_static(v4, target: Path, observation: dict, mutate) -> None:
    path = target / "state/00-static.json"
    record = json.loads(path.read_text(encoding="ascii"))
    mutate(record)
    record = _reseal(v4, record)
    _write(path, v4.canonical_bytes(record) + b"\n")
    observation["static_record_sha256"] = record["record_sha256"]
    observation["material_files"][0] = v4._stable_target_file(
        target, Path("state/00-static.json"), cap=v4.base.MAX_JSON_BYTES
    )


def _make_static_target(
    v4, parent: Path, batch: Path, *, lane: int, descendant: int,
    candidate: int | None = None,
) -> tuple[Path, int]:
    target = parent / f"target-l{lane}-d{descendant}"
    _mkdir(target)
    lock = target / ".adaptive-child.lock"
    _write(lock, b"")
    for name in ("static", "state", "artifacts", "runtime"):
        _mkdir(target / name)
    _mkdir(target / "state/actions")
    materials = {
        "parent_manifest": ("parent-manifest.json", "parent-manifest", b"{}\n"),
        "width6_campaign": ("width6-campaign.json", "width6-campaign", b"{}\n"),
        "width10_campaign": ("width10-campaign.json", "width10-campaign", b"{}\n"),
        "adaptive_overlay": ("adaptive-overlay.json", "adaptive-overlay", b"{}\n"),
        "hard_evidence": ("hard-evidence.json", "hard-evidence", b"{}\n"),
        "switch_evidence": ("switch-evidence.json", "switch-evidence", b"{}\n"),
        "descendant_cnf": ("descendant.cnf", "exact-descendant-cnf", b"p cnf 1 1\n1 0\n"),
    }
    material_records = {}
    for key, (name, role, payload) in materials.items():
        path = target / "static" / name
        _write(path, payload)
        material_records[key] = _flat_material(path, target, role)
    overlay_pin = _sha(f"overlay-{lane}")
    descendant_pin = _sha(f"descendant-{lane}-{descendant}")
    chosen = 17 + lane if candidate is None else candidate
    root_identity = v4.base._root_identity(target)
    full_lock_identity = v4.base._stat_identity(lock.lstat())
    lock_identity = {
        "relative_path": ".adaptive-child.lock",
        **{
            field: full_lock_identity[field]
            for field in (
                "device", "inode", "uid", "mode", "links", "bytes",
            )
        },
    }
    observation_policy = v4.base._observation_policy(
        86400.0, [1.0, 2.0, 3.0, 4.0]
    )
    policy = {
        "timeout_seconds": observation_policy["timeout_seconds"],
        "elapsed_seconds_by_lane": list(
            observation_policy["elapsed_seconds_by_lane"]
        ),
    }
    record = v4.seal({
        "schema_version": 5,
        "kind": "paper400-dic5-adaptive-child-resume-static-v5",
        "gate": "paper400-dic5-adaptive-child-resume-v5",
        "state": "RESUMABLE_STATIC_SEALED",
        "authority": "TEST_ONLY_CANDIDATE_ONLY_V5",
        "test_only": True,
        "production_eligible": False,
        "root": str(target),
        "root_identity": root_identity,
        "root_lock_identity": lock_identity,
        "batch_root_identity": v4.base._root_identity(batch),
        "strict_base": True,
        "python_startup": {},
        "external_pins": {
            "expected_overlay_sha256": overlay_pin,
            "expected_hard_evidence_sha256":
                v4.EXPECTED_HARD_EVIDENCE_SHA256S[lane],
            "expected_switch_evidence_sha256":
                v4.EXPECTED_SWITCH_EVIDENCE_SHA256,
            "expected_batch_manifest_sha256":
                v4.EXPECTED_BATCH_MANIFEST_SHA256,
        },
        "selection": {
            "global_leaf_index": lane * 64,
            "descendant_index": descendant,
            "descendant_sha256": descendant_pin,
            "adaptive_node_id": f"lane-{lane}",
            "relative_assignment_literals": [chosen if descendant == 0 else -chosen],
            "candidate_variables": [chosen],
        },
        "switch_policy": policy,
        "material_files": material_records,
        "campaign_manifest_sha256": _sha("campaign"),
        "overlay_manifest_sha256": overlay_pin,
        "hard_evidence_sha256": v4.EXPECTED_HARD_EVIDENCE_SHA256S[lane],
        "switch_evidence_sha256": v4.EXPECTED_SWITCH_EVIDENCE_SHA256,
        "overlay_verification": {},
        "campaign_verification": {},
        "switch_structure_validation": {},
        "descendant": {
            "descendant_index": descendant,
            "descendant_sha256": descendant_pin,
            "pending": True,
            "observed_status": "PENDING",
            "solver_terminal_authenticated": False,
        },
        "descendant_cnf": {},
        "source_binding": {},
        "execution_module_binding": {},
        "toolchain_binding": {},
        "resource_policy": {},
        "launch_attestation": {
            "serialized_overlay_launch_authorized": False,
            "serialized_switch_launch_authorized": False,
            "serialized_composite_launch_authorized": False,
            "candidate_exact_bytes_replayed": True,
            "atomic_switch_v4_lease_required": True,
            "strict_first_start_requires_complete_eight_root_cover": True,
            "adaptive_handoff_reentry_supported": False,
            "maximum_live_workers_during_handoff": 4,
        },
        "resume_policy": {
            "single_process": True,
            "single_cpu": True,
            "cpu_rlimit_unlimited": True,
            "proof_fsize_cap_required": True,
            "dmtcp_checkpoint_resource_hard_limit": None,
            "dmtcp_checkpoint_oom_risk_accepted": True,
            "controller": "cadical-dmtcp-exact-resume-v1",
            "checkpoint_has_scientific_authority": False,
            "resume_has_scientific_authority": False,
        },
        "claim_scope": {
            "pending_is_solver_evidence": False,
            "overlay_proves_leaf_unsat": False,
            "switch_record_proves_leaf_unsat": False,
            "checkpoint_proves_leaf_unsat": False,
            "only_final_fresh_drat_lrat_certificate_authenticates_leaf_unsat": True,
            "parent_leaf_unsat_claim": False,
            "distance_lower_bound_claim": False,
        },
        "publication_certificate": False,
        "upload_authorized": False,
    })
    _write(target / "state/00-static.json", v4.canonical_bytes(record) + b"\n")
    fd = os.open(lock, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    return target, fd


def _switch(v4) -> dict:
    return {
        "observation_policy":
            v4.base._observation_policy(86400.0, [1.0, 2.0, 3.0, 4.0]),
        "lanes": [
            {
                "lane_index": lane,
                "global_leaf_index": lane * 64,
                "hard_evidence_sha256":
                    v4.EXPECTED_HARD_EVIDENCE_SHA256S[lane],
            }
            for lane in range(4)
        ],
    }


def test_execution_closure_splits_fixed_replay_from_current_science(v4):
    binding = v4._v4_source_binding()
    assert [item["role"] for item in binding["sources"]] == [
        "adaptive_switch_evidence_v4_source",
        "adaptive_switch_evidence_v2_primitives_source",
    ]
    dependency = binding["historical_fixed_replay_dependency"]
    assert dependency["readonly_api"] == [
        "load_legacy_exact", "load_overlay_exact",
    ]
    assert dependency["historical_v3_calls_are_readonly_loaders_only"] is True
    assert dependency["fixed_record_primitives"] == (
        "current-v4-frozen-v2-exact-source"
    )
    assert dependency["dynamic_source_binding_sha256"] == (
        v4.FIXED_REPLAY_DYNAMIC_SOURCE_BINDING_SHA256
    )
    assert dependency["static_source_binding"] == (
        v4._expected_failed_v3_source_binding()
    )
    assert [item["sha256"] for item in dependency["sources"]] == [
        v4.FAILED_V3_SOURCE_SHA256,
        v4.EXPECTED_V2_SOURCE_SHA256,
        v4.FIXED_REPLAY_OVERLAY_SOURCE_SHA256,
    ]
    assert [item["execution"] for item in dependency["sources"]] == [
        (
            "on-demand-fixed-replay-"
            "compile-exact-source-bytes-v4-fixed-bootstrap"
        ),
        "on-demand-fixed-replay-compile-exact-source-bytes-v3",
        (
            "on-demand-fixed-replay-historical-v3-readonly-loader-"
            "compile-exact-source-bytes-v3"
        ),
    ]
    assert [Path(item["absolute_path"]) for item in dependency["sources"]] == [
        v4.FIXED_REPLAY_V3_SOURCE,
        v4.FIXED_REPLAY_V2_SOURCE,
        v4.FIXED_REPLAY_OVERLAY_SOURCE,
    ]
    assert v4._FixedReplayReadonly.__slots__ == (
        "_load_legacy", "_load_overlay",
    )
    assert not hasattr(v4, "_FIXED_REPLAY_READONLY")

    class HistoricalModule:
        _load_legacy_exact = staticmethod(lambda discovery: discovery)
        _load_overlay_exact = staticmethod(lambda: None)

    facade = v4._FixedReplayReadonly(HistoricalModule())
    public_methods = {
        name for name, value in vars(v4._FixedReplayReadonly).items()
        if not name.startswith("_") and callable(value)
    }
    assert public_methods == {"load_legacy_exact", "load_overlay_exact"}
    assert not hasattr(facade, "_snapshot")
    assert not hasattr(facade, "_build_record")
    assert not hasattr(facade, "_source_binding")
    assert not hasattr(facade, "_validate_record")
    assert not hasattr(facade, "action")
    assert v4.EXPECTED_V2_SOURCE_SHA256 == binding["sources"][1]["sha256"]


def test_fixed_attempt_and_production_hard_pins(v4):
    assert len(v4.ATTEMPT_ID) == 64
    assert v4.ATTEMPT_ID == (
        "0476098fb46e7acf70c9b568835052b917af8590aa85612492e3168e998b5bff"
    )
    assert v4.ATTEMPT_ROOT.name.endswith(v4.ATTEMPT_ID)
    assert len(v4.EXPECTED_HARD_EVIDENCE_SHA256S) == 4
    assert all(len(item) == 64 for item in v4.EXPECTED_HARD_EVIDENCE_SHA256S)
    assert v4.TARGET_KEYS == (
        (0, 0), (1, 0), (2, 0), (3, 0),
        (0, 1), (1, 1), (2, 1), (3, 1),
    )


def test_attempt_root_and_nested_directory_fsync_direct_parents(v4, tmp_path, monkeypatch):
    root = tmp_path / "batch"
    _mkdir(root)
    observed = []
    monkeypatch.setattr(v4, "_fsync_directory", lambda path: observed.append(Path(path)))
    attempt = v4._make_attempt_root(root)
    journal = v4._make_journal_directory(root, v4.TARGET_DIRECTORY)
    assert attempt == root / v4.ATTEMPT_ROOT
    assert journal.parent == attempt
    assert observed == [root, attempt]


def test_stable_raw_json_rejects_non_0600(v4, tmp_path):
    record = v4.seal({"kind": "fixture"})
    payload = v4.canonical_bytes(record) + b"\n"
    path = tmp_path / "record.json"
    path.write_bytes(payload)
    path.chmod(0o644)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._stable_raw_json(
            path,
            expected_record_sha256=record["record_sha256"],
            expected_physical_sha256=hashlib.sha256(payload).hexdigest(),
        )


def test_stable_owned_json_rejects_noncanonical_mode_and_rename(
    v4, tmp_path, monkeypatch,
):
    record = v4.seal({"kind": "stable-owned-fixture"})
    canonical = v4.canonical_bytes(record) + b"\n"
    path = tmp_path / "owned.json"
    _write(path, canonical)
    assert v4._stable_owned_json(path) == record

    _write(
        path,
        json.dumps(record, indent=2, sort_keys=True).encode("ascii") + b"\n",
    )
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._stable_owned_json(path)

    _write(path, canonical)
    path.chmod(0o644)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._stable_owned_json(path)

    _write(path, canonical)
    replacement = tmp_path / "replacement.json"
    _write(replacement, canonical)
    stable_bytes = v4.base._stable_bytes

    def swap_after_read(checked_path, *, cap, require_owned=True):
        payload, identity = stable_bytes(
            checked_path, cap=cap, require_owned=require_owned
        )
        if Path(checked_path) == path:
            os.replace(replacement, path)
        return payload, identity

    monkeypatch.setattr(v4.base, "_stable_bytes", swap_after_read)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._stable_owned_json(path)


def _make_attempt_inventory(v4, root: Path, *, handoff_published: bool):
    _mkdir(root / v4.ATTEMPT_ROOT)
    for relative in (
        v4.TARGET_DIRECTORY,
        v4.STARTED_DIRECTORY,
        v4.QUIESCENCE_DIRECTORY,
    ):
        _mkdir(root / relative)
    for relative in (
        v4.INCIDENT_PRECONDITION,
        v4.RETIREMENT_INTENT,
        v4.PREPARED_COMMIT,
    ):
        _write(root / relative, b"{}\n")
    if handoff_published:
        _write(root / v4.HANDOFF_COMMIT, b"{}\n")
    for lane, descendant in v4.TARGET_KEYS:
        name = f"lane-{lane}-descendant-{descendant}.json"
        _write(root / v4.TARGET_DIRECTORY / name, b"{}\n")
        _write(root / v4.STARTED_DIRECTORY / name, b"{}\n")
        if descendant == 0:
            _write(root / v4.QUIESCENCE_DIRECTORY / name, b"{}\n")


def test_attempt_inventory_distinguishes_prepublish_and_committed(v4, tmp_path):
    root = tmp_path / "batch"
    _mkdir(root)
    _make_attempt_inventory(v4, root, handoff_published=False)
    v4._verify_attempt_inventory(root, handoff_published=False)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._verify_attempt_inventory(root, handoff_published=True)

    _write(root / v4.HANDOFF_COMMIT, b"{}\n")
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._verify_attempt_inventory(root, handoff_published=False)
    v4._verify_attempt_inventory(root, handoff_published=True)

    extra = root / v4.TARGET_DIRECTORY / "extra.json"
    _write(extra, b"{}\n")
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._verify_attempt_inventory(root, handoff_published=True)
    extra.unlink()
    (root / v4.STARTED_DIRECTORY).chmod(0o755)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._verify_attempt_inventory(root, handoff_published=True)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._verify_attempt_inventory(root, handoff_published=None)

def test_outer_fd_requires_exact_exclusive_owned_lock(v4, tmp_path):
    root = tmp_path / "root"
    _mkdir(root)
    lock = root / ".adaptive-child.lock"
    _write(lock, b"")
    fd = os.open(lock, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert v4._validate_target_outer_fd(root, fd) == v4.base._stat_identity(lock.lstat())
        readonly = os.open(lock, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
        try:
            with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
                v4._validate_target_outer_fd(root, readonly)
        finally:
            os.close(readonly)
    finally:
        os.close(fd)


def test_v5_declared_outer_identity_is_projected_type_exact(v4, tmp_path):
    root = tmp_path / "root-v5-shape"
    _mkdir(root)
    lock = root / ".adaptive-child.lock"
    _write(lock, b"")
    full = v4.base._stat_identity(lock.lstat())
    declared = {
        "relative_path": ".adaptive-child.lock",
        **{
            field: full[field]
            for field in (
                "device", "inode", "uid", "mode", "links", "bytes",
            )
        },
    }
    assert v4._validate_v5_declared_outer_identity(
        declared, full
    ) == declared
    missing = dict(declared)
    missing.pop("relative_path")
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_v5_declared_outer_identity(missing, full)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_v5_declared_outer_identity(dict(full), full)
    replaced = dict(declared)
    replaced["inode"] += 1
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_v5_declared_outer_identity(replaced, full)


def _neutral_quiescence(v4) -> dict:
    return v4.seal({
        "schema_version": 5,
        "kind": v4.QUIESCENCE_INPUT_KIND,
        "lane_index": 0,
        "descendant_index": 0,
        "new_root_identity": {
            "path": "/tmp/root", "device": 1, "inode": 2,
            "uid": os.geteuid(), "mode": 0o700,
        },
        "new_pid": 123,
        "new_proc_start_ticks": 456,
        "state": "CHECKPOINTED",
        "pid_identity_alive": False,
        "checkpoint_commit_sha256": _sha("checkpoint"),
        "proof_sha256": _sha("proof"),
        "proof_bytes": 17,
        "writable_holders": [],
    })


def test_neutral_v5_quiescence_is_wrapped_as_incident_bound_v4(v4):
    neutral = _neutral_quiescence(v4)
    assert v4._validate_quiescence_record(neutral) == neutral
    incident_pin = _sha("incident")
    journal = v4._seal_v4_quiescence_journal(neutral, incident_pin)
    assert journal["schema_version"] == 4
    assert journal["kind"] == v4.QUIESCENCE_KIND
    assert journal["input_observation_sha256"] == neutral["record_sha256"]
    assert journal["incident_precondition_sha256"] == incident_pin
    assert v4._validate_v4_quiescence_journal(journal, incident_pin) == journal
    tampered = dict(journal)
    tampered["proof_bytes"] += 1
    tampered = v4.seal({k: value for k, value in tampered.items() if k != "record_sha256"})
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_v4_quiescence_journal(tampered, incident_pin)


    malformed = dict(neutral)
    malformed["writable_holders"] = "none"
    malformed = v4.seal({
        key: value for key, value in malformed.items()
        if key != "record_sha256"
    })
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_quiescence_record(malformed)

    malformed = dict(neutral)
    malformed["new_root_identity"] = None
    malformed = v4.seal({
        key: value for key, value in malformed.items()
        if key != "record_sha256"
    })
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_quiescence_record(malformed)


def test_target_and_outer_fd_collection_types_fail_closed(v4, tmp_path):
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_unstarted_target_roots(
            tmp_path, [], {}, _switch(v4)
        )
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._adopt_exclusive_outer_locks([], {})

def test_eight_unstarted_targets_exact_inventory_and_sibling_policy(v4, tmp_path):
    batch = tmp_path / "batch"
    roots_parent = tmp_path / "roots"
    _mkdir(batch)
    _mkdir(roots_parent)
    targets = []
    fds = []
    try:
        for lane, descendant in v4.TARGET_KEYS:
            target, fd = _make_static_target(
                v4, roots_parent, batch, lane=lane, descendant=descendant,
            )
            targets.append(target)
            fds.append(fd)
        observed = v4._validate_unstarted_target_roots(
            batch, targets, fds, _switch(v4)
        )
        assert [
            (item["lane_index"], item["descendant_index"])
            for item in observed
        ] == list(v4.TARGET_KEYS)
        assert all(item["solver_never_started"] is True for item in observed)
    finally:
        for fd in fds:
            os.close(fd)


def test_eight_target_sibling_candidate_mismatch_fails_closed(v4, tmp_path):
    batch = tmp_path / "batch"
    roots_parent = tmp_path / "roots"
    _mkdir(batch)
    _mkdir(roots_parent)
    targets = []
    fds = []
    try:
        for lane, descendant in v4.TARGET_KEYS:
            target, fd = _make_static_target(
                v4, roots_parent, batch, lane=lane, descendant=descendant,
                candidate=(399 if (lane, descendant) == (2, 1) else None),
            )
            targets.append(target)
            fds.append(fd)
        with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
            v4._validate_unstarted_target_roots(batch, targets, fds, _switch(v4))
    finally:
        for fd in fds:
            os.close(fd)


def test_prepare_has_single_full_incident_replay_before_first_write(v4):
    enter_source = inspect.getsource(v4._enter)
    prepare_source = inspect.getsource(v4.AtomicSwitchLease.prepare_retirement)
    assert enter_source.count("_build_incident_precondition_locked(") == 1
    assert "_build_incident_precondition_locked(" not in prepare_source
    assert prepare_source.index("_lightweight_incident_prewrite_fence()") < prepare_source.index("_make_attempt_root")
    assert prepare_source.index("INCIDENT_PRECONDITION") < prepare_source.index("TARGET_DIRECTORY")
    assert "suffix = ATTEMPT_ID[:16]" in prepare_source


@pytest.mark.parametrize(
    "appeared",
    ["handoff", "failed-retired"],
)
def test_prewrite_fence_rejects_new_historical_names(
    v4, tmp_path, appeared,
):
    root = tmp_path / "batch"
    _mkdir(root)
    retired = root / "old.lock.retired-v3-test"
    incident = v4.seal({
        "attempt_id": v4.ATTEMPT_ID,
        "failed_attempt": {
            "restored_old_locks": [{
                "failed_retired_path": str(retired),
            }],
        },
    })
    lease = object.__new__(v4.AtomicSwitchLease)
    object.__setattr__(lease, "_root", root)
    object.__setattr__(lease, "_locks", [None] * 9)
    object.__setattr__(lease, "_incident_precondition", incident)
    object.__setattr__(
        lease, "_incident_external_pin", incident["record_sha256"]
    )
    path = root / v4.FAILED_V3_HANDOFF if appeared == "handoff" else retired
    _write(path, b"appeared\n")
    with pytest.raises(
        v4.AdaptiveSwitchEvidenceV4Error,
        match="terminal/retired name appeared",
    ):
        lease._lightweight_incident_prewrite_fence()


def test_public_api_exposes_incident_bound_contract(v4):
    assert "build_incident_precondition" in v4.__all__
    assert "ATTEMPT_ID" in v4.__all__
    verify = inspect.signature(v4.verify_committed_handoff)
    assert "expected_attempt_id" in verify.parameters
    assert "expected_incident_precondition_sha256" in verify.parameters
    rollback = inspect.signature(v4.rollback_committed_handoff)
    assert "expected_attempt_id" in rollback.parameters
    assert "expected_incident_precondition_sha256" in rollback.parameters


@pytest.mark.parametrize(
    "api_name",
    ["verify_committed_handoff", "rollback_committed_handoff"],
)
def test_public_apis_reject_wrong_production_path_or_pin_before_io(
    v4, tmp_path, monkeypatch, api_name,
):
    def forbidden_read(*args, **kwargs):
        raise AssertionError("public API performed I/O before fixed-pin checks")

    monkeypatch.setattr(v4, "_stable_owned_json", forbidden_read)
    api = getattr(v4, api_name)
    base_kwargs = {
        "expected_batch_commit_sha256": _sha("commit"),
        "expected_batch_manifest_sha256":
            v4.EXPECTED_BATCH_MANIFEST_SHA256,
        "expected_attempt_id": v4.ATTEMPT_ID,
        "expected_incident_precondition_sha256": _sha("incident"),
    }
    if api_name == "rollback_committed_handoff":
        base_kwargs.update({
            "expected_switch_record": {},
            "quiescence_records": [],
        })
    cases = [
        (
            v4.EXPECTED_BATCH_ROOT / v4.HANDOFF_COMMIT,
            _sha("wrong-switch"),
        ),
        (
            tmp_path / "wrong-90-handoff.commit.json",
            v4.EXPECTED_SWITCH_EVIDENCE_SHA256,
        ),
    ]
    for path, switch_pin in cases:
        with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
            api(
                path,
                expected_switch_evidence_sha256=switch_pin,
                **base_kwargs,
            )


def test_incident_file_requires_owned_0600_and_calls_nested_validator(
    v4, tmp_path, monkeypatch,
):
    root = tmp_path / "batch"
    _mkdir(root)
    monkeypatch.setattr(v4, "EXPECTED_BATCH_ROOT", root)
    _mkdir(root / v4.ATTEMPT_ROOT)
    policy = v4.base._observation_policy(
        86400.0, [1.0, 2.0, 3.0, 4.0]
    )
    record = v4.seal({
        "schema_version": 4,
        "kind": "paper400-dic5-adaptive-incident-precondition-v4",
        "gate": v4.GATE,
        "attempt_id": v4.ATTEMPT_ID,
        "fixed_attempt_namespace": v4.ATTEMPT_ROOT.as_posix(),
        "test_only": True,
        "production_eligible": False,
        "authenticated": False,
        "launch_authorized": False,
        "scientific_claim": False,
        "batch_root": str(root),
        "batch_root_identity": v4.base._root_identity(root),
        "batch_manifest_sha256": v4.EXPECTED_BATCH_MANIFEST_SHA256,
        "switch_evidence_sha256": v4.EXPECTED_SWITCH_EVIDENCE_SHA256,
        "switch_observation_policy": policy,
        "hard_evidence_sha256s":
            list(v4.EXPECTED_HARD_EVIDENCE_SHA256S),
        "failed_attempt": {},
        "fresh_old_lanes": [],
        "target_roots": [{} for _ in v4.TARGET_KEYS],
        "target_key_order": [
            {"lane_index": lane, "descendant_index": descendant}
            for lane, descendant in v4.TARGET_KEYS
        ],
        "readonly_precondition": {},
        "source_binding": v4._v4_source_binding(),
        "claim_scope": {},
    })
    path = root / v4.INCIDENT_PRECONDITION
    _write(path, v4.canonical_bytes(record) + b"\n")
    calls = []
    monkeypatch.setattr(
        v4, "_validate_incident_nested",
        lambda checked_root, checked_record:
            calls.append((checked_root, checked_record["record_sha256"])),
    )
    assert v4._validate_incident_file(
        root, record["record_sha256"]
    )["record_sha256"] == record["record_sha256"]
    assert calls == [(root, record["record_sha256"])]
    path.chmod(0o644)
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._validate_incident_file(root, record["record_sha256"])


def test_historical_source_helper_is_named_v3_and_never_executes_it(v4):
    assert hasattr(v4, "_expected_failed_v3_source_binding")
    assert not hasattr(v4, "_expected_failed_v4_source_binding")
    historical = v4._expected_failed_v3_source_binding()
    assert historical["sources"][0]["sha256"] == v4.FAILED_V3_SOURCE_SHA256
    assert all(
        item["role"] != "adaptive_switch_evidence_v3_execution_base_source"
        for item in v4._v4_source_binding()["sources"]
    )


def test_module_import_captures_historical_sources_without_exact_exec(
    monkeypatch,
):
    compiled_paths = []
    real_compile = builtins.compile

    def audited_compile(*args, **kwargs):
        if len(args) >= 2:
            compiled_paths.append(str(args[1]))
        return real_compile(*args, **kwargs)

    monkeypatch.setattr(builtins, "compile", audited_compile)
    module = _load_module()
    assert str(module.FIXED_REPLAY_V3_SOURCE) not in compiled_paths
    assert str((PROJECT / module.BASE_RELATIVE).resolve()) in compiled_paths
    assert not hasattr(module, "_FIXED_REPLAY_READONLY")
    assert [
        hashlib.sha256(payload).hexdigest()
        for payload in module._FIXED_REPLAY_SOURCE_PAYLOADS
    ] == [
        module.FAILED_V3_SOURCE_SHA256,
        module.EXPECTED_V2_SOURCE_SHA256,
        module.FIXED_REPLAY_OVERLAY_SOURCE_SHA256,
    ]


def test_real_failed_v3_incident_is_readonly_if_available(v4):
    root = v4.EXPECTED_BATCH_ROOT
    if not root.is_dir():
        pytest.skip("production incident batch is not mounted")
    try:
        locks, _ = v4.base._acquire_all_locks(root)
    except BlockingIOError:
        pytest.skip("production old-batch locks are busy")
    try:
        before = {
            relative: (root / relative).lstat()
            for relative in (
                v4.FAILED_V3_INTENT, v4.FAILED_V3_PREPARED,
                v4.FAILED_V3_TARGET_DIRECTORY,
                v4.FAILED_V3_STARTED_DIRECTORY,
                v4.FAILED_V3_QUIESCENCE_DIRECTORY,
            )
        }
        record = v4._validate_failed_v3_incident_locked(root, locks)
        after = {
            relative: (root / relative).lstat()
            for relative in before
        }
        assert record["historical_prepared_reuse_forbidden"] is True
        assert all(
            (before[key].st_dev, before[key].st_ino, before[key].st_mtime_ns,
             before[key].st_ctime_ns)
            == (after[key].st_dev, after[key].st_ino, after[key].st_mtime_ns,
                after[key].st_ctime_ns)
            for key in before
        )
        assert not (root / v4.ATTEMPT_ROOT).exists()
    finally:
        for held in reversed(locks):
            held.close()

def test_old_proof_replay_and_post_fences_do_not_rehash(
    v4, tmp_path, monkeypatch,
):
    batch = tmp_path / "batch-no-rehash"
    _mkdir(batch)
    active_records = {}
    checkpoint_records = {}
    snapshots = []
    switch_lanes = []

    class FixedEnvironment:
        def __enter__(self):
            return None

        def __exit__(self, *args):
            return None

    class Controller:
        @staticmethod
        def _pid_identity(pid, ticks):
            assert type(pid) is int and type(ticks) is int
            return False

        @staticmethod
        def _generation_numbers(runtime_root):
            assert runtime_root.name == "dmtcp"
            return [0]

        @staticmethod
        def _claim_without_commit(generation_dir):
            assert generation_dir.name == "000000"
            return None

        @staticmethod
        def _active_commit(generation_dir, generation):
            assert generation == 0
            return dict(active_records[str(generation_dir)])

        @staticmethod
        def _checkpoint_commit(generation_dir, generation):
            assert generation == 0
            return dict(checkpoint_records[str(generation_dir)])

        @staticmethod
        def stable_file_record(*args, **kwargs):
            raise AssertionError("old proof stable_file_record rehash")

    class Child:
        RUNTIME_ROOT = Path("runtime/dmtcp")
        TERMINAL_CLAIM = Path("state/30-terminal-claim.json")
        FINAL_COMMIT = Path("state/40-final.json")
        controller = Controller()

        @staticmethod
        def _fixed_environment():
            return FixedEnvironment()

    for lane in range(v4.LANE_COUNT):
        lane_root = batch / "lanes" / f"lane-{lane}"
        generation_dir = (
            lane_root / Child.RUNTIME_ROOT / "generations/000000"
        )
        generation_dir.mkdir(parents=True, mode=0o700)
        proof = lane_root / Child.RUNTIME_ROOT / "proof.drat"
        _write(proof, f"proof-{lane}".encode("ascii"))
        identity = v4.base._stat_identity(proof.lstat())
        proof_sha = _sha(f"fresh-v2-authenticated-proof-{lane}")
        active_sha = _sha(f"active-{lane}")
        checkpoint_sha = _sha(f"checkpoint-{lane}")
        chain_sha = _sha(f"chain-{lane}")
        pid = 1000 + lane
        ticks = 2000 + lane
        prefix = {
            "bytes": identity["bytes"],
            "mode": 0o600,
            "path": "proof.drat",
            "path_kind": "root_relative",
            "sha256": proof_sha,
        }
        physical = {
            "bytes": identity["bytes"],
            "device": identity["device"],
            "file_sha256": proof_sha,
            "inode": identity["inode"],
            "links": identity["links"],
            "mode": identity["mode"],
            "relative_path": "runtime/dmtcp/proof.drat",
            "role": "raw-binary-drat",
            "uid": identity["uid"],
        }
        generation = {
            "generation": 0,
            "pid": pid,
            "proc_start_ticks": ticks,
            "active_kind": "start.commit",
            "active_manifest_sha256": active_sha,
            "checkpoint_manifest_sha256": checkpoint_sha,
            "pid_identity_alive": False,
        }
        chain = {
            "state": "CHECKPOINTED",
            "record_sha256": chain_sha,
            "generations": [generation],
            "latest_checkpoint_sha256": checkpoint_sha,
            "latest_proof_prefix": prefix,
            "latest_proof_physical": physical,
        }
        inspection = {
            "state": "CHECKPOINTED",
            "hash_verification_requested": True,
            "generations": [{
                "generation": 0,
                "pid_identity_alive": False,
                "checkpoint_hashes_valid": True,
                "active_manifest_sha256": active_sha,
                "checkpoint_manifest_sha256": checkpoint_sha,
            }],
        }
        snapshots.append({"chain": chain, "inspection": inspection})
        switch_lanes.append({
            "lane_index": lane,
            "global_leaf_index": lane * 64,
            "transport_chain_sha256": chain_sha,
            "hard_evidence_sha256":
                v4.EXPECTED_HARD_EVIDENCE_SHA256S[lane],
            "checkpoint_proof_prefix": prefix,
            "checkpoint_proof_physical": physical,
            "solver_stopped": True,
            "terminal_claimed": False,
            "terminal_committed": False,
        })
        active_records[str(generation_dir)] = {
            "kind": "start.commit",
            "self_sha256": active_sha,
            "pid": pid,
            "proc_start_ticks": ticks,
        }
        checkpoint_records[str(generation_dir)] = {
            "kind": "checkpoint.commit",
            "self_sha256": checkpoint_sha,
            "single_writer_stopped": True,
            "proof_prefix": prefix,
        }

    monkeypatch.setattr(v4, "EXPECTED_OLD_LANE_TUPLES", tuple(
        (
            item["global_leaf_index"],
            item["transport_chain_sha256"],
            item["checkpoint_proof_prefix"]["sha256"],
            item["checkpoint_proof_prefix"]["bytes"],
            item["hard_evidence_sha256"],
        )
        for item in switch_lanes
    ))
    monkeypatch.setattr(
        v4, "EXPECTED_OLD_PROOF_PHYSICAL_TUPLES", tuple(
            tuple(
                item["checkpoint_proof_physical"][field]
                for field in (
                    "device", "inode", "uid", "mode", "links", "bytes",
                )
            )
            for item in switch_lanes
        ),
    )

    def forbidden_hash(*args, **kwargs):
        raise AssertionError("old proof content was hashed after fresh v2 replay")

    monkeypatch.setattr(v4, "_stream_hash_size_identity", forbidden_hash)
    monkeypatch.setattr(v4, "_direct_controller_inspect", forbidden_hash)
    observations = v4._fresh_old_lane_observations(
        batch, {"lanes": snapshots}, {"lanes": switch_lanes}, Child(),
    )
    assert [item["proof_sha256"] for item in observations] == [
        item["checkpoint_proof_prefix"]["sha256"]
        for item in switch_lanes
    ]
    forged_switch_lanes = copy.deepcopy(switch_lanes)
    forged_switch_lanes[0]["transport_chain_sha256"] = _sha(
        "forged-old-transport"
    )
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._fresh_old_lane_observations(
            batch,
            {"lanes": snapshots},
            {"lanes": forged_switch_lanes},
            Child(),
        )

    forged_snapshots = copy.deepcopy(snapshots)
    forged_physical_lanes = copy.deepcopy(switch_lanes)
    forged_physical_lanes[0]["checkpoint_proof_physical"]["inode"] += 1
    forged_snapshots[0]["chain"]["latest_proof_physical"]["inode"] += 1
    with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
        v4._fresh_old_lane_observations(
            batch,
            {"lanes": forged_snapshots},
            {"lanes": forged_physical_lanes},
            Child(),
        )

    incident = {"fresh_old_lanes": observations}
    # This models all repeated old-state fences in prepare, target replay,
    # outer-lock adoption, eight post-start fences, and final commit.
    for _ in range(1 + 8 + 1 + 8 + 1):
        v4._lightweight_old_checkpoint_fence(
            batch, {"lanes": snapshots}, incident, Child(),
        )

    fresh_source = inspect.getsource(v4._fresh_old_lane_observations)
    fence_source = inspect.getsource(v4._lightweight_old_checkpoint_fence)
    post_source = inspect.getsource(
        v4.AtomicSwitchLease._old_post_retirement_fence
    )
    assert "_stream_hash_size_identity" not in fresh_source
    assert "_stream_hash_size_identity" not in fence_source
    assert "stable_file_record" not in fence_source
    assert "_direct_controller_inspect" not in fence_source
    assert "_lightweight_old_checkpoint_fence" in post_source

    proof0 = batch / "lanes/lane-0/runtime/dmtcp/proof.drat"
    proof0.chmod(0o400)
    with pytest.raises(
        v4.AdaptiveSwitchEvidenceV4Error,
        match="old stopped checkpoint changed",
    ):
        v4._lightweight_old_checkpoint_fence(
            batch, {"lanes": snapshots}, incident, Child(),
        )


def _make_target_cover(v4, tmp_path):
    batch = tmp_path / "batch"
    roots_parent = tmp_path / "new-roots"
    _mkdir(batch)
    _mkdir(roots_parent)
    switch = _switch(v4)
    targets = []
    fds = []
    for lane, descendant in v4.TARGET_KEYS:
        target, fd = _make_static_target(
            v4,
            roots_parent,
            batch,
            lane=lane,
            descendant=descendant,
        )
        targets.append(target)
        fds.append(fd)
    observations = v4._validate_unstarted_target_roots(
        batch, targets, fds, switch
    )
    return (
        batch,
        targets,
        fds,
        observations,
        copy.deepcopy(switch["lanes"]),
        switch["observation_policy"],
    )


def _validate_target_cover(v4, batch, observations, old_lanes, policy):
    v4._validate_incident_target_semantics(
        batch,
        observations,
        old_lanes,
        list(v4.EXPECTED_HARD_EVIDENCE_SHA256S),
        policy,
    )


def test_incident_accepts_runner_compact_policy_bound_to_full_switch(
    v4, tmp_path,
):
    batch, targets, fds, observations, old_lanes, policy = (
        _make_target_cover(v4, tmp_path)
    )
    del targets
    try:
        assert set(policy) == {
            "annotation_source", "elapsed_seconds_by_lane",
            "hardness_only", "status", "timed_out", "timeout_seconds",
        }
        _validate_target_cover(
            v4, batch, observations, old_lanes, policy
        )
    finally:
        for fd in fds:
            os.close(fd)


def test_incident_rejects_noncanonical_full_switch_policy(v4, tmp_path):
    batch, targets, fds, observations, old_lanes, policy = (
        _make_target_cover(v4, tmp_path)
    )
    del targets
    try:
        policy = copy.deepcopy(policy)
        policy["status"] = "SAT"
        with pytest.raises(
            v4.AdaptiveSwitchEvidenceV4Error,
            match="switch observation policy is noncanonical",
        ):
            _validate_target_cover(
                v4, batch, observations, old_lanes, policy
            )
    finally:
        for fd in fds:
            os.close(fd)


def test_incident_target_rechecks_actual_material_bytes(v4, tmp_path):
    batch, targets, fds, observations, old_lanes, policy = (
        _make_target_cover(v4, tmp_path)
    )
    try:
        _validate_target_cover(
            v4, batch, observations, old_lanes, policy
        )
        _write(
            targets[0] / "static/descendant.cnf",
            b"p cnf 1 1\n-1 0\n",
        )
        with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
            _validate_target_cover(
                v4, batch, observations, old_lanes, policy
            )
    finally:
        for fd in fds:
            os.close(fd)


@pytest.mark.parametrize(
    "tamper",
    ["material-declaration", "claim-authority", "sibling-selection"],
)
def test_incident_target_rejects_self_resealed_static_semantic_tamper(
    v4, tmp_path, tamper,
):
    batch, targets, fds, observations, old_lanes, policy = (
        _make_target_cover(v4, tmp_path)
    )
    try:
        index = (
            v4.TARGET_KEYS.index((0, 1))
            if tamper == "sibling-selection" else 0
        )

        def mutate(record):
            if tamper == "material-declaration":
                record["material_files"]["descendant_cnf"][
                    "sha256"
                ] = _sha("forged-declared-cnf")
            elif tamper == "claim-authority":
                record["claim_scope"][
                    "checkpoint_proves_leaf_unsat"
                ] = True
            else:
                record["selection"]["candidate_variables"] = [18]
                record["selection"][
                    "relative_assignment_literals"
                ] = [-18]

        _rewrite_static(
            v4, targets[index], observations[index], mutate
        )
        if tamper == "sibling-selection":
            observations[index]["candidate_variables"] = [18]
            observations[index][
                "relative_assignment_literals"
            ] = [-18]
        with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
            _validate_target_cover(
                v4, batch, observations, old_lanes, policy
            )
    finally:
        for fd in fds:
            os.close(fd)


@pytest.mark.parametrize(
    "field",
    ["global_leaf_index", "hard_evidence_sha256"],
)
def test_incident_target_is_fixed_to_old_lane_and_hard_pin(
    v4, tmp_path, field,
):
    batch, targets, fds, observations, old_lanes, policy = (
        _make_target_cover(v4, tmp_path)
    )
    del targets
    try:
        if field == "global_leaf_index":
            observations[0][field] += 1
        else:
            observations[0][field] = _sha("forged-hard-pin")
        with pytest.raises(v4.AdaptiveSwitchEvidenceV4Error):
            _validate_target_cover(
                v4, batch, observations, old_lanes, policy
            )
    finally:
        for fd in fds:
            os.close(fd)


@pytest.mark.parametrize(
    "mutation",
    [
        "batch-manifest", "switch-evidence", "source-binding",
        "root-link-policy", "claim-scope",
    ],
)
def test_resealed_committed_record_cannot_replace_fixed_authority(
    v4, tmp_path, monkeypatch, mutation,
):
    root = tmp_path / "batch"
    _mkdir(root)
    monkeypatch.setattr(v4, "EXPECTED_BATCH_ROOT", root)
    incident_pin = _sha("incident")
    record = {
        "schema_version": 4,
        "kind": v4.HANDOFF_KIND,
        "gate": v4.GATE,
        "test_only": True,
        "production_eligible": False,
        "authenticated": False,
        "launch_authorized": False,
        "scientific_claim": False,
        "historical_atomic_handoff_observed": True,
        "batch_root": str(root),
        "batch_root_identity": v4.base._root_identity(root),
        "batch_manifest_sha256": v4.EXPECTED_BATCH_MANIFEST_SHA256,
        "switch_evidence_sha256": v4.EXPECTED_SWITCH_EVIDENCE_SHA256,
        "switch_observation_policy":
            _switch(v4)["observation_policy"],
        "prepared_retirement_sha256": _sha("prepared"),
        "retired_locks": [],
        "root_bindings": [],
        "fence_sha256s": [],
        "cohort_policy": {},
        "source_binding": v4._v4_source_binding(),
        "root_link_policy": {
            "relative_path": "state/15-batch-handoff.json",
            "publish": "o-excl-canonical-json-fsync-v1",
            "repair_only_from_externally_pinned_batch_commit": True,
        },
        "claim_scope": {
            "old_transport_durably_retired_before_first_new_start": True,
            "eight_new_processes_observed_started": True,
            "four_new_processes_checkpointed_at_commit": True,
            "four_new_processes_observed_alive_at_commit": True,
            "max_live_workers": v4.MAX_LIVE_WORKERS,
            "serialized_record_can_authorize_launch": False,
            "serialized_record_can_authenticate_unsat": False,
        },
        **v4._attempt_binding(incident_pin),
    }
    if mutation == "batch-manifest":
        record["batch_manifest_sha256"] = _sha("forged-batch")
    elif mutation == "switch-evidence":
        record["switch_evidence_sha256"] = _sha("forged-switch")
    elif mutation == "source-binding":
        record["source_binding"] = {}
    elif mutation == "root-link-policy":
        record["root_link_policy"]["relative_path"] = "forged.json"
    else:
        record["claim_scope"][
            "old_transport_durably_retired_before_first_new_start"
        ] = False
    with pytest.raises(
        v4.AdaptiveSwitchEvidenceV4Error,
        match="handoff authority/hash mismatch",
    ):
        v4._validate_committed(_reseal(v4, record))


@pytest.mark.parametrize(
    "field",
    [
        "batch_root", "batch_root_identity", "batch_manifest_sha256",
        "switch_evidence_sha256", "switch_observation_policy",
        "source_binding",
    ],
)
def test_commit_is_directly_bound_to_incident_top_level(
    v4, tmp_path, monkeypatch, field,
):
    root = tmp_path / "batch"
    _mkdir(root)
    incident_pin = _sha("incident")
    common = {
        "batch_root": str(root),
        "batch_root_identity": v4.base._root_identity(root),
        "batch_manifest_sha256": _sha("batch"),
        "switch_evidence_sha256": _sha("switch"),
        "switch_observation_policy":
            _switch(v4)["observation_policy"],
        "source_binding": {"source": _sha("source")},
    }
    record = {
        **copy.deepcopy(common),
        "incident_precondition_sha256": incident_pin,
        "root_bindings": [{} for _ in v4.TARGET_KEYS],
    }
    incident = copy.deepcopy(common)
    if field == "batch_root":
        incident[field] = str(tmp_path / "forged-batch")
    elif field in {"batch_manifest_sha256", "switch_evidence_sha256"}:
        incident[field] = _sha(f"forged-{field}")
    elif field == "batch_root_identity":
        incident[field]["inode"] += 1
    elif field == "switch_observation_policy":
        incident[field]["timeout_seconds"] += 1.0
    else:
        incident[field] = {"source": _sha("forged-source")}
    monkeypatch.setattr(
        v4, "_verify_attempt_inventory", lambda *args, **kwargs: None
    )
    monkeypatch.setattr(
        v4, "_validate_incident_file", lambda *args, **kwargs: incident
    )
    monkeypatch.setattr(
        v4,
        "_read_handoff_journal",
        lambda *args, **kwargs: (_ for _ in ()).throw(
            AssertionError("journal read preceded commit/incident cross-check")
        ),
    )
    with pytest.raises(
        v4.AdaptiveSwitchEvidenceV4Error,
        match="handoff commit misses incident precondition",
    ):
        v4._verify_committed_journals(root, record)


@pytest.mark.parametrize(
    "field",
    [
        "global_leaf_index", "descendant_sha256",
        "overlay_manifest_sha256", "hard_evidence_sha256",
        "root_identity", "static_record_sha256",
        "outer_lock_identity",
    ],
)
def test_prepared_target_journal_is_directly_bound_to_incident_target(
    v4, tmp_path, monkeypatch, field,
):
    root = tmp_path / "batch"
    new_root = tmp_path / "new-root"
    _mkdir(root)
    _mkdir(new_root)
    root_identity = v4.base._root_identity(new_root)
    outer_identity = {"device": 1, "inode": 2}
    common = {
        "batch_root": str(root),
        "batch_root_identity": v4.base._root_identity(root),
        "batch_manifest_sha256": _sha("batch"),
        "switch_evidence_sha256": _sha("switch"),
        "switch_observation_policy":
            _switch(v4)["observation_policy"],
        "source_binding": {"source": _sha("source")},
    }
    incident_target = {
        "global_leaf_index": 0,
        "descendant_sha256": _sha("descendant"),
        "overlay_manifest_sha256": _sha("overlay"),
        "hard_evidence_sha256": _sha("hard"),
        "root_identity": root_identity,
        "static_record_sha256": _sha("static"),
        "outer_lock_identity": outer_identity,
    }
    if field in {"root_identity", "outer_lock_identity"}:
        incident_target[field] = copy.deepcopy(incident_target[field])
        incident_target[field]["inode"] += 1
    elif field == "global_leaf_index":
        incident_target[field] += 1
    else:
        incident_target[field] = _sha(f"forged-{field}")
    incident = v4.seal({
        **copy.deepcopy(common),
        "target_roots": [
            incident_target,
            *[{} for _ in range(v4.TARGET_COUNT - 1)],
        ],
    })
    incident_pin = incident["record_sha256"]
    binding = {
        "lane_index": 0,
        "descendant_index": 0,
        "global_leaf_index": 0,
        "descendant_sha256": _sha("descendant"),
        "permit_binding_sha256": _sha("permit"),
        "prepared_target_sha256": _sha("prepared-target"),
        "started_worker_journal_sha256": _sha("started"),
        "new_root_identity": root_identity,
        "new_pid": 123,
        "new_proc_start_ticks": 456,
    }
    target = {
        "lane_index": 0,
        "global_leaf_index": 0,
        "descendant_index": 0,
        "descendant_sha256": _sha("descendant"),
        "overlay_manifest_sha256": _sha("overlay"),
        "hard_evidence_sha256": _sha("hard"),
        "permit_binding_sha256": _sha("permit"),
        "new_root_identity": root_identity,
        "switch_evidence_sha256": common["switch_evidence_sha256"],
        "prepared_retirement_sha256": _sha("prepared"),
        "target_static_sha256": _sha("static"),
        "target_outer_lock_identity": outer_identity,
        "record_sha256": _sha("prepared-target"),
        **v4._attempt_binding(incident_pin),
    }
    record = {
        **copy.deepcopy(common),
        "incident_precondition_sha256": incident_pin,
        "prepared_retirement_sha256": _sha("prepared"),
        "root_bindings": [
            binding,
            *[
                {"lane_index": lane, "descendant_index": descendant}
                for lane, descendant in v4.TARGET_KEYS[1:]
            ],
        ],
    }
    monkeypatch.setattr(
        v4, "_verify_attempt_inventory", lambda *args, **kwargs: None
    )
    monkeypatch.setattr(
        v4, "_validate_incident_file", lambda *args, **kwargs: incident
    )

    def read_journal(path, *, expected_fields, expected_kind):
        del path, expected_fields
        if expected_kind == "paper400-adaptive-prepared-target-v4":
            return target
        return {}

    monkeypatch.setattr(v4, "_read_handoff_journal", read_journal)
    with pytest.raises(
        v4.AdaptiveSwitchEvidenceV4Error,
        match="prepared-target journal misses commit",
    ):
        v4._verify_committed_journals(root, record)


@pytest.mark.parametrize(
    "owner,field,bad_value",
    [
        ("intent", "test_only", False),
        ("intent", "production_eligible", True),
        ("prepared", "test_only", False),
        ("prepared", "production_eligible", True),
        ("intent", "retirement_complete", True),
        ("prepared", "retirement_complete", False),
        ("prepared", "old_runner_entrypoints_reachable", True),
        ("prepared", "scientific_claim", True),
    ],
)
def test_retirement_authority_flags_fail_closed(
    v4, tmp_path, monkeypatch, owner, field, bad_value,
):
    root = tmp_path / "batch"
    _mkdir(root)
    incident_pin = _sha("incident")
    manifest_pin = _sha("manifest")
    switch_pin = _sha("switch")
    intent_sha = _sha("intent")
    prepared_sha = _sha("prepared")
    source = v4._v4_source_binding()
    intent = {
        **v4._attempt_binding(incident_pin),
        "test_only": True,
        "production_eligible": False,
        "batch_root": str(root),
        "batch_manifest_sha256": manifest_pin,
        "switch_evidence_sha256": switch_pin,
        "target_journal_directory": str(root / v4.TARGET_DIRECTORY),
        "started_journal_directory": str(root / v4.STARTED_DIRECTORY),
        "quiescence_journal_directory":
            str(root / v4.QUIESCENCE_DIRECTORY),
        "retirement_complete": False,
        "source_binding": source,
        "lock_plan": [{} for _ in range(9)],
        "record_sha256": intent_sha,
    }
    retired = [{} for _ in range(9)]
    prepared = {
        **v4._attempt_binding(incident_pin),
        "test_only": True,
        "production_eligible": False,
        "scientific_claim": False,
        "batch_root": str(root),
        "batch_root_identity": v4.base._root_identity(root),
        "batch_manifest_sha256": manifest_pin,
        "switch_evidence_sha256": switch_pin,
        "retirement_intent_sha256": intent_sha,
        "retired_locks": retired,
        "retirement_complete": True,
        "old_runner_entrypoints_reachable": False,
        "source_binding": source,
        "record_sha256": prepared_sha,
    }
    commit = {
        "batch_manifest_sha256": manifest_pin,
        "switch_evidence_sha256": switch_pin,
        "prepared_retirement_sha256": prepared_sha,
        "retired_locks": retired,
    }
    selected = intent if owner == "intent" else prepared
    selected[field] = bad_value

    def read_journal(path, *, expected_fields, expected_kind):
        del expected_fields, expected_kind
        return intent if path == root / v4.RETIREMENT_INTENT else prepared

    monkeypatch.setattr(v4, "_read_handoff_journal", read_journal)
    with pytest.raises(
        v4.AdaptiveSwitchEvidenceV4Error,
        match="v4 retirement journal chain mismatch",
    ):
        v4._validate_retirement_chain(root, commit, incident_pin)

def test_runner_style_isolated_fixed_replay_bootstrap(v4):
    dependency_root = Path(
        "/root/qcode-stage3-distqldpc-lower-v1/qcode-discovery/.venv/"
        "lib/python3.12/site-packages"
    )
    strict_python = Path(
        "/root/qcode-stage3-distqldpc-lower-v1/qcode-discovery/.venv/bin/python"
    )
    if (
        not v4.EXPECTED_BATCH_ROOT.is_dir()
        or not dependency_root.is_dir()
        or not strict_python.is_file()
    ):
        pytest.skip("production replay inputs are not mounted")
    probe = f"""
import importlib.util
import json
import sys
from pathlib import Path
project = Path({str(PROJECT)!r})
dependency_root = Path({str(dependency_root)!r})
sys.path[:0] = [str(project), str(dependency_root)]
source = project / "scripts/paper400_dic5_adaptive_switch_evidence_v4.py"
spec = importlib.util.spec_from_file_location(
    "scripts.paper400_dic5_adaptive_switch_evidence_v4", source
)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
discovery = module.base._discover_sources(
    module.EXPECTED_BATCH_ROOT,
    expected_batch_manifest_sha256=module.EXPECTED_BATCH_MANIFEST_SHA256,
)
with module._LOAD_GUARD:
    fixed_replay_readonly = module._load_fixed_replay_readonly()
    _, _, legacy = fixed_replay_readonly.load_legacy_exact(discovery)
    _, overlay_record, overlay = (
        fixed_replay_readonly.load_overlay_exact()
    )
binding = module._validate_fixed_dynamic_source_binding(
    discovery, legacy, overlay_record, overlay
)
print(json.dumps({{
    "attempt_id": module.ATTEMPT_ID,
    "dynamic": binding["source_binding_sha256"],
    "legacy": len(legacy),
    "overlay": len(overlay),
    "overlay_execution": overlay_record["execution"],
    "overlay_sha256": overlay_record["sha256"],
}}, sort_keys=True))
"""
    completed = subprocess.run(
        [str(strict_python), "-I", "-S", "-B", "-c", probe],
        check=False, capture_output=True, text=True, timeout=120,
        env={"LANG": "C", "LC_ALL": "C", "TZ": "UTC"},
    )
    assert completed.returncode == 0, completed.stderr
    observed = json.loads(completed.stdout)
    assert observed == {
        "attempt_id": v4.ATTEMPT_ID,
        "dynamic": v4.FIXED_REPLAY_DYNAMIC_SOURCE_BINDING_SHA256,
        "legacy": 25,
        "overlay": 19,
        "overlay_execution": "compile-exact-source-bytes-v3",
        "overlay_sha256": v4.FIXED_REPLAY_OVERLAY_SOURCE_SHA256,
    }


def test_fixed_bundle_validates_provenance_before_snapshot_under_v4_guard(
    v4, monkeypatch,
):
    calls = []

    class Guard:
        entered = False

        def __enter__(self):
            assert self.entered is False
            self.entered = True
            calls.append("guard-enter")
            return self

        def __exit__(self, *args):
            self.entered = False
            calls.append("guard-exit")
            return False

    guard = Guard()
    coordinator = object()
    child = object()
    overlay = object()
    legacy_executed = [{"kind": "historical-legacy"}]
    overlay_executed = [{"kind": "historical-overlay"}]
    overlay_record = {
        "role": "adaptive_leaf_overlay_v2_source",
        "relative_path": v4.OVERLAY_RELATIVE.as_posix(),
        "sha256": v4.FIXED_REPLAY_OVERLAY_SOURCE_SHA256,
        "bytes": v4.FIXED_REPLAY_OVERLAY_SOURCE_BYTES,
        "execution": "compile-exact-source-bytes-v3",
    }

    class HistoricalLoaders:
        @staticmethod
        def load_legacy_exact(discovery):
            assert discovery == {"fixture": True}
            assert guard.entered is True
            calls.append("historical-legacy")
            return coordinator, child, legacy_executed

        @staticmethod
        def load_overlay_exact():
            assert guard.entered is True
            calls.append("historical-overlay")
            return overlay, overlay_record, overlay_executed

    binding = {"fixed": True}
    snapshot = {"snapshot": True}
    record = {
        "source_binding": binding,
        "record_sha256": v4.EXPECTED_SWITCH_EVIDENCE_SHA256,
    }
    monkeypatch.setattr(v4, "_LOAD_GUARD", guard)

    def load_historical_readonly():
        assert guard.entered is True
        calls.append("historical-bootstrap")
        return HistoricalLoaders()

    monkeypatch.setattr(
        v4, "_load_fixed_replay_readonly", load_historical_readonly
    )
    monkeypatch.setattr(
        v4, "_fixed_replay_sources_unchanged",
        lambda: calls.append("source-pins"),
    )

    def validate_binding(*args):
        assert guard.entered is False
        assert args == (
            {"fixture": True}, legacy_executed,
            overlay_record, overlay_executed,
        )
        calls.append("dynamic-binding")
        return binding

    def snapshot_locked(root, observed_coordinator, observed_child):
        assert root == Path("/fixed-root")
        assert observed_coordinator is coordinator
        assert observed_child is child
        calls.append("snapshot")
        return snapshot

    def build_record(
        root, observed_snapshot, discovery, observed_overlay,
        observed_legacy, observed_overlay_record, observed_overlay_executed,
        **policy,
    ):
        assert root == Path("/fixed-root")
        assert observed_snapshot is snapshot
        assert discovery == {"fixture": True}
        assert observed_overlay is overlay
        assert observed_legacy == legacy_executed
        assert observed_overlay_record == overlay_record
        assert observed_overlay_executed == overlay_executed
        assert policy == {
            "timeout_seconds": 10.0,
            "elapsed_seconds_by_lane": [1.0, 2.0, 3.0, 4.0],
        }
        calls.append("build-record")
        return record

    monkeypatch.setattr(
        v4, "_validate_fixed_dynamic_source_binding", validate_binding
    )
    monkeypatch.setattr(v4.base, "_snapshot_locked", snapshot_locked)
    monkeypatch.setattr(v4.base, "_build_record", build_record)
    monkeypatch.setattr(
        v4, "validate_switch_record_structure",
        lambda value: calls.append(("validate-record", value)),
    )
    bundle = v4._load_fixed_replay_bundle(
        Path("/fixed-root"), {"fixture": True},
        timeout_seconds=10.0,
        elapsed_seconds_by_lane=[1.0, 2.0, 3.0, 4.0],
    )
    assert bundle.record == record
    assert calls == [
        "source-pins", "guard-enter", "historical-bootstrap",
        "historical-legacy", "historical-overlay", "guard-exit",
        "dynamic-binding", "snapshot", "build-record",
        ("validate-record", record),
    ]


def test_fixed_and_current_bundle_consumers_do_not_cross(v4):
    current = inspect.getsource(v4._load_current_science_bundle)
    enter = inspect.getsource(v4._enter)
    lease_init = inspect.getsource(v4.AtomicSwitchLease.__init__)
    verify_target = inspect.getsource(v4.AtomicSwitchLease.verify_target)
    base_verify_target = inspect.getsource(v4.base.AtomicSwitchLease.verify_target)
    verify_worker = inspect.getsource(
        v4.AtomicSwitchLease._verify_quiescent_worker
    )
    prewrite = inspect.getsource(
        v4.AtomicSwitchLease._lightweight_incident_prewrite_fence
    )
    post_retirement = inspect.getsource(
        v4.AtomicSwitchLease._old_post_retirement_fence
    )
    prepare = inspect.getsource(v4.AtomicSwitchLease.prepare_retirement)
    fresh = inspect.getsource(v4.AtomicSwitchLease._fresh_record)
    rollback = inspect.getsource(
        v4.AtomicSwitchLease.rollback_after_new_quiescent
    )
    restored = inspect.getsource(v4._fresh_restored_old_checkpoint)
    committed_rollback = inspect.getsource(v4.rollback_committed_handoff)
    assert "_load_legacy_exact(discovery)" in current
    assert "_load_overlay_exact()" in current
    assert "fixed_replay_bundle = _load_fixed_replay_bundle(" in enter
    assert "current_science_bundle = _load_current_science_bundle(" in enter
    assert "snapshot=fixed_replay_bundle.snapshot" in enter
    assert "child=fixed_replay_bundle.child" in enter
    assert "science.coordinator, science.child, science.overlay" in enter
    assert "self._child is not current_science_bundle.child" in lease_init
    assert "self._overlay is not current_science_bundle.overlay" in lease_init
    assert "super().verify_target(" in verify_target
    assert "self._overlay" in base_verify_target
    assert "_direct_controller_inspect(self._child, root)" in verify_worker
    assert "self._fixed_replay_bundle.snapshot" in prewrite
    assert "self._fixed_replay_bundle.child" in prewrite
    assert "self._fixed_replay_bundle.snapshot" in post_retirement
    assert "self._fixed_replay_bundle.child" in post_retirement
    assert "self._fixed_replay_bundle.snapshot" in prepare
    assert "self._fixed_replay_bundle.child" in prepare
    assert "fixed = self._fixed_replay_bundle" in fresh
    assert "fixed = self._fixed_replay_bundle" in rollback
    assert "fixed = _load_fixed_replay_bundle(" in restored
    assert "_, child, _ = _load_legacy_exact(discovery)" in committed_rollback
    assert "_direct_controller_inspect(child, target_root)" in committed_rollback
