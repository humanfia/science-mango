from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from evaluation.selection_ledger import validate_selection_ledger
import humanize.stage2_ledger_recovery as recovery
from humanize.stage2_ledger_recovery import (
    RecoveryError,
    canonical_sha256,
    generic_genesis_sha256,
    make_completed_ack,
    rebind_selection_prefix,
    validate_patched_scheduler_migration,
    install_patched_scheduler_migration,
    rollback_patched_scheduler_migration,
    validate_patched_scheduler_install,
)


def _scan(identity: str, start: int, next_index: int) -> dict:
    payload = {
        "schema_version": 1,
        "gate": "qldpc-stage2-ranked-scan",
        "snapshot_identity_sha256": identity,
        "start_index": start,
        "next_index": next_index,
        "snapshot_rows": 4,
        "eligible_rows": 4,
        "selection_exhausted": next_index == 4,
    }
    return {**payload, "scan_sha256": canonical_sha256(payload)}


def _page(
    binding: str,
    identity: str,
    sequence: int,
    previous: str,
    digest: str,
) -> dict:
    payload = {
        "binding_sha256": binding,
        "snapshot_identity_sha256": identity,
        "page_sequence": sequence,
        "previous_ack_sha256": previous,
        "start_index": sequence,
        "next_index": sequence + 1,
        "selected_digests": [digest],
        "scan_evidence": _scan(identity, sequence, sequence + 1),
    }
    return {**payload, "page_sha256": canonical_sha256(payload)}


def _two_page_core() -> dict:
    binding = "a" * 64
    identity = "b" * 64
    previous = generic_genesis_sha256(binding, identity, 4, 4)
    chain = []
    for sequence, digest in enumerate(("1" * 64, "2" * 64)):
        page = _page(binding, identity, sequence, previous, digest)
        ack = make_completed_ack(
            page,
            sequence=sequence,
            previous_ack_sha256=previous,
        )
        chain.append(ack)
        previous = ack["ack_sha256"]
    pending = _page(binding, identity, 2, previous, "3" * 64)
    return {
        "schema_version": 2,
        "gate": "qldpc-stage2-selection-ledger",
        "binding_sha256": binding,
        "snapshot_identity_sha256": identity,
        "snapshot_rows": 4,
        "eligible_rows": 4,
        "generation": 0,
        "generation_history": [],
        "cursor": 2,
        "committed_digests": ["1" * 64, "2" * 64],
        "completed_pages": 2,
        "ack_chain": chain,
        "genesis_sha256": generic_genesis_sha256(binding, identity, 4, 4),
        "last_ack_sha256": previous,
        "pending": pending,
        "deferred_pages": [],
    }


def test_rebind_selection_prefix_resigns_two_pages_and_pending() -> None:
    core = _two_page_core()
    rebound, mapping = rebind_selection_prefix(
        core,
        binding_sha256="c" * 64,
        identity_sha256="d" * 64,
        top=2,
        completed_pages=2,
        include_pending=True,
        acknowledged_at="2026-08-17T00:00:00+00:00",
    )

    validate_selection_ledger(
        rebound,
        binding_sha256="c" * 64,
        snapshot_identity_sha256_value="d" * 64,
        snapshot_rows=4,
        eligible_rows=4,
    )
    assert len(mapping) == 3
    assert mapping[-1]["pending"] is True
    assert rebound["cursor"] == 2
    assert rebound["pending"]["next_index"] == 3
    assert rebound["last_ack_sha256"] != core["last_ack_sha256"]
    assert rebound["ack_chain"][0]["page"]["scan_evidence"][
        "snapshot_identity_sha256"
    ] == "d" * 64


def test_rebound_ledger_tamper_fails_closed() -> None:
    rebound, _ = rebind_selection_prefix(
        _two_page_core(),
        binding_sha256="c" * 64,
        identity_sha256="d" * 64,
        top=2,
        completed_pages=2,
        include_pending=True,
    )
    tampered = copy.deepcopy(rebound)
    tampered["ack_chain"][0]["page"]["selected_digests"][0] = "f" * 64
    with pytest.raises(ValueError):
        validate_selection_ledger(
            tampered,
            binding_sha256="c" * 64,
            snapshot_identity_sha256_value="d" * 64,
            snapshot_rows=4,
            eligible_rows=4,
        )


def test_source_cursor_tamper_fails_closed() -> None:
    core = _two_page_core()
    core["ack_chain"][1]["page"]["start_index"] = 0
    with pytest.raises(RecoveryError, match="source ACK 1"):
        rebind_selection_prefix(
            core,
            binding_sha256="c" * 64,
            identity_sha256="d" * 64,
            top=2,
            completed_pages=2,
        )


def test_public_validator_rejects_certificate_tamper_before_file_trust(
    tmp_path: Path,
) -> None:
    certificate = {
        "schema_version": 1,
        "gate": "qldpc-stage2-patched-identity-scheduler-migration-v1",
        "status": "PATCHED_IDENTITY_SCHEDULER_MIGRATION_VALIDATED",
        "reason": "SEALED_CORE_RECOVERY",
        "certificate_sha256": "0" * 64,
    }

@pytest.mark.parametrize(
    ("mutate", "expected_message"),
    [
        (
            lambda certificate: certificate["old_anchors"].__setitem__(
                "last_ack_sha256", "f" * 64,
            ),
            "compiled old anchors",
        ),
        (
            lambda certificate: certificate["validation"].__setitem__(
                "production_files_modified", True,
            ),
            "compiled old anchors",
        ),
    ],
)
def test_public_validator_rejects_self_resealed_compiled_claims(
    tmp_path: Path,
    mutate: object,
    expected_message: str,
) -> None:
    """An attacker cannot bless changed anchors by resealing both JSON files."""

    certificate_payload = {
        "schema_version": 1,
        "gate": recovery.MIGRATION_GATE,
        "status": "PATCHED_IDENTITY_SCHEDULER_MIGRATION_VALIDATED",
        "reason": recovery.RECOVERY_REASON,
        "created_at": "2026-08-17T00:00:00+00:00",
        "intended_output": str(tmp_path),
        "same_filesystem_as": str(tmp_path),
        "old_anchors": {
            "snapshot_sha256": recovery.EXPECTED["snapshot_sha256"],
            "offsets_sha256": recovery.OLD_OFFSETS_SHA256,
            "snapshot_identity_sha256": recovery.EXPECTED[
                "snapshot_identity_sha256"
            ],
            "binding_sha256": recovery.EXPECTED["final_binding_sha256"],
            "last_ack_sha256": recovery.EXPECTED["last_ack_sha256"],
            "pending_page_sha256": recovery.EXPECTED["pending_page_sha256"],
            "original_ledger_file_sha256": recovery.EXPECTED[
                "original_ledger_file_sha256"
            ],
            "original_ledger_progress_sha256": recovery.EXPECTED[
                "original_ledger_progress_sha256"
            ],
        },
        "evidence": {},
        "successor": {},
        "validation": {
            "selection_ledger": "PASS",
            "pipeline_scheduler": "PASS",
            "production_files_modified": False,
        },
    }
    assert callable(mutate)
    mutate(certificate_payload)
    certificate = {
        **certificate_payload,
        "certificate_sha256": canonical_sha256(certificate_payload),
    }
    certificate_bytes = json.dumps(certificate, sort_keys=True).encode()
    (tmp_path / "scheduler-migration-certificate.json").write_bytes(
        certificate_bytes,
    )
    package_payload = {
        "schema_version": 1,
        "gate": "qldpc-stage2-scheduler-migration-package-v1",
        "certificate_sha256": certificate["certificate_sha256"],
        "files": [{
            "path": "scheduler-migration-certificate.json",
            "bytes": len(certificate_bytes),
            "sha256": hashlib.sha256(certificate_bytes).hexdigest(),
        }],
    }
    package = {**package_payload, "package_sha256": canonical_sha256(package_payload)}
    (tmp_path / "package-manifest.json").write_text(
        json.dumps(package, sort_keys=True), encoding="utf-8",
    )
    with pytest.raises(RecoveryError, match=expected_message):
        validate_patched_scheduler_migration(tmp_path)

    package_payload = {
        "schema_version": 1,
        "gate": "qldpc-stage2-scheduler-migration-package-v1",
        "certificate_sha256": "0" * 64,
        "files": [],
    }
    package = {
        **package_payload,
        "package_sha256": canonical_sha256(package_payload),
    }
    (tmp_path / "scheduler-migration-certificate.json").write_text(
        json.dumps(certificate), encoding="utf-8",
    )
    (tmp_path / "package-manifest.json").write_text(
        json.dumps(package), encoding="utf-8",
    )
    with pytest.raises(RecoveryError, match="certificate/package seal"):
        validate_patched_scheduler_migration(tmp_path)


def test_public_validator_rejects_symlinked_certificate(tmp_path: Path) -> None:
    outside = tmp_path.parent / f"{tmp_path.name}-outside-certificate.json"
    outside.write_text("{}", encoding="utf-8")
    (tmp_path / "scheduler-migration-certificate.json").symlink_to(outside)
    (tmp_path / "package-manifest.json").write_text("{}", encoding="utf-8")
    try:
        with pytest.raises(RecoveryError, match="symlink"):
            validate_patched_scheduler_migration(tmp_path)
    finally:
        outside.unlink()


def test_migration_evidence_claim_schema_rejects_unknown_resealed_field() -> None:
    evidence = {key: None for key in recovery.MIGRATION_EVIDENCE_FIELDS}
    evidence["validator_source_path"] = str(Path(recovery.__file__).absolute())
    assert (
        recovery._validate_migration_evidence_claim_schema(evidence)
        == Path(recovery.__file__).absolute()
    )
    evidence["attacker_unconsumed_claim"] = "self-resealed"
    with pytest.raises(RecoveryError, match="evidence fields"):
        recovery._validate_migration_evidence_claim_schema(evidence)


def test_migration_evidence_claim_schema_rejects_changed_source_path(
    tmp_path: Path,
) -> None:
    evidence = {key: None for key in recovery.MIGRATION_EVIDENCE_FIELDS}
    evidence["validator_source_path"] = str(
        tmp_path / "attacker-validator.py"
    )
    with pytest.raises(RecoveryError, match="source path differs"):
        recovery._validate_migration_evidence_claim_schema(evidence)




def test_rung_outcome_evidence_self_reseal_fails_closed() -> None:
    outcome = {
        "source_gate": "qldpc-stage2-selection-ledger-page-size-transition-archive",
        "source_sha256": "1" * 64,
        "page_sequence": 30,
    }
    expected = recovery._expected_rung_record(
        sequence=2,
        path="selection-ledger-page-size-transitions/archive.json",
        sha256="2" * 64,
        progress_sha256="3" * 64,
        outcome_evidence=outcome,
    )
    recovery._validate_exact_rung_record(
        expected,
        sequence=2,
        path=expected["path"],
        sha256=expected["sha256"],
        progress_sha256=expected["progress_sha256"],
        outcome_evidence=outcome,
    )

    tampered = copy.deepcopy(expected)
    tampered["outcome_evidence"]["source_sha256"] = "f" * 64
    attacker_certificate_payload = {
        "gate": recovery.MIGRATION_GATE,
        "rung_archives": [tampered],
    }
    attacker_certificate = {
        **attacker_certificate_payload,
        "certificate_sha256": canonical_sha256(attacker_certificate_payload),
    }
    unsigned = dict(attacker_certificate)
    attacker_seal = unsigned.pop("certificate_sha256")
    assert attacker_seal == canonical_sha256(unsigned)
    with pytest.raises(RecoveryError, match="core/outcome evidence"):
        recovery._validate_exact_rung_record(
            tampered,
            sequence=2,
            path=expected["path"],
            sha256=expected["sha256"],
            progress_sha256=expected["progress_sha256"],
            outcome_evidence=outcome,
        )


def test_clean_artifact_outcome_self_reseal_fails_closed() -> None:
    trusted_outcome = {
        "source_gate": "trusted-transition-archive",
        "source_sha256": "1" * 64,
    }
    expected_payload = recovery._expected_clean_recovery_payload(
        sequence=2,
        completed_pages=31,
        new_snapshot_identity_sha256="2" * 64,
        old_page_sha256="3" * 64,
        old_ack_sha256="4" * 64,
        new_page_sha256="5" * 64,
        new_ack_sha256="6" * 64,
        selected_digests_sha256="7" * 64,
        rejected_count=1024,
        core_report_sha256="8" * 64,
        terminal_report_sha256="9" * 64,
        created_at="2026-08-17T00:00:00+00:00",
        outcome_evidence=trusted_outcome,
    )
    expected_artifact = {
        **expected_payload,
        "artifact_sha256": canonical_sha256(expected_payload),
    }
    recovery._validate_exact_clean_recovery_artifact(
        expected_artifact, expected_payload,
    )

    attacker_payload = copy.deepcopy(expected_payload)
    attacker_payload["outcome_evidence"]["source_sha256"] = "f" * 64
    attacker_artifact = {
        **attacker_payload,
        "artifact_sha256": canonical_sha256(attacker_payload),
    }
    attacker_certificate_payload = {
        "gate": recovery.MIGRATION_GATE,
        "clean_recovery_artifacts": [attacker_artifact],
    }
    attacker_certificate = {
        **attacker_certificate_payload,
        "certificate_sha256": canonical_sha256(attacker_certificate_payload),
    }
    unsigned = dict(attacker_certificate)
    attacker_seal = unsigned.pop("certificate_sha256")
    assert attacker_seal == canonical_sha256(unsigned)
    with pytest.raises(RecoveryError, match="core-derived evidence"):
        recovery._validate_exact_clean_recovery_artifact(
            attacker_artifact, expected_payload,
        )

def _tiny_transaction_fixture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[Path, Path, dict, dict, list[dict]]:
    package = tmp_path / "package"
    live = tmp_path / "solver-state"
    (tmp_path / "pipeline.lock").write_bytes(b"")
    package.mkdir()
    live.mkdir()
    relative_paths = [
        "selection-ledger-page-size-transitions/archive.json",
        "sealed-clean-page-recovery/clean.json",
        "stage2-selection-ledger.json.ranked-snapshot.jsonl",
        "stage2-selection-ledger.json.ranked-snapshot.offsets",
        "stage2-selection-ledger.json.ranked-snapshot.manifest.json",
        "stage2-selection-ledger.json",
    ]
    entries: list[dict] = []
    for index, relative in enumerate(relative_paths):
        source = package / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        payload = f"new-{index}-{relative}".encode()
        source.write_bytes(payload)
        entries.append({
            "path": relative,
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
        })
        target = live / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(f"old-{index}-{relative}".encode())
    certificate = {"certificate_sha256": "a" * 64, "successor": {}}
    package_manifest = {"package_sha256": "b" * 64}
    migration = {
        "certificate_sha256": certificate["certificate_sha256"],
        "package_sha256": package_manifest["package_sha256"],
    }
    state = {
        "certificate": certificate,
        "package_manifest": package_manifest,
        "migration": migration,
    }

    def validate(package_root: Path, *, same_filesystem_as: Path | None = None) -> dict:
        assert Path(package_root) == package
        assert same_filesystem_as == live
        return dict(state["migration"])

    def install_entries(package_root: Path) -> tuple[dict, dict, list[dict]]:
        assert Path(package_root) == package
        return (
            state["certificate"], state["package_manifest"], entries,
        )

    def validated_material(
        package_root: Path,
        solver_state: Path,
    ) -> tuple[dict, dict, dict, list[dict]]:
        assert Path(package_root) == package
        assert Path(solver_state) == live
        return (
            dict(state["migration"]), state["certificate"],
            state["package_manifest"], entries,
        )

    def live_summary(
        package_root: Path,
        solver_state: Path,
        cert: dict,
        installed: list[dict],
        *, root_fd: int | None = None,
    ) -> dict:
        assert Path(package_root) == package
        assert Path(solver_state) == live
        assert cert == state["certificate"]
        observed = []
        for entry in installed:
            payload = (live / entry["path"]).read_bytes()
            observed.append(hashlib.sha256(payload).hexdigest())
        return {"installed_sha256": observed}

    monkeypatch.setattr(recovery, "validate_patched_scheduler_migration", validate)
    monkeypatch.setattr(recovery, "_migration_install_entries", install_entries)
    monkeypatch.setattr(recovery, "_validated_install_material", validated_material)
    monkeypatch.setattr(recovery, "_installed_live_summary", live_summary)
    return package, live, state, migration, entries


def test_installer_happy_idempotent_commit_and_rollback(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, migration, entries = _tiny_transaction_fixture(
        tmp_path, monkeypatch,
    )
    old_ledger = (live / "stage2-selection-ledger.json").read_bytes()

    first = install_patched_scheduler_migration(package, solver_state=live)
    assert first["state"] == "COMMITTED"
    assert first["certificate_sha256"] == migration["certificate_sha256"]
    assert Path(first["marker_path"]).is_file()
    validated = validate_patched_scheduler_install(package, solver_state=live)
    second = install_patched_scheduler_migration(package, solver_state=live)
    assert second["commit_sha256"] == validated["commit_sha256"]
    for entry in entries:
        assert hashlib.sha256((live / entry["path"]).read_bytes()).hexdigest() == entry["sha256"]

    rolled_back = rollback_patched_scheduler_migration(package, solver_state=live)
    assert rolled_back["status"] == "ROLLED_BACK"
    assert not (live / recovery.INSTALL_COMMIT_NAME).exists()
    assert (live / "stage2-selection-ledger.json").read_bytes() == old_ledger
    archived_marker = (
        Path(rolled_back["backup_root"])
        / "committed-marker.rolled-back.json"
    )
    assert archived_marker.is_file()


def test_rollback_requires_pipeline_quiescence_and_is_zero_write_on_conflict(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, _, _ = _tiny_transaction_fixture(
        tmp_path, monkeypatch,
    )
    committed = install_patched_scheduler_migration(
        package, solver_state=live,
    )
    assert committed["state"] == "COMMITTED"

    def live_inventory() -> dict[str, tuple[bytes, int, int, int, int]]:
        inventory: dict[str, tuple[bytes, int, int, int, int]] = {}
        for path in sorted(live.rglob("*")):
            if not path.is_file() or path.is_symlink():
                continue
            metadata = path.stat(follow_symlinks=False)
            inventory[str(path.relative_to(live))] = (
                path.read_bytes(), metadata.st_mode, metadata.st_nlink,
                metadata.st_mtime_ns, metadata.st_ctime_ns,
            )
        return inventory

    lock_fd = recovery.os.open(
        live.parent / "pipeline.lock",
        recovery.os.O_RDWR | recovery.os.O_NOFOLLOW,
    )
    recovery.fcntl.flock(
        lock_fd, recovery.fcntl.LOCK_EX | recovery.fcntl.LOCK_NB,
    )
    try:
        before = live_inventory()
        with pytest.raises(
            RecoveryError,
            match="production pipeline is active; migration requires quiescence",
        ):
            rollback_patched_scheduler_migration(package, solver_state=live)
        assert live_inventory() == before
        assert (live / recovery.INSTALL_COMMIT_NAME).is_file()
    finally:
        recovery.fcntl.flock(lock_fd, recovery.fcntl.LOCK_UN)
        recovery.os.close(lock_fd)

    rolled_back = rollback_patched_scheduler_migration(
        package, solver_state=live,
    )
    assert rolled_back["status"] == "ROLLED_BACK"
    assert not (live / recovery.INSTALL_COMMIT_NAME).exists()


def test_installer_resumes_crash_after_manifest_before_ledger(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, _, entries = _tiny_transaction_fixture(tmp_path, monkeypatch)
    old_ledger = (live / "stage2-selection-ledger.json").read_bytes()
    original = recovery._atomic_install_file

    def crash(source: Path, target: Path, **kwargs: object) -> None:
        if target.name == "stage2-selection-ledger.json":
            raise RecoveryError("injected crash before ledger commit")
        original(source, target, **kwargs)

    monkeypatch.setattr(recovery, "_atomic_install_file", crash)
    with pytest.raises(RecoveryError, match="injected crash"):
        install_patched_scheduler_migration(package, solver_state=live)
    assert (live / "stage2-selection-ledger.json").read_bytes() == old_ledger
    journal = json.loads((live / recovery.INSTALL_JOURNAL_NAME).read_text())
    assert journal["state"] == "PREPARED"
    assert not (live / recovery.INSTALL_COMMIT_NAME).exists()

    monkeypatch.setattr(recovery, "_atomic_install_file", original)
    resumed = install_patched_scheduler_migration(package, solver_state=live)
    assert resumed["state"] == "COMMITTED"
    assert hashlib.sha256((live / entries[-1]["path"]).read_bytes()).hexdigest() == entries[-1]["sha256"]


def test_installer_rejects_different_package_while_prepared(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, state, _, _ = _tiny_transaction_fixture(tmp_path, monkeypatch)
    original = recovery._atomic_install_file
    monkeypatch.setattr(
        recovery, "_atomic_install_file",
        lambda *args, **kwargs: (_ for _ in ()).throw(RecoveryError("crash")),
    )
    with pytest.raises(RecoveryError, match="crash"):
        install_patched_scheduler_migration(package, solver_state=live)
    monkeypatch.setattr(recovery, "_atomic_install_file", original)
    state["certificate"] = {"certificate_sha256": "c" * 64, "successor": {}}
    state["package_manifest"] = {"package_sha256": "d" * 64}
    state["migration"] = {
        "certificate_sha256": "c" * 64,
        "package_sha256": "d" * 64,
    }
    with pytest.raises(RecoveryError, match="different or closed transaction"):
        install_patched_scheduler_migration(package, solver_state=live)

def test_installer_resumes_preparing_after_backup_crash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, _, entries = _tiny_transaction_fixture(
        tmp_path, monkeypatch,
    )
    original = recovery._atomic_install_relative_at
    injected = False

    def crash_first_backup(*args: object, **kwargs: object) -> None:
        nonlocal injected
        if not injected:
            injected = True
            raise RecoveryError("injected backup crash")
        original(*args, **kwargs)

    monkeypatch.setattr(
        recovery, "_atomic_install_relative_at", crash_first_backup,
    )
    with pytest.raises(RecoveryError, match="injected backup crash"):
        install_patched_scheduler_migration(package, solver_state=live)
    journal = json.loads(
        (live / recovery.INSTALL_JOURNAL_NAME).read_text()
    )
    assert journal["state"] == "PREPARING"
    assert not (live / recovery.INSTALL_COMMIT_NAME).exists()

    monkeypatch.setattr(recovery, "_atomic_install_relative_at", original)
    resumed = install_patched_scheduler_migration(package, solver_state=live)
    assert resumed["state"] == "COMMITTED"
    for entry in entries:
        assert hashlib.sha256(
            (live / entry["path"]).read_bytes()
        ).hexdigest() == entry["sha256"]


def test_installer_rolls_forward_marker_durable_journal_prepared_crash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, _, _ = _tiny_transaction_fixture(tmp_path, monkeypatch)
    original = recovery._atomic_json_relative_at
    injected = False

    def crash_journal_commit(
        root_fd: int,
        relative: str,
        value: dict,
        *,
        replace: bool,
    ) -> None:
        nonlocal injected
        if (
            not injected
            and relative == recovery.INSTALL_JOURNAL_NAME
            and value.get("state") == "COMMITTED"
        ):
            injected = True
            raise RecoveryError("injected journal commit crash")
        original(root_fd, relative, value, replace=replace)

    monkeypatch.setattr(
        recovery, "_atomic_json_relative_at", crash_journal_commit,
    )
    with pytest.raises(RecoveryError, match="injected journal commit crash"):
        install_patched_scheduler_migration(package, solver_state=live)
    assert (live / recovery.INSTALL_COMMIT_NAME).is_file()
    journal = json.loads(
        (live / recovery.INSTALL_JOURNAL_NAME).read_text()
    )
    assert journal["state"] == "PREPARED"

    monkeypatch.setattr(recovery, "_atomic_json_relative_at", original)
    resumed = install_patched_scheduler_migration(package, solver_state=live)
    assert resumed["state"] == "COMMITTED"
    journal = json.loads(
        (live / recovery.INSTALL_JOURNAL_NAME).read_text()
    )
    assert journal["state"] == "COMMITTED"
    assert journal["commit_sha256"] == resumed["commit_sha256"]


def test_validated_install_material_rejects_post_validate_certificate_swap(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package = tmp_path / "package"
    live = tmp_path / "live"
    package.mkdir()
    live.mkdir()
    valid_certificate_payload = {"successor": {}}
    valid_certificate_sha256 = canonical_sha256(valid_certificate_payload)
    valid_package_payload = {"files": []}
    valid_package_sha256 = canonical_sha256(valid_package_payload)
    summary = {
        "certificate_sha256": valid_certificate_sha256,
        "package_sha256": valid_package_sha256,
    }
    attacker_certificate = {
        "successor": {"ledger_path": "attacker.json"},
        "certificate_sha256": valid_certificate_sha256,
    }
    captured_package = {
        **valid_package_payload,
        "package_sha256": valid_package_sha256,
    }
    monkeypatch.setattr(
        recovery, "validate_patched_scheduler_migration",
        lambda *args, **kwargs: dict(summary),
    )
    monkeypatch.setattr(
        recovery, "_migration_install_entries",
        lambda package_root: (attacker_certificate, captured_package, []),
    )

    with pytest.raises(
        RecoveryError,
        match="captured install certificate/package objects differ",
    ):
        recovery._validated_install_material(package, live)


def test_atomic_control_crash_never_publishes_truncated_record(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = tmp_path / "live"
    root.mkdir()
    root_fd = recovery._open_path_nofollow(root, directory=True)
    original_link = recovery.os.link
    payload = {"state": "PREPARING", "value": "durable"}

    def crash_before_publish(*args: object, **kwargs: object) -> None:
        raise OSError("injected publish crash")

    monkeypatch.setattr(recovery.os, "link", crash_before_publish)
    try:
        with pytest.raises(RecoveryError, match="atomic control write failed"):
            recovery._atomic_json_relative_at(
                root_fd, "control.json", payload, replace=False,
            )
        assert not (root / "control.json").exists()
        assert list(root.glob(".control.json.writing-*")) == []
        monkeypatch.setattr(recovery.os, "link", original_link)
        recovery._atomic_json_relative_at(
            root_fd, "control.json", payload, replace=False,
        )
    finally:
        recovery.os.close(root_fd)
    assert json.loads((root / "control.json").read_text()) == payload


def test_atomic_install_ancestor_swap_cannot_overwrite_external_victim(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    live = tmp_path / "live"
    branch = live / "branch"
    external = tmp_path / "external"
    branch.mkdir(parents=True)
    external.mkdir()
    target = branch / "target.json"
    target.write_bytes(b"old-live")
    victim = external / "target.json"
    victim.write_bytes(b"external-victim")
    source = tmp_path / "source.json"
    source_payload = b"new-migration-bytes"
    source.write_bytes(source_payload)
    expected_sha256 = hashlib.sha256(source_payload).hexdigest()
    root_fd = recovery._open_path_nofollow(live, directory=True)
    original_replace = recovery.os.replace
    swapped = False

    def swap_ancestor_then_replace(
        source_name: object,
        target_name: object,
        *args: object,
        **kwargs: object,
    ) -> None:
        nonlocal swapped
        if kwargs.get("dst_dir_fd") is not None and not swapped:
            swapped = True
            original_replace(branch, live / "branch-held")
            branch.symlink_to(external, target_is_directory=True)
        original_replace(source_name, target_name, *args, **kwargs)

    monkeypatch.setattr(recovery.os, "replace", swap_ancestor_then_replace)
    try:
        with pytest.raises(RecoveryError, match="ancestor is unsafe"):
            recovery._atomic_install_file(
                source,
                target,
                root_fd=root_fd,
                target_relative="branch/target.json",
                expected_sha256=expected_sha256,
                expected_bytes=len(source_payload),
            )
    finally:
        os_close = recovery.os.close
        os_close(root_fd)

    assert swapped is True
    assert victim.read_bytes() == b"external-victim"
    assert (live / "branch-held" / "target.json").read_bytes() == source_payload


def test_installed_live_summary_uses_lexical_production_manifest_path(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from evaluation import selection_ledger
    from humanize.pipeline import FiveStagePipeline

    live = tmp_path / "solver-state"
    package = tmp_path / "package"
    live.mkdir()
    package.mkdir()
    known_answer = tmp_path / "known-answer.json"
    known_answer.write_text("{}")
    ledger_relative = "stage2-selection-ledger.json"
    manifest_relative = (
        "stage2-selection-ledger.json.ranked-snapshot.manifest.json"
    )
    snapshot_relative = (
        "stage2-selection-ledger.json.ranked-snapshot.jsonl"
    )
    offsets_relative = (
        "stage2-selection-ledger.json.ranked-snapshot.offsets"
    )
    binding_payload = {
        "schema_version": 1,
        "gate": "qldpc-stage2-ranked-snapshot-binding",
        "inputs": [],
        "source_fingerprint": "1" * 64,
        "solver_runtime": {},
        "known_code_registry": {},
        "target_mode": "scalar-fom-inclusive-v1",
    }
    binding = {
        **binding_payload,
        "binding_sha256": canonical_sha256(binding_payload),
    }
    identity = {
        "binding_sha256": binding["binding_sha256"],
        "snapshot_sha256": hashlib.sha256(b"snapshot\n").hexdigest(),
        "offsets_sha256": hashlib.sha256(b"offsets\n").hexdigest(),
        "chunk_index_sha256": "2" * 64,
        "counts_sha256": "3" * 64,
        "rows": 1,
        "eligible_rows": 1,
        "chunk_rows": 1,
    }
    manifest_payload = {
        "schema_version": 1,
        "gate": "qldpc-stage2-ranked-snapshot",
        "binding": binding,
        "binding_sha256": binding["binding_sha256"],
        "identity": identity,
        "snapshot_rows": 1,
        "counts": {"eligible_candidates": 1},
    }
    manifest = {
        **manifest_payload,
        "manifest_sha256": canonical_sha256(manifest_payload),
    }
    identity_sha256 = canonical_sha256(identity)
    ledger = {
        "binding_sha256": "4" * 64,
        "snapshot_identity_sha256": identity_sha256,
        "progress_sha256": "5" * 64,
        "last_ack_sha256": "6" * 64,
        "pending": {"page_sha256": "7" * 64},
        "adaptive_page_scheduler": {"state_sha256": "8" * 64},
    }
    payloads = {
        ledger_relative: (
            json.dumps(ledger, sort_keys=True) + "\n"
        ).encode(),
        manifest_relative: (
            json.dumps(manifest, sort_keys=True) + "\n"
        ).encode(),
        snapshot_relative: b"snapshot\n",
        offsets_relative: b"offsets\n",
    }
    entries = []
    for relative, payload in payloads.items():
        target = live / relative
        target.write_bytes(payload)
        entries.append({
            "path": relative,
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
        })
    certificate = {
        "successor": {
            "snapshot_identity_sha256": identity_sha256,
            "page_bindings": ["4" * 64] * 4,
        },
        "evidence": {"known_answer_path": str(known_answer)},
    }
    monkeypatch.setattr(
        selection_ledger, "validate_selection_ledger",
        lambda *args, **kwargs: None,
    )
    monkeypatch.setattr(
        FiveStagePipeline, "_validated_stage2_selection_ledger",
        lambda *args, **kwargs: None,
    )
    monkeypatch.setattr(
        FiveStagePipeline, "_validate_stage2_page_scheduler",
        lambda *args, **kwargs: None,
    )
    root_fd = recovery._open_path_nofollow(live, directory=True)
    try:
        summary = recovery._installed_live_summary(
            package, live, certificate, entries, root_fd=root_fd,
        )
    finally:
        recovery.os.close(root_fd)
    assert summary["ledger_path"] == str(live / ledger_relative)
    assert not summary["manifest_path"].startswith("/proc/")


def test_installer_never_overwrites_ledger_mutated_after_prepared(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, _, _ = _tiny_transaction_fixture(
        tmp_path, monkeypatch,
    )
    ledger_path = live / "stage2-selection-ledger.json"
    foreground_progress = b"foreground-stage2-progress-must-survive"
    original = recovery._atomic_json_relative_at
    injected = False

    def mutate_after_prepared(
        root_fd: int,
        relative: str,
        value: dict,
        *,
        replace: bool,
    ) -> None:
        nonlocal injected
        original(root_fd, relative, value, replace=replace)
        if (
            not injected
            and relative == recovery.INSTALL_JOURNAL_NAME
            and value.get("state") == "PREPARED"
        ):
            injected = True
            ledger_path.write_bytes(foreground_progress)

    monkeypatch.setattr(
        recovery, "_atomic_json_relative_at", mutate_after_prepared,
    )
    with pytest.raises(
        RecoveryError,
        match="live install target changed after PREPARED",
    ):
        install_patched_scheduler_migration(package, solver_state=live)
    assert injected is True
    assert ledger_path.read_bytes() == foreground_progress
    assert not (live / recovery.INSTALL_COMMIT_NAME).exists()
    journal = json.loads((live / recovery.INSTALL_JOURNAL_NAME).read_text())
    assert journal["state"] == "PREPARED"


def test_installer_requires_exclusive_production_pipeline_lock(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, _, _ = _tiny_transaction_fixture(
        tmp_path, monkeypatch,
    )
    lock_path = live.parent / "pipeline.lock"
    lock_fd = recovery.os.open(
        lock_path,
        recovery.os.O_RDWR | recovery.os.O_NOFOLLOW,
    )
    recovery.fcntl.flock(
        lock_fd, recovery.fcntl.LOCK_EX | recovery.fcntl.LOCK_NB,
    )
    try:
        with pytest.raises(
            RecoveryError,
            match="production pipeline is active; migration requires quiescence",
        ):
            install_patched_scheduler_migration(package, solver_state=live)
        assert not (live / recovery.INSTALL_JOURNAL_NAME).exists()
        assert not (live / recovery.INSTALL_COMMIT_NAME).exists()
    finally:
        recovery.fcntl.flock(lock_fd, recovery.fcntl.LOCK_UN)
        recovery.os.close(lock_fd)

    committed = install_patched_scheduler_migration(
        package, solver_state=live,
    )
    assert committed["state"] == "COMMITTED"


def test_installer_commit_boundary_cas_rejects_last_moment_ledger_race(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    package, live, _, _, _ = _tiny_transaction_fixture(
        tmp_path, monkeypatch,
    )
    ledger_path = live / "stage2-selection-ledger.json"
    foreground_progress = b"foreground-race-before-commit-marker"
    original = recovery._publish_commit_marker_cas
    injected = False

    def mutate_before_commit_cas(
        root_fd: int,
        marker: dict,
        entries: list[dict],
        expected_tokens: dict[str, list[int]],
        **kwargs: object,
    ) -> None:
        nonlocal injected
        injected = True
        ledger_path.write_bytes(foreground_progress)
        original(
            root_fd, marker, entries, expected_tokens, **kwargs,
        )

    monkeypatch.setattr(
        recovery, "_publish_commit_marker_cas", mutate_before_commit_cas,
    )
    with pytest.raises(
        RecoveryError,
        match="live package member changed at commit boundary",
    ):
        install_patched_scheduler_migration(package, solver_state=live)
    assert injected is True
    assert ledger_path.read_bytes() == foreground_progress
    assert not (live / recovery.INSTALL_COMMIT_NAME).exists()
    journal = json.loads((live / recovery.INSTALL_JOURNAL_NAME).read_text())
    assert journal["state"] == "PREPARED"
