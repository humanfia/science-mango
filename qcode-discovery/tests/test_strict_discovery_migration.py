from __future__ import annotations

import hashlib
import inspect
import json
import struct
from pathlib import Path
from types import SimpleNamespace

import pytest

from evaluation.selection_ledger import (
    acknowledge_selection_page,
    install_pending_page,
    make_scan_evidence,
    make_selection_page,
    new_selection_ledger,
    seal_selection_ledger,
)
from humanize import strict_discovery_cli as cli
from humanize import strict_discovery_migration as migration
from humanize import stage2_ledger_recovery as recovery


def _json_sha(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode()
    ).hexdigest()


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value) + "\n", encoding="utf-8")


def _paths(tmp_path: Path) -> cli.SidecarPaths:
    repo = tmp_path / "repo"
    run_root = repo / "results" / "humanize" / "pipelines" / "run"
    root = run_root / "sidecars" / cli.SIDECAR_NAME
    root.mkdir(parents=True)
    (repo / "scripts").mkdir()
    return cli.SidecarPaths(
        repo=repo,
        run_root=run_root,
        root=root,
        process=root / "process.json",
        lock=root / "process.lock",
        log=root / "worker.log",
        progress=root / "progress.json",
        batches=root / "batches",
    )


def _snapshot_manifest(
    ledger: Path,
    rows: list[dict[str, object]],
    *,
    binding_tag: str,
) -> tuple[Path, dict[str, object], bytes, bytes]:
    snapshot = ledger.with_name(f"{ledger.name}.ranked-snapshot.jsonl")
    offsets = ledger.with_name(f"{ledger.name}.ranked-snapshot.offsets")
    manifest_path = ledger.with_name(
        f"{ledger.name}.ranked-snapshot.manifest.json"
    )
    encoded = [
        (json.dumps(row, sort_keys=True) + "\n").encode()
        for row in rows
    ]
    snapshot_payload = b"".join(encoded)
    positions = [0]
    for row in encoded:
        positions.append(positions[-1] + len(row))
    offsets_payload = b"".join(struct.pack(">Q", value) for value in positions)
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(snapshot_payload)
    offsets.write_bytes(offsets_payload)
    counts = {
        "input_records": len(rows),
        "unique_candidates": len(rows),
        "duplicate_candidates": 0,
        "rejected_candidates": 0,
        "eligible_candidates": len(rows),
    }
    binding_unsigned = {
        "schema_version": 1,
        "gate": "qldpc-stage2-ranked-snapshot",
        "target_mode": cli.TARGET_MODE,
        "source_fingerprint": binding_tag * 64,
        "solver_runtime": {"test": binding_tag},
        "inputs": [],
    }
    binding = {
        **binding_unsigned,
        "binding_sha256": _json_sha(binding_unsigned),
    }
    chunk = {
        "start_row": 0,
        "end_row": len(rows),
        "snapshot_start": 0,
        "snapshot_end": len(snapshot_payload),
        "snapshot_sha256": hashlib.sha256(snapshot_payload).hexdigest(),
        "offsets_start": 0,
        "offsets_end": len(offsets_payload),
        "offsets_sha256": hashlib.sha256(offsets_payload).hexdigest(),
    }
    identity = {
        "binding_sha256": binding["binding_sha256"],
        "snapshot_sha256": hashlib.sha256(snapshot_payload).hexdigest(),
        "offsets_sha256": hashlib.sha256(offsets_payload).hexdigest(),
        "chunk_index_sha256": _json_sha([chunk]),
        "chunk_rows": 4096,
        "rows": len(rows),
        "eligible_rows": len(rows),
        "counts_sha256": _json_sha(counts),
    }
    payload = {
        "schema_version": 1,
        "gate": "qldpc-stage2-ranked-snapshot",
        "binding": binding,
        "binding_sha256": binding["binding_sha256"],
        "identity": identity,
        "snapshot_rows": len(rows),
        "snapshot_stat": {
            "device": snapshot.stat().st_dev,
            "inode": snapshot.stat().st_ino,
            "bytes": snapshot.stat().st_size,
            "mtime_ns": snapshot.stat().st_mtime_ns,
        },
        "offsets_stat": {
            "device": offsets.stat().st_dev,
            "inode": offsets.stat().st_ino,
            "bytes": offsets.stat().st_size,
            "mtime_ns": offsets.stat().st_mtime_ns,
        },
        "chunk_rows": 4096,
        "chunks": [chunk],
        "counts": counts,
        "created_at": 1.0,
    }
    manifest = {**payload, "manifest_sha256": _json_sha(payload)}
    _write_json(manifest_path, manifest)
    return manifest_path, manifest, snapshot_payload, offsets_payload


def _fixture(tmp_path: Path) -> dict[str, object]:
    paths = _paths(tmp_path)
    ledger_path = paths.run_root / "solver-state" / "stage2-selection-ledger.json"
    candidate_rows = [
        {"canonical_digest": "1" * 64, "candidate": 1},
        {"canonical_digest": "2" * 64, "candidate": 2},
    ]
    manifest_path, successor_manifest, snapshot_payload, offsets_payload = (
        _snapshot_manifest(ledger_path, candidate_rows, binding_tag="b")
    )
    new_identity = successor_manifest["identity"]
    assert isinstance(new_identity, dict)
    live_ledger = new_selection_ledger(
        binding_sha256=str(new_identity["binding_sha256"]),
        snapshot_identity_sha256_value=_json_sha(new_identity),
        snapshot_rows=2,
        eligible_rows=2,
    )
    _write_json(ledger_path, live_ledger)

    old_identity = dict(new_identity)
    old_identity["binding_sha256"] = "a" * 64
    old_identity_sha = _json_sha(old_identity)
    recovered = paths.run_root / "recovery"
    recovered.mkdir()
    old_snapshot = recovered / "old-snapshot.jsonl"
    old_offsets = recovered / "old-snapshot.offsets"
    old_snapshot.write_bytes(snapshot_payload)
    old_offsets.write_bytes(offsets_payload)

    ranked_input = paths.root / "ranked-input.jsonl"
    ranked_input.write_bytes(
        b"".join(cli._canonical_bytes(row) + b"\n" for row in candidate_rows)
    )
    items = [
        {
            "canonical_digest": row["canonical_digest"],
            "snapshot_index": index,
            "portfolio_rank": index + 1,
            "scheduling_only": True,
            "n": 12,
            "k": 1,
            "d_req": 13,
            "required_distance": 13,
            "cutoff": 12,
        }
        for index, row in enumerate(candidate_rows)
    ]
    portfolio = {
        "schema_version": cli.PORTFOLIO_SCHEMA_VERSION,
        "gate": cli.PORTFOLIO_GATE,
        "producer": {
            "module": "humanize.strict_discovery_ranking",
            "source_sha256": cli._file_sha256(
                Path(cli.__file__).resolve().with_name(
                    "strict_discovery_ranking.py"
                )
            ),
        },
        "publication_certificate": False,
        "pipeline_promotion": False,
        "target_mode": cli.TARGET_MODE,
        "source": {
            "ledger_path": str(ledger_path.resolve()),
            "ledger_generation": 0,
            "ledger_cursor": 0,
            "portfolio_cursor": 0,
            "snapshot_identity": old_identity,
            "snapshot_identity_sha256": old_identity_sha,
            "manifest_path": str(manifest_path.resolve()),
            "manifest_file_sha256": "c" * 64,
            "manifest_sha256": "d" * 64,
        },
        "items": items,
        "batches": [{
            "sequence": 0,
            "count": 2,
            "digests": [row["canonical_digest"] for row in candidate_rows],
        }],
        "ranked_input": {
            "path": str(ranked_input.resolve()),
            "bytes": ranked_input.stat().st_size,
            "rows": 2,
            "sha256": cli._file_sha256(ranked_input),
            "payload_kind": cli.PORTFOLIO_PAYLOAD_KIND,
        },
    }
    portfolio["portfolio_sha256"] = cli._sha256(portfolio)
    portfolio_path = paths.root / "portfolio.json"
    _write_json(portfolio_path, portfolio)
    _, _, bound = cli.load_portfolio_manifest(portfolio_path, paths=paths)

    batch_root = paths.batches / "batch-0000"
    batch_root.mkdir(parents=True)
    input_path = batch_root / "input.jsonl"
    input_path.write_bytes(cli._canonical_bytes(candidate_rows[0]) + b"\n")
    ranked_output = batch_root / "ranked.jsonl"
    ranked_output.write_text(
        json.dumps({
            "campaign_selected": True,
            "campaign_audit": {
                "canonical_digest": "1" * 64,
                "status": "REJECTED",
            },
        }) + "\n",
        encoding="utf-8",
    )
    summary = batch_root / "summary.json"
    _write_json(summary, {
        "target_mode": cli.TARGET_MODE,
        "selected_candidates": 1,
        "top": 1,
        "canonical_duplicates_skipped": 0,
        "known_codes_skipped": 0,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "structural_unresolved_candidates": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
        "certificate_operational_errors": 0,
    })
    batch_binding = "3" * 64
    batch_identity = "4" * 64
    batch_ledger = new_selection_ledger(
        binding_sha256=batch_binding,
        snapshot_identity_sha256_value=batch_identity,
        snapshot_rows=1,
        eligible_rows=1,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=batch_identity,
        start_index=0,
        next_index=1,
        snapshot_rows=1,
        eligible_rows=1,
        selection_exhausted=True,
    )
    page = make_selection_page(
        binding_sha256=batch_binding,
        snapshot_identity_sha256_value=batch_identity,
        page_sequence=0,
        previous_ack_sha256=str(batch_ledger["last_ack_sha256"]),
        start_index=0,
        next_index=1,
        selected_digests=["1" * 64],
        scan_evidence=scan,
    )
    batch_ledger = install_pending_page(batch_ledger, page)
    batch_ledger = acknowledge_selection_page(
        batch_ledger,
        page,
        disposition="COMPLETED",
    )
    _write_json(batch_root / "selection-ledger.json", batch_ledger)
    batch = {
        "batch_index": 0,
        "manifest_start_row": 0,
        "manifest_next_row": 1,
        "selected_source_rows": [0],
        "selected_portfolio_ranks": [1],
        "selected_digests": ["1" * 64],
        "rows": 1,
        "input_path": str(input_path.resolve()),
        "input_sha256": cli._file_sha256(input_path),
        "argv": ["python"],
        "started_at": 1.0,
        "attempts": 1,
        "live_source": {"check_scope": "test"},
        "skipped_foreground_owned_count": 0,
        "skipped_foreground_owned_digests": [],
        "skipped_foreground_owned_sha256": cli._sha256([]),
        "ranked_output": str(ranked_output),
        "summary_output": str(summary),
        "disposition": "COMPLETED",
        "status_counts": {"REJECTED": 1},
        "returncode": 0,
        "wins": [],
        "completed_at": 2.0,
    }
    config = cli.DiscoveryConfig().as_dict()
    cli._write_progress(paths.progress, {
        "schema_version": cli.PROGRESS_SCHEMA_VERSION,
        "gate": cli.PROGRESS_GATE,
        "status": "RUNNING",
        "source": bound,
        "config": config,
        "config_sha256": cli._sha256(config),
        "next_row": 1,
        "batches": [batch],
        "wins": [],
        "foreground_skips": [],
        "updated_at": 2.0,
    })
    return {
        "paths": paths,
        "portfolio_path": portfolio_path,
        "manifest_path": manifest_path,
        "old_snapshot": old_snapshot,
        "old_offsets": old_offsets,
        "batch_input": input_path,
    }


def _complete_no_win(argv: list[str]) -> None:
    count = int(argv[argv.index("--top") + 1])
    input_path = Path(argv[2])
    input_rows = [json.loads(line) for line in input_path.read_text().splitlines()]
    digests = [str(row["canonical_digest"]) for row in input_rows]
    assert len(digests) == count
    ranked = Path(argv[argv.index("--ranked-output") + 1])
    summary = Path(argv[argv.index("--summary-output") + 1])
    ranked.parent.mkdir(parents=True, exist_ok=True)
    ranked.write_text(
        "".join(
            json.dumps({
                "campaign_selected": True,
                "campaign_audit": {
                    "canonical_digest": digest,
                    "status": "REJECTED",
                },
            }) + "\n"
            for digest in digests
        ),
        encoding="utf-8",
    )
    ledger_path = Path(argv[argv.index("--selection-ledger") + 1])
    binding = "5" * 64
    identity = "6" * 64
    ledger = new_selection_ledger(
        binding_sha256=binding,
        snapshot_identity_sha256_value=identity,
        snapshot_rows=count,
        eligible_rows=count,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=identity,
        start_index=0,
        next_index=count,
        snapshot_rows=count,
        eligible_rows=count,
        selection_exhausted=True,
    )
    page = make_selection_page(
        binding_sha256=binding,
        snapshot_identity_sha256_value=identity,
        page_sequence=0,
        previous_ack_sha256=str(ledger["last_ack_sha256"]),
        start_index=0,
        next_index=count,
        selected_digests=digests,
        scan_evidence=scan,
    )
    ledger = install_pending_page(ledger, page)
    _write_json(ledger_path, ledger)
    _write_json(summary, {
        "target_mode": cli.TARGET_MODE,
        "selected_candidates": count,
        "top": count,
        "canonical_duplicates_skipped": 0,
        "known_codes_skipped": 0,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "structural_unresolved_candidates": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
        "certificate_operational_errors": 0,
        "selection_page": page,
    })


def _complete_win(argv: list[str]) -> None:
    _complete_no_win(argv)
    ranked = Path(argv[argv.index("--ranked-output") + 1])
    rows = [json.loads(line) for line in ranked.read_text().splitlines()]
    rows[0]["campaign_audit"].update({
        "status": "THRESHOLD_PROVEN",
        "certificate": {
            "attempted": True,
            "certificate_exact": True,
            "certificate_passed": True,
            "verification_attempted": True,
            "verification_passed": True,
            "certificate_sha256": "c" * 64,
        },
    })
    ranked.write_text(
        "".join(json.dumps(row) + "\n" for row in rows),
        encoding="utf-8",
    )


def _temporary_committed_install(
    fixture: dict[str, object],
    monkeypatch: pytest.MonkeyPatch,
    *,
    pending_digest: str = "f" * 64,
) -> tuple[Path, dict[str, object], dict[str, object]]:
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    solver_state = paths.run_root / "solver-state"
    package = paths.run_root / "migration-package"
    package.mkdir()
    certificate_path = package / "scheduler-migration-certificate.json"
    _write_json(certificate_path, {"fixture": "externally validated package"})

    manifest_path = Path(fixture["manifest_path"])
    manifest = json.loads(manifest_path.read_text())
    identity = manifest["identity"]
    assert isinstance(identity, dict)
    binding_sha256 = str(manifest["binding_sha256"])
    identity_sha256 = _json_sha(identity)
    live_ledger_path = solver_state / "stage2-selection-ledger.json"
    ledger = new_selection_ledger(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=identity_sha256,
        snapshot_rows=2,
        eligible_rows=2,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=identity_sha256,
        start_index=0,
        next_index=1,
        snapshot_rows=2,
        eligible_rows=2,
        selection_exhausted=False,
    )
    pending_page = make_selection_page(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=identity_sha256,
        page_sequence=0,
        previous_ack_sha256=str(ledger["last_ack_sha256"]),
        start_index=0,
        next_index=1,
        selected_digests=[pending_digest],
        scan_evidence=scan,
    )
    ledger = install_pending_page(ledger, pending_page)

    immutable_recovery_artifact = solver_state / "stage2-transition-archive.json"
    immutable_recovery_artifact.write_text(
        "immutable transition evidence\n", encoding="utf-8",
    )
    relative_paths = (
        "stage2-selection-ledger.json.ranked-snapshot.jsonl",
        "stage2-selection-ledger.json.ranked-snapshot.offsets",
        "stage2-selection-ledger.json.ranked-snapshot.manifest.json",
        "stage2-transition-archive.json",
        "stage2-selection-ledger.json",
    )
    live_paths = {
        relative: solver_state / relative for relative in relative_paths
    }
    package_paths = {
        relative: package / relative for relative in relative_paths
    }
    for relative in relative_paths[:-1]:
        package_paths[relative].write_bytes(live_paths[relative].read_bytes())
    _write_json(package_paths[relative_paths[-1]], ledger)
    entries = [
        {
            "path": relative,
            "sha256": cli._file_sha256(package_paths[relative]),
            "bytes": package_paths[relative].stat().st_size,
            "source_token": [
                int(value)
                for value in (
                    package_paths[relative].stat().st_mode,
                    package_paths[relative].stat().st_nlink,
                    package_paths[relative].stat().st_dev,
                    package_paths[relative].stat().st_ino,
                    package_paths[relative].stat().st_size,
                    package_paths[relative].stat().st_mtime_ns,
                    package_paths[relative].stat().st_ctime_ns,
                )
            ],
        }
        for relative in relative_paths
    ]
    for index, relative in enumerate(relative_paths):
        live_paths[relative].write_bytes(f"pre-install-{index}".encode())

    validator_source_sha256 = cli._file_sha256(Path(recovery.__file__))
    normalized = {
        "certificate_sha256": "a" * 64,
        "package_sha256": "b" * 64,
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": identity_sha256,
        "active_ledger_progress_sha256": ledger["progress_sha256"],
        "active_last_ack_sha256": ledger["last_ack_sha256"],
        "active_pending_page_sha256": ledger["pending"]["page_sha256"],
        "terminal_report_sha256": "9" * 64,
        "validator_source_sha256": validator_source_sha256,
        "production_files_modified": False,
    }
    recovery_certificate = {
        "certificate_sha256": normalized["certificate_sha256"],
        "successor": {},
    }
    package_manifest = {"package_sha256": normalized["package_sha256"]}

    def validate_package(
        package_root: Path,
        *,
        same_filesystem_as: Path | None = None,
    ) -> dict[str, object]:
        assert Path(package_root) == package
        assert Path(same_filesystem_as) == solver_state
        return dict(normalized)

    def install_entries(
        package_root: Path,
    ) -> tuple[dict[str, object], dict[str, object], list[dict[str, object]]]:
        assert Path(package_root) == package
        return recovery_certificate, package_manifest, entries

    def validated_material(
        package_root: Path,
        live_root: Path,
    ) -> tuple[
        dict[str, object],
        dict[str, object],
        dict[str, object],
        list[dict[str, object]],
    ]:
        assert Path(package_root) == package
        assert Path(live_root) == solver_state
        return (
            dict(normalized),
            recovery_certificate,
            package_manifest,
            entries,
        )

    def live_summary(
        package_root: Path,
        live_root: Path,
        certificate: dict[str, object],
        installed: list[dict[str, object]],
        *,
        root_fd: int | None = None,
    ) -> dict[str, object]:
        assert Path(package_root) == package
        assert Path(live_root) == solver_state
        assert certificate == recovery_certificate
        assert installed == entries
        for entry in entries:
            target = solver_state / str(entry["path"])
            assert cli._file_sha256(target) == entry["sha256"]
            assert target.stat().st_size == entry["bytes"]
        live_ledger = json.loads(live_ledger_path.read_text())
        live_manifest = json.loads(manifest_path.read_text())
        return {
            "ledger_path": str(live_ledger_path),
            "manifest_path": str(manifest_path),
            "snapshot_path": str(live_paths[relative_paths[0]]),
            "offsets_path": str(live_paths[relative_paths[1]]),
            "ledger_file_sha256": cli._file_sha256(live_ledger_path),
            "manifest_file_sha256": cli._file_sha256(manifest_path),
            "snapshot_file_sha256": cli._file_sha256(
                live_paths[relative_paths[0]]
            ),
            "offsets_file_sha256": cli._file_sha256(
                live_paths[relative_paths[1]]
            ),
            "binding_sha256": live_ledger["binding_sha256"],
            "snapshot_identity_sha256": live_ledger[
                "snapshot_identity_sha256"
            ],
            "progress_sha256": live_ledger["progress_sha256"],
            "ledger_content_sha256": live_ledger["progress_sha256"],
            "manifest_content_sha256": live_manifest["manifest_sha256"],
            "snapshot_content_sha256": live_manifest["identity"][
                "snapshot_sha256"
            ],
            "offsets_content_sha256": live_manifest["identity"][
                "offsets_sha256"
            ],
            "validator_source_sha256": validator_source_sha256,
            "last_ack_sha256": live_ledger["last_ack_sha256"],
            "pending_page_sha256": live_ledger["pending"]["page_sha256"],
            "scheduler_state_sha256": "8" * 64,
        }

    portfolio = json.loads(Path(fixture["portfolio_path"]).read_text())
    old_identity = portfolio["source"]["snapshot_identity"]
    old_expected = dict(recovery.EXPECTED)
    old_expected.update({
        "snapshot_sha256": old_identity["snapshot_sha256"],
        "snapshot_rows": old_identity["rows"],
        "eligible_rows": old_identity["eligible_rows"],
        "snapshot_identity_sha256": portfolio["source"][
            "snapshot_identity_sha256"
        ],
    })
    monkeypatch.setattr(recovery, "EXPECTED", old_expected)
    monkeypatch.setattr(
        recovery, "OLD_OFFSETS_SHA256", old_identity["offsets_sha256"]
    )
    monkeypatch.setattr(
        recovery, "OLD_CHUNK_INDEX_SHA256", old_identity["chunk_index_sha256"]
    )
    monkeypatch.setattr(
        recovery, "OLD_COUNTS_SHA256", old_identity["counts_sha256"]
    )
    monkeypatch.setattr(recovery, "RANKED_CHUNK_ROWS", old_identity["chunk_rows"])
    monkeypatch.setattr(
        recovery, "validate_patched_scheduler_migration", validate_package
    )
    monkeypatch.setattr(recovery, "_migration_install_entries", install_entries)
    monkeypatch.setattr(
        recovery, "_validated_install_material", validated_material
    )
    monkeypatch.setattr(recovery, "_installed_live_summary", live_summary)

    (solver_state.parent / "pipeline.lock").touch()
    receipt = recovery.install_patched_scheduler_migration(
        package, solver_state=solver_state,
    )
    assert receipt["state"] == "COMMITTED"
    assert recovery.validate_patched_scheduler_install(
        package, solver_state=solver_state,
    )["commit_sha256"] == receipt["commit_sha256"]
    return certificate_path, ledger, receipt



def _committed_arguments(
    fixture: dict[str, object],
    monkeypatch: pytest.MonkeyPatch,
    *,
    pending_digest: str = "f" * 64,
) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    certificate, installed_ledger, receipt = _temporary_committed_install(
        fixture, monkeypatch, pending_digest=pending_digest,
    )
    return (
        {
            "paths": fixture["paths"],
            "portfolio_manifest": Path(fixture["portfolio_path"]),
            "new_snapshot_manifest": Path(fixture["manifest_path"]),
            "identity_rebase_certificate": certificate,
        },
        installed_ledger,
        receipt,
    )


def _live_ledger_path(fixture: dict[str, object]) -> Path:
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    return paths.run_root / "solver-state" / "stage2-selection-ledger.json"


def _ack_live_pending(fixture: dict[str, object]) -> dict[str, object]:
    ledger_path = _live_ledger_path(fixture)
    ledger = json.loads(ledger_path.read_text())
    pending = ledger["pending"]
    assert isinstance(pending, dict)
    acknowledged = acknowledge_selection_page(
        ledger,
        pending,
        disposition="COMPLETED",
    )
    acknowledged["last_acknowledged_page_sha256"] = pending["page_sha256"]
    acknowledged["last_acknowledged_at"] = "2026-08-17T00:00:00+00:00"
    acknowledged = seal_selection_ledger(acknowledged)
    _write_json(ledger_path, acknowledged)
    return acknowledged


def _replacement_live_ledger(
    fixture: dict[str, object],
    *,
    digest: str,
    acknowledge: bool,
) -> dict[str, object]:
    manifest = json.loads(Path(fixture["manifest_path"]).read_text())
    identity = manifest["identity"]
    assert isinstance(identity, dict)
    identity_sha256 = _json_sha(identity)
    ledger = new_selection_ledger(
        binding_sha256=str(manifest["binding_sha256"]),
        snapshot_identity_sha256_value=identity_sha256,
        snapshot_rows=2,
        eligible_rows=2,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=identity_sha256,
        start_index=0,
        next_index=1,
        snapshot_rows=2,
        eligible_rows=2,
        selection_exhausted=False,
    )
    page = make_selection_page(
        binding_sha256=str(manifest["binding_sha256"]),
        snapshot_identity_sha256_value=identity_sha256,
        page_sequence=0,
        previous_ack_sha256=str(ledger["last_ack_sha256"]),
        start_index=0,
        next_index=1,
        selected_digests=[digest],
        scan_evidence=scan,
    )
    ledger = install_pending_page(ledger, page)
    if acknowledge:
        ledger = acknowledge_selection_page(
            ledger,
            page,
            disposition="COMPLETED",
        )
        ledger["last_acknowledged_page_sha256"] = page["page_sha256"]
        ledger["last_acknowledged_at"] = "2026-08-17T00:00:00+00:00"
        ledger = seal_selection_ledger(ledger)
    return ledger


def _rewrite_completed_batch(
    fixture: dict[str, object],
    *,
    audited_digests: list[str],
    ledger_digests: list[str],
    known_skipped: int = 0,
    duplicate_skipped: int = 0,
) -> None:
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    portfolio = json.loads(Path(fixture["portfolio_path"]).read_text())
    items = portfolio["items"]
    assert isinstance(items, list)
    input_rows = [
        json.loads(line)
        for line in Path(portfolio["ranked_input"]["path"]).read_text().splitlines()
    ]
    all_digests = [str(item["canonical_digest"]) for item in items]
    batch_root = paths.batches / "batch-0000"
    input_path = batch_root / "input.jsonl"
    input_path.write_bytes(
        b"".join(cli._canonical_bytes(row) + b"\n" for row in input_rows)
    )
    ranked_path = batch_root / "ranked.jsonl"
    ranked_path.write_text(
        "".join(
            json.dumps({
                "campaign_selected": True,
                "campaign_audit": {
                    "canonical_digest": digest,
                    "status": "REJECTED",
                },
            }) + "\n"
            for digest in audited_digests
        ),
        encoding="utf-8",
    )
    summary_path = batch_root / "summary.json"
    _write_json(summary_path, {
        "target_mode": cli.TARGET_MODE,
        "selected_candidates": len(audited_digests),
        "top": len(input_rows),
        "canonical_duplicates_skipped": duplicate_skipped,
        "known_codes_skipped": known_skipped,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "structural_unresolved_candidates": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
        "certificate_operational_errors": 0,
    })
    binding_sha256 = "3" * 64
    identity_sha256 = "4" * 64
    ledger = new_selection_ledger(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=identity_sha256,
        snapshot_rows=len(input_rows),
        eligible_rows=len(input_rows),
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=identity_sha256,
        start_index=0,
        next_index=len(input_rows),
        snapshot_rows=len(input_rows),
        eligible_rows=len(input_rows),
        selection_exhausted=True,
    )
    page = make_selection_page(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=identity_sha256,
        page_sequence=0,
        previous_ack_sha256=str(ledger["last_ack_sha256"]),
        start_index=0,
        next_index=len(input_rows),
        selected_digests=ledger_digests,
        scan_evidence=scan,
    )
    ledger = acknowledge_selection_page(
        install_pending_page(ledger, page),
        page,
        disposition="COMPLETED",
    )
    _write_json(batch_root / "selection-ledger.json", ledger)
    progress = cli._load_progress(paths.progress)
    assert progress is not None
    batch = dict(progress["batches"][0])
    batch.update({
        "manifest_start_row": 0,
        "manifest_next_row": len(input_rows),
        "selected_source_rows": list(range(len(input_rows))),
        "selected_portfolio_ranks": [
            int(item["portfolio_rank"]) for item in items
        ],
        "selected_digests": all_digests,
        "rows": len(input_rows),
        "input_path": str(input_path.resolve()),
        "input_sha256": cli._file_sha256(input_path),
        "ranked_output": str(ranked_path),
        "summary_output": str(summary_path),
        "status_counts": {"REJECTED": len(audited_digests)},
    })
    cli._write_progress(paths.progress, {
        **progress,
        "next_row": len(input_rows),
        "batches": [batch],
    })


def test_successor_preserves_predecessor_and_accepts_legal_post_install_ack(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    immutable = {
        path: cli._file_sha256(path)
        for path in (
            Path(fixture["portfolio_path"]),
            paths.progress,
            Path(fixture["batch_input"]),
        )
    }
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    assert created["status"] == "SUCCESSOR_READY"
    assert created["next_row"] == 1
    assert created["completed_batches"] == 1
    assert created["equivalence_method"] == migration.REBASE_EQUIVALENCE_METHOD

    acknowledged = _ack_live_pending(fixture)
    assert acknowledged["completed_pages"] == 1
    certificate = migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    successor_paths = migration.successor_sidecar_paths(paths, certificate)
    calls = 0

    def backend(argv: list[str], **_: object) -> SimpleNamespace:
        nonlocal calls
        calls += 1
        _complete_no_win(argv)
        return SimpleNamespace(returncode=0)

    result = cli.run_discovery(
        paths=successor_paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
        config=cli.DiscoveryConfig(),
        run_command=backend,
        live_source_validator=migration.successor_live_source_validator(
            certificate
        ),
    )
    assert calls == 1
    assert result["status"] == "EXHAUSTED"
    assert result["next_row"] == 2
    assert [batch["batch_index"] for batch in result["batches"]] == [0, 1]
    assert (successor_paths.batches / "batch-0001" / "input.jsonl").is_file()
    migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    assert all(cli._file_sha256(path) == digest for path, digest in immutable.items())


def test_successor_tampering_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    Path(fixture["batch_input"]).write_text("tampered\n", encoding="utf-8")
    with pytest.raises(migration.StrictDiscoveryMigrationError, match="changed|replay"):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


def test_parser_and_api_expose_only_trusted_successor_creation() -> None:
    parameters = inspect.signature(migration.create_successor_migration).parameters
    assert "old_snapshot" not in parameters
    assert "old_offsets" not in parameters
    assert parameters["identity_rebase_certificate"].default is inspect.Parameter.empty
    parser = cli.build_parser()
    with pytest.raises(SystemExit):
        parser.parse_args([
            "migrate-successor",
            "--run-id", "r",
            "--portfolio-manifest", "portfolio.json",
            "--new-snapshot-manifest", "manifest.json",
        ])
    migrated = parser.parse_args([
        "migrate-successor",
        "--run-id", "r",
        "--portfolio-manifest", "portfolio.json",
        "--new-snapshot-manifest", "manifest.json",
        "--identity-rebase-certificate", "certificate.json",
    ])
    assert migrated.identity_rebase_certificate == Path("certificate.json")
    run = parser.parse_args([
        "run",
        "--run-id", "r",
        "--portfolio-manifest", "portfolio.json",
        "--config", "config.json",
        "--successor-migration", "migration.json",
    ])
    assert run.successor_migration == Path("migration.json")


def test_self_signed_rebase_package_is_rejected(tmp_path: Path) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    certificate = (
        paths.run_root / "solver-state" / "scheduler-migration-certificate.json"
    )
    _write_json(certificate, {
        "schema_version": 1,
        "gate": migration.IDENTITY_REBASE_GATE,
        "status": "IDENTITY_REBASE_VALIDATED",
    })
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="validated main recovery package|validated COMMITTED",
    ):
        migration.create_successor_migration(
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
            new_snapshot_manifest=Path(fixture["manifest_path"]),
            identity_rebase_certificate=certificate,
        )


def test_live_ledger_must_match_committed_successor_baseline(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    manifest = json.loads(Path(fixture["manifest_path"]).read_text())
    identity = manifest["identity"]
    assert isinstance(identity, dict)
    _write_json(
        _live_ledger_path(fixture),
        new_selection_ledger(
            binding_sha256="f" * 64,
            snapshot_identity_sha256_value=_json_sha(identity),
            snapshot_rows=2,
            eligible_rows=2,
        ),
    )
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="validated COMMITTED|ledger identity/seal|COMMITTED receipt",
    ):
        migration.create_successor_migration(**arguments)


def test_successor_output_symlink_is_rejected_without_external_write(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    outside = tmp_path / "outside"
    outside.mkdir()
    (paths.root / "successors").symlink_to(outside, target_is_directory=True)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="symlink|ancestor",
    ):
        migration.create_successor_migration(**arguments)
    assert list(outside.iterdir()) == []


def test_successor_cursor_fork_and_extra_root_are_rejected(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="immutable successor lineage",
    ):
        migration.create_successor_migration(**arguments)

    progress_path = Path(created["successor_progress"])
    progress = cli._load_progress(progress_path)
    assert progress is not None
    progress["next_row"] = 2
    progress["status"] = "EXHAUSTED"
    cli._write_progress(progress_path, progress)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="next_row|terminal",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )

    extra = paths.root / "successors" / ("f" * 64)
    extra.mkdir()
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="root set|fork",
    ):
        migration.load_successor_lineage(paths, required=True)


def test_private_rowwise_verifier_rejects_symlink_and_has_no_public_route(
    tmp_path: Path,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    snapshot = Path(fixture["old_snapshot"])
    moved = snapshot.with_suffix(".real")
    snapshot.rename(moved)
    snapshot.symlink_to(moved)
    successor_snapshot = Path(fixture["manifest_path"]).with_name(
        "stage2-selection-ledger.json.ranked-snapshot.jsonl"
    )
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="symlink|regular file",
    ):
        migration._compare_rowwise(
            snapshot,
            successor_snapshot,
            run_root=paths.run_root,
            expected_rows=2,
        )


def test_lineage_routes_status_and_blocks_plain_predecessor_resume(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    report = cli.status_report(SimpleNamespace(), paths)
    assert report["status"] == "RUNNING"
    assert report["root"] == created["successor_root"]
    assert report["lineage"]["migration_sha256"] == created["migration_sha256"]
    with pytest.raises(cli.StrictDiscoveryError, match="predecessor.*immutable"):
        cli.run_discovery(
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
            config=cli.DiscoveryConfig(),
        )


def test_missing_lineage_marker_with_successor_artifacts_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    migration.create_successor_migration(**arguments)
    migration.successor_lineage_path(paths).unlink()
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="lineage is absent.*artifacts",
    ):
        migration.load_successor_lineage(paths)
    report = cli.status_report(SimpleNamespace(), paths)
    assert report["status"] == "invalid-successor-lineage"
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="lineage is absent.*artifacts",
    ):
        cli.run_discovery(
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
            config=cli.DiscoveryConfig(),
        )


def test_missing_committed_receipt_after_creation_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    marker = (
        paths.run_root / "solver-state" / recovery.INSTALL_COMMIT_NAME
    )
    marker.unlink()
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="COMMITTED marker.*regular",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


def test_crash_retry_reuses_same_certificate_and_lineage(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    original = migration._write_new_json
    failed_once = False

    def interrupt(
        path: Path,
        value: object,
        *,
        run_root: Path,
        label: str,
    ) -> None:
        nonlocal failed_once
        if label == "strict successor progress" and not failed_once:
            failed_once = True
            raise RuntimeError("injected crash")
        original(path, value, run_root=run_root, label=label)

    monkeypatch.setattr(migration, "_write_new_json", interrupt)
    with pytest.raises(RuntimeError, match="injected crash"):
        migration.create_successor_migration(**arguments)
    roots = list((paths.root / "successors").iterdir())
    assert len(roots) == 1
    first_sha = roots[0].name
    pre_link_temp = roots[0] / (
        ".progress.json.123." + ("a" * 32) + ".tmp"
    )
    pre_link_temp.write_text("staged progress\n", encoding="utf-8")
    post_link_temp = roots[0] / (
        ".migration.json.123." + ("b" * 32) + ".tmp"
    )
    post_link_temp.hardlink_to(roots[0] / "migration.json")

    monkeypatch.setattr(migration, "_write_new_json", original)
    created = migration.create_successor_migration(**arguments)
    assert created["migration_sha256"] == first_sha
    assert migration.load_successor_lineage(paths)["migration_sha256"] == first_sha


def test_crash_recovery_rejects_unexpected_successor_artifact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    original = migration._write_new_json

    def interrupt(
        path: Path,
        value: object,
        *,
        run_root: Path,
        label: str,
    ) -> None:
        if label == "strict successor progress":
            raise RuntimeError("injected crash")
        original(path, value, run_root=run_root, label=label)

    monkeypatch.setattr(migration, "_write_new_json", interrupt)
    with pytest.raises(RuntimeError, match="injected crash"):
        migration.create_successor_migration(**arguments)
    successor_root = next((paths.root / "successors").iterdir())
    (successor_root / "unexpected").mkdir()
    monkeypatch.setattr(migration, "_write_new_json", original)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="unexpected artifacts",
    ):
        migration.create_successor_migration(**arguments)


def test_chunk_identity_and_batch_semantics_are_replayed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    chunk_fixture = _fixture(tmp_path / "chunk")
    manifest_path = Path(chunk_fixture["manifest_path"])
    manifest = json.loads(manifest_path.read_text())
    manifest["identity"]["chunk_index_sha256"] = "f" * 64
    unsigned = dict(manifest)
    unsigned.pop("manifest_sha256", None)
    manifest["manifest_sha256"] = _json_sha(unsigned)
    _write_json(manifest_path, manifest)
    arguments, _, _ = _committed_arguments(chunk_fixture, monkeypatch)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="chunk index|identity",
    ):
        migration.create_successor_migration(**arguments)

    monkeypatch.undo()
    batch_fixture = _fixture(tmp_path / "batch")
    summary = Path(batch_fixture["batch_input"]).with_name("summary.json")
    _write_json(summary, {"status": "complete"})
    arguments, _, _ = _committed_arguments(batch_fixture, monkeypatch)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="output semantics",
    ):
        migration.create_successor_migration(**arguments)


def test_trusted_rebase_binds_immutable_receipt_and_rejects_illegal_first_ack(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, installed_ledger, receipt = _committed_arguments(
        fixture, monkeypatch,
    )
    created = migration.create_successor_migration(**arguments)
    successor = migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    equivalence = successor["successor"]["equivalence"]
    assert equivalence["method"] == migration.REBASE_EQUIVALENCE_METHOD
    install = equivalence["identity_rebase"]["install"]
    assert install["state"] == "COMMITTED"
    assert install["commit_sha256"] == receipt["commit_sha256"]

    replacement = _replacement_live_ledger(
        fixture,
        digest="2" * 64,
        acknowledge=True,
    )
    assert replacement["progress_sha256"] != installed_ledger["progress_sha256"]
    _write_json(_live_ledger_path(fixture), replacement)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="no longer extends",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


def test_post_ack_static_ledger_tamper_is_not_a_legal_extension(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    acknowledged = _ack_live_pending(fixture)
    acknowledged["generation_history"] = [{"tampered": True}]
    _write_json(
        _live_ledger_path(fixture),
        seal_selection_ledger(acknowledged),
    )
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="no longer extends",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


def test_resealed_receipt_tamper_is_rejected(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    journal_path = (
        paths.run_root / "solver-state" / recovery.INSTALL_JOURNAL_NAME
    )
    journal = json.loads(journal_path.read_text())
    journal["package_root"] = str(paths.run_root / "different-package")
    unsigned = dict(journal)
    unsigned.pop("journal_sha256", None)
    journal["journal_sha256"] = recovery.canonical_sha256(unsigned)
    _write_json(journal_path, journal)
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="COMMITTED receipt|immutable receipt",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


@pytest.mark.parametrize(
    ("known_skipped", "duplicate_skipped"),
    [(1, 0), (0, 1)],
)
def test_completed_batch_allows_exact_known_or_duplicate_skip_accounting(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    known_skipped: int,
    duplicate_skipped: int,
) -> None:
    fixture = _fixture(tmp_path)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    _rewrite_completed_batch(
        fixture,
        audited_digests=["2" * 64],
        ledger_digests=["2" * 64],
        known_skipped=known_skipped,
        duplicate_skipped=duplicate_skipped,
    )
    created = migration.create_successor_migration(**arguments)
    assert created["status"] == "SUCCESSOR_READY"


@pytest.mark.parametrize(
    ("audited", "ledger", "known_skipped"),
    [
        (["2" * 64, "1" * 64], ["2" * 64, "1" * 64], 0),
        (["1" * 64], ["1" * 64, "2" * 64], 1),
        (["1" * 64, "2" * 64], ["1" * 64], 0),
    ],
)
def test_completed_batch_rejects_reordered_inserted_or_dropped_ledger_digest(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    audited: list[str],
    ledger: list[str],
    known_skipped: int,
) -> None:
    fixture = _fixture(tmp_path)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    _rewrite_completed_batch(
        fixture,
        audited_digests=audited,
        ledger_digests=ledger,
        known_skipped=known_skipped,
    )
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="ledger selected digests diverge",
    ):
        migration.create_successor_migration(**arguments)


def test_successor_batches_symlink_fails_before_backend_and_external_write(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    certificate = migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    successor_paths = migration.successor_sidecar_paths(paths, certificate)
    outside = tmp_path / "outside-batches"
    outside.mkdir()
    successor_paths.batches.symlink_to(outside, target_is_directory=True)
    calls = 0

    def backend(*_: object, **__: object) -> SimpleNamespace:
        nonlocal calls
        calls += 1
        return SimpleNamespace(returncode=0)

    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="symlink|ancestor",
    ):
        cli.run_discovery(
            paths=successor_paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
            config=cli.DiscoveryConfig(),
            run_command=backend,
            live_source_validator=migration.successor_live_source_validator(
                certificate
            ),
        )
    assert calls == 0
    assert list(outside.iterdir()) == []


@pytest.mark.parametrize("tamper", ["digest", "next_row", "argv"])
def test_active_successor_batch_full_replay_rejects_tamper(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    tamper: str,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    certificate = migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    successor_paths = migration.successor_sidecar_paths(paths, certificate)
    result = cli.run_discovery(
        paths=successor_paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
        config=cli.DiscoveryConfig(),
        run_command=lambda *_args, **_kwargs: SimpleNamespace(returncode=1),
        live_source_validator=migration.successor_live_source_validator(
            certificate
        ),
    )
    assert result["status"] == "FAILED"
    progress = cli._load_progress(successor_paths.progress)
    assert progress is not None
    active = dict(progress["active_batch"])
    if tamper == "digest":
        active["selected_digests"] = ["f" * 64]
    elif tamper == "next_row":
        active["manifest_next_row"] = active["manifest_start_row"]
    else:
        active["argv"] = [*active["argv"], "--tampered"]
    cli._write_progress(successor_paths.progress, {
        **progress,
        "active_batch": active,
    })
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="active batch|argv",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


@pytest.mark.parametrize("phase", ["launch_live_source", "post_live_source"])
def test_completed_successor_overlap_fence_tamper_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    phase: str,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    certificate = migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    successor_paths = migration.successor_sidecar_paths(paths, certificate)

    def backend(argv: list[str], **_: object) -> SimpleNamespace:
        _complete_no_win(argv)
        return SimpleNamespace(returncode=0)

    result = cli.run_discovery(
        paths=successor_paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
        config=cli.DiscoveryConfig(),
        run_command=backend,
        live_source_validator=migration.successor_live_source_validator(
            certificate
        ),
    )
    batch = dict(result["batches"][1])
    fence = dict(batch[phase])
    fence["overlap"] = True
    batch[phase] = fence
    cli._write_progress(successor_paths.progress, {
        **result,
        "batches": [result["batches"][0], batch],
    })
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="overlap fences",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


def test_validator_source_symlink_ancestor_is_rejected(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, receipt = _committed_arguments(fixture, monkeypatch)
    monkeypatch.setattr(
        recovery,
        "validate_patched_scheduler_install",
        lambda *_args, **_kwargs: dict(receipt),
    )
    real_source = Path(recovery.__file__).resolve(strict=True)
    source_root = paths.run_root / "validator-source"
    source_root.mkdir()
    (source_root / "linked-parent").symlink_to(
        real_source.parent,
        target_is_directory=True,
    )
    monkeypatch.setattr(
        recovery,
        "__file__",
        str(source_root / "linked-parent" / real_source.name),
    )
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="symlink|ancestor",
    ):
        migration.create_successor_migration(**arguments)

def test_create_rejects_foreground_overlap_with_predecessor_prefix(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    arguments, _, _ = _committed_arguments(
        fixture, monkeypatch, pending_digest="1" * 64,
    )
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="ownership overlaps",
    ):
        migration.create_successor_migration(**arguments)


def test_load_rejects_tampered_immutable_installed_artifact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    artifact = paths.run_root / "solver-state" / "stage2-transition-archive.json"
    artifact.write_text("tampered transition evidence\n", encoding="utf-8")
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="immutable installed migration artifact",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


def test_load_rejects_resealed_last_ack_metadata_tamper(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    acknowledged = _ack_live_pending(fixture)
    acknowledged["last_acknowledged_page_sha256"] = "e" * 64
    _write_json(
        _live_ledger_path(fixture), seal_selection_ledger(acknowledged),
    )
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="no longer extends",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


def test_load_rejects_foreground_collision_after_completed_successor_batch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    _ack_live_pending(fixture)
    certificate = migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    successor_paths = migration.successor_sidecar_paths(paths, certificate)
    result = cli.run_discovery(
        paths=successor_paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
        config=cli.DiscoveryConfig(),
        run_command=lambda argv, **_: (
            _complete_no_win(argv) or SimpleNamespace(returncode=0)
        ),
        live_source_validator=migration.successor_live_source_validator(
            certificate
        ),
    )
    assert result["status"] == "EXHAUSTED"

    ledger_path = _live_ledger_path(fixture)
    ledger = json.loads(ledger_path.read_text())
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=ledger["snapshot_identity_sha256"],
        start_index=1,
        next_index=2,
        snapshot_rows=2,
        eligible_rows=2,
        selection_exhausted=True,
    )
    page = make_selection_page(
        binding_sha256=ledger["binding_sha256"],
        snapshot_identity_sha256_value=ledger["snapshot_identity_sha256"],
        page_sequence=1,
        previous_ack_sha256=ledger["last_ack_sha256"],
        start_index=1,
        next_index=2,
        selected_digests=["2" * 64],
        scan_evidence=scan,
    )
    ledger = acknowledge_selection_page(
        install_pending_page(ledger, page), page, disposition="COMPLETED",
    )
    ledger["last_acknowledged_page_sha256"] = page["page_sha256"]
    ledger["last_acknowledged_at"] = "2026-08-17T00:00:01+00:00"
    _write_json(ledger_path, seal_selection_ledger(ledger))
    with pytest.raises(
        migration.StrictDiscoveryMigrationError,
        match="foreground ownership overlaps",
    ):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )


@pytest.mark.parametrize("tamper", ["summary", "running_with_win"])
def test_proven_successor_requires_complete_output_and_terminal_state(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    tamper: str,
) -> None:
    fixture = _fixture(tmp_path)
    paths = fixture["paths"]
    assert isinstance(paths, cli.SidecarPaths)
    arguments, _, _ = _committed_arguments(fixture, monkeypatch)
    created = migration.create_successor_migration(**arguments)
    certificate = migration.load_successor_migration(
        Path(created["certificate"]),
        paths=paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
    )
    successor_paths = migration.successor_sidecar_paths(paths, certificate)
    result = cli.run_discovery(
        paths=successor_paths,
        portfolio_manifest=Path(fixture["portfolio_path"]),
        config=cli.DiscoveryConfig(),
        run_command=lambda argv, **_: (
            _complete_win(argv) or SimpleNamespace(returncode=2)
        ),
        live_source_validator=migration.successor_live_source_validator(
            certificate
        ),
    )
    assert result["status"] == "STRICT_THRESHOLD_PROVEN"
    if tamper == "summary":
        summary = Path(result["batches"][-1]["summary_output"])
        value = json.loads(summary.read_text())
        value["selected_candidates"] = 0
        _write_json(summary, value)
        expected = "output semantics"
    else:
        cli._write_progress(successor_paths.progress, {
            **result,
            "status": "RUNNING",
        })
        expected = "terminal/active status"
    with pytest.raises(migration.StrictDiscoveryMigrationError, match=expected):
        migration.load_successor_migration(
            Path(created["certificate"]),
            paths=paths,
            portfolio_manifest=Path(fixture["portfolio_path"]),
        )
