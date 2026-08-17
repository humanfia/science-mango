"""Offline, fail-closed replay of the lost Stage 2 selection ACK prefix.

This is deliberately not part of the live pipeline.  It reconstructs only the
cryptographic selection-ledger core from immutable evidence and writes to a
new caller-selected directory.  It never edits the snapshot, transition
archive, registry, pending page, or a production run directory.

The recovery is accepted only if all independently recorded anchors from the
2026-08 Stage 2 run match, including the 851 MB snapshot hash, the rebound
44-page ACK head, and the already-sealed sequence-44 pending page.
"""

from __future__ import annotations

import fcntl
import argparse
import hashlib
import json
import os
import shutil
import stat
import struct
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Iterable, Iterator, Mapping, Sequence


EXPECTED = {
    "snapshot_sha256": (
        "9dcda8afa9dda8a6b076a062913f7869b2fac5847cbd2f62c9eb54155b9c78ef"
    ),
    "snapshot_bytes": 851_334_437,
    "snapshot_rows": 148_339,
    "eligible_rows": 148_285,
    "snapshot_identity_sha256": (
        "68301ae1caa36c3a80506833db5932272717e79c99ef10d52011dcc6392959e1"
    ),
    "final_binding_sha256": (
        "cb786f019313fcf7cc8f4fb53cbfda214b6f649c8a776895e5fe4521d24f6d54"
    ),
    "transition_archive_sha256": (
        "1591abf2a1f3f20091574f3b826c9dfaff012127fe9469893fdb298c71d20ee7"
    ),
    "transition_cursor": 4_000,
    "transition_completed_pages": 31,
    "transition_committed": 4_000,
    "pending_file_sha256": (
        "54ced9d53e5b8883eb24789908c16e72cc6b37afd3922b116c9bedf0cfc2119b"
    ),
    "pending_sequence": 44,
    "pending_start": 57_253,
    "pending_next": 61_350,
    "pending_selected": 4_096,
    "pending_page_sha256": (
        "3185381d94d6b887e660fc868e07202bcbc2bddc8be448156ab64d898c9fb6aa"
    ),
    "registry_file_sha256": (
        "265f1a3fefef884adeaa980a5dce2441dee4f6f6d71c253ba7a6491360733689"
    ),
    "evaluations_sha256": (
        "83bb05c1c56adfa7061cb7ef77f9a6e2935a814c086da9688c04412b4c7d4ccb"
    ),
    "evaluations_bytes": 395_994,
    "terminal_rows": 54,
    "terminal_symplectic_witnesses": 25,
    "terminal_css_witnesses": 29,
    "completed_pages": 44,
    "cursor": 57_253,
    "committed": 57_248,
    "last_ack_sha256": (
        "7dba1fb3b09b0b268c324772cdc057f73d94bc5ef64a8571d1c0078ed112248b"
    ),
    "original_ledger_file_sha256": (
        "19ef21b47308757655727c95741d1020cceaca398f5338cbecb313503dbb4598"
    ),
    "original_ledger_progress_sha256": (
        "bafa0c11afa870a4fa5e13cf1fd84d0085a52fb29cf0da1680a495d3388c03a9"
    ),
}

LEDGER_SCHEMA_VERSION = 2
LEDGER_GATE = "qldpc-stage2-selection-ledger"
SCAN_SCHEMA_VERSION = 1
SCAN_GATE = "qldpc-stage2-ranked-scan"
ACK_GATE = "qldpc-stage2-selection-ack"
GENESIS_GATE = "qldpc-stage2-selection-genesis"

PAGE_POLICY = (
    {"top": 96, "clean_pages": 4},
    {"top": 192, "clean_pages": 1},
    {"top": 1024, "clean_pages": 1},
    {"top": 4096, "clean_pages": None},
)
PAGE_SCHEDULER_GATE = "qldpc-stage2-adaptive-page-scheduler"
PAGE_TRANSITION_GATE = "qldpc-stage2-page-size-transition"
MIGRATION_GATE = "qldpc-stage2-patched-identity-scheduler-migration-v1"
RECOVERY_REASON = "SEALED_CORE_RECOVERY"
OLD_COUNTS = {
    "input_records": 329_048,
    "unique_candidates": 148_339,
    "duplicate_records": 180_709,
    "rejected_candidates": 54,
    "eligible_candidates": 148_285,
    "structural_unresolved_candidates": 0,
    "trusted_stage1_rejections": 54,
}
OLD_COUNTS_SHA256 = (
    "1fc8380565e5e81be92191521ea6e627abd3da9b224229852e1bcd6d992ecc75"
)
OLD_OFFSETS_SHA256 = (
    "6885e59955d50e621236dd4c3ec220900b8433ac4959deae540da28da833b74f"
)
OLD_OFFSETS_BYTES = (EXPECTED["snapshot_rows"] + 1) * 8
OLD_CHUNK_INDEX_SHA256 = (
    "1cb6e65c7e042ba2e7301bded56f34cb44a0df0ee16a2ffa7abf52286387e5f1"
)
RANKED_CHUNK_ROWS = 128


class RecoveryError(RuntimeError):
    """Raised whenever an offline input or reconstructed anchor diverges."""


def canonical_sha256(value: Any) -> str:
    payload = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RecoveryError(message)


def require_regular_input(path: Path, label: str) -> os.stat_result:
    try:
        metadata = path.lstat()
    except OSError as exc:
        raise RecoveryError(f"{label} is unavailable: {path}") from exc
    require(
        stat.S_ISREG(metadata.st_mode) and not stat.S_ISLNK(metadata.st_mode),
        f"{label} must be a regular non-symlink file: {path}",
    )
    return metadata


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json_object(path: Path, label: str) -> dict[str, Any]:
    require_regular_input(path, label)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecoveryError(f"{label} is not valid JSON: {path}") from exc
    require(isinstance(value, dict), f"{label} must contain a JSON object")
    return value


def genesis_sha256(binding_sha256: str, generation: int = 0) -> str:
    return canonical_sha256({
        "gate": GENESIS_GATE,
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": EXPECTED[
            "snapshot_identity_sha256"
        ],
        "snapshot_rows": EXPECTED["snapshot_rows"],
        "eligible_rows": EXPECTED["eligible_rows"],
        "generation": generation,
    })


def make_scan_evidence(start_index: int, next_index: int) -> dict[str, Any]:
    payload = {
        "schema_version": SCAN_SCHEMA_VERSION,
        "gate": SCAN_GATE,
        "snapshot_identity_sha256": EXPECTED[
            "snapshot_identity_sha256"
        ],
        "start_index": start_index,
        "next_index": next_index,
        "snapshot_rows": EXPECTED["snapshot_rows"],
        "eligible_rows": EXPECTED["eligible_rows"],
        "selection_exhausted": next_index == EXPECTED["eligible_rows"],
    }
    return {**payload, "scan_sha256": canonical_sha256(payload)}


def make_page(
    *,
    sequence: int,
    previous_ack_sha256: str,
    start_index: int,
    next_index: int,
    selected_digests: Sequence[str],
) -> dict[str, Any]:
    payload = {
        "binding_sha256": EXPECTED["final_binding_sha256"],
        "snapshot_identity_sha256": EXPECTED[
            "snapshot_identity_sha256"
        ],
        "page_sequence": sequence,
        "previous_ack_sha256": previous_ack_sha256,
        "start_index": start_index,
        "next_index": next_index,
        "selected_digests": list(selected_digests),
        "scan_evidence": make_scan_evidence(start_index, next_index),
    }
    return {**payload, "page_sha256": canonical_sha256(payload)}


def make_completed_ack(
    page: Mapping[str, Any],
    *,
    sequence: int,
    previous_ack_sha256: str,
) -> dict[str, Any]:
    payload = {
        "gate": ACK_GATE,
        "sequence": sequence,
        "previous_ack_sha256": previous_ack_sha256,
        "disposition": "COMPLETED",
        "deferred_entry_sha256": None,
        "page_sha256": page["page_sha256"],
        "page": dict(page),
    }
    return {**payload, "ack_sha256": canonical_sha256(payload)}


@dataclass(frozen=True)
class ReplayState:
    ack_chain: list[dict[str, Any]]
    committed_digests: list[str]
    cursor: int
    last_ack_sha256: str


def validate_and_rebind_archive(
    archive: Mapping[str, Any],
) -> ReplayState:
    """Validate the page-31 archive and rebind all ACKs to final top=4096."""

    require(
        archive.get("schema_version") == LEDGER_SCHEMA_VERSION
        and archive.get("gate") == LEDGER_GATE,
        "transition archive is not a Stage 2 v2 selection ledger",
    )
    require(
        archive.get("snapshot_identity_sha256")
        == EXPECTED["snapshot_identity_sha256"]
        and archive.get("snapshot_rows") == EXPECTED["snapshot_rows"]
        and archive.get("eligible_rows") == EXPECTED["eligible_rows"],
        "transition archive snapshot identity diverges",
    )
    require(
        archive.get("cursor") == EXPECTED["transition_cursor"]
        and archive.get("completed_pages")
        == EXPECTED["transition_completed_pages"],
        "transition archive cursor/page count diverges",
    )
    committed = archive.get("committed_digests")
    raw_chain = archive.get("ack_chain")
    require(
        isinstance(committed, list)
        and len(committed) == EXPECTED["transition_committed"]
        and len(set(committed)) == len(committed)
        and all(is_sha256(item) for item in committed),
        "transition archive committed digests are malformed",
    )
    require(
        isinstance(raw_chain, list)
        and len(raw_chain) == EXPECTED["transition_completed_pages"],
        "transition archive ACK chain length diverges",
    )
    unsigned_archive = dict(archive)
    progress_sha256 = unsigned_archive.pop("progress_sha256", None)
    require(
        is_sha256(progress_sha256)
        and canonical_sha256(unsigned_archive) == progress_sha256,
        "transition archive progress seal is invalid",
    )

    old_binding = archive.get("binding_sha256")
    generation = archive.get("generation")
    require(is_sha256(old_binding), "archive binding is malformed")
    require(
        isinstance(generation, int)
        and not isinstance(generation, bool)
        and generation == 0,
        "only generation-zero recovery is supported",
    )

    old_previous = genesis_sha256(str(old_binding), generation)
    new_previous = genesis_sha256(EXPECTED["final_binding_sha256"], generation)
    old_cursor = 0
    old_committed: list[str] = []
    rebound_chain: list[dict[str, Any]] = []
    for sequence, raw_ack in enumerate(raw_chain):
        require(isinstance(raw_ack, Mapping), f"ACK {sequence} is malformed")
        ack = dict(raw_ack)
        unsigned_ack = dict(ack)
        ack_sha256 = unsigned_ack.pop("ack_sha256", None)
        page = ack.get("page")
        require(isinstance(page, Mapping), f"ACK {sequence} lacks a page")
        page = dict(page)
        unsigned_page = dict(page)
        page_sha256 = unsigned_page.pop("page_sha256", None)
        scan = page.get("scan_evidence")
        require(isinstance(scan, Mapping), f"page {sequence} lacks scan evidence")
        unsigned_scan = dict(scan)
        scan_sha256 = unsigned_scan.pop("scan_sha256", None)
        selected = page.get("selected_digests")
        require(
            ack.get("gate") == ACK_GATE
            and ack.get("sequence") == sequence
            and ack.get("previous_ack_sha256") == old_previous
            and ack.get("disposition") == "COMPLETED"
            and ack.get("deferred_entry_sha256") is None
            and ack.get("page_sha256") == page_sha256
            and ack_sha256 == canonical_sha256(unsigned_ack),
            f"archive ACK {sequence} does not replay",
        )
        require(
            page.get("binding_sha256") == old_binding
            and page.get("snapshot_identity_sha256")
            == EXPECTED["snapshot_identity_sha256"]
            and page.get("page_sequence") == sequence
            and page.get("previous_ack_sha256") == old_previous
            and page.get("start_index") == old_cursor
            and isinstance(page.get("next_index"), int)
            and page["next_index"] > old_cursor
            and isinstance(selected, list)
            and selected
            and all(is_sha256(item) for item in selected)
            and not set(old_committed).intersection(selected)
            and page_sha256 == canonical_sha256(unsigned_page),
            f"archive page {sequence} does not replay",
        )
        require(
            scan.get("schema_version") == SCAN_SCHEMA_VERSION
            and scan.get("gate") == SCAN_GATE
            and scan.get("snapshot_identity_sha256")
            == EXPECTED["snapshot_identity_sha256"]
            and scan.get("start_index") == old_cursor
            and scan.get("next_index") == page["next_index"]
            and scan.get("snapshot_rows") == EXPECTED["snapshot_rows"]
            and scan.get("eligible_rows") == EXPECTED["eligible_rows"]
            and scan.get("selection_exhausted") is False
            and scan_sha256 == canonical_sha256(unsigned_scan),
            f"archive scan evidence {sequence} does not replay",
        )

        rebound_page = make_page(
            sequence=sequence,
            previous_ack_sha256=new_previous,
            start_index=old_cursor,
            next_index=int(page["next_index"]),
            selected_digests=selected,
        )
        rebound_ack = make_completed_ack(
            rebound_page,
            sequence=sequence,
            previous_ack_sha256=new_previous,
        )
        rebound_chain.append(rebound_ack)
        old_previous = str(ack_sha256)
        new_previous = rebound_ack["ack_sha256"]
        old_cursor = int(page["next_index"])
        old_committed.extend(selected)

    require(
        old_previous == archive.get("last_ack_sha256")
        and old_cursor == archive.get("cursor")
        and old_committed == committed,
        "archive terminal progress does not match its ACK replay",
    )
    return ReplayState(
        ack_chain=rebound_chain,
        committed_digests=list(committed),
        cursor=old_cursor,
        last_ack_sha256=new_previous,
    )


def registry_digests(registry: Mapping[str, Any]) -> set[str]:
    entries = registry.get("entries")
    require(isinstance(entries, list), "known-code registry lacks entries")
    digests: set[str] = set()
    for index, entry in enumerate(entries):
        require(
            isinstance(entry, Mapping)
            and is_sha256(entry.get("canonical_digest")),
            f"known-code registry entry {index} lacks a canonical digest",
        )
        digests.add(str(entry["canonical_digest"]))
    return digests


def replay_terminal_evaluations(
    path: Path,
    *,
    evaluations_payload: bytes | None = None,
    evidence_overrides: Mapping[str, Path] | None = None,
    stable_root: Path | None = None,
) -> dict[str, Any]:
    """Rebuild and reverify all 54 legacy Stage 1 terminal witnesses."""

    from evaluation.bb_code import (
        build_bb_code,
        get_code_params_fast,
        validate_terms,
    )
    from evaluation.evaluator import (
        _validate_replayable_css_witness,
        _validate_replayable_symplectic_witness,
    )
    from evaluation.geometry import candidate_geometry

    metadata_before: os.stat_result | None = None
    if evaluations_payload is None:
        metadata_before = require_regular_input(path, "Stage 1 evaluations")
        require(
            metadata_before.st_size == EXPECTED["evaluations_bytes"]
            and file_sha256(path) == EXPECTED["evaluations_sha256"],
            "Stage 1 evaluations do not match the old snapshot binding",
        )
        evaluations_payload = path.read_bytes()
    require(
        len(evaluations_payload) == EXPECTED["evaluations_bytes"]
        and hashlib.sha256(evaluations_payload).hexdigest()
        == EXPECTED["evaluations_sha256"],
        "Stage 1 evaluations bytes do not match the old snapshot binding",
    )
    records: list[dict[str, Any]] = []
    candidate_keys: set[str] = set()
    canonical_digests: set[str] = set()
    kind_counts = {"SYMPLECTIC": 0, "CSS": 0}
    for line_number, payload in enumerate(
        evaluations_payload.splitlines(keepends=True), start=1,
    ):
            require(
                payload.endswith(b"\n"),
                f"evaluations row {line_number} is partial",
            )
            try:
                row = json.loads(payload)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise RecoveryError(
                    f"evaluations row {line_number} is invalid JSON"
                ) from exc
            require(
                isinstance(row, dict),
                f"evaluations row {line_number} is not an object",
            )
            audit = row.get("audit_attempt")
            structural = row.get("structural_novelty")
            witness = row.get("threshold_proof_witness")
            candidate_key = row.get("candidate_key")
            canonical_digest = (
                structural.get("canonical_digest")
                if isinstance(structural, Mapping)
                else None
            )
            n = row.get("n")
            k = row.get("k")
            distance = row.get("threshold_proof_distance")
            ell = row.get("ell")
            m = row.get("m")
            a_terms = row.get("A_terms")
            b_terms = row.get("B_terms")
            require(
                isinstance(audit, Mapping)
                and audit.get("schema_version") == 2
                and audit.get("candidate_key") == candidate_key
                and audit.get("n") == n
                and audit.get("k") == k
                and row.get("threshold_rejection_proven") is True
                and row.get("threshold_proof_trusted") is True
                and row.get("search_status") in {"terminal_negative", "exact"},
                f"evaluations row {line_number} lacks a sealed terminal audit",
            )
            require(
                isinstance(candidate_key, str)
                and candidate_key
                and candidate_key not in candidate_keys
                and is_sha256(canonical_digest)
                and canonical_digest not in canonical_digests,
                f"evaluations row {line_number} has a malformed identity",
            )
            require(
                all(
                    isinstance(value, int)
                    and not isinstance(value, bool)
                    and value > 0
                    for value in (n, k, distance, ell, m)
                )
                and row.get("d") == distance
                and isinstance(a_terms, list)
                and isinstance(b_terms, list),
                f"evaluations row {line_number} has malformed parameters",
            )
            assert isinstance(n, int)
            assert isinstance(k, int)
            assert isinstance(distance, int)
            assert isinstance(ell, int)
            assert isinstance(m, int)
            validate_terms(ell, m, a_terms, "A")
            validate_terms(ell, m, b_terms, "B")
            code = build_bb_code(
                ell,
                m,
                a_terms,
                b_terms,
                geometry=candidate_geometry(row),
            )
            rebuilt_n, rebuilt_k = get_code_params_fast(code)
            require(
                rebuilt_n == n and rebuilt_k == k,
                f"evaluations row {line_number} rebuild changed n/k",
            )
            fields = set(witness) if isinstance(witness, Mapping) else set()
            if fields == {
                "side",
                "index",
                "dual_side",
                "dual_index",
                "weight",
                "bits",
            }:
                witness_kind = "SYMPLECTIC"
                replayed = _validate_replayable_symplectic_witness(
                    code,
                    witness,
                    distance=distance,
                )
            elif fields == {"side", "index", "weight", "bits"}:
                witness_kind = "CSS"
                replayed = _validate_replayable_css_witness(
                    code,
                    witness,
                    distance=distance,
                )
            else:
                raise RecoveryError(
                    f"evaluations row {line_number} has unknown witness kind"
                )
            require(
                replayed == witness,
                f"evaluations row {line_number} witness failed matrix replay",
            )
            lhs = k * distance * distance
            rhs = 12 * n
            require(
                lhs < rhs,
                f"evaluations row {line_number} does not prove FOM < 12",
            )
            evidence = audit.get("evidence")
            require(
                isinstance(evidence, Mapping)
                and is_sha256(evidence.get("sha256"))
                and isinstance(evidence.get("path"), str),
                f"evaluations row {line_number} lacks checkpoint evidence",
            )
            source_evidence_path = str(evidence["path"])
            evidence_path = (
                evidence_overrides.get(source_evidence_path)
                if evidence_overrides is not None
                else Path(source_evidence_path)
            )
            require(
                isinstance(evidence_path, Path),
                f"evaluations row {line_number} checkpoint is not packaged",
            )
            if stable_root is None:
                evidence_metadata = require_regular_input(
                    evidence_path,
                    f"row {line_number} checkpoint evidence",
                )
                evidence_bytes = int(evidence_metadata.st_size)
                evidence_sha256 = file_sha256(evidence_path)
            else:
                evidence_sha256, evidence_bytes = _stable_sha256(
                    evidence_path, expected_root=stable_root,
                )
            require(
                evidence_bytes == evidence.get("bytes")
                and evidence_sha256 == evidence.get("sha256"),
                f"evaluations row {line_number} evidence diverges",
            )
            record_payload = {
                "source_line": line_number,
                "candidate_key": candidate_key,
                "canonical_digest": canonical_digest,
                "n": n,
                "k": k,
                "distance_upper_bound": distance,
                "threshold_lhs": lhs,
                "threshold_rhs": rhs,
                "strictly_below_12": True,
                "witness_kind": witness_kind,
                "witness_sha256": canonical_sha256(witness),
                "checkpoint_evidence_sha256": evidence["sha256"],
                "source_search_status": row["search_status"],
                "verifier_result": "VALID",
            }
            records.append({
                **record_payload,
                "record_sha256": canonical_sha256(record_payload),
            })
            candidate_keys.add(candidate_key)
            canonical_digests.add(str(canonical_digest))
            kind_counts[witness_kind] += 1
    if metadata_before is not None:
        metadata_after = path.lstat()
        require(
            (
                metadata_before.st_dev,
                metadata_before.st_ino,
                metadata_before.st_size,
                metadata_before.st_mtime_ns,
            )
            == (
                metadata_after.st_dev,
                metadata_after.st_ino,
                metadata_after.st_size,
                metadata_after.st_mtime_ns,
            ),
            "Stage 1 evaluations changed during terminal replay",
        )
    require(
        len(records) == EXPECTED["terminal_rows"]
        and kind_counts["SYMPLECTIC"]
        == EXPECTED["terminal_symplectic_witnesses"]
        and kind_counts["CSS"] == EXPECTED["terminal_css_witnesses"],
        "terminal replay row/witness counts diverge",
    )
    report_payload = {
        "schema_version": 1,
        "gate": "qldpc-stage2-recovered-terminal-witness-replay-v1",
        "source_evaluations": {
            "path": str(path),
            "bytes": EXPECTED["evaluations_bytes"],
            "sha256": EXPECTED["evaluations_sha256"],
        },
        "rows": len(records),
        "valid_witnesses": len(records),
        "witness_kind_counts": kind_counts,
        "all_rebuilt_n_k_match": True,
        "all_strictly_below_12": True,
        "records": records,
    }
    return {
        **report_payload,
        "report_sha256": canonical_sha256(report_payload),
    }


def terminal_checkpoint_records(
    evaluations_payload: bytes,
) -> list[dict[str, Any]]:
    """Return the exact 54 checkpoint references embedded in evaluations."""

    require(
        len(evaluations_payload) == EXPECTED["evaluations_bytes"]
        and hashlib.sha256(evaluations_payload).hexdigest()
        == EXPECTED["evaluations_sha256"],
        "terminal checkpoint inventory evaluations bytes diverge",
    )
    records: list[dict[str, Any]] = []
    source_paths: set[str] = set()
    for line_number, payload in enumerate(
        evaluations_payload.splitlines(keepends=True), start=1,
    ):
        try:
            row = json.loads(payload)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise RecoveryError(
                f"terminal checkpoint row {line_number} is malformed"
            ) from exc
        evidence = row.get("audit_attempt", {}).get("evidence")
        source_path = evidence.get("path") if isinstance(evidence, Mapping) else None
        require(
            isinstance(source_path, str) and source_path not in source_paths
            and is_sha256(evidence.get("sha256"))
            and isinstance(evidence.get("bytes"), int)
            and not isinstance(evidence.get("bytes"), bool)
            and evidence["bytes"] >= 0,
            f"terminal checkpoint row {line_number} has invalid evidence",
        )
        records.append({
            "source_line": line_number,
            "source_path": source_path,
            "bytes": evidence["bytes"],
            "sha256": evidence["sha256"],
        })
        source_paths.add(source_path)
    require(len(records) == EXPECTED["terminal_rows"], "terminal checkpoint count diverges")
    return records


def trusted_terminal_rejection(row: Mapping[str, Any]) -> bool:
    trusted = row.get("trusted_stage1_audit")
    formal = bool(
        isinstance(trusted, Mapping)
        and trusted.get("validated") is True
        and trusted.get("outcome") == "REJECTED"
    )
    oracle = row.get("trusted_search_oracle_rejection")
    search_oracle = bool(
        isinstance(oracle, Mapping)
        and oracle.get("validated") is True
        and oracle.get("outcome") == "REJECTED"
        and oracle.get("source") == "low_weight_oracle"
    )
    return formal or search_oracle


@dataclass(frozen=True)
class SnapshotRow:
    index: int
    canonical_digest: str
    known_code: bool


def read_and_verify_snapshot(
    path: Path,
    *,
    known_digests: set[str],
) -> list[SnapshotRow]:
    """Hash every byte while retaining only the prefix needed for replay."""

    metadata_before = require_regular_input(path, "ranked snapshot")
    require(
        metadata_before.st_size == EXPECTED["snapshot_bytes"],
        "ranked snapshot byte count does not match the sealed old snapshot",
    )
    digest = hashlib.sha256()
    replay_rows: list[SnapshotRow] = []
    row_count = 0
    with path.open("rb") as stream:
        for index, payload in enumerate(stream):
            digest.update(payload)
            row_count = index + 1
            require(payload.endswith(b"\n"), f"snapshot row {index} is partial")
            if index >= EXPECTED["pending_next"]:
                continue
            try:
                row = json.loads(payload)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise RecoveryError(f"snapshot row {index} is invalid JSON") from exc
            require(isinstance(row, dict), f"snapshot row {index} is not an object")
            require(
                not trusted_terminal_rejection(row),
                f"snapshot eligible-prefix row {index} is terminal",
            )
            require(
                not row.get("C_terms") and not row.get("D_terms"),
                f"snapshot row {index} unexpectedly uses non-CSS terms",
            )
            marker = row.get("stage2_structural_screen")
            static = row.get("static_eligibility")
            structural = row.get("structural_novelty")
            require(
                isinstance(marker, Mapping)
                and marker.get("status") == "COMPLETE"
                and isinstance(static, Mapping)
                and static.get("checked") is True
                and static.get("eligible") is True
                and isinstance(structural, Mapping)
                and structural.get("checked") is True
                and is_sha256(structural.get("canonical_digest")),
                f"snapshot row {index} lacks complete structural evidence",
            )
            canonical_digest = str(structural["canonical_digest"])
            replay_rows.append(SnapshotRow(
                index=index,
                canonical_digest=canonical_digest,
                known_code=canonical_digest in known_digests,
            ))
    metadata_after = path.lstat()
    require(
        (
            metadata_before.st_dev,
            metadata_before.st_ino,
            metadata_before.st_size,
            metadata_before.st_mtime_ns,
        )
        == (
            metadata_after.st_dev,
            metadata_after.st_ino,
            metadata_after.st_size,
            metadata_after.st_mtime_ns,
        ),
        "ranked snapshot changed while hashing",
    )
    require(
        digest.hexdigest() == EXPECTED["snapshot_sha256"],
        "ranked snapshot SHA-256 does not match the sealed old snapshot",
    )
    require(
        row_count == EXPECTED["snapshot_rows"],
        "ranked snapshot row count does not match its identity",
    )
    require(
        len(replay_rows) == EXPECTED["pending_next"],
        "ranked snapshot does not contain the required replay prefix",
    )
    return replay_rows


def replay_new_pages(
    state: ReplayState,
    rows: Sequence[SnapshotRow],
) -> tuple[ReplayState, dict[str, Any], list[dict[str, Any]]]:
    """Replay completed sequences 31..43, then construct pending sequence 44."""

    require(
        [row.canonical_digest for row in rows[: state.cursor]]
        == state.committed_digests,
        "snapshot prefix does not reproduce the archive committed digests",
    )
    ack_chain = list(state.ack_chain)
    committed = list(state.committed_digests)
    seen = set(committed)
    cursor = state.cursor
    previous = state.last_ack_sha256
    page_reports: list[dict[str, Any]] = []

    for sequence in range(
        EXPECTED["transition_completed_pages"],
        EXPECTED["pending_sequence"] + 1,
    ):
        start = cursor
        selected: list[str] = []
        known_skips: list[dict[str, Any]] = []
        duplicate_skips: list[dict[str, Any]] = []
        while len(selected) < EXPECTED["pending_selected"]:
            require(cursor < len(rows), f"page {sequence} exceeds replay prefix")
            row = rows[cursor]
            require(row.index == cursor, "snapshot replay index is discontinuous")
            cursor += 1
            if row.known_code:
                known_skips.append({
                    "snapshot_index": row.index,
                    "canonical_digest": row.canonical_digest,
                })
                continue
            if row.canonical_digest in seen:
                duplicate_skips.append({
                    "snapshot_index": row.index,
                    "canonical_digest": row.canonical_digest,
                })
                continue
            seen.add(row.canonical_digest)
            selected.append(row.canonical_digest)

        page = make_page(
            sequence=sequence,
            previous_ack_sha256=previous,
            start_index=start,
            next_index=cursor,
            selected_digests=selected,
        )
        page_reports.append({
            "sequence": sequence,
            "start_index": start,
            "next_index": cursor,
            "selected": len(selected),
            "known_code_skips": known_skips,
            "canonical_duplicate_skips": duplicate_skips,
            "page_sha256": page["page_sha256"],
        })
        if sequence == EXPECTED["pending_sequence"]:
            return (
                ReplayState(
                    ack_chain=ack_chain,
                    committed_digests=committed,
                    cursor=start,
                    last_ack_sha256=previous,
                ),
                page,
                page_reports,
            )
        ack = make_completed_ack(
            page,
            sequence=sequence,
            previous_ack_sha256=previous,
        )
        ack_chain.append(ack)
        committed.extend(selected)
        previous = str(ack["ack_sha256"])

    raise AssertionError("unreachable")


def replay_sealed_core_from_snapshot(
    rows: Sequence[SnapshotRow],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Select every old page from snapshot/registry, trusting no core page."""

    require(
        len(rows) >= EXPECTED["pending_next"],
        "snapshot replay prefix is shorter than the sealed pending page",
    )
    capacities = [96] * 29 + [192, 1024] + [4096] * 14
    require(
        len(capacities) == EXPECTED["pending_sequence"] + 1,
        "compiled Stage 2 page schedule is inconsistent",
    )
    previous = genesis_sha256(EXPECTED["final_binding_sha256"])
    cursor = 0
    seen: set[str] = set()
    committed: list[str] = []
    ack_chain: list[dict[str, Any]] = []
    pending: dict[str, Any] | None = None
    for sequence, capacity in enumerate(capacities):
        start = cursor
        selected: list[str] = []
        while len(selected) < capacity:
            require(cursor < len(rows), f"independent page {sequence} exceeded snapshot prefix")
            row = rows[cursor]
            require(row.index == cursor, "independent snapshot cursor is discontinuous")
            cursor += 1
            if row.known_code or row.canonical_digest in seen:
                continue
            seen.add(row.canonical_digest)
            selected.append(row.canonical_digest)
        page = make_page(
            sequence=sequence,
            previous_ack_sha256=previous,
            start_index=start,
            next_index=cursor,
            selected_digests=selected,
        )
        if sequence == EXPECTED["pending_sequence"]:
            pending = page
            cursor = start
            break
        ack = make_completed_ack(
            page,
            sequence=sequence,
            previous_ack_sha256=previous,
        )
        ack_chain.append(ack)
        committed.extend(selected)
        previous = str(ack["ack_sha256"])
    require(
        pending is not None
        and len(ack_chain) == EXPECTED["completed_pages"]
        and cursor == EXPECTED["cursor"]
        and len(committed) == EXPECTED["committed"]
        and previous == EXPECTED["last_ack_sha256"]
        and pending.get("page_sha256") == EXPECTED["pending_page_sha256"]
        and pending.get("next_index") == EXPECTED["pending_next"],
        "independent snapshot/registry replay missed a sealed core anchor",
    )
    state = ReplayState(
        ack_chain=ack_chain,
        committed_digests=committed,
        cursor=cursor,
        last_ack_sha256=previous,
    )
    return seal_ledger_core(state, pending), pending


def seal_ledger_core(
    state: ReplayState,
    pending: Mapping[str, Any],
) -> dict[str, Any]:
    ledger = {
        "schema_version": LEDGER_SCHEMA_VERSION,
        "gate": LEDGER_GATE,
        "binding_sha256": EXPECTED["final_binding_sha256"],
        "snapshot_identity_sha256": EXPECTED[
            "snapshot_identity_sha256"
        ],
        "snapshot_rows": EXPECTED["snapshot_rows"],
        "eligible_rows": EXPECTED["eligible_rows"],
        "generation": 0,
        "generation_history": [],
        "cursor": state.cursor,
        "committed_digests": state.committed_digests,
        "completed_pages": len(state.ack_chain),
        "ack_chain": state.ack_chain,
        "genesis_sha256": genesis_sha256(EXPECTED["final_binding_sha256"]),
        "last_ack_sha256": state.last_ack_sha256,
        "pending": dict(pending),
        "deferred_pages": [],
    }
    return {**ledger, "progress_sha256": canonical_sha256(ledger)}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def generic_genesis_sha256(
    binding_sha256: str,
    snapshot_identity_sha256: str,
    snapshot_rows: int,
    eligible_rows: int,
    generation: int = 0,
) -> str:
    return canonical_sha256({
        "gate": GENESIS_GATE,
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": snapshot_identity_sha256,
        "snapshot_rows": snapshot_rows,
        "eligible_rows": eligible_rows,
        "generation": generation,
    })


def _bound_scan(
    source: Mapping[str, Any],
    *,
    identity_sha256: str,
    snapshot_rows: int,
    eligible_rows: int,
) -> dict[str, Any]:
    start = source.get("start_index")
    next_index = source.get("next_index")
    require(
        source.get("schema_version") == SCAN_SCHEMA_VERSION
        and source.get("gate") == SCAN_GATE
        and isinstance(start, int) and not isinstance(start, bool)
        and isinstance(next_index, int) and not isinstance(next_index, bool)
        and 0 <= start <= next_index <= eligible_rows,
        "source scan evidence is malformed",
    )
    payload = {
        "schema_version": SCAN_SCHEMA_VERSION,
        "gate": SCAN_GATE,
        "snapshot_identity_sha256": identity_sha256,
        "start_index": start,
        "next_index": next_index,
        "snapshot_rows": snapshot_rows,
        "eligible_rows": eligible_rows,
        "selection_exhausted": next_index == eligible_rows,
    }
    return {**payload, "scan_sha256": canonical_sha256(payload)}


def _bound_page(
    source: Mapping[str, Any],
    *,
    binding_sha256: str,
    identity_sha256: str,
    snapshot_rows: int,
    eligible_rows: int,
    sequence: int,
    previous_ack_sha256: str,
    top: int,
) -> dict[str, Any]:
    selected = source.get("selected_digests")
    scan = source.get("scan_evidence")
    require(
        isinstance(selected, list)
        and 0 < len(selected) <= top
        and len(set(selected)) == len(selected)
        and all(is_sha256(item) for item in selected)
        and source.get("page_sequence") == sequence
        and isinstance(scan, Mapping),
        f"source page {sequence} is malformed or exceeds top={top}",
    )
    rebound_scan = _bound_scan(
        scan,
        identity_sha256=identity_sha256,
        snapshot_rows=snapshot_rows,
        eligible_rows=eligible_rows,
    )
    payload = {
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": identity_sha256,
        "page_sequence": sequence,
        "previous_ack_sha256": previous_ack_sha256,
        "start_index": rebound_scan["start_index"],
        "next_index": rebound_scan["next_index"],
        "selected_digests": list(selected),
        "scan_evidence": rebound_scan,
    }
    return {**payload, "page_sha256": canonical_sha256(payload)}


def rebind_selection_prefix(
    core: Mapping[str, Any],
    *,
    binding_sha256: str,
    identity_sha256: str,
    top: int,
    completed_pages: int,
    include_pending: bool = False,
    acknowledged_at: str | None = None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Resign one exact source prefix from genesis under a successor rung."""

    chain = core.get("ack_chain")
    rows = core.get("snapshot_rows")
    eligible = core.get("eligible_rows")
    generation = core.get("generation")
    require(
        is_sha256(binding_sha256) and is_sha256(identity_sha256)
        and isinstance(top, int) and not isinstance(top, bool) and top > 0
        and isinstance(chain, list)
        and isinstance(completed_pages, int)
        and not isinstance(completed_pages, bool)
        and 0 <= completed_pages <= len(chain)
        and isinstance(rows, int) and not isinstance(rows, bool)
        and isinstance(eligible, int) and not isinstance(eligible, bool)
        and 0 <= eligible <= rows
        and isinstance(generation, int) and not isinstance(generation, bool),
        "successor prefix inputs are malformed",
    )
    previous = generic_genesis_sha256(
        binding_sha256, identity_sha256, rows, eligible, generation,
    )
    rebound_chain: list[dict[str, Any]] = []
    committed: list[str] = []
    mapping: list[dict[str, Any]] = []
    cursor = 0
    for sequence, raw_ack in enumerate(chain[:completed_pages]):
        require(
            isinstance(raw_ack, Mapping)
            and raw_ack.get("disposition") == "COMPLETED"
            and is_sha256(raw_ack.get("ack_sha256"))
            and isinstance(raw_ack.get("page"), Mapping)
            and raw_ack["page"].get("start_index") == cursor,
            f"source ACK {sequence} is malformed",
        )
        old_page = raw_ack["page"]
        page = _bound_page(
            old_page,
            binding_sha256=binding_sha256,
            identity_sha256=identity_sha256,
            snapshot_rows=rows,
            eligible_rows=eligible,
            sequence=sequence,
            previous_ack_sha256=previous,
            top=top,
        )
        ack = make_completed_ack(
            page, sequence=sequence, previous_ack_sha256=previous,
        )
        rebound_chain.append(ack)
        committed.extend(page["selected_digests"])
        cursor = int(page["next_index"])
        mapping.append({
            "sequence": sequence,
            "old_page_sha256": old_page["page_sha256"],
            "old_ack_sha256": raw_ack["ack_sha256"],
            "new_page_sha256": page["page_sha256"],
            "new_ack_sha256": ack["ack_sha256"],
        })
        previous = str(ack["ack_sha256"])
    pending: dict[str, Any] | None = None
    if include_pending:
        old_pending = core.get("pending")
        require(
            completed_pages == len(chain) and isinstance(old_pending, Mapping),
            "pending migration requires the complete ACK prefix",
        )
        pending = _bound_page(
            old_pending,
            binding_sha256=binding_sha256,
            identity_sha256=identity_sha256,
            snapshot_rows=rows,
            eligible_rows=eligible,
            sequence=completed_pages,
            previous_ack_sha256=previous,
            top=top,
        )
        mapping.append({
            "sequence": completed_pages,
            "pending": True,
            "old_page_sha256": old_pending["page_sha256"],
            "old_ack_sha256": None,
            "new_page_sha256": pending["page_sha256"],
            "new_ack_sha256": None,
        })
    ledger = {
        "schema_version": LEDGER_SCHEMA_VERSION,
        "gate": LEDGER_GATE,
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": identity_sha256,
        "snapshot_rows": rows,
        "eligible_rows": eligible,
        "generation": generation,
        "generation_history": [dict(x) for x in core.get("generation_history", [])],
        "cursor": cursor,
        "committed_digests": committed,
        "completed_pages": completed_pages,
        "ack_chain": rebound_chain,
        "genesis_sha256": generic_genesis_sha256(
            binding_sha256, identity_sha256, rows, eligible, generation,
        ),
        "last_ack_sha256": previous,
        "pending": pending,
        "deferred_pages": [],
    }
    if rebound_chain:
        ledger["last_acknowledged_page_sha256"] = rebound_chain[-1]["page_sha256"]
        ledger["last_acknowledged_at"] = acknowledged_at or utc_now()
    ledger["progress_sha256"] = canonical_sha256(ledger)
    return ledger, mapping


def seal_page_scheduler(
    active_step: int,
    baseline: int,
    transitions: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    policy = [dict(step) for step in PAGE_POLICY]
    payload = {
        "schema_version": 1,
        "gate": PAGE_SCHEDULER_GATE,
        "policy": policy,
        "policy_sha256": canonical_sha256(policy),
        "active_step": active_step,
        "step_started_completed_pages": baseline,
        "transitions": [dict(item) for item in transitions],
    }
    return {**payload, "state_sha256": canonical_sha256(payload)}


def attach_scheduler(
    ledger: Mapping[str, Any], scheduler: Mapping[str, Any],
) -> dict[str, Any]:
    value = dict(ledger)
    value["adaptive_page_scheduler"] = dict(scheduler)
    value.pop("progress_sha256", None)
    value["progress_sha256"] = canonical_sha256(value)
    return value


def _validate_report_seal(report: Mapping[str, Any], label: str) -> None:
    unsigned = dict(report)
    seal = unsigned.pop("report_sha256", None)
    require(
        is_sha256(seal) and seal == canonical_sha256(unsigned),
        f"{label} seal is invalid",
    )


def _validate_migration_evidence_objects(
    core: dict[str, Any],
    report: dict[str, Any],
    terminal: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    _validate_report_seal(report, "core recovery report")
    _validate_report_seal(terminal, "terminal replay report")
    require(
        report.get("gate") == "qldpc-stage2-offline-ledger-core-recovery-v1"
        and report.get("status") == "EXACT_CORE_REPLAY_VERIFIED"
        and report.get("replay", {}).get("ledger_core_progress_sha256")
        == core.get("progress_sha256")
        and report.get("replay", {}).get("last_ack_sha256")
        == EXPECTED["last_ack_sha256"]
        and report.get("replay", {}).get("pending_page_sha256")
        == EXPECTED["pending_page_sha256"],
        "core recovery report does not bind the exact recovered ledger",
    )
    require(
        terminal.get("gate")
        == "qldpc-stage2-recovered-terminal-witness-replay-v1"
        and terminal.get("rows") == EXPECTED["terminal_rows"]
        and terminal.get("valid_witnesses") == EXPECTED["terminal_rows"]
        and terminal.get("all_rebuilt_n_k_match") is True
        and terminal.get("all_strictly_below_12") is True
        and report.get("inputs", {}).get("terminal_witness_replay", {}).get(
            "report_sha256"
        ) == terminal.get("report_sha256"),
        "54-row terminal replay is missing or not bound by the core report",
    )
    try:
        from evaluation.selection_ledger import validate_selection_ledger

        validate_selection_ledger(
            core,
            binding_sha256=EXPECTED["final_binding_sha256"],
            snapshot_identity_sha256_value=EXPECTED[
                "snapshot_identity_sha256"
            ],
            snapshot_rows=EXPECTED["snapshot_rows"],
            eligible_rows=EXPECTED["eligible_rows"],
        )
    except (TypeError, ValueError) as exc:
        raise RecoveryError("recovered ledger core does not replay") from exc
    require(
        core.get("completed_pages") == EXPECTED["completed_pages"]
        and core.get("cursor") == EXPECTED["cursor"]
        and len(core.get("committed_digests", [])) == EXPECTED["committed"]
        and core.get("last_ack_sha256") == EXPECTED["last_ack_sha256"]
        and core.get("pending", {}).get("page_sha256")
        == EXPECTED["pending_page_sha256"],
        "recovered ledger core terminal anchors diverge",
    )
    return core, report, terminal



def validate_migration_evidence(
    *,
    core_ledger_path: Path,
    core_report_path: Path,
    terminal_report_path: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Validate pathname inputs through the shared object-level verifier."""

    return _validate_migration_evidence_objects(
        load_json_object(core_ledger_path, "recovered ledger core"),
        load_json_object(core_report_path, "core recovery report"),
        load_json_object(terminal_report_path, "terminal replay report"),
    )

def _stat_identity(path: Path) -> dict[str, int]:
    metadata = require_regular_input(path, "staged ranked artifact")
    return {
        "device": int(metadata.st_dev),
        "inode": int(metadata.st_ino),
        "bytes": int(metadata.st_size),
        "mtime_ns": int(metadata.st_mtime_ns),
    }


def _copy_exact_file(
    source: Path,
    destination: Path,
    *,
    expected_sha256: str,
    expected_bytes: int,
    label: str,
) -> None:
    source_descriptor = _open_path_nofollow(source, regular=True)
    parent_descriptor = _open_path_nofollow(destination.parent, directory=True)
    destination_descriptor: int | None = None
    digest = hashlib.sha256()
    total = 0
    try:
        before = os.fstat(source_descriptor)
        destination_descriptor = os.open(
            destination.name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL
            | getattr(os, "O_CLOEXEC", 0) | os.O_NOFOLLOW,
            0o600,
            dir_fd=parent_descriptor,
        )
        while True:
            payload = os.read(source_descriptor, 1024 * 1024)
            if not payload:
                break
            digest.update(payload)
            total += len(payload)
            view = memoryview(payload)
            while view:
                written = os.write(destination_descriptor, view)
                require(written > 0, f"staged {label} write stalled")
                view = view[written:]
        os.fsync(destination_descriptor)
        after = os.fstat(source_descriptor)
    except OSError as exc:
        raise RecoveryError(f"staged {label} copy failed") from exc
    finally:
        if destination_descriptor is not None:
            os.close(destination_descriptor)
        os.close(source_descriptor)
        os.fsync(parent_descriptor)
        os.close(parent_descriptor)
    current_descriptor = _open_path_nofollow(source, regular=True)
    try:
        current = os.fstat(current_descriptor)
    finally:
        os.close(current_descriptor)
    require(
        _stable_token(before) == _stable_token(after) == _stable_token(current)
        and before.st_size == expected_bytes
        and total == expected_bytes
        and digest.hexdigest() == expected_sha256,
        f"{label} does not match its exact stable anchor",
    )
    staged_sha256, staged_bytes = _stable_sha256(destination)
    require(
        staged_bytes == expected_bytes and staged_sha256 == expected_sha256,
        f"staged {label} changed during copy",
    )


def _ranked_chunks(snapshot: Path, offsets: Path) -> list[dict[str, Any]]:
    offsets_payload = offsets.read_bytes()
    require(
        len(offsets_payload) == OLD_OFFSETS_BYTES,
        "old offsets byte count diverges",
    )
    positions = [item[0] for item in struct.iter_unpack(">Q", offsets_payload)]
    require(
        len(positions) == EXPECTED["snapshot_rows"] + 1
        and positions[0] == 0
        and positions[-1] == EXPECTED["snapshot_bytes"]
        and all(left < right for left, right in zip(positions, positions[1:])),
        "old offsets are not a complete monotonic row index",
    )
    chunks: list[dict[str, Any]] = []
    with snapshot.open("rb") as stream:
        for start in range(0, EXPECTED["snapshot_rows"], RANKED_CHUNK_ROWS):
            end = min(start + RANKED_CHUNK_ROWS, EXPECTED["snapshot_rows"])
            snapshot_start = positions[start]
            snapshot_end = positions[end]
            payload = stream.read(snapshot_end - snapshot_start)
            require(
                len(payload) == snapshot_end - snapshot_start,
                "ranked snapshot ended inside a chunk",
            )
            offsets_start = start * 8
            offsets_end = (end + 1) * 8
            chunks.append({
                "start_row": start,
                "end_row": end,
                "snapshot_start": snapshot_start,
                "snapshot_end": snapshot_end,
                "snapshot_sha256": hashlib.sha256(payload).hexdigest(),
                "offsets_start": offsets_start,
                "offsets_end": offsets_end,
                "offsets_sha256": hashlib.sha256(
                    offsets_payload[offsets_start:offsets_end]
                ).hexdigest(),
            })
    require(
        canonical_sha256(chunks) == OLD_CHUNK_INDEX_SHA256,
        "old snapshot/offset chunk index does not match the sealed identity",
    )
    return chunks


def capture_patched_binding(
    route_manifest_path: Path,
    *,
    registry_path: Path,
) -> dict[str, Any]:
    route = load_json_object(route_manifest_path, "binding route manifest")
    unsigned_route = dict(route)
    route_seal = unsigned_route.pop("manifest_sha256", None)
    routing_binding = route.get("binding")
    inputs = routing_binding.get("inputs") if isinstance(routing_binding, Mapping) else None
    target_mode = routing_binding.get("target_mode") if isinstance(routing_binding, Mapping) else None
    require(
        is_sha256(route_seal)
        and route_seal == canonical_sha256(unsigned_route)
        and isinstance(inputs, list)
        and len(inputs) == 10
        and all(isinstance(item, Mapping) and isinstance(item.get("path"), str) for item in inputs)
        and target_mode == "scalar-fom-inclusive-v1",
        "binding route manifest is malformed",
    )
    try:
        from scripts.audit_candidate_pool import _ranked_snapshot_binding

        binding = _ranked_snapshot_binding(
            [Path(str(item["path"])) for item in inputs],
            target_mode=str(target_mode),
        )
    except (ImportError, OSError, TypeError, ValueError) as exc:
        raise RecoveryError("current patched snapshot binding capture failed") from exc
    registry = binding.get("known_code_registry")
    input_hashes = [item.get("sha256") for item in binding.get("inputs", [])]
    require(
        isinstance(registry, Mapping)
        and registry.get("path") == str(_no_symlink_path(registry_path))
        and registry.get("sha256") == EXPECTED["registry_file_sha256"]
        and EXPECTED["evaluations_sha256"] in input_hashes
        and is_sha256(binding.get("source_fingerprint"))
        and isinstance(binding.get("solver_runtime"), Mapping)
        and is_sha256(binding.get("binding_sha256")),
        "current patched binding does not preserve trusted inputs/registry",
    )
    return dict(binding)


def selection_binding_for_top(
    top: int,
    *,
    manifest: Mapping[str, Any],
    known_answer_sha256: str,
) -> str:
    binding = manifest["binding"]
    return canonical_sha256({
        "schema_version": LEDGER_SCHEMA_VERSION,
        "top": top,
        "ranked": {"snapshot": dict(manifest["identity"])},
        "known_answer_sha256": known_answer_sha256,
        "solver_runtime": binding["solver_runtime"],
        "source_fingerprint": binding["source_fingerprint"],
        "target_mode": binding["target_mode"],
    })


def write_sealed_artifact(path: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    artifact = {**dict(payload), "artifact_sha256": canonical_sha256(payload)}
    write_json(path, artifact)
    return {
        "path": path,
        "relative_path": path.relative_to(path.parents[1]).as_posix(),
        "file_sha256": file_sha256(path),
        "artifact": artifact,
    }


def _write_transition_archive(
    root: Path,
    ledger: Mapping[str, Any],
    *,
    completed_pages: int,
    from_top: int,
    to_top: int,
) -> tuple[str, str]:
    directory = root / "selection-ledger-page-size-transitions"
    _mkdir_synced(directory, exist_ok=True)
    temporary = directory / f"archive-{completed_pages:06d}.json"
    write_json(temporary, ledger)
    digest = file_sha256(temporary)
    final = directory / (
        f"pages-{completed_pages:06d}-{from_top}-to-{to_top}-"
        f"{digest[:16]}.json"
    )
    temporary.rename(final)
    return final.relative_to(root).as_posix(), digest


def _expected_rung_record(
    *,
    sequence: int,
    path: str,
    sha256: str,
    progress_sha256: str,
    outcome_evidence: Mapping[str, Any],
) -> dict[str, Any]:
    """Return the one exact certificate record for a recovered rung."""

    return {
        "sequence": sequence,
        "path": path,
        "outcome_evidence": dict(outcome_evidence),
        "sha256": sha256,
        "progress_sha256": progress_sha256,
    }


def _validate_exact_rung_record(
    actual: Any,
    *,
    sequence: int,
    path: str,
    sha256: str,
    progress_sha256: str,
    outcome_evidence: Mapping[str, Any],
) -> dict[str, Any]:
    """Reject omitted, added, or self-resealed rung certificate fields."""

    expected = _expected_rung_record(
        sequence=sequence,
        path=path,
        sha256=sha256,
        progress_sha256=progress_sha256,
        outcome_evidence=outcome_evidence,
    )
    require(
        actual == expected,
        "rung archive record differs from exact core/outcome evidence",
    )
    return expected



def _expected_clean_recovery_payload(
    *,
    sequence: int,
    completed_pages: int,
    new_snapshot_identity_sha256: str,
    old_page_sha256: str,
    old_ack_sha256: str,
    new_page_sha256: str,
    new_ack_sha256: str,
    selected_digests_sha256: str,
    rejected_count: int,
    core_report_sha256: str,
    terminal_report_sha256: str,
    created_at: str,
    outcome_evidence: Mapping[str, Any],
) -> dict[str, Any]:
    """Canonical clean artifact payload, derived from strong replay inputs."""

    return {
        "schema_version": 1,
        "gate": "qldpc-stage2-sealed-clean-page-recovery-v1",
        "reason": RECOVERY_REASON,
        "transition_sequence": sequence,
        "completed_pages": completed_pages,
        "page_sequence": completed_pages - 1,
        "old_snapshot_identity_sha256": EXPECTED[
            "snapshot_identity_sha256"
        ],
        "new_snapshot_identity_sha256": new_snapshot_identity_sha256,
        "old_page_sha256": old_page_sha256,
        "old_ack_sha256": old_ack_sha256,
        "new_page_sha256": new_page_sha256,
        "new_ack_sha256": new_ack_sha256,
        "selected_digests_sha256": selected_digests_sha256,
        "status_counts": {"REJECTED": rejected_count},
        "core_report_sha256": core_report_sha256,
        "terminal_report_sha256": terminal_report_sha256,
        "created_at": created_at,
        "outcome_evidence": dict(outcome_evidence),
    }


def _validate_exact_clean_recovery_artifact(
    actual: Any,
    expected_payload: Mapping[str, Any],
) -> dict[str, Any]:
    """Reject a self-resealed clean artifact that differs from replay."""

    expected = {
        **dict(expected_payload),
        "artifact_sha256": canonical_sha256(expected_payload),
    }
    require(
        actual == expected,
        "sealed clean recovery artifact differs from core-derived evidence",
    )
    return expected


def _make_recovery_transition(
    *,
    sequence: int,
    from_ledger: Mapping[str, Any],
    to_ledger: Mapping[str, Any],
    archive_path: str,
    archive_sha256: str,
    clean_evidence: Mapping[str, Any],
    transitions: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    from_step = sequence
    to_step = sequence + 1
    payload = {
        "schema_version": 1,
        "gate": PAGE_TRANSITION_GATE,
        "sequence": sequence,
        "previous_transition_sha256": (
            transitions[-1]["entry_sha256"]
            if transitions else canonical_sha256([dict(x) for x in PAGE_POLICY])
        ),
        "from_step": from_step,
        "to_step": to_step,
        "from_top": PAGE_POLICY[from_step]["top"],
        "to_top": PAGE_POLICY[to_step]["top"],
        "from_binding_sha256": from_ledger["binding_sha256"],
        "to_binding_sha256": to_ledger["binding_sha256"],
        "snapshot_identity_sha256": from_ledger[
            "snapshot_identity_sha256"
        ],
        "cursor": from_ledger["cursor"],
        "completed_pages": from_ledger["completed_pages"],
        "committed_digests_sha256": canonical_sha256(
            from_ledger["committed_digests"]
        ),
        "from_progress_sha256": from_ledger["progress_sha256"],
        "from_last_ack_sha256": from_ledger["last_ack_sha256"],
        "to_last_ack_sha256": to_ledger["last_ack_sha256"],
        "from_last_page_sha256": from_ledger[
            "last_acknowledged_page_sha256"
        ],
        "to_last_page_sha256": to_ledger[
            "last_acknowledged_page_sha256"
        ],
        "archive_path": archive_path,
        "archive_sha256": archive_sha256,
        "clean_evidence": dict(clean_evidence),
        "reason": RECOVERY_REASON,
        "transitioned_at": utc_now(),
    }
    return {**payload, "entry_sha256": canonical_sha256(payload)}


def build_patched_scheduler_migration(
    *,
    snapshot_path: Path,
    offsets_path: Path,
    core_ledger_path: Path,
    core_report_path: Path,
    terminal_report_path: Path,
    route_manifest_path: Path,
    registry_path: Path,
    known_answer_path: Path,
    output_dir: Path,
    same_filesystem_as: Path,
) -> dict[str, Any]:
    """Build, validate, and atomically publish an installable dry-run package."""

    source_paths = [
        _no_symlink_path(path) for path in (
            snapshot_path, offsets_path, core_ledger_path, core_report_path,
            terminal_report_path, route_manifest_path, registry_path,
            known_answer_path,
        )
    ]
    (
        snapshot,
        offsets,
        core_path,
        core_report_file,
        terminal_report_file,
        route_manifest,
        registry,
        known_answer,
    ) = source_paths
    core, core_report, terminal_report = validate_migration_evidence(
        core_ledger_path=core_path,
        core_report_path=core_report_file,
        terminal_report_path=terminal_report_file,
    )
    old_archive_input = core_report.get("inputs", {}).get("transition_archive")
    require(
        isinstance(old_archive_input, Mapping)
        and old_archive_input.get("sha256") == EXPECTED["transition_archive_sha256"]
        and isinstance(old_archive_input.get("path"), str),
        "core report does not bind the immutable old transition archive",
    )
    old_transition_archive = _no_symlink_path(
        Path(str(old_archive_input["path"]))
    )
    require(
        _stable_sha256(old_transition_archive)[0]
        == EXPECTED["transition_archive_sha256"],
        "immutable old transition archive changed",
    )
    old_archive_value = load_json_object(
        old_transition_archive, "immutable old transition archive",
    )
    validate_and_rebind_archive(old_archive_value)
    old_scheduler = old_archive_value.get("adaptive_page_scheduler")
    old_transitions = (
        old_scheduler.get("transitions")
        if isinstance(old_scheduler, Mapping) else None
    )
    require(
        isinstance(old_transitions, list) and len(old_transitions) == 2,
        "old transition archive lacks its two sealed clean transitions",
    )
    clean_outcome_sources = [
        {
            "source": "SEALED_OLD_TRANSITION_CLEAN_EVIDENCE",
            "old_transition_archive_sha256": EXPECTED["transition_archive_sha256"],
            "old_transition_entry_sha256": old_transitions[index]["entry_sha256"],
            "old_clean_evidence": old_transitions[index]["clean_evidence"],
        }
        for index in range(2)
    ]
    clean_outcome_sources.append({
        "source": "SEALED_PAGE31_TRANSITION_ARCHIVE_CREATION",
        "old_transition_archive_sha256": EXPECTED["transition_archive_sha256"],
        "archive_completed_pages": EXPECTED["transition_completed_pages"],
        "archive_cursor": EXPECTED["transition_cursor"],
        "page_sequence": 30,
        "old_page_sha256": core["ack_chain"][30]["page_sha256"],
        "production_protocol": "clean-summary-validated-before-page31-archive",
    })
    require(
        file_sha256(registry) == EXPECTED["registry_file_sha256"],
        "known-code registry changed after core replay",
    )
    live_binding = capture_patched_binding(
        route_manifest, registry_path=registry,
    )
    evaluation_input = next(
        _no_symlink_path(Path(str(item["path"])))
        for item in live_binding["inputs"]
        if item.get("sha256") == EXPECTED["evaluations_sha256"]
    )
    fresh_terminal = replay_terminal_evaluations(evaluation_input)
    evaluation_payload = evaluation_input.read_bytes()
    checkpoint_sources = terminal_checkpoint_records(evaluation_payload)
    require(
        fresh_terminal.get("records") == terminal_report.get("records")
        and fresh_terminal.get("witness_kind_counts")
        == terminal_report.get("witness_kind_counts"),
        "fresh 54-row terminal witness replay differs from sealed evidence",
    )
    registry_value = load_json_object(registry, "known-code registry")
    snapshot_rows = read_and_verify_snapshot(
        snapshot,
        known_digests=registry_digests(registry_value),
    )
    independently_replayed_core, _ = replay_sealed_core_from_snapshot(
        snapshot_rows,
    )
    require(
        independently_replayed_core == core,
        "snapshot/registry selection replay differs from recovered core",
    )
    known_answer_sha256 = file_sha256(known_answer)
    require(is_sha256(known_answer_sha256), "known-answer artifact is unavailable")
    require(
        canonical_sha256(OLD_COUNTS) == OLD_COUNTS_SHA256,
        "compiled old counts object does not match its portfolio anchor",
    )

    parent = _no_symlink_path(output_dir.parent)
    intended = parent / output_dir.name
    same_fs = _no_symlink_path(same_filesystem_as)
    require(not intended.exists(), f"migration output already exists: {intended}")
    require(
        parent.stat().st_dev == same_fs.stat().st_dev,
        "migration output is not on the intended target filesystem",
    )
    build_root = parent / (
        f".{output_dir.name}.building-{os.getpid()}-{time.time_ns()}"
    )
    _mkdir_synced(build_root)
    try:
        ledger_name = "stage2-selection-ledger.json"
        staged_snapshot = build_root / f"{ledger_name}.ranked-snapshot.jsonl"
        staged_offsets = build_root / f"{ledger_name}.ranked-snapshot.offsets"
        staged_manifest = (
            build_root / f"{ledger_name}.ranked-snapshot.manifest.json"
        )
        _copy_exact_file(
            snapshot,
            staged_snapshot,
            expected_sha256=EXPECTED["snapshot_sha256"],
            expected_bytes=EXPECTED["snapshot_bytes"],
            label="exact old ranked snapshot",
        )
        _copy_exact_file(
            offsets,
            staged_offsets,
            expected_sha256=OLD_OFFSETS_SHA256,
            expected_bytes=OLD_OFFSETS_BYTES,
            label="exact old ranked offsets",
        )
        chunks = _ranked_chunks(staged_snapshot, staged_offsets)
        identity = {
            "binding_sha256": live_binding["binding_sha256"],
            "snapshot_sha256": EXPECTED["snapshot_sha256"],
            "offsets_sha256": OLD_OFFSETS_SHA256,
            "chunk_index_sha256": OLD_CHUNK_INDEX_SHA256,
            "chunk_rows": RANKED_CHUNK_ROWS,
            "rows": EXPECTED["snapshot_rows"],
            "eligible_rows": EXPECTED["eligible_rows"],
            "counts_sha256": OLD_COUNTS_SHA256,
        }
        identity_sha256 = canonical_sha256(identity)
        manifest_payload = {
            "schema_version": 1,
            "gate": "qldpc-stage2-ranked-snapshot",
            "binding": live_binding,
            "binding_sha256": live_binding["binding_sha256"],
            "identity": identity,
            "snapshot_rows": EXPECTED["snapshot_rows"],
            "snapshot_stat": _stat_identity(staged_snapshot),
            "offsets_stat": _stat_identity(staged_offsets),
            "chunk_rows": RANKED_CHUNK_ROWS,
            "chunks": chunks,
            "counts": dict(OLD_COUNTS),
            "created_at": time.time(),
        }
        manifest = {
            **manifest_payload,
            "manifest_sha256": canonical_sha256(manifest_payload),
        }
        write_json(staged_manifest, manifest)

        bindings = [
            selection_binding_for_top(
                int(step["top"]),
                manifest=manifest,
                known_answer_sha256=known_answer_sha256,
            )
            for step in PAGE_POLICY
        ]
        ack_time = utc_now()

        def prefix(step: int, pages: int) -> dict[str, Any]:
            ledger, _ = rebind_selection_prefix(
                core,
                binding_sha256=bindings[step],
                identity_sha256=identity_sha256,
                top=int(PAGE_POLICY[step]["top"]),
                completed_pages=pages,
                acknowledged_at=ack_time,
            )
            return ledger

        clean_directory = build_root / "sealed-clean-page-recovery"
        _mkdir_synced(clean_directory)
        transitions: list[dict[str, Any]] = []
        archive_records: list[dict[str, Any]] = []
        clean_records: list[dict[str, Any]] = []
        boundaries = (29, 30, 31)
        active_ledger: dict[str, Any] | None = None
        for sequence, completed_pages in enumerate(boundaries):
            from_ledger = prefix(sequence, completed_pages)
            from_ledger = attach_scheduler(
                from_ledger,
                seal_page_scheduler(
                    sequence,
                    0 if sequence == 0 else boundaries[sequence - 1],
                    transitions,
                ),
            )
            archive_path, archive_sha256 = _write_transition_archive(
                build_root,
                from_ledger,
                completed_pages=completed_pages,
                from_top=int(PAGE_POLICY[sequence]["top"]),
                to_top=int(PAGE_POLICY[sequence + 1]["top"]),
            )
            to_ledger = prefix(sequence + 1, completed_pages)
            old_ack = core["ack_chain"][completed_pages - 1]
            recovery_payload = _expected_clean_recovery_payload(
                sequence=sequence,
                completed_pages=completed_pages,
                new_snapshot_identity_sha256=identity_sha256,
                old_page_sha256=old_ack["page_sha256"],
                old_ack_sha256=old_ack["ack_sha256"],
                new_page_sha256=from_ledger["last_acknowledged_page_sha256"],
                new_ack_sha256=from_ledger["last_ack_sha256"],
                selected_digests_sha256=canonical_sha256(
                    old_ack["page"]["selected_digests"]
                ),
                rejected_count=len(old_ack["page"]["selected_digests"]),
                core_report_sha256=core_report["report_sha256"],
                terminal_report_sha256=terminal_report["report_sha256"],
                created_at=utc_now(),
                outcome_evidence=clean_outcome_sources[sequence],
            )
            recovery_path = clean_directory / (
                f"transition-{sequence:03d}-page-"
                f"{completed_pages - 1:06d}.json"
            )
            recovery_record = write_sealed_artifact(
                recovery_path, recovery_payload,
            )
            clean_evidence = {
                "schema_version": 1,
                "gate": "qldpc-stage2-clean-page-evidence",
                "page_sha256": from_ledger[
                    "last_acknowledged_page_sha256"
                ],
                "summary_sha256": recovery_record["file_sha256"],
                "status_counts_sha256": canonical_sha256(
                    recovery_payload["status_counts"]
                ),
                "completed_pages": completed_pages,
                "verified_at": utc_now(),
            }
            transition = _make_recovery_transition(
                sequence=sequence,
                from_ledger=from_ledger,
                to_ledger=to_ledger,
                archive_path=archive_path,
                archive_sha256=archive_sha256,
                clean_evidence=clean_evidence,
                transitions=transitions,
            )
            transitions.append(transition)
            archive_records.append(_expected_rung_record(
                sequence=sequence,
                path=archive_path,
                outcome_evidence=clean_outcome_sources[sequence],
                sha256=archive_sha256,
                progress_sha256=from_ledger["progress_sha256"],
            ))
            clean_records.append({
                "sequence": sequence,
                "path": recovery_record["relative_path"],
                "file_sha256": recovery_record["file_sha256"],
                "artifact_sha256": recovery_record["artifact"][
                    "artifact_sha256"
                ],
            })

        active_ledger, final_mapping = rebind_selection_prefix(
            core,
            binding_sha256=bindings[3],
            identity_sha256=identity_sha256,
            top=int(PAGE_POLICY[3]["top"]),
            completed_pages=EXPECTED["completed_pages"],
            include_pending=True,
            acknowledged_at=ack_time,
        )
        active_ledger = attach_scheduler(
            active_ledger,
            seal_page_scheduler(3, boundaries[-1], transitions),
        )
        write_json(build_root / ledger_name, active_ledger)
        evidence_directory = build_root / "recovery-evidence"
        _mkdir_synced(evidence_directory)
        packaged_evidence = {
            "core_ledger": evidence_directory / "selection-ledger-core.json",
            "core_report": evidence_directory / "recovery-report.json",
            "terminal_report": evidence_directory / "terminal-witness-replay.json",
            "terminal_evaluations": evidence_directory / "terminal-evaluations.jsonl",
            "known_code_registry": evidence_directory / "known-code-registry.json",
            "old_transition_archive": evidence_directory / "old-transition-archive.json",
        }
        for source, destination in (
            (core_path, packaged_evidence["core_ledger"]),
            (core_report_file, packaged_evidence["core_report"]),
            (terminal_report_file, packaged_evidence["terminal_report"]),
            (evaluation_input, packaged_evidence["terminal_evaluations"]),
            (registry, packaged_evidence["known_code_registry"]),
            (old_transition_archive, packaged_evidence["old_transition_archive"]),
        ):
            source_sha256, source_bytes = _stable_sha256(source)
            _copy_exact_file(
                source, destination,
                expected_sha256=source_sha256,
                expected_bytes=source_bytes,
                label=f"packaged recovery evidence {destination.name}",
            )

        checkpoint_directory = evidence_directory / "terminal-checkpoints"
        _mkdir_synced(checkpoint_directory)
        checkpoint_mapping: list[dict[str, Any]] = []
        for record in checkpoint_sources:
            source = _no_symlink_path(Path(str(record["source_path"])))
            relative = (
                "recovery-evidence/terminal-checkpoints/"
                f"{record['source_line']:03d}-{record['sha256']}.evidence"
            )
            destination = build_root / relative
            _copy_exact_file(
                source, destination,
                expected_sha256=str(record["sha256"]),
                expected_bytes=int(record["bytes"]),
                label=f"terminal checkpoint row {record['source_line']}",
            )
            checkpoint_mapping.append({**record, "package_path": relative})

        from evaluation.selection_ledger import validate_selection_ledger

        validate_selection_ledger(
            active_ledger,
            binding_sha256=bindings[3],
            snapshot_identity_sha256_value=identity_sha256,
            snapshot_rows=EXPECTED["snapshot_rows"],
            eligible_rows=EXPECTED["eligible_rows"],
        )
        try:
            from humanize.pipeline import FiveStagePipeline

            validator = object.__new__(FiveStagePipeline)
            validator.config = SimpleNamespace(
                stage2_page_schedule=[
                    (int(x["top"]), x["clean_pages"]) for x in PAGE_POLICY
                ],
                target_mode=live_binding["target_mode"],
                known_answer_artifact=known_answer,
            )
            validator.paths = SimpleNamespace(
                solver_state=build_root,
                stage2_selection_ledger=build_root / ledger_name,
            )
            require(
                validator._stage2_snapshot_manifest() == manifest,
                "production manifest validator changed staged manifest",
            )
            validator._validated_stage2_selection_ledger(active_ledger)
            validator._validate_stage2_page_scheduler(
                active_ledger, manifest,
            )
        except Exception as exc:
            raise RecoveryError(
                "production pipeline scheduler validator rejected migration"
            ) from exc

        certificate_payload = {
            "schema_version": 1,
            "gate": MIGRATION_GATE,
            "status": "PATCHED_IDENTITY_SCHEDULER_MIGRATION_VALIDATED",
            "reason": RECOVERY_REASON,
            "created_at": utc_now(),
            "intended_output": str(intended),
            "same_filesystem_as": str(same_fs),
            "old_anchors": {
                "snapshot_sha256": EXPECTED["snapshot_sha256"],
                "offsets_sha256": OLD_OFFSETS_SHA256,
                "snapshot_identity_sha256": EXPECTED[
                    "snapshot_identity_sha256"
                ],
                "binding_sha256": EXPECTED["final_binding_sha256"],
                "last_ack_sha256": EXPECTED["last_ack_sha256"],
                "pending_page_sha256": EXPECTED["pending_page_sha256"],
                "original_ledger_file_sha256": EXPECTED[
                    "original_ledger_file_sha256"
                ],
                "original_ledger_progress_sha256": EXPECTED[
                    "original_ledger_progress_sha256"
                ],
            },
            "evidence": {
                "core_ledger_path": "recovery-evidence/selection-ledger-core.json",
                "core_ledger_file_sha256": file_sha256(
                    packaged_evidence["core_ledger"]
                ),
                "core_progress_sha256": core["progress_sha256"],
                "core_report_path": "recovery-evidence/recovery-report.json",
                "core_report_file_sha256": file_sha256(
                    packaged_evidence["core_report"]
                ),
                "core_report_sha256": core_report["report_sha256"],
                "terminal_report_path": (
                    "recovery-evidence/terminal-witness-replay.json"
                ),
                "terminal_report_file_sha256": file_sha256(
                    packaged_evidence["terminal_report"]
                ),
                "terminal_report_sha256": terminal_report["report_sha256"],
                "terminal_rows": terminal_report["rows"],
                "terminal_evaluations_path": (
                    "recovery-evidence/terminal-evaluations.jsonl"
                ),
                "terminal_evaluations_sha256": file_sha256(
                    packaged_evidence["terminal_evaluations"]
                ),
                "packaged_registry_path": (
                    "recovery-evidence/known-code-registry.json"
                ),
                "packaged_registry_sha256": file_sha256(
                    packaged_evidence["known_code_registry"]
                ),
                "binding_route_manifest_path": str(route_manifest),
                "terminal_checkpoint_mapping": checkpoint_mapping,
                "terminal_checkpoint_count": len(checkpoint_mapping),
                "terminal_checkpoint_mapping_sha256": canonical_sha256(checkpoint_mapping),
                "binding_route_manifest_file_sha256": file_sha256(
                    route_manifest
                ),
                "known_code_registry_path": str(registry),
                "known_code_registry_sha256": EXPECTED[
                    "registry_file_sha256"
                ],
                "known_answer_path": str(known_answer),
                "known_answer_sha256": known_answer_sha256,
                "validator_source_path": str(_no_symlink_path(Path(__file__))),
                "validator_source_sha256": file_sha256(Path(__file__)),
                "old_transition_archive_path": (
                    "recovery-evidence/old-transition-archive.json"
                ),
                "old_transition_archive_sha256": file_sha256(
                    packaged_evidence["old_transition_archive"]
                ),
                "clean_outcome_sources": clean_outcome_sources,
            },
            "successor": {
                "manifest_file_sha256": file_sha256(staged_manifest),
                "manifest_sha256": manifest["manifest_sha256"],
                "binding_sha256": live_binding["binding_sha256"],
                "source_fingerprint": live_binding["source_fingerprint"],
                "snapshot_identity": identity,
                "snapshot_identity_sha256": identity_sha256,
                "page_bindings": bindings,
                "active_ledger_progress_sha256": active_ledger[
                    "progress_sha256"
                ],
                "active_last_ack_sha256": active_ledger["last_ack_sha256"],
                "active_pending_page_sha256": active_ledger["pending"][
                    "page_sha256"
                ],
                "active_scheduler_state_sha256": active_ledger[
                    "adaptive_page_scheduler"
                ]["state_sha256"],
            },
            "rung_archives": archive_records,
            "clean_recovery_artifacts": clean_records,
            "page30_recovery_artifact": clean_records[2],
            "old_to_new_page_ack_mapping": final_mapping,
            "validation": {
                "selection_ledger": "PASS",
                "pipeline_scheduler": "PASS",
                "production_files_modified": False,
            },
        }
        certificate = {
            **certificate_payload,
            "certificate_sha256": canonical_sha256(certificate_payload),
        }
        certificate_path = build_root / "scheduler-migration-certificate.json"
        write_json(certificate_path, certificate)
        package_files = []
        for path in sorted(build_root.rglob("*")):
            if path.is_file():
                package_files.append({
                    "path": path.relative_to(build_root).as_posix(),
                    "bytes": path.stat().st_size,
                    "sha256": file_sha256(path),
                })
        package_payload = {
            "schema_version": 1,
            "gate": "qldpc-stage2-scheduler-migration-package-v1",
            "certificate_sha256": certificate["certificate_sha256"],
            "files": package_files,
        }
        package = {
            **package_payload,
            "package_sha256": canonical_sha256(package_payload),
        }
        write_json(build_root / "package-manifest.json", package)
        prepublication_validation = validate_patched_scheduler_migration(
            build_root, same_filesystem_as=same_fs,
        )
        require(
            prepublication_validation.get("certificate_sha256")
            == certificate["certificate_sha256"],
            "public validator rejected the pre-publication package",
        )
        build_root.rename(intended)
        _fsync_directory(parent)
    except BaseException:
        if build_root.exists():
            shutil.rmtree(build_root)
        raise
    return {
        "output_dir": str(intended),
        "certificate_sha256": certificate["certificate_sha256"],
        "package_sha256": package["package_sha256"],
        "snapshot_identity_sha256": identity_sha256,
        "binding_sha256": live_binding["binding_sha256"],
        "active_ledger_progress_sha256": active_ledger["progress_sha256"],
        "active_last_ack_sha256": active_ledger["last_ack_sha256"],
        "active_pending_page_sha256": active_ledger["pending"]["page_sha256"],
        "production_files_modified": False,
    }


def _lexical_absolute_path(path: Path) -> Path:
    return Path(os.path.abspath(os.fspath(path)))


def _open_path_nofollow(
    path: Path,
    *,
    regular: bool = False,
    directory: bool = False,
) -> int:
    """Open every component with openat/O_NOFOLLOW; caller owns the fd."""

    require(
        hasattr(os, "O_NOFOLLOW"),
        "O_NOFOLLOW is required for migration validation",
    )
    absolute = _lexical_absolute_path(path)
    directory_flags = (
        os.O_RDONLY | os.O_DIRECTORY | getattr(os, "O_CLOEXEC", 0)
        | os.O_NOFOLLOW
    )
    try:
        descriptor = os.open(absolute.anchor, directory_flags)
        for index, part in enumerate(absolute.parts[1:]):
            final = index == len(absolute.parts[1:]) - 1
            if final and not directory:
                flags = (
                    (os.O_RDONLY if regular else getattr(os, "O_PATH", os.O_RDONLY))
                    | getattr(os, "O_CLOEXEC", 0) | os.O_NOFOLLOW
                )
            else:
                flags = directory_flags
            try:
                next_descriptor = os.open(part, flags, dir_fd=descriptor)
            finally:
                os.close(descriptor)
            descriptor = next_descriptor
    except OSError as exc:
        raise RecoveryError(
            f"migration path is unavailable or unsafe: {absolute}"
        ) from exc
    metadata = os.fstat(descriptor)
    if stat.S_ISLNK(metadata.st_mode):
        os.close(descriptor)
        raise RecoveryError(f"migration path contains symlink: {absolute}")
    if regular and not stat.S_ISREG(metadata.st_mode):
        os.close(descriptor)
        raise RecoveryError(f"migration path is not regular: {absolute}")
    if directory and not stat.S_ISDIR(metadata.st_mode):
        os.close(descriptor)
        raise RecoveryError(f"migration path is not a directory: {absolute}")
    return descriptor


def _stable_token(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        int(metadata.st_mode), int(metadata.st_nlink), int(metadata.st_dev),
        int(metadata.st_ino), int(metadata.st_size), int(metadata.st_mtime_ns),
        int(metadata.st_ctime_ns),
    )


def _no_symlink_path(path: Path) -> Path:
    absolute = _lexical_absolute_path(path)
    descriptor = _open_path_nofollow(absolute)
    os.close(descriptor)
    return absolute


def _confined_package_path(root: Path, relative: str) -> Path:
    rel = Path(relative)
    require(
        not rel.is_absolute()
        and rel.parts
        and all(part not in {"", ".", ".."} for part in rel.parts),
        f"package path is not confined: {relative}",
    )
    candidate = _lexical_absolute_path(root) / rel
    _no_symlink_path(candidate)
    return candidate


def _stable_read(path: Path, *, expected_root: Path | None = None) -> bytes:
    absolute = _lexical_absolute_path(path)
    if expected_root is not None:
        require(
            absolute.is_relative_to(_lexical_absolute_path(expected_root)),
            "stable read escaped package root",
        )
    descriptor = _open_path_nofollow(absolute, regular=True)
    try:
        before = os.fstat(descriptor)
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    current_descriptor = _open_path_nofollow(absolute, regular=True)
    try:
        current = os.fstat(current_descriptor)
    finally:
        os.close(current_descriptor)
    require(
        _stable_token(before) == _stable_token(after) == _stable_token(current)
        and total == before.st_size,
        f"package member changed during stable read: {absolute}",
    )
    return b"".join(chunks)


def _stable_sha256(path: Path, *, expected_root: Path | None = None) -> tuple[str, int]:
    absolute = _lexical_absolute_path(path)
    if expected_root is not None:
        require(
            absolute.is_relative_to(_lexical_absolute_path(expected_root)),
            "stable hash escaped package root",
        )
    descriptor = _open_path_nofollow(absolute, regular=True)
    digest = hashlib.sha256()
    total = 0
    try:
        before = os.fstat(descriptor)
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            total += len(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    current_descriptor = _open_path_nofollow(absolute, regular=True)
    try:
        current = os.fstat(current_descriptor)
    finally:
        os.close(current_descriptor)
    require(
        _stable_token(before) == _stable_token(after) == _stable_token(current)
        and total == before.st_size,
        f"package member changed during stable hash: {absolute}",
    )
    return digest.hexdigest(), int(after.st_size)


def _stable_json(path: Path, *, root: Path) -> dict[str, Any]:
    try:
        value = json.loads(_stable_read(path, expected_root=root))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecoveryError(f"package JSON is malformed: {path}") from exc
    require(isinstance(value, dict), f"package JSON is not an object: {path}")
    return value


def _package_files(root: Path) -> set[str]:
    found: set[str] = set()

    def visit(directory: Path) -> None:
        with os.scandir(directory) as entries:
            for entry in entries:
                path = Path(entry.path)
                metadata = entry.stat(follow_symlinks=False)
                require(not stat.S_ISLNK(metadata.st_mode), f"package contains symlink: {path}")
                if stat.S_ISDIR(metadata.st_mode):
                    visit(path)
                else:
                    require(stat.S_ISREG(metadata.st_mode), f"package member is unsafe: {path}")
                    found.add(path.relative_to(root).as_posix())

    visit(root)
    return found


def _stable_ranked_chunks(
    snapshot: Path,
    offsets: Path,
    *,
    root: Path,
    known_digests: set[str],
) -> tuple[list[dict[str, Any]], list[SnapshotRow]]:
    offsets_payload = _stable_read(offsets, expected_root=root)
    require(len(offsets_payload) == OLD_OFFSETS_BYTES, "package offsets byte count diverges")
    positions = [item[0] for item in struct.iter_unpack(">Q", offsets_payload)]
    require(
        len(positions) == EXPECTED["snapshot_rows"] + 1
        and positions[0] == 0
        and positions[-1] == EXPECTED["snapshot_bytes"]
        and all(a < b for a, b in zip(positions, positions[1:])),
        "package offsets are not monotonic",
    )
    descriptor = _open_path_nofollow(snapshot, regular=True)
    chunks: list[dict[str, Any]] = []
    replay_rows: list[SnapshotRow] = []
    try:
        before = os.fstat(descriptor)
        require(
            stat.S_ISREG(before.st_mode) and before.st_size == EXPECTED["snapshot_bytes"],
            "package snapshot is not the expected regular file",
        )
        for start in range(0, EXPECTED["snapshot_rows"], RANKED_CHUNK_ROWS):
            end = min(start + RANKED_CHUNK_ROWS, EXPECTED["snapshot_rows"])
            snapshot_start, snapshot_end = positions[start], positions[end]
            payload = os.pread(descriptor, snapshot_end - snapshot_start, snapshot_start)
            require(len(payload) == snapshot_end - snapshot_start, "package snapshot chunk is partial")
            encoded_rows = payload.splitlines(keepends=True)
            require(
                len(encoded_rows) == end - start
                and all(item.endswith(b"\n") for item in encoded_rows),
                "package snapshot chunk does not follow its offset rows",
            )
            for relative_index, encoded_row in enumerate(encoded_rows):
                row_index = start + relative_index
                if row_index >= EXPECTED["pending_next"]:
                    continue
                try:
                    row = json.loads(encoded_row)
                except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                    raise RecoveryError(
                        f"package snapshot row {row_index} is invalid"
                    ) from exc
                marker = row.get("stage2_structural_screen")
                static = row.get("static_eligibility")
                structural = row.get("structural_novelty")
                require(
                    isinstance(row, dict)
                    and not trusted_terminal_rejection(row)
                    and not row.get("C_terms")
                    and not row.get("D_terms")
                    and isinstance(marker, Mapping)
                    and marker.get("status") == "COMPLETE"
                    and isinstance(static, Mapping)
                    and static.get("checked") is True
                    and static.get("eligible") is True
                    and isinstance(structural, Mapping)
                    and structural.get("checked") is True
                    and is_sha256(structural.get("canonical_digest")),
                    f"package snapshot row {row_index} lacks eligible evidence",
                )
                canonical_digest = str(structural["canonical_digest"])
                replay_rows.append(SnapshotRow(
                    index=row_index,
                    canonical_digest=canonical_digest,
                    known_code=canonical_digest in known_digests,
                ))
            offsets_start, offsets_end = start * 8, (end + 1) * 8
            chunks.append({
                "start_row": start,
                "end_row": end,
                "snapshot_start": snapshot_start,
                "snapshot_end": snapshot_end,
                "snapshot_sha256": hashlib.sha256(payload).hexdigest(),
                "offsets_start": offsets_start,
                "offsets_end": offsets_end,
                "offsets_sha256": hashlib.sha256(offsets_payload[offsets_start:offsets_end]).hexdigest(),
            })
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    current_descriptor = _open_path_nofollow(snapshot, regular=True)
    try:
        current = os.fstat(current_descriptor)
    finally:
        os.close(current_descriptor)
    require(
        _stable_token(before) == _stable_token(after) == _stable_token(current),
        "package snapshot changed during chunk replay",
    )
    require(
        len(replay_rows) == EXPECTED["pending_next"],
        "stable snapshot replay prefix is incomplete",
    )
    return chunks, replay_rows


MIGRATION_EVIDENCE_FIELDS = frozenset({
    "core_ledger_path",
    "core_ledger_file_sha256",
    "core_progress_sha256",
    "core_report_path",
    "core_report_file_sha256",
    "core_report_sha256",
    "terminal_report_path",
    "terminal_report_file_sha256",
    "terminal_report_sha256",
    "terminal_rows",
    "terminal_evaluations_path",
    "terminal_evaluations_sha256",
    "packaged_registry_path",
    "packaged_registry_sha256",
    "binding_route_manifest_path",
    "terminal_checkpoint_mapping",
    "terminal_checkpoint_count",
    "terminal_checkpoint_mapping_sha256",
    "binding_route_manifest_file_sha256",
    "known_code_registry_path",
    "known_code_registry_sha256",
    "known_answer_path",
    "known_answer_sha256",
    "validator_source_path",
    "validator_source_sha256",
    "old_transition_archive_path",
    "old_transition_archive_sha256",
    "clean_outcome_sources",
})


def _validate_migration_evidence_claim_schema(
    evidence: Mapping[str, Any],
) -> Path:
    """Reject unconsumed claims and bind the source path, not only its digest."""

    require(
        set(evidence) == MIGRATION_EVIDENCE_FIELDS,
        "migration evidence fields differ from the compiled schema",
    )
    source_claim = evidence.get("validator_source_path")
    require(
        isinstance(source_claim, str)
        and _lexical_absolute_path(Path(source_claim))
        == _lexical_absolute_path(Path(__file__)),
        "migration validator source path differs from current source",
    )
    source_path = _no_symlink_path(Path(source_claim))
    require(
        source_path == _no_symlink_path(Path(__file__)),
        "migration validator source path is not canonical",
    )
    return source_path


def validate_patched_scheduler_migration(
    package_root: Path,
    *,
    same_filesystem_as: Path | None = None,
) -> dict[str, Any]:
    """Recompute a migration package from disk; trust no self-asserted seal."""

    supplied = _no_symlink_path(Path(package_root))
    supplied_descriptor = _open_path_nofollow(supplied)
    try:
        supplied_metadata = os.fstat(supplied_descriptor)
    finally:
        os.close(supplied_descriptor)
    supplied_is_file = stat.S_ISREG(supplied_metadata.st_mode)
    require(
        supplied_is_file or stat.S_ISDIR(supplied_metadata.st_mode),
        "migration package argument is neither file nor directory",
    )
    root = supplied.parent if supplied_is_file else supplied
    root = _no_symlink_path(root)
    root_descriptor = _open_path_nofollow(root, directory=True)
    try:
        root_metadata = os.fstat(root_descriptor)
    finally:
        os.close(root_descriptor)
    if supplied_is_file:
        require(supplied.name == "scheduler-migration-certificate.json", "file argument is not a migration certificate")
    certificate_path = _confined_package_path(root, "scheduler-migration-certificate.json")
    package_path = _confined_package_path(root, "package-manifest.json")
    certificate = _stable_json(certificate_path, root=root)
    package = _stable_json(package_path, root=root)
    unsigned_certificate = dict(certificate)
    certificate_sha256 = unsigned_certificate.pop("certificate_sha256", None)
    unsigned_package = dict(package)
    package_sha256 = unsigned_package.pop("package_sha256", None)
    require(
        certificate.get("gate") == MIGRATION_GATE
        and certificate.get("status") == "PATCHED_IDENTITY_SCHEDULER_MIGRATION_VALIDATED"
        and certificate.get("reason") == RECOVERY_REASON
        and is_sha256(certificate_sha256)
        and certificate_sha256 == canonical_sha256(unsigned_certificate)
        and package.get("gate") == "qldpc-stage2-scheduler-migration-package-v1"
        and package.get("certificate_sha256") == certificate_sha256
        and is_sha256(package_sha256)
        and package_sha256 == canonical_sha256(unsigned_package),
        "migration certificate/package seal is invalid",
    )
    intended_output = certificate.get("intended_output")
    claimed_same_filesystem = certificate.get("same_filesystem_as")
    require(
        isinstance(intended_output, str)
        and isinstance(claimed_same_filesystem, str),
        "migration path claims are malformed",
    )
    intended = _lexical_absolute_path(Path(intended_output))
    prepublication_staging = bool(
        root.parent == intended.parent
        and root.name.startswith(f".{intended.name}.building-")
    )
    require(
        root == intended or prepublication_staging,
        "certificate intended output does not match package root",
    )
    claimed_target = _no_symlink_path(Path(claimed_same_filesystem))
    target_descriptor = _open_path_nofollow(claimed_target)
    try:
        target_metadata = os.fstat(target_descriptor)
    finally:
        os.close(target_descriptor)
    require(
        root_metadata.st_dev == target_metadata.st_dev,
        "certificate package/target filesystem claim diverges",
    )
    if same_filesystem_as is not None:
        caller_target = _no_symlink_path(same_filesystem_as)
        require(
            caller_target == claimed_target,
            "caller target differs from certificate target",
        )
    indexed = package.get("files")
    require(isinstance(indexed, list), "package file index is malformed")
    indexed_paths: set[str] = set()
    for item in indexed:
        require(
            isinstance(item, Mapping)
            and isinstance(item.get("path"), str)
            and item["path"] not in indexed_paths
            and isinstance(item.get("bytes"), int)
            and not isinstance(item.get("bytes"), bool)
            and is_sha256(item.get("sha256")),
            "package file index entry is malformed",
        )
        member = _confined_package_path(root, str(item["path"]))
        digest, size = _stable_sha256(member, expected_root=root)
        require(digest == item["sha256"] and size == item["bytes"], f"package member changed: {item['path']}")
        indexed_paths.add(str(item["path"]))
    require(
        _package_files(root) == indexed_paths | {"package-manifest.json"},
        "package tree contains an unindexed or missing member",
    )

    evidence = certificate.get("evidence")
    successor = certificate.get("successor")
    require(isinstance(evidence, Mapping) and isinstance(successor, Mapping), "migration evidence/successor is malformed")
    expected_old_anchors = {
        "snapshot_sha256": EXPECTED["snapshot_sha256"],
        "offsets_sha256": OLD_OFFSETS_SHA256,
        "snapshot_identity_sha256": EXPECTED["snapshot_identity_sha256"],
        "binding_sha256": EXPECTED["final_binding_sha256"],
        "last_ack_sha256": EXPECTED["last_ack_sha256"],
        "pending_page_sha256": EXPECTED["pending_page_sha256"],
        "original_ledger_file_sha256": EXPECTED["original_ledger_file_sha256"],
        "original_ledger_progress_sha256": EXPECTED["original_ledger_progress_sha256"],
    }
    require(
        certificate.get("old_anchors") == expected_old_anchors
        and certificate.get("validation") == {
            "selection_ledger": "PASS", "pipeline_scheduler": "PASS",
            "production_files_modified": False,
        },
        "compiled old anchors or validation claims diverge",
    )
    core_path = _confined_package_path(root, str(evidence.get("core_ledger_path")))
    validator_source_path = _validate_migration_evidence_claim_schema(evidence)
    report_path = _confined_package_path(root, str(evidence.get("core_report_path")))
    terminal_path = _confined_package_path(root, str(evidence.get("terminal_report_path")))
    evaluations_path = _confined_package_path(
        root, str(evidence.get("terminal_evaluations_path"))
    )
    packaged_registry_path = _confined_package_path(
        root, str(evidence.get("packaged_registry_path"))
    )
    old_transition_archive_path = _confined_package_path(
        root, str(evidence.get("old_transition_archive_path"))
    )
    for path, expected in (
        (core_path, evidence.get("core_ledger_file_sha256")),
        (report_path, evidence.get("core_report_file_sha256")),
        (terminal_path, evidence.get("terminal_report_file_sha256")),
        (evaluations_path, evidence.get("terminal_evaluations_sha256")),
        (packaged_registry_path, evidence.get("packaged_registry_sha256")),
        (old_transition_archive_path, evidence.get("old_transition_archive_sha256")),
    ):
        require(_stable_sha256(path, expected_root=root)[0] == expected, "packaged recovery evidence hash diverges")
    core = _stable_json(core_path, root=root)
    report = _stable_json(report_path, root=root)
    terminal = _stable_json(terminal_path, root=root)
    packaged_registry = _stable_json(packaged_registry_path, root=root)
    _validate_migration_evidence_objects(core, report, terminal)
    old_archive_value = _stable_json(old_transition_archive_path, root=root)
    require(
        evidence.get("old_transition_archive_sha256")
        == EXPECTED["transition_archive_sha256"],
        "packaged old transition archive anchor diverges",
    )
    validate_and_rebind_archive(old_archive_value)
    old_scheduler = old_archive_value.get("adaptive_page_scheduler")
    old_transitions = (
        old_scheduler.get("transitions")
        if isinstance(old_scheduler, Mapping) else None
    )
    require(
        isinstance(old_transitions, list) and len(old_transitions) == 2,
        "packaged old transition archive lacks clean transitions",
    )
    expected_clean_outcome_sources = [
        {
            "source": "SEALED_OLD_TRANSITION_CLEAN_EVIDENCE",
            "old_transition_archive_sha256": EXPECTED["transition_archive_sha256"],
            "old_transition_entry_sha256": old_transitions[index]["entry_sha256"],
            "old_clean_evidence": old_transitions[index]["clean_evidence"],
        }
        for index in range(2)
    ]
    expected_clean_outcome_sources.append({
        "source": "SEALED_PAGE31_TRANSITION_ARCHIVE_CREATION",
        "old_transition_archive_sha256": EXPECTED["transition_archive_sha256"],
        "archive_completed_pages": EXPECTED["transition_completed_pages"],
        "archive_cursor": EXPECTED["transition_cursor"],
        "page_sequence": 30,
        "old_page_sha256": core["ack_chain"][30]["page_sha256"],
        "production_protocol": "clean-summary-validated-before-page31-archive",
    })
    require(
        evidence.get("clean_outcome_sources")
        == expected_clean_outcome_sources,
        "clean-page outcome provenance differs from old sealed archive",
    )
    require(
        evidence.get("core_progress_sha256") == core.get("progress_sha256")
        and evidence.get("core_report_sha256") == report.get("report_sha256")
        and evidence.get("terminal_report_sha256") == terminal.get("report_sha256")
        and evidence.get("terminal_rows") == EXPECTED["terminal_rows"]
        and evidence.get("terminal_evaluations_sha256") == EXPECTED["evaluations_sha256"]
        and evidence.get("packaged_registry_sha256") == EXPECTED["registry_file_sha256"],
        "packaged recovery evidence claims diverge",
    )
    evaluations_payload = _stable_read(evaluations_path, expected_root=root)
    checkpoint_sources = terminal_checkpoint_records(evaluations_payload)
    expected_checkpoint_mapping = [
        {
            **record,
            "package_path": (
                "recovery-evidence/terminal-checkpoints/"
                f"{record['source_line']:03d}-{record['sha256']}.evidence"
            ),
        }
        for record in checkpoint_sources
    ]
    checkpoint_mapping = evidence.get("terminal_checkpoint_mapping")
    require(
        checkpoint_mapping == expected_checkpoint_mapping
        and evidence.get("terminal_checkpoint_count") == EXPECTED["terminal_rows"]
        and evidence.get("terminal_checkpoint_mapping_sha256")
        == canonical_sha256(expected_checkpoint_mapping),
        "terminal checkpoint package mapping diverges",
    )
    checkpoint_overrides: dict[str, Path] = {}
    for record in expected_checkpoint_mapping:
        checkpoint_path = _confined_package_path(root, str(record["package_path"]))
        checkpoint_sha256, checkpoint_bytes = _stable_sha256(
            checkpoint_path, expected_root=root,
        )
        require(
            checkpoint_sha256 == record["sha256"]
            and checkpoint_bytes == record["bytes"],
            f"terminal checkpoint row {record['source_line']} diverges",
        )
        checkpoint_overrides[str(record["source_path"])] = checkpoint_path
    fresh_terminal = replay_terminal_evaluations(
        evaluations_path,
        evaluations_payload=evaluations_payload,
        evidence_overrides=checkpoint_overrides,
        stable_root=root,
    )
    require(
        fresh_terminal.get("records") == terminal.get("records")
        and fresh_terminal.get("witness_kind_counts") == terminal.get("witness_kind_counts")
        and fresh_terminal.get("rows") == terminal.get("rows")
        and fresh_terminal.get("valid_witnesses") == terminal.get("valid_witnesses")
        and fresh_terminal.get("all_rebuilt_n_k_match") is True
        and fresh_terminal.get("all_strictly_below_12") is True,
        "54 packaged terminal witnesses do not independently replay",
    )
    known_digests = registry_digests(packaged_registry)

    ledger_path = _confined_package_path(root, "stage2-selection-ledger.json")
    manifest_path = _confined_package_path(root, "stage2-selection-ledger.json.ranked-snapshot.manifest.json")
    snapshot_path = _confined_package_path(root, "stage2-selection-ledger.json.ranked-snapshot.jsonl")
    offsets_path = _confined_package_path(root, "stage2-selection-ledger.json.ranked-snapshot.offsets")
    ledger = _stable_json(ledger_path, root=root)
    manifest = _stable_json(manifest_path, root=root)
    unsigned_manifest = dict(manifest)
    manifest_sha256 = unsigned_manifest.pop("manifest_sha256", None)
    binding = manifest.get("binding")
    identity = manifest.get("identity")
    require(
        manifest.get("gate") == "qldpc-stage2-ranked-snapshot"
        and is_sha256(manifest_sha256)
        and manifest_sha256 == canonical_sha256(unsigned_manifest)
        and isinstance(binding, Mapping)
        and isinstance(identity, Mapping)
        and canonical_sha256(OLD_COUNTS) == OLD_COUNTS_SHA256
        and manifest.get("counts") == OLD_COUNTS
        and identity.get("counts_sha256") == OLD_COUNTS_SHA256
        and canonical_sha256(identity) == successor.get("snapshot_identity_sha256"),
        "successor ranked manifest does not replay",
    )
    unsigned_binding = dict(binding)
    binding_sha256 = unsigned_binding.pop("binding_sha256", None)
    expected_identity = {
        "binding_sha256": binding_sha256,
        "snapshot_sha256": EXPECTED["snapshot_sha256"],
        "offsets_sha256": OLD_OFFSETS_SHA256,
        "chunk_index_sha256": OLD_CHUNK_INDEX_SHA256,
        "chunk_rows": RANKED_CHUNK_ROWS,
        "rows": EXPECTED["snapshot_rows"],
        "eligible_rows": EXPECTED["eligible_rows"],
        "counts_sha256": OLD_COUNTS_SHA256,
    }
    require(
        is_sha256(binding_sha256)
        and binding_sha256 == canonical_sha256(unsigned_binding)
        and manifest.get("binding_sha256") == binding_sha256
        and manifest.get("snapshot_rows") == EXPECTED["snapshot_rows"]
        and manifest.get("chunk_rows") == RANKED_CHUNK_ROWS
        and identity == expected_identity
        and successor.get("manifest_sha256") == manifest_sha256
        and successor.get("binding_sha256") == binding_sha256
        and successor.get("source_fingerprint")
        == binding.get("source_fingerprint")
        and successor.get("snapshot_identity") == expected_identity
        and successor.get("snapshot_identity_sha256")
        == canonical_sha256(expected_identity),
        "successor identity/binding claims do not exactly replay",
    )
    snapshot_digest, snapshot_bytes = _stable_sha256(snapshot_path, expected_root=root)
    offsets_digest, offsets_bytes = _stable_sha256(offsets_path, expected_root=root)
    chunks, replay_rows = _stable_ranked_chunks(
        snapshot_path, offsets_path, root=root,
        known_digests=known_digests,
    )
    require(
        snapshot_digest == EXPECTED["snapshot_sha256"]
        and snapshot_bytes == EXPECTED["snapshot_bytes"]
        and offsets_digest == OLD_OFFSETS_SHA256
        and offsets_bytes == OLD_OFFSETS_BYTES
        and chunks == manifest.get("chunks")
        and canonical_sha256(chunks) == OLD_CHUNK_INDEX_SHA256
        and identity.get("snapshot_sha256") == snapshot_digest
        and identity.get("offsets_sha256") == offsets_digest
        and identity.get("chunk_index_sha256") == OLD_CHUNK_INDEX_SHA256,
        "successor snapshot/offset/chunk bytes diverge",
    )
    independently_replayed_core, independently_replayed_pending = (
        replay_sealed_core_from_snapshot(replay_rows)
    )
    require(
        independently_replayed_core == core
        and independently_replayed_pending == core.get("pending"),
        "snapshot/registry replay differs from the packaged sealed core",
    )
    require(
        manifest.get("snapshot_stat") == _stat_identity(snapshot_path)
        and manifest.get("offsets_stat") == _stat_identity(offsets_path),
        "successor manifest stat identity diverges",
    )
    try:
        from scripts.audit_candidate_pool import _binding_dependencies_unchanged

        binding_unchanged = _binding_dependencies_unchanged(
            binding,
            [Path(str(item["path"])) for item in binding["inputs"]],
        )
    except (ImportError, OSError, KeyError, TypeError, ValueError) as exc:
        raise RecoveryError("live patched dependency binding could not be replayed") from exc
    require(binding_unchanged, "live source/runtime/input binding changed")
    for item in binding["inputs"]:
        dependency = _no_symlink_path(Path(str(item["path"])))
        dependency_sha256, dependency_bytes = _stable_sha256(dependency)
        require(
            dependency_sha256 == item.get("sha256")
            and dependency_bytes == item.get("stat", {}).get("bytes")
            and _stat_identity(dependency) == item.get("stat"),
            f"candidate input changed or is unsafe: {dependency}",
        )
    registry_identity = binding.get("known_code_registry")
    require(isinstance(registry_identity, Mapping), "binding registry identity is missing")
    registry_path = _no_symlink_path(Path(str(registry_identity.get("path"))))
    claimed_registry_path = _no_symlink_path(
        Path(str(evidence.get("known_code_registry_path")))
    )
    registry_sha256, registry_bytes = _stable_sha256(registry_path)
    require(
        registry_sha256 == registry_identity.get("sha256")
        and registry_bytes == registry_identity.get("stat", {}).get("bytes")
        and _stat_identity(registry_path) == registry_identity.get("stat")
        and registry_sha256 == evidence.get("known_code_registry_sha256")
        and claimed_registry_path == registry_path,
        "known-code registry changed or is unsafe",
    )
    route_path = _no_symlink_path(
        Path(str(evidence.get("binding_route_manifest_path")))
    )
    require(
        _stable_sha256(route_path)[0]
        == evidence.get("binding_route_manifest_file_sha256"),
        "binding route manifest changed or is unsafe",
    )
    route = _stable_json(route_path, root=route_path.parent)
    unsigned_route = dict(route)
    route_seal = unsigned_route.pop("manifest_sha256", None)
    route_binding = route.get("binding")
    route_inputs = (
        route_binding.get("inputs")
        if isinstance(route_binding, Mapping) else None
    )
    require(
        is_sha256(route_seal)
        and route_seal == canonical_sha256(unsigned_route)
        and isinstance(route_inputs, list)
        and len(route_inputs) == len(binding["inputs"]) == 10
        and all(
            isinstance(item, Mapping) and isinstance(item.get("path"), str)
            for item in route_inputs
        )
        and [item["path"] for item in route_inputs]
        == [item["path"] for item in binding["inputs"]]
        and route_binding.get("target_mode") == binding.get("target_mode")
        == "scalar-fom-inclusive-v1",
        "binding route manifest does not route the successor binding inputs",
    )
    validator_source_sha256 = _stable_sha256(validator_source_path)[0]
    require(
        evidence.get("validator_source_sha256") == validator_source_sha256,
        "migration validator source changed after package creation",
    )
    known_answer = _no_symlink_path(Path(str(evidence.get("known_answer_path"))))
    known_answer_sha256 = _stable_sha256(known_answer)[0]
    require(known_answer_sha256 == evidence.get("known_answer_sha256"), "known-answer artifact changed")
    identity_sha256 = canonical_sha256(identity)
    page_bindings = [
        selection_binding_for_top(int(step["top"]), manifest=manifest, known_answer_sha256=known_answer_sha256)
        for step in PAGE_POLICY
    ]
    require(page_bindings == successor.get("page_bindings"), "successor page binding vector diverges")
    from evaluation.selection_ledger import validate_selection_ledger

    validate_selection_ledger(
        ledger,
        binding_sha256=page_bindings[3],
        snapshot_identity_sha256_value=identity_sha256,
        snapshot_rows=EXPECTED["snapshot_rows"],
        eligible_rows=EXPECTED["eligible_rows"],
    )
    rebound, mapping = rebind_selection_prefix(
        core,
        binding_sha256=page_bindings[3],
        identity_sha256=identity_sha256,
        top=4096,
        completed_pages=44,
        include_pending=True,
        acknowledged_at=ledger.get("last_acknowledged_at"),
    )
    for field in (
        "binding_sha256", "snapshot_identity_sha256", "cursor",
        "committed_digests", "completed_pages", "ack_chain",
        "genesis_sha256", "last_ack_sha256", "pending", "deferred_pages",
    ):
        require(rebound.get(field) == ledger.get(field), f"active ledger {field} differs from core replay")
    require(
        len(mapping) == EXPECTED["completed_pages"] + 1
        and mapping == certificate.get("old_to_new_page_ack_mapping"),
        "old-to-new page/ACK mapping diverges",
    )

    archive_records = certificate.get("rung_archives")
    clean_records = certificate.get("clean_recovery_artifacts")
    scheduler = ledger.get("adaptive_page_scheduler")
    require(
        isinstance(archive_records, list) and len(archive_records) == 3
        and isinstance(clean_records, list) and len(clean_records) == 3
        and isinstance(scheduler, Mapping)
        and scheduler.get("active_step") == 3
        and len(scheduler.get("transitions", [])) == 3,
        "scheduler recovery topology is incomplete",
    )
    boundaries = (29, 30, 31)
    expected_transitions: list[dict[str, Any]] = []
    acknowledged_at = ledger.get("last_acknowledged_at")
    for sequence, (archive_record, clean_record, transition) in enumerate(
        zip(archive_records, clean_records, scheduler["transitions"], strict=True)
    ):
        completed_pages = boundaries[sequence]
        expected_from, _ = rebind_selection_prefix(
            core,
            binding_sha256=page_bindings[sequence],
            identity_sha256=identity_sha256,
            top=int(PAGE_POLICY[sequence]["top"]),
            completed_pages=completed_pages,
            acknowledged_at=acknowledged_at,
        )
        expected_from = attach_scheduler(
            expected_from,
            seal_page_scheduler(
                sequence,
                0 if sequence == 0 else boundaries[sequence - 1],
                expected_transitions,
            ),
        )
        expected_to, _ = rebind_selection_prefix(
            core,
            binding_sha256=page_bindings[sequence + 1],
            identity_sha256=identity_sha256,
            top=int(PAGE_POLICY[sequence + 1]["top"]),
            completed_pages=completed_pages,
            acknowledged_at=acknowledged_at,
        )
        archive = _confined_package_path(root, str(archive_record["path"]))
        clean = _confined_package_path(root, str(clean_record["path"]))
        archive_value = _stable_json(archive, root=root)
        archive_digest = _stable_sha256(archive, expected_root=root)[0]
        expected_archive_path = (
            "selection-ledger-page-size-transitions/"
            f"pages-{completed_pages:06d}-{PAGE_POLICY[sequence]['top']}-"
            f"to-{PAGE_POLICY[sequence + 1]['top']}-{archive_digest[:16]}.json"
        )
        _validate_exact_rung_record(
            archive_record,
            sequence=sequence,
            path=expected_archive_path,
            outcome_evidence=expected_clean_outcome_sources[sequence],
            sha256=archive_digest,
            progress_sha256=expected_from["progress_sha256"],
        )
        require(
            archive_value == expected_from
            and transition.get("archive_path") == expected_archive_path
            and transition.get("archive_sha256") == archive_digest,
            "rung archive differs from exact core-derived prefix",
        )
        clean_digest = _stable_sha256(clean, expected_root=root)[0]
        clean_value = _stable_json(clean, root=root)
        old_ack = core["ack_chain"][completed_pages - 1]
        clean_created_at = clean_value.get("created_at")
        require(
            isinstance(clean_created_at, str) and clean_created_at,
            "clean recovery timestamp is missing",
        )
        expected_clean_payload = _expected_clean_recovery_payload(
            sequence=sequence,
            completed_pages=completed_pages,
            new_snapshot_identity_sha256=identity_sha256,
            old_page_sha256=old_ack["page_sha256"],
            old_ack_sha256=old_ack["ack_sha256"],
            new_page_sha256=expected_from["last_acknowledged_page_sha256"],
            new_ack_sha256=expected_from["last_ack_sha256"],
            selected_digests_sha256=canonical_sha256(
                old_ack["page"]["selected_digests"]
            ),
            rejected_count=len(old_ack["page"]["selected_digests"]),
            core_report_sha256=report["report_sha256"],
            terminal_report_sha256=terminal["report_sha256"],
            created_at=clean_created_at,
            outcome_evidence=expected_clean_outcome_sources[sequence],
        )
        expected_clean = _validate_exact_clean_recovery_artifact(
            clean_value, expected_clean_payload,
        )
        expected_clean_path = (
            "sealed-clean-page-recovery/"
            f"transition-{sequence:03d}-page-{completed_pages - 1:06d}.json"
        )
        require(
            clean_record == {
                "sequence": sequence,
                "path": expected_clean_path,
                "file_sha256": clean_digest,
                "artifact_sha256": expected_clean["artifact_sha256"],
            },
            "sealed clean recovery artifact differs from core-derived evidence",
        )
        transition_clean = transition.get("clean_evidence")
        require(
            isinstance(transition_clean, Mapping)
            and isinstance(transition_clean.get("verified_at"), str)
            and transition_clean.get("verified_at"),
            "transition clean evidence timestamp is missing",
        )
        expected_clean_evidence = {
            "schema_version": 1,
            "gate": "qldpc-stage2-clean-page-evidence",
            "page_sha256": expected_from["last_acknowledged_page_sha256"],
            "summary_sha256": clean_digest,
            "status_counts_sha256": canonical_sha256(
                expected_clean_payload["status_counts"]
            ),
            "completed_pages": completed_pages,
            "verified_at": transition_clean["verified_at"],
        }
        transitioned_at = transition.get("transitioned_at")
        require(
            isinstance(transitioned_at, str) and transitioned_at,
            "transition timestamp is missing",
        )
        expected_transition_payload = {
            "schema_version": 1,
            "gate": PAGE_TRANSITION_GATE,
            "sequence": sequence,
            "previous_transition_sha256": (
                expected_transitions[-1]["entry_sha256"]
                if expected_transitions
                else canonical_sha256([dict(x) for x in PAGE_POLICY])
            ),
            "from_step": sequence,
            "to_step": sequence + 1,
            "from_top": PAGE_POLICY[sequence]["top"],
            "to_top": PAGE_POLICY[sequence + 1]["top"],
            "from_binding_sha256": expected_from["binding_sha256"],
            "to_binding_sha256": expected_to["binding_sha256"],
            "snapshot_identity_sha256": identity_sha256,
            "cursor": expected_from["cursor"],
            "completed_pages": expected_from["completed_pages"],
            "committed_digests_sha256": canonical_sha256(
                expected_from["committed_digests"]
            ),
            "from_progress_sha256": expected_from["progress_sha256"],
            "from_last_ack_sha256": expected_from["last_ack_sha256"],
            "to_last_ack_sha256": expected_to["last_ack_sha256"],
            "from_last_page_sha256": expected_from["last_acknowledged_page_sha256"],
            "to_last_page_sha256": expected_to["last_acknowledged_page_sha256"],
            "archive_path": expected_archive_path,
            "archive_sha256": archive_digest,
            "clean_evidence": expected_clean_evidence,
            "reason": RECOVERY_REASON,
            "transitioned_at": transitioned_at,
        }
        expected_transition = {
            **expected_transition_payload,
            "entry_sha256": canonical_sha256(expected_transition_payload),
        }
        require(
            transition == expected_transition,
            "scheduler transition differs from exact rebound prefixes",
        )
        expected_transitions.append(expected_transition)
    require(
        scheduler == seal_page_scheduler(3, boundaries[-1], expected_transitions),
        "active scheduler state differs from exact recovered transitions",
    )
    require(certificate.get("page30_recovery_artifact") == clean_records[2], "page30 recovery artifact is not explicitly bound")
    try:
        from humanize.pipeline import FiveStagePipeline

        validator = object.__new__(FiveStagePipeline)
        validator.config = SimpleNamespace(
            stage2_page_schedule=[(int(x["top"]), x["clean_pages"]) for x in PAGE_POLICY],
            target_mode=binding["target_mode"],
            known_answer_artifact=known_answer,
        )
        validator.paths = SimpleNamespace(
            solver_state=root,
            stage2_selection_ledger=ledger_path,
        )
        require(validator._stage2_snapshot_manifest() == manifest, "production manifest validator changed the manifest")
        validator._validated_stage2_selection_ledger(ledger)
        validator._validate_stage2_page_scheduler(ledger, manifest)
    except Exception as exc:
        raise RecoveryError("production scheduler validator rejected package") from exc
    expected_successor = {
        "manifest_file_sha256": _stable_sha256(
            manifest_path, expected_root=root,
        )[0],
        "manifest_sha256": manifest_sha256,
        "binding_sha256": binding_sha256,
        "source_fingerprint": binding["source_fingerprint"],
        "snapshot_identity": expected_identity,
        "snapshot_identity_sha256": identity_sha256,
        "page_bindings": page_bindings,
        "active_ledger_progress_sha256": ledger["progress_sha256"],
        "active_last_ack_sha256": ledger["last_ack_sha256"],
        "active_pending_page_sha256": ledger["pending"]["page_sha256"],
        "active_scheduler_state_sha256": scheduler["state_sha256"],
    }
    require(
        successor == expected_successor,
        "successor certificate claims diverge from independently replayed files",
    )
    return {
        "certificate_sha256": certificate_sha256,
        "prepublication_staging": prepublication_staging,
        "package_sha256": package_sha256,
        "binding_sha256": binding["binding_sha256"],
        "snapshot_identity_sha256": identity_sha256,
        "active_ledger_progress_sha256": ledger["progress_sha256"],
        "active_last_ack_sha256": ledger["last_ack_sha256"],
        "active_pending_page_sha256": ledger["pending"]["page_sha256"],
        "terminal_report_sha256": terminal["report_sha256"],
        "validator_source_sha256": validator_source_sha256,
        "production_files_modified": False,
    }



INSTALL_JOURNAL_GATE = "qldpc-stage2-scheduler-migration-install-journal-v1"
INSTALL_COMMIT_GATE = "qldpc-stage2-scheduler-migration-install-commit-v1"
INSTALL_JOURNAL_NAME = "stage2-scheduler-migration-install-journal.json"
INSTALL_COMMIT_NAME = "stage2-scheduler-migration-install-commit.json"
INSTALL_LOCK_NAME = "stage2-scheduler-migration-install.lock"
INSTALL_BACKUP_DIR = "stage2-scheduler-migration-backups"


def _sealed_control(
    payload: Mapping[str, Any], *, seal_field: str,
) -> dict[str, Any]:
    return {**dict(payload), seal_field: canonical_sha256(payload)}


def _validate_control_seal(
    value: Mapping[str, Any], *, seal_field: str, label: str,
) -> None:
    unsigned = dict(value)
    seal = unsigned.pop(seal_field, None)
    require(
        is_sha256(seal) and seal == canonical_sha256(unsigned),
        f"{label} seal is invalid",
    )


def _migration_install_entries(
    package_root: Path,
) -> tuple[dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    root = _no_symlink_path(package_root)
    certificate = _stable_json(
        _confined_package_path(root, "scheduler-migration-certificate.json"),
        root=root,
    )
    package = _stable_json(
        _confined_package_path(root, "package-manifest.json"), root=root,
    )
    indexed = package.get("files")
    require(isinstance(indexed, list), "migration package index is malformed")
    by_path = {
        str(item["path"]): item for item in indexed
        if isinstance(item, Mapping) and isinstance(item.get("path"), str)
    }
    archive_records = certificate.get("rung_archives")
    clean_records = certificate.get("clean_recovery_artifacts")
    require(
        isinstance(archive_records, list) and len(archive_records) == 3
        and isinstance(clean_records, list) and len(clean_records) == 3,
        "migration install topology is incomplete",
    )
    relative_paths = [
        *[str(item["path"]) for item in archive_records],
        *[str(item["path"]) for item in clean_records],
        "stage2-selection-ledger.json.ranked-snapshot.jsonl",
        "stage2-selection-ledger.json.ranked-snapshot.offsets",
        "stage2-selection-ledger.json.ranked-snapshot.manifest.json",
        "stage2-selection-ledger.json",
    ]
    require(
        len(relative_paths) == len(set(relative_paths)),
        "migration install path list contains duplicates",
    )
    entries: list[dict[str, Any]] = []
    for relative in relative_paths:
        item = by_path.get(relative)
        require(
            isinstance(item, Mapping)
            and is_sha256(item.get("sha256"))
            and isinstance(item.get("bytes"), int)
            and not isinstance(item.get("bytes"), bool),
            f"migration install member is not indexed: {relative}",
        )
        member = _confined_package_path(root, relative)
        member_fd = _open_path_nofollow(member, regular=True)
        try:
            source_token = list(_stable_token(os.fstat(member_fd)))
        finally:
            os.close(member_fd)
        entries.append({
            "path": relative,
            "sha256": item["sha256"],
            "bytes": item["bytes"],
            "source_token": source_token,
        })
    return certificate, package, entries


def _validated_install_material(
    package: Path,
    live_root: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    """Bracket exact cert/package/token capture with two full validations."""

    first = validate_patched_scheduler_migration(
        package, same_filesystem_as=live_root,
    )
    certificate, package_manifest, entries = _migration_install_entries(package)
    unsigned_certificate = dict(certificate)
    certificate_sha256 = unsigned_certificate.pop("certificate_sha256", None)
    unsigned_package = dict(package_manifest)
    package_sha256 = unsigned_package.pop("package_sha256", None)
    require(
        certificate_sha256 == canonical_sha256(unsigned_certificate)
        and certificate_sha256 == first.get("certificate_sha256")
        and package_sha256 == canonical_sha256(unsigned_package)
        and package_sha256 == first.get("package_sha256"),
        "captured install certificate/package objects differ from validation",
    )
    second = validate_patched_scheduler_migration(
        package, same_filesystem_as=live_root,
    )
    require(
        first == second,
        "migration package changed around install-material capture",
    )
    return second, certificate, package_manifest, entries


def _install_relative_parts(relative: str) -> tuple[str, ...]:
    rel = Path(relative)
    require(
        not rel.is_absolute() and bool(rel.parts)
        and all(part not in {"", ".", ".."} for part in rel.parts),
        f"install target escapes solver-state: {relative}",
    )
    return tuple(rel.parts)


def _open_relative_parent_at(
    root_fd: int, relative: str, *, create: bool = False,
    missing_ok: bool = False,
) -> tuple[int, str] | None:
    """Pin all ancestors beneath an already-open solver-state directory."""
    parts = _install_relative_parts(relative)
    flags = (os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
             | getattr(os, "O_CLOEXEC", 0))
    current = os.dup(root_fd)
    try:
        for part in parts[:-1]:
            try:
                following = os.open(part, flags, dir_fd=current)
            except FileNotFoundError:
                if missing_ok and not create:
                    os.close(current)
                    return None
                if not create:
                    raise RecoveryError(f"install parent is missing: {relative}")
                try:
                    os.mkdir(part, 0o700, dir_fd=current)
                    os.fsync(current)
                    following = os.open(part, flags, dir_fd=current)
                    os.fsync(following)
                except OSError as exc:
                    raise RecoveryError(
                        f"install parent creation failed: {relative}"
                    ) from exc
            except OSError as exc:
                raise RecoveryError(
                    f"install ancestor is unsafe: {relative}"
                ) from exc
            os.close(current)
            current = following
        return current, parts[-1]
    except BaseException:
        try:
            os.close(current)
        except OSError:
            pass
        raise


def _relative_metadata_at(
    root_fd: int, relative: str, *, missing_ok: bool = False,
) -> os.stat_result | None:
    opened = _open_relative_parent_at(
        root_fd, relative, missing_ok=missing_ok,
    )
    if opened is None:
        return None
    parent_fd, name = opened
    try:
        try:
            metadata = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            if missing_ok:
                return None
            raise RecoveryError(f"install target is missing: {relative}")
        require(stat.S_ISREG(metadata.st_mode), f"install target is unsafe: {relative}")
        return metadata
    finally:
        os.close(parent_fd)


def _relative_regular_exists_at(root_fd: int, relative: str) -> bool:
    return _relative_metadata_at(root_fd, relative, missing_ok=True) is not None


def _open_relative_regular_at(
    root_fd: int, relative: str,
) -> tuple[int, int, str]:
    opened = _open_relative_parent_at(root_fd, relative)
    assert opened is not None
    parent_fd, name = opened
    try:
        descriptor = os.open(
            name, os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0),
            dir_fd=parent_fd,
        )
    except OSError as exc:
        os.close(parent_fd)
        raise RecoveryError(f"install source is unavailable: {relative}") from exc
    require(stat.S_ISREG(os.fstat(descriptor).st_mode), f"unsafe file: {relative}")
    return parent_fd, descriptor, name


def _stable_relative_bytes(
    root_fd: int, relative: str, *, digest_only: bool = False,
) -> bytes | tuple[str, int]:
    parent_fd, descriptor, name = _open_relative_regular_at(root_fd, relative)
    digest = hashlib.sha256()
    chunks: list[bytes] = []
    total = 0
    try:
        before = os.fstat(descriptor)
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            total += len(chunk)
            if not digest_only:
                chunks.append(chunk)
        after = os.fstat(descriptor)
        current = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        require(
            _stable_token(before) == _stable_token(after) == _stable_token(current)
            and total == before.st_size,
            f"installed file changed during read: {relative}",
        )
    finally:
        os.close(descriptor)
        os.close(parent_fd)
    return (digest.hexdigest(), total) if digest_only else b"".join(chunks)


def _stable_read_relative_at(root_fd: int, relative: str) -> bytes:
    value = _stable_relative_bytes(root_fd, relative)
    assert isinstance(value, bytes)
    return value


def _stable_sha256_relative_at(root_fd: int, relative: str) -> tuple[str, int]:
    value = _stable_relative_bytes(root_fd, relative, digest_only=True)
    assert isinstance(value, tuple)
    return value


def _stable_sha256_token_relative_at(
    root_fd: int, relative: str,
) -> tuple[str, int, list[int]]:
    """Bind stable content to the exact regular-file token used for CAS."""

    before = _relative_metadata_at(root_fd, relative, missing_ok=False)
    assert before is not None
    digest, size = _stable_sha256_relative_at(root_fd, relative)
    after = _relative_metadata_at(root_fd, relative, missing_ok=False)
    assert after is not None
    before_token = list(_stable_token(before))
    after_token = list(_stable_token(after))
    require(
        before_token == after_token and size == int(after.st_size),
        f"installed file token changed during stable read: {relative}",
    )
    return digest, size, after_token


def _stable_json_relative_at(root_fd: int, relative: str) -> dict[str, Any]:
    try:
        value = json.loads(_stable_read_relative_at(root_fd, relative))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise RecoveryError(f"transaction JSON is malformed: {relative}") from exc
    require(isinstance(value, dict), f"transaction JSON is not an object: {relative}")
    return value


def _write_descriptor_all(descriptor: int, payload: bytes) -> None:
    view = memoryview(payload)
    while view:
        written = os.write(descriptor, view)
        require(written > 0, "transaction write stalled")
        view = view[written:]


def _atomic_bytes_relative_at(
    root_fd: int, relative: str, payload: bytes, *, replace: bool,
) -> None:
    opened = _open_relative_parent_at(root_fd, relative, create=True)
    assert opened is not None
    parent_fd, name = opened
    temporary = f".{name}.writing-{os.getpid()}-{time.time_ns()}"
    descriptor: int | None = None
    temporary_exists = False
    try:
        descriptor = os.open(
            temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
            | getattr(os, "O_CLOEXEC", 0), 0o600, dir_fd=parent_fd,
        )
        temporary_exists = True
        _write_descriptor_all(descriptor, payload)
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = None
        try:
            existing = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            existing = None
        require(
            existing is None or (replace and stat.S_ISREG(existing.st_mode)),
            f"control target exists or is unsafe: {relative}",
        )
        if replace:
            os.replace(temporary, name, src_dir_fd=parent_fd, dst_dir_fd=parent_fd)
            temporary_exists = False
        else:
            os.link(
                temporary, name, src_dir_fd=parent_fd, dst_dir_fd=parent_fd,
                follow_symlinks=False,
            )
            os.fsync(parent_fd)
            os.unlink(temporary, dir_fd=parent_fd)
            temporary_exists = False
        os.fsync(parent_fd)
    except (OSError, RecoveryError) as exc:
        if isinstance(exc, RecoveryError):
            raise
        raise RecoveryError(f"atomic control write failed: {relative}") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if temporary_exists:
            try:
                os.unlink(temporary, dir_fd=parent_fd)
                os.fsync(parent_fd)
            except OSError:
                pass
        os.close(parent_fd)
    require(_stable_read_relative_at(root_fd, relative) == payload,
            f"atomic control write changed: {relative}")


def _atomic_json_relative_at(
    root_fd: int, relative: str, value: Mapping[str, Any], *, replace: bool,
) -> None:
    payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    _atomic_bytes_relative_at(root_fd, relative, payload, replace=replace)


def _copy_descriptor_to_relative_at(
    source_fd: int, *, root_fd: int, target_relative: str,
    expected_sha256: str, expected_bytes: int,
    expected_source_token: Sequence[int] | None = None,
    expected_target_token: Sequence[int] | None = None,
    expected_target_absent: bool = False,
) -> None:
    opened = _open_relative_parent_at(root_fd, target_relative, create=True)
    assert opened is not None
    parent_fd, name = opened
    temporary = f".{name}.installing-{os.getpid()}-{time.time_ns()}"
    destination: int | None = None
    temporary_exists = False
    try:
        before = os.fstat(source_fd)
        require(stat.S_ISREG(before.st_mode), "install source is not regular")
        require(
            not (expected_target_absent and expected_target_token is not None),
            "install target CAS expectation is contradictory",
        )
        if expected_source_token is not None:
            require(
                list(_stable_token(before)) == list(expected_source_token),
                "install source token changed after package validation",
            )
        os.lseek(source_fd, 0, os.SEEK_SET)
        destination = os.open(
            temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
            | getattr(os, "O_CLOEXEC", 0), 0o600, dir_fd=parent_fd,
        )
        temporary_exists = True
        digest = hashlib.sha256()
        total = 0
        while True:
            chunk = os.read(source_fd, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            total += len(chunk)
            _write_descriptor_all(destination, chunk)
        os.fsync(destination)
        os.close(destination)
        destination = None
        require(
            _stable_token(before) == _stable_token(os.fstat(source_fd))
            and total == expected_bytes and digest.hexdigest() == expected_sha256,
            "install source changed or differs from package index",
        )
        try:
            existing = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            existing = None
        require(
            existing is None or stat.S_ISREG(existing.st_mode),
            f"installed target is unsafe: {target_relative}",
        )
        if expected_target_absent:
            require(
                existing is None,
                f"install target appeared before replace: {target_relative}",
            )
        elif expected_target_token is not None:
            require(
                existing is not None
                and list(_stable_token(existing)) == list(expected_target_token),
                f"install target changed before replace: {target_relative}",
            )
        os.replace(temporary, name, src_dir_fd=parent_fd, dst_dir_fd=parent_fd)
        temporary_exists = False
        os.fsync(parent_fd)
    except (OSError, RecoveryError) as exc:
        if isinstance(exc, RecoveryError):
            raise
        raise RecoveryError(f"atomic install failed: {target_relative}") from exc
    finally:
        if destination is not None:
            os.close(destination)
        if temporary_exists:
            try:
                os.unlink(temporary, dir_fd=parent_fd)
                os.fsync(parent_fd)
            except OSError:
                pass
        os.close(parent_fd)
    require(
        _stable_sha256_relative_at(root_fd, target_relative)
        == (expected_sha256, expected_bytes),
        f"installed target changed: {target_relative}",
    )


def _atomic_install_file(
    source: Path, target: Path, *, root_fd: int, target_relative: str,
    expected_sha256: str, expected_bytes: int,
    expected_source_token: Sequence[int] | None = None,
    expected_target_token: Sequence[int] | None = None,
    expected_target_absent: bool = False,
) -> None:
    source_fd = _open_path_nofollow(source, regular=True)
    try:
        _copy_descriptor_to_relative_at(
            source_fd, root_fd=root_fd, target_relative=target_relative,
            expected_sha256=expected_sha256, expected_bytes=expected_bytes,
            expected_source_token=expected_source_token,
            expected_target_token=expected_target_token,
            expected_target_absent=expected_target_absent,
        )
    finally:
        os.close(source_fd)

def _atomic_install_relative_at(
    root_fd: int, source_relative: str, target_relative: str, *,
    expected_sha256: str, expected_bytes: int,
    expected_source_token: Sequence[int] | None = None,
) -> None:
    parent_fd, source_fd, _ = _open_relative_regular_at(root_fd, source_relative)
    try:
        _copy_descriptor_to_relative_at(
            source_fd, root_fd=root_fd, target_relative=target_relative,
            expected_sha256=expected_sha256, expected_bytes=expected_bytes,
            expected_source_token=expected_source_token,
        )
    finally:
        os.close(source_fd)
        os.close(parent_fd)


def _relative_replace_at(root_fd: int, source: str, target: str) -> None:
    source_opened = _open_relative_parent_at(root_fd, source)
    target_opened = _open_relative_parent_at(root_fd, target, create=True)
    assert source_opened is not None and target_opened is not None
    source_parent, source_name = source_opened
    target_parent, target_name = target_opened
    try:
        require(stat.S_ISREG(os.stat(
            source_name, dir_fd=source_parent, follow_symlinks=False,
        ).st_mode), "relative move source is unsafe")
        try:
            os.stat(target_name, dir_fd=target_parent, follow_symlinks=False)
        except FileNotFoundError:
            pass
        else:
            raise RecoveryError(f"relative move target already exists: {target}")
        os.replace(source_name, target_name,
                   src_dir_fd=source_parent, dst_dir_fd=target_parent)
        os.fsync(source_parent)
        os.fsync(target_parent)
    finally:
        os.close(source_parent)
        os.close(target_parent)


def _require_directory_binding(root_fd: int, root: Path) -> None:
    current = _open_path_nofollow(root, directory=True)
    try:
        expected, observed = os.fstat(root_fd), os.fstat(current)
        require(expected.st_dev == observed.st_dev and expected.st_ino == observed.st_ino,
                "solver-state path changed during transaction")
    finally:
        os.close(current)


def _installed_live_summary(
    package_root: Path,
    solver_state: Path,
    certificate: Mapping[str, Any],
    entries: Sequence[Mapping[str, Any]],
    *,
    root_fd: int | None = None,
) -> dict[str, Any]:
    root = _no_symlink_path(solver_state)
    owns_root_fd = root_fd is None
    descriptor = (
        _open_path_nofollow(root, directory=True)
        if root_fd is None else root_fd
    )
    assert descriptor is not None
    try:
        _require_directory_binding(descriptor, root)
        root_metadata = os.fstat(descriptor)
        root_identity = (int(root_metadata.st_dev), int(root_metadata.st_ino))
        target_tokens: dict[str, list[int]] = {}
        for entry in entries:
            relative = str(entry["path"])
            metadata = _relative_metadata_at(
                descriptor, relative, missing_ok=False,
            )
            assert metadata is not None
            target_tokens[relative] = list(_stable_token(metadata))

        for entry in entries:
            digest, size = _stable_sha256_relative_at(
                descriptor, str(entry["path"]),
            )
            require(
                digest == entry["sha256"] and size == entry["bytes"],
                f"live installed member differs: {entry['path']}",
            )
        ledger_relative = "stage2-selection-ledger.json"
        manifest_relative = (
            "stage2-selection-ledger.json.ranked-snapshot.manifest.json"
        )
        snapshot_relative = "stage2-selection-ledger.json.ranked-snapshot.jsonl"
        offsets_relative = "stage2-selection-ledger.json.ranked-snapshot.offsets"
        ledger_path = root / ledger_relative
        manifest_path = root / manifest_relative
        snapshot_path = root / snapshot_relative
        offsets_path = root / offsets_relative
        ledger = _stable_json_relative_at(descriptor, ledger_relative)
        manifest = _stable_json_relative_at(descriptor, manifest_relative)
        successor = certificate["successor"]
        require(
            canonical_sha256(manifest["identity"])
            == successor["snapshot_identity_sha256"],
            "live manifest identity differs from migration successor",
        )
        known_answer = _no_symlink_path(
            Path(str(certificate["evidence"]["known_answer_path"]))
        )
        from evaluation.selection_ledger import validate_selection_ledger
        validate_selection_ledger(
            ledger,
            binding_sha256=successor["page_bindings"][3],
            snapshot_identity_sha256_value=successor["snapshot_identity_sha256"],
            snapshot_rows=EXPECTED["snapshot_rows"],
            eligible_rows=EXPECTED["eligible_rows"],
        )
        from humanize.pipeline import FiveStagePipeline
        validator = object.__new__(FiveStagePipeline)
        validator.config = SimpleNamespace(
            stage2_page_schedule=[
                (int(x["top"]), x["clean_pages"]) for x in PAGE_POLICY
            ],
            target_mode=manifest["binding"]["target_mode"],
            known_answer_artifact=known_answer,
        )
        validator.paths = SimpleNamespace(
            solver_state=root,
            stage2_selection_ledger=root / ledger_relative,
        )
        require(validator._stage2_snapshot_manifest() == manifest,
                "live production manifest validator diverged")
        validator._validated_stage2_selection_ledger(ledger)
        validator._validate_stage2_page_scheduler(ledger, manifest)
        summary = {
            "ledger_path": str(ledger_path), "manifest_path": str(manifest_path),
            "snapshot_path": str(snapshot_path), "offsets_path": str(offsets_path),
            "ledger_file_sha256": _stable_sha256_relative_at(descriptor, ledger_relative)[0],
            "manifest_file_sha256": _stable_sha256_relative_at(descriptor, manifest_relative)[0],
            "snapshot_file_sha256": _stable_sha256_relative_at(descriptor, snapshot_relative)[0],
            "offsets_file_sha256": _stable_sha256_relative_at(descriptor, offsets_relative)[0],
            "binding_sha256": ledger["binding_sha256"],
            "snapshot_identity_sha256": ledger["snapshot_identity_sha256"],
            "progress_sha256": ledger["progress_sha256"],
            "ledger_content_sha256": ledger["progress_sha256"],
            "manifest_content_sha256": manifest["manifest_sha256"],
            "snapshot_content_sha256": manifest["identity"]["snapshot_sha256"],
            "offsets_content_sha256": manifest["identity"]["offsets_sha256"],
            "validator_source_sha256": _stable_sha256(Path(__file__))[0],
            "last_ack_sha256": ledger["last_ack_sha256"],
            "pending_page_sha256": ledger["pending"]["page_sha256"],
            "scheduler_state_sha256": ledger["adaptive_page_scheduler"]["state_sha256"],
        }
        _require_directory_binding(descriptor, root)
        current_root = os.fstat(descriptor)
        require(
            (int(current_root.st_dev), int(current_root.st_ino))
            == root_identity,
            "solver-state directory identity changed during live validation",
        )
        current_tokens: dict[str, list[int]] = {}
        for entry in entries:
            relative = str(entry["path"])
            metadata = _relative_metadata_at(
                descriptor, relative, missing_ok=False,
            )
            assert metadata is not None
            current_tokens[relative] = list(_stable_token(metadata))
        require(
            current_tokens == target_tokens,
            "installed target changed during production validation",
        )
        return summary
    finally:
        if owns_root_fd:
            os.close(descriptor)


def _open_pipeline_quiescence_lock(
    solver_state: Path,
) -> tuple[Path, int, int]:
    """Acquire the exact lock held by the production pipeline writer."""

    root = _no_symlink_path(solver_state)
    require(
        root.name == "solver-state",
        "migration target is not a production solver-state directory",
    )
    pipeline_root = _no_symlink_path(root.parent)
    pipeline_fd = _open_path_nofollow(pipeline_root, directory=True)
    lock_fd: int | None = None
    try:
        try:
            lock_fd = os.open(
                "pipeline.lock",
                os.O_RDWR | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0),
                dir_fd=pipeline_fd,
            )
        except OSError as exc:
            raise RecoveryError(
                "production pipeline lock is unavailable"
            ) from exc
        opened = os.fstat(lock_fd)
        current = os.stat(
            "pipeline.lock", dir_fd=pipeline_fd, follow_symlinks=False,
        )
        require(
            stat.S_ISREG(opened.st_mode)
            and opened.st_nlink == 1
            and _stable_token(opened) == _stable_token(current),
            "production pipeline lock is unsafe",
        )
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RecoveryError(
                "production pipeline is active; migration requires quiescence"
            ) from exc
        return pipeline_root, pipeline_fd, lock_fd
    except BaseException:
        if lock_fd is not None:
            os.close(lock_fd)
        os.close(pipeline_fd)
        raise


def _require_pipeline_quiescence_lock(
    pipeline_root: Path,
    pipeline_fd: int,
    lock_fd: int,
) -> None:
    current_pipeline_fd = _open_path_nofollow(
        pipeline_root, directory=True,
    )
    try:
        expected_root = os.fstat(pipeline_fd)
        current_root = os.fstat(current_pipeline_fd)
        current_lock = os.stat(
            "pipeline.lock", dir_fd=pipeline_fd, follow_symlinks=False,
        )
        opened_lock = os.fstat(lock_fd)
        require(
            expected_root.st_dev == current_root.st_dev
            and expected_root.st_ino == current_root.st_ino
            and stat.S_ISREG(opened_lock.st_mode)
            and opened_lock.st_nlink == 1
            and _stable_token(opened_lock) == _stable_token(current_lock),
            "production pipeline lock binding changed",
        )
    finally:
        os.close(current_pipeline_fd)


def _release_pipeline_quiescence_lock(
    pipeline_fd: int,
    lock_fd: int,
) -> None:
    fcntl.flock(lock_fd, fcntl.LOCK_UN)
    os.close(lock_fd)
    os.close(pipeline_fd)


def _exact_package_target_tokens(
    root_fd: int,
    entries: Sequence[Mapping[str, Any]],
    *,
    expected_tokens: Mapping[str, Sequence[int]] | None = None,
) -> dict[str, list[int]]:
    observed: dict[str, list[int]] = {}
    for entry in entries:
        relative = str(entry["path"])
        digest, size, token = _stable_sha256_token_relative_at(
            root_fd, relative,
        )
        require(
            (digest, size) == (entry["sha256"], entry["bytes"]),
            f"live package member changed at commit boundary: {relative}",
        )
        if expected_tokens is not None:
            require(
                relative in expected_tokens
                and token == list(expected_tokens[relative]),
                f"live package token changed at commit boundary: {relative}",
            )
        observed[relative] = token
    if expected_tokens is not None:
        require(
            set(observed) == set(expected_tokens),
            "commit target token inventory changed",
        )
    return observed


def _publish_commit_marker_cas(
    root_fd: int,
    marker: Mapping[str, Any],
    entries: Sequence[Mapping[str, Any]],
    expected_tokens: Mapping[str, Sequence[int]],
    *,
    pipeline_root: Path,
    pipeline_fd: int,
    pipeline_lock_fd: int,
) -> None:
    _require_pipeline_quiescence_lock(
        pipeline_root, pipeline_fd, pipeline_lock_fd,
    )
    _exact_package_target_tokens(
        root_fd, entries, expected_tokens=expected_tokens,
    )
    _atomic_json_relative_at(
        root_fd, INSTALL_COMMIT_NAME, marker, replace=False,
    )


def _open_install_lock(root_fd: int) -> int:
    try:
        descriptor = os.open(
            INSTALL_LOCK_NAME,
            os.O_RDWR | os.O_CREAT | getattr(os, "O_CLOEXEC", 0)
            | os.O_NOFOLLOW,
            0o600,
            dir_fd=root_fd,
        )
    except OSError as exc:
        raise RecoveryError("migration install lock is unavailable") from exc
    require(
        stat.S_ISREG(os.fstat(descriptor).st_mode),
        "migration install lock is not regular",
    )
    fcntl.flock(descriptor, fcntl.LOCK_EX)
    return descriptor


def validate_patched_scheduler_install(
    package_root: Path,
    *,
    solver_state: Path,
) -> dict[str, Any]:
    """Validate a COMMITTED receipt and every installed live artifact."""
    package = _no_symlink_path(package_root)
    live_root = _no_symlink_path(solver_state)
    root_fd = _open_path_nofollow(live_root, directory=True)
    marker_path = live_root / INSTALL_COMMIT_NAME
    lock: int | None = None
    journal_path = live_root / INSTALL_JOURNAL_NAME
    try:
        migration, certificate, _, entries = _validated_install_material(
            package, live_root,
        )
        lock = _open_install_lock(root_fd)
        _require_directory_binding(root_fd, live_root)
        marker = _stable_json_relative_at(root_fd, INSTALL_COMMIT_NAME)
        journal = _stable_json_relative_at(root_fd, INSTALL_JOURNAL_NAME)
        _validate_control_seal(
            marker, seal_field="commit_sha256", label="migration commit marker",
        )
        _validate_control_seal(
            journal, seal_field="journal_sha256",
            label="migration install journal",
        )
        live = _installed_live_summary(
            package, live_root, certificate, entries, root_fd=root_fd,
        )
        require(
            marker.get("schema_version") == 1
            and marker.get("gate") == INSTALL_COMMIT_GATE
            and marker.get("state") == "COMMITTED"
            and marker.get("package_root") == str(package)
            and marker.get("solver_state") == str(live_root)
            and marker.get("certificate_sha256") == migration["certificate_sha256"]
            and marker.get("package_sha256") == migration["package_sha256"]
            and marker.get("installed_files") == entries
            and marker.get("live") == live
            and marker.get("validator_source_sha256")
            == _stable_sha256(Path(__file__))[0]
            and isinstance(marker.get("committed_at"), str)
            and marker.get("committed_at")
            and journal.get("gate") == INSTALL_JOURNAL_GATE
            and journal.get("state") == "COMMITTED"
            and journal.get("certificate_sha256")
            == migration["certificate_sha256"]
            and journal.get("package_sha256") == migration["package_sha256"]
            and journal.get("commit_sha256") == marker.get("commit_sha256"),
            "COMMITTED migration receipt or live mapping diverges",
        )
        _require_directory_binding(root_fd, live_root)
        return {
            **marker,
            "marker_path": str(marker_path),
            "journal_path": str(journal_path),
            "production_files_modified": True,
        }
    finally:
        if lock is not None:
            fcntl.flock(lock, fcntl.LOCK_UN)
            os.close(lock)
        os.close(root_fd)


def install_patched_scheduler_migration(
    package_root: Path,
    *,
    solver_state: Path,
) -> dict[str, Any]:
    """Install one validated package transactionally; ledger is written last."""

    package = _no_symlink_path(package_root)
    live_root = _no_symlink_path(solver_state)
    root_fd = _open_path_nofollow(live_root, directory=True)
    migration, certificate, _, entries = _validated_install_material(
        package, live_root,
    )
    pipeline_root, pipeline_fd, pipeline_lock_fd = (
        _open_pipeline_quiescence_lock(live_root)
    )
    try:
        _require_directory_binding(root_fd, live_root)
        lock = _open_install_lock(root_fd)
    except BaseException:
        _release_pipeline_quiescence_lock(pipeline_fd, pipeline_lock_fd)
        os.close(root_fd)
        raise
    marker_path = live_root / INSTALL_COMMIT_NAME
    journal_path = live_root / INSTALL_JOURNAL_NAME
    try:
        journal_exists = _relative_regular_exists_at(
            root_fd, INSTALL_JOURNAL_NAME,
        )
        marker_exists = _relative_regular_exists_at(
            root_fd, INSTALL_COMMIT_NAME,
        )
        if journal_exists:
            journal = _stable_json_relative_at(root_fd, INSTALL_JOURNAL_NAME)
            _validate_control_seal(
                journal, seal_field="journal_sha256",
                label="migration install journal",
            )
            require(
                journal.get("gate") == INSTALL_JOURNAL_GATE
                and journal.get("state") in {"PREPARING", "PREPARED", "COMMITTED"}
                and journal.get("certificate_sha256")
                == migration["certificate_sha256"]
                and journal.get("package_sha256") == migration["package_sha256"]
                and journal.get("package_root") == str(package)
                and journal.get("solver_state") == str(live_root)
                and journal.get("install_files") == entries,
                "existing install journal is for a different or closed transaction",
            )
        else:
            require(not marker_exists, "commit marker exists without install journal")
            backup_root = (
                f"{INSTALL_BACKUP_DIR}/"
                f"{migration['certificate_sha256'][:16]}"
            )
            old_files: list[dict[str, Any]] = []
            for entry in entries:
                relative = str(entry["path"])
                existed = _relative_regular_exists_at(root_fd, relative)
                old_record: dict[str, Any] = {
                    "path": relative, "existed": existed,
                    "backup_path": None, "sha256": None, "bytes": None,
                    "token": None,
                }
                if existed:
                    old_sha256, old_bytes, old_token = _stable_sha256_token_relative_at(
                        root_fd, relative,
                    )
                    old_record.update({
                        "backup_path": f"{backup_root}/{relative}",
                        "sha256": old_sha256, "bytes": old_bytes,
                        "token": old_token,
                    })
                old_files.append(old_record)
            journal_payload = {
                "schema_version": 1, "gate": INSTALL_JOURNAL_GATE,
                "state": "PREPARING", "package_root": str(package),
                "solver_state": str(live_root),
                "certificate_sha256": migration["certificate_sha256"],
                "package_sha256": migration["package_sha256"],
                "validator_source_sha256": _stable_sha256(Path(__file__))[0],
                "backup_root": backup_root, "install_files": entries,
                "old_files": old_files, "prepared_at": utc_now(),
            }
            journal = _sealed_control(
                journal_payload, seal_field="journal_sha256",
            )
            _atomic_json_relative_at(
                root_fd, INSTALL_JOURNAL_NAME, journal, replace=False,
            )

        if marker_exists:
            marker = _stable_json_relative_at(root_fd, INSTALL_COMMIT_NAME)
            _validate_control_seal(
                marker, seal_field="commit_sha256",
                label="migration commit marker",
            )
            live = _installed_live_summary(
                package, live_root, certificate, entries, root_fd=root_fd,
            )
            require(
                journal.get("state") in {"PREPARED", "COMMITTED"}
                and marker.get("gate") == INSTALL_COMMIT_GATE
                and marker.get("state") == "COMMITTED"
                and marker.get("certificate_sha256")
                == migration["certificate_sha256"]
                and marker.get("package_sha256") == migration["package_sha256"]
                and marker.get("installed_files") == entries
                and marker.get("live") == live,
                "durable commit marker differs from installed transaction",
            )
            if journal["state"] == "PREPARED":
                journal_payload = dict(journal)
                journal_payload.pop("journal_sha256", None)
                journal_payload.update({
                    "state": "COMMITTED",
                    "commit_sha256": marker["commit_sha256"],
                    "committed_at": marker["committed_at"],
                })
                journal = _sealed_control(
                    journal_payload, seal_field="journal_sha256",
                )
                _atomic_json_relative_at(
                    root_fd, INSTALL_JOURNAL_NAME, journal, replace=True,
                )
            _require_directory_binding(root_fd, live_root)
            return {
                **marker, "marker_path": str(marker_path),
                "journal_path": str(journal_path),
                "production_files_modified": True,
            }
        old_by_path = {
            str(item["path"]): item for item in journal["old_files"]
        }
        require(
            set(old_by_path) == {str(item["path"]) for item in entries},
            "install journal old-file inventory is incomplete",
        )

        if journal["state"] == "PREPARING":
            for old in journal["old_files"]:
                relative = str(old["path"])
                if old["existed"]:
                    old_sha256, old_bytes, old_token = (
                        _stable_sha256_token_relative_at(root_fd, relative)
                    )
                    require(
                        (old_sha256, old_bytes) == (old["sha256"], old["bytes"])
                        and old_token == old["token"],
                        f"pre-install live file changed: {relative}",
                    )
                    backup_relative = str(old["backup_path"])
                    if _relative_regular_exists_at(root_fd, backup_relative):
                        require(
                            _stable_sha256_relative_at(root_fd, backup_relative)
                            == (old["sha256"], old["bytes"]),
                            f"partial backup differs: {relative}",
                        )
                    else:
                        _atomic_install_relative_at(
                            root_fd, relative, backup_relative,
                            expected_sha256=str(old["sha256"]),
                            expected_bytes=int(old["bytes"]),
                            expected_source_token=old["token"],
                        )
                else:
                    require(
                        not _relative_regular_exists_at(root_fd, relative),
                        f"new live file appeared during PREPARING: {relative}",
                    )
            journal_payload = dict(journal)
            journal_payload.pop("journal_sha256", None)
            journal_payload.update({
                "state": "PREPARED", "backups_completed_at": utc_now(),
            })
            journal = _sealed_control(
                journal_payload, seal_field="journal_sha256",
            )
            _atomic_json_relative_at(
                root_fd, INSTALL_JOURNAL_NAME, journal, replace=True,
            )

        require(journal["state"] == "PREPARED", "install is not PREPARED")
        for entry in entries:
            relative = str(entry["path"])
            source = _confined_package_path(package, relative)
            target = live_root / relative
            if _relative_regular_exists_at(root_fd, relative):
                current_sha256, current_bytes, current_token = (
                    _stable_sha256_token_relative_at(root_fd, relative)
                )
                if (current_sha256, current_bytes) == (
                    entry["sha256"], entry["bytes"],
                ):
                    continue
                old = old_by_path[relative]
                require(
                    old["existed"]
                    and (current_sha256, current_bytes)
                    == (old["sha256"], old["bytes"])
                    and current_token == old["token"],
                    f"live install target changed after PREPARED: {relative}",
                )
                expected_target_token: Sequence[int] | None = current_token
                expected_target_absent = False
            else:
                old = old_by_path[relative]
                require(
                    not old["existed"],
                    f"pre-existing live install target disappeared: {relative}",
                )
                expected_target_token = None
                expected_target_absent = True
            _atomic_install_file(
                source, target,
                root_fd=root_fd, target_relative=relative,
                expected_sha256=str(entry["sha256"]),
                expected_bytes=int(entry["bytes"]),
                expected_source_token=entry.get("source_token"),
                expected_target_token=expected_target_token,
                expected_target_absent=expected_target_absent,
            )
        live = _installed_live_summary(
            package, live_root, certificate, entries, root_fd=root_fd,
        )
        publish_tokens = _exact_package_target_tokens(
            root_fd, entries,
        )
        marker_payload = {
            "schema_version": 1, "gate": INSTALL_COMMIT_GATE,
            "state": "COMMITTED", "package_root": str(package),
            "solver_state": str(live_root),
            "certificate_sha256": migration["certificate_sha256"],
            "package_sha256": migration["package_sha256"],
            "installed_files": entries, "live": live,
            "validator_source_sha256": _stable_sha256(Path(__file__))[0],
            "committed_at": utc_now(),
        }
        marker = _sealed_control(marker_payload, seal_field="commit_sha256")
        _publish_commit_marker_cas(
            root_fd, marker, entries, publish_tokens,
            pipeline_root=pipeline_root,
            pipeline_fd=pipeline_fd,
            pipeline_lock_fd=pipeline_lock_fd,
        )
        journal_payload = dict(journal)
        journal_payload.pop("journal_sha256", None)
        journal_payload.update({
            "state": "COMMITTED", "commit_sha256": marker["commit_sha256"],
            "committed_at": marker["committed_at"],
        })
        journal = _sealed_control(
            journal_payload, seal_field="journal_sha256",
        )
        _atomic_json_relative_at(
            root_fd, INSTALL_JOURNAL_NAME, journal, replace=True,
        )
        _require_directory_binding(root_fd, live_root)
        final_live = _installed_live_summary(
            package, live_root, certificate, entries, root_fd=root_fd,
        )
        _exact_package_target_tokens(
            root_fd, entries, expected_tokens=publish_tokens,
        )
        _require_pipeline_quiescence_lock(
            pipeline_root, pipeline_fd, pipeline_lock_fd,
        )
        require(
            final_live == live
            and _stable_json_relative_at(root_fd, INSTALL_COMMIT_NAME)
            == marker
            and _stable_json_relative_at(root_fd, INSTALL_JOURNAL_NAME)
            == journal,
            "committed baseline changed before quiescence release",
        )
        return {
            **marker, "marker_path": str(marker_path),
            "journal_path": str(journal_path),
            "production_files_modified": True,
        }
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
        os.close(lock)
        _release_pipeline_quiescence_lock(pipeline_fd, pipeline_lock_fd)
        os.close(root_fd)


def rollback_patched_scheduler_migration(
    package_root: Path,
    *,
    solver_state: Path,
) -> dict[str, Any]:
    """Recoverably restore every pre-install target recorded in PREPARED."""

    package = _no_symlink_path(package_root)
    live_root = _no_symlink_path(solver_state)
    migration, certificate, package_manifest, entries = (
        _validated_install_material(package, live_root)
    )
    root_fd = _open_path_nofollow(live_root, directory=True)
    try:
        pipeline_root, pipeline_fd, pipeline_lock_fd = (
            _open_pipeline_quiescence_lock(live_root)
        )
    except BaseException:
        os.close(root_fd)
        raise
    try:
        _require_directory_binding(root_fd, live_root)
        lock = _open_install_lock(root_fd)
    except BaseException:
        _release_pipeline_quiescence_lock(pipeline_fd, pipeline_lock_fd)
        os.close(root_fd)
        raise
    journal_path = live_root / INSTALL_JOURNAL_NAME
    marker_path = live_root / INSTALL_COMMIT_NAME
    try:
        require(
            _relative_regular_exists_at(root_fd, INSTALL_JOURNAL_NAME),
            "install journal is unavailable",
        )
        journal = _stable_json_relative_at(root_fd, INSTALL_JOURNAL_NAME)
        _validate_control_seal(
            journal, seal_field="journal_sha256",
            label="migration install journal",
        )
        require(
            journal.get("gate") == INSTALL_JOURNAL_GATE
            and journal.get("certificate_sha256")
            == certificate.get("certificate_sha256")
            and journal.get("package_sha256") == package_manifest.get("package_sha256")
            and journal.get("install_files") == entries
            and journal.get("state")
            in {"PREPARING", "PREPARED", "COMMITTED", "ROLLED_BACK"},
            "rollback journal does not match package",
        )
        if journal["state"] == "ROLLED_BACK":
            return {
                "status": "ROLLED_BACK",
                "journal_path": str(journal_path),
                "journal_sha256": journal["journal_sha256"],
                "production_files_modified": True,
            }
        backup_root_relative = str(journal["backup_root"])
        _install_relative_parts(backup_root_relative)
        require(
            backup_root_relative == INSTALL_BACKUP_DIR
            or backup_root_relative.startswith(INSTALL_BACKUP_DIR + "/"),
            "rollback backup root is outside the transaction archive",
        )
        backup_root = live_root / backup_root_relative
        old_by_path = {
            str(item["path"]): item for item in journal["old_files"]
        }
        require(
            set(old_by_path) == {str(item["path"]) for item in entries},
            "rollback journal old-file inventory is incomplete",
        )
        _require_pipeline_quiescence_lock(
            pipeline_root, pipeline_fd, pipeline_lock_fd,
        )
        if journal["state"] != "PREPARING":
            for entry in entries:
                relative = str(entry["path"])
                old = old_by_path[relative]
                if old["existed"]:
                    backup_relative = str(old["backup_path"])
                    require(
                        backup_relative.startswith(backup_root_relative + "/"),
                        "rollback backup member escapes backup root",
                    )
                    _atomic_install_relative_at(
                        root_fd, backup_relative, relative,
                        expected_sha256=str(old["sha256"]),
                        expected_bytes=int(old["bytes"]),
                    )
                elif _relative_regular_exists_at(root_fd, relative):
                    orphan_relative = (
                        f"{backup_root_relative}/rollback-new-files/{relative}"
                    )
                    _relative_replace_at(root_fd, relative, orphan_relative)
            if _relative_regular_exists_at(root_fd, INSTALL_COMMIT_NAME):
                archived_marker_relative = (
                    f"{backup_root_relative}/committed-marker.rolled-back.json"
                )
                _relative_replace_at(
                    root_fd, INSTALL_COMMIT_NAME, archived_marker_relative,
                )
        _require_pipeline_quiescence_lock(
            pipeline_root, pipeline_fd, pipeline_lock_fd,
        )
        journal_payload = dict(journal)
        journal_payload.pop("journal_sha256", None)
        journal_payload.update({"state": "ROLLED_BACK", "rolled_back_at": utc_now()})
        journal = _sealed_control(journal_payload, seal_field="journal_sha256")
        _atomic_json_relative_at(
            root_fd, INSTALL_JOURNAL_NAME, journal, replace=True,
        )
        _require_directory_binding(root_fd, live_root)
        _require_pipeline_quiescence_lock(
            pipeline_root, pipeline_fd, pipeline_lock_fd,
        )
        return {
            "status": "ROLLED_BACK",
            "journal_path": str(journal_path),
            "journal_sha256": journal["journal_sha256"],
            "backup_root": str(backup_root),
            "production_files_modified": True,
        }
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
        os.close(lock)
        _release_pipeline_quiescence_lock(pipeline_fd, pipeline_lock_fd)
        os.close(root_fd)

def prepare_output_dir(path: Path) -> Path:
    resolved_parent = path.parent.resolve(strict=True)
    resolved = resolved_parent / path.name
    require(not resolved.exists(), f"output directory already exists: {resolved}")
    resolved.mkdir(mode=0o700)
    return resolved


def _fsync_directory(path: Path) -> None:
    descriptor = _open_path_nofollow(path, directory=True)
    try:
        os.fsync(descriptor)

    finally:
        os.close(descriptor)


def _mkdir_synced(path: Path, *, exist_ok: bool = False) -> None:
    parent = _no_symlink_path(path.parent)
    path.mkdir(mode=0o700, exist_ok=exist_ok)
    _fsync_directory(path)
    _fsync_directory(parent)


def write_json(path: Path, value: Any) -> None:
    payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    parent_descriptor = _open_path_nofollow(path.parent, directory=True)
    descriptor: int | None = None
    try:
        descriptor = os.open(
            path.name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL
            | getattr(os, "O_CLOEXEC", 0) | os.O_NOFOLLOW,
            0o600,
            dir_fd=parent_descriptor,
        )
        view = memoryview(payload)
        while view:
            written = os.write(descriptor, view)
            require(written > 0, f"JSON write stalled: {path}")
            view = view[written:]
        os.fsync(descriptor)
    except OSError as exc:
        raise RecoveryError(f"exclusive JSON write failed: {path}") from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.fsync(parent_descriptor)
        os.close(parent_descriptor)
    require(
        _stable_read(path) == payload,
        f"JSON write changed before verification: {path}",
    )


def run(args: argparse.Namespace) -> dict[str, Any]:
    snapshot_path = args.snapshot.resolve(strict=True)
    archive_path = args.transition_archive.resolve(strict=True)
    pending_path = args.pending_page.resolve(strict=True)
    registry_path = args.registry.resolve(strict=True)
    evaluations_path = args.evaluations.resolve(strict=True)

    require(
        file_sha256(archive_path) == EXPECTED["transition_archive_sha256"],
        "transition archive file SHA-256 diverges",
    )
    require(
        file_sha256(pending_path) == EXPECTED["pending_file_sha256"],
        "pending page file SHA-256 diverges",
    )
    require(
        file_sha256(registry_path) == EXPECTED["registry_file_sha256"],
        "known-code registry file SHA-256 diverges",
    )
    archive = load_json_object(archive_path, "transition archive")
    expected_pending = load_json_object(pending_path, "pending page")
    registry = load_json_object(registry_path, "known-code registry")

    rebound = validate_and_rebind_archive(archive)
    known_digests = registry_digests(registry)
    terminal_replay = replay_terminal_evaluations(evaluations_path)
    rows = read_and_verify_snapshot(snapshot_path, known_digests=known_digests)
    completed, pending, page_reports = replay_new_pages(rebound, rows)

    require(
        len(completed.ack_chain) == EXPECTED["completed_pages"]
        and completed.cursor == EXPECTED["cursor"]
        and len(completed.committed_digests) == EXPECTED["committed"]
        and completed.last_ack_sha256 == EXPECTED["last_ack_sha256"],
        "reconstructed completed ACK prefix does not match sealed anchors",
    )
    require(
        pending == expected_pending
        and pending.get("page_sequence") == EXPECTED["pending_sequence"]
        and pending.get("start_index") == EXPECTED["pending_start"]
        and pending.get("next_index") == EXPECTED["pending_next"]
        and len(pending.get("selected_digests", []))
        == EXPECTED["pending_selected"]
        and pending.get("page_sha256") == EXPECTED["pending_page_sha256"],
        "reconstructed pending page does not match sealed sequence 44",
    )

    ledger = seal_ledger_core(completed, pending)
    report = {
        "schema_version": 1,
        "gate": "qldpc-stage2-offline-ledger-core-recovery-v1",
        "status": "EXACT_CORE_REPLAY_VERIFIED",
        "inputs": {
            "snapshot": {
                "path": str(snapshot_path),
                "bytes": EXPECTED["snapshot_bytes"],
                "rows": EXPECTED["snapshot_rows"],
                "sha256": EXPECTED["snapshot_sha256"],
            },
            "transition_archive": {
                "path": str(archive_path),
                "sha256": EXPECTED["transition_archive_sha256"],
            },
            "pending_page": {
                "path": str(pending_path),
                "file_sha256": EXPECTED["pending_file_sha256"],
                "page_sha256": EXPECTED["pending_page_sha256"],
            },
            "known_code_registry": {
                "path": str(registry_path),
                "file_sha256": EXPECTED["registry_file_sha256"],
                "canonical_digests": len(known_digests),
            },
            "terminal_witness_replay": {
                "source_path": str(evaluations_path),
                "source_sha256": EXPECTED["evaluations_sha256"],
                "report_sha256": terminal_replay["report_sha256"],
                "rows": terminal_replay["rows"],
                "valid_witnesses": terminal_replay["valid_witnesses"],
            },
        },
        "replay": {
            "binding_sha256": EXPECTED["final_binding_sha256"],
            "snapshot_identity_sha256": EXPECTED[
                "snapshot_identity_sha256"
            ],
            "completed_pages": len(completed.ack_chain),
            "cursor": completed.cursor,
            "committed_digests": len(completed.committed_digests),
            "last_ack_sha256": completed.last_ack_sha256,
            "pending_page_sha256": pending["page_sha256"],
            "pending_next_index": pending["next_index"],
            "pages_31_through_44": page_reports,
            "ledger_core_progress_sha256": ledger["progress_sha256"],
        },
        "not_claimed": {
            "original_ledger_file_sha256": EXPECTED[
                "original_ledger_file_sha256"
            ],
            "original_ledger_progress_sha256": EXPECTED[
                "original_ledger_progress_sha256"
            ],
            "reason": (
                "The original outer ledger bytes also contained the third "
                "adaptive-page transition timestamp/evidence and the final "
                "last_acknowledged_at timestamp. Those wall-clock fields are "
                "not derivable from ACK/page hashes, so this output proves "
                "the complete selection ACK core but does not impersonate "
                "the lost original file/progress seal."
            ),
            "missing_original_fields": [
                "adaptive_page_scheduler.transitions[2].clean_evidence.verified_at",
                "adaptive_page_scheduler.transitions[2].transitioned_at",
                "adaptive_page_scheduler.transitions[2].entry_sha256",
                "adaptive_page_scheduler.state_sha256",
                "last_acknowledged_at",
            ],
        },
    }
    report_unsigned = dict(report)
    report["report_sha256"] = canonical_sha256(report_unsigned)

    output_dir = prepare_output_dir(args.output_dir)
    write_json(output_dir / "selection-ledger-core.json", ledger)
    write_json(output_dir / "recovery-report.json", report)
    write_json(output_dir / "pending-page-seq44.json", pending)
    write_json(
        output_dir / "terminal-witness-replay.json",
        terminal_replay,
    )
    result = {**report, "output_dir": str(output_dir)}
    if args.migration_output_dir is not None:
        require(
            args.offsets is not None
            and args.binding_route_manifest is not None
            and args.known_answer_artifact is not None
            and args.same_filesystem_as is not None,
            "migration output requires offsets, binding route, known answer, and same-filesystem target",
        )
        result["scheduler_migration"] = build_patched_scheduler_migration(
            snapshot_path=snapshot_path,
            offsets_path=args.offsets,
            core_ledger_path=output_dir / "selection-ledger-core.json",
            core_report_path=output_dir / "recovery-report.json",
            terminal_report_path=output_dir / "terminal-witness-replay.json",
            route_manifest_path=args.binding_route_manifest,
            registry_path=registry_path,
            known_answer_path=args.known_answer_artifact,
            output_dir=args.migration_output_dir,
            same_filesystem_as=args.same_filesystem_as,
        )
    return result


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--transition-archive", type=Path, required=True)
    parser.add_argument("--pending-page", type=Path, required=True)
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--evaluations", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--offsets", type=Path)
    parser.add_argument("--binding-route-manifest", type=Path)
    parser.add_argument("--known-answer-artifact", type=Path)
    parser.add_argument("--same-filesystem-as", type=Path)
    parser.add_argument(
        "--migration-output-dir",
        type=Path,
        help=(
            "also build a validated patched-identity scheduler package in "
            "this new same-filesystem staging directory"
        ),
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        report = run(args)
    except (OSError, RecoveryError) as exc:
        print(f"recovery failed: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
