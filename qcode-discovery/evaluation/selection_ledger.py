"""Fail-closed Stage 2 ranked-pool pagination evidence.

The proof CLI owns pending-page creation while Humanize owns acknowledgement.
Both sides use this module so cursor movement, committed digests, and empty
diagnostic pages are governed by one cryptographic lifecycle contract.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping


SELECTION_LEDGER_SCHEMA_VERSION = 2
SELECTION_LEDGER_GATE = "qldpc-stage2-selection-ledger"
SCAN_EVIDENCE_SCHEMA_VERSION = 1
SCAN_EVIDENCE_GATE = "qldpc-stage2-ranked-scan"
ACK_GATE = "qldpc-stage2-selection-ack"
ACK_DISPOSITIONS = frozenset({"COMPLETED", "DEFERRED"})


def canonical_sha256(value: Any) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def snapshot_identity_sha256(identity: Mapping[str, Any]) -> str:
    return canonical_sha256(dict(identity))


def make_scan_evidence(
    *,
    snapshot_identity_sha256_value: str,
    start_index: int,
    next_index: int,
    snapshot_rows: int,
    eligible_rows: int,
    selection_exhausted: bool,
) -> dict[str, Any]:
    payload = {
        "schema_version": SCAN_EVIDENCE_SCHEMA_VERSION,
        "gate": SCAN_EVIDENCE_GATE,
        "snapshot_identity_sha256": snapshot_identity_sha256_value,
        "start_index": start_index,
        "next_index": next_index,
        "snapshot_rows": snapshot_rows,
        "eligible_rows": eligible_rows,
        "selection_exhausted": selection_exhausted,
    }
    return {**payload, "scan_sha256": canonical_sha256(payload)}


def validate_scan_evidence(
    evidence: Mapping[str, Any],
    *,
    snapshot_identity_sha256_value: str,
    snapshot_rows: int,
    eligible_rows: int,
    start_index: int,
    next_index: int,
    selection_exhausted: bool | None = None,
) -> dict[str, Any]:
    normalized = dict(evidence)
    unsigned = dict(normalized)
    scan_sha256 = unsigned.pop("scan_sha256", None)
    evidence_start = normalized.get("start_index")
    evidence_next = normalized.get("next_index")
    evidence_rows = normalized.get("snapshot_rows")
    evidence_eligible = normalized.get("eligible_rows")
    exhausted = normalized.get("selection_exhausted")
    if (
        normalized.get("schema_version") != SCAN_EVIDENCE_SCHEMA_VERSION
        or normalized.get("gate") != SCAN_EVIDENCE_GATE
        or normalized.get("snapshot_identity_sha256")
        != snapshot_identity_sha256_value
        or isinstance(evidence_start, bool)
        or not isinstance(evidence_start, int)
        or evidence_start != start_index
        or isinstance(evidence_next, bool)
        or not isinstance(evidence_next, int)
        or evidence_next != next_index
        or isinstance(evidence_eligible, bool)
        or not isinstance(evidence_eligible, int)
        or evidence_eligible != eligible_rows
        or isinstance(evidence_rows, bool)
        or not isinstance(evidence_rows, int)
        or evidence_rows != snapshot_rows
        or not 0 <= evidence_eligible <= evidence_rows
        or not 0 <= evidence_start <= evidence_next <= evidence_eligible
        or not isinstance(exhausted, bool)
        or exhausted != (evidence_next == evidence_eligible)
        or (
            selection_exhausted is not None
            and exhausted is not selection_exhausted
        )
        or not is_sha256(scan_sha256)
        or scan_sha256 != canonical_sha256(unsigned)
    ):
        raise ValueError("selection page scan evidence is malformed")
    return normalized


def make_selection_page(
    *,
    binding_sha256: str,
    snapshot_identity_sha256_value: str,
    page_sequence: int,
    previous_ack_sha256: str,
    start_index: int,
    next_index: int,
    selected_digests: list[str],
    scan_evidence: Mapping[str, Any],
) -> dict[str, Any]:
    payload = {
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": snapshot_identity_sha256_value,
        "page_sequence": page_sequence,
        "previous_ack_sha256": previous_ack_sha256,
        "start_index": start_index,
        "next_index": next_index,
        "selected_digests": list(selected_digests),
        "scan_evidence": dict(scan_evidence),
    }
    return {**payload, "page_sha256": canonical_sha256(payload)}


def validate_selection_page(
    page: Mapping[str, Any],
    *,
    binding_sha256: str,
    snapshot_identity_sha256_value: str,
    snapshot_rows: int,
    eligible_rows: int,
    page_sequence: int,
    previous_ack_sha256: str,
    cursor: int,
    committed_digests: set[str],
    selection_exhausted: bool | None = None,
) -> dict[str, Any]:
    normalized = dict(page)
    unsigned = dict(normalized)
    page_sha256 = unsigned.pop("page_sha256", None)
    start_index = normalized.get("start_index")
    next_index = normalized.get("next_index")
    selected = normalized.get("selected_digests")
    evidence = normalized.get("scan_evidence")
    if (
        normalized.get("binding_sha256") != binding_sha256
        or normalized.get("snapshot_identity_sha256")
        != snapshot_identity_sha256_value
        or isinstance(normalized.get("page_sequence"), bool)
        or normalized.get("page_sequence") != page_sequence
        or normalized.get("previous_ack_sha256") != previous_ack_sha256
        or isinstance(start_index, bool)
        or not isinstance(start_index, int)
        or start_index != cursor
        or isinstance(next_index, bool)
        or not isinstance(next_index, int)
        or not start_index <= next_index <= eligible_rows
        or not isinstance(selected, list)
        or any(not isinstance(item, str) or not item for item in selected)
        or len(set(selected)) != len(selected)
        or committed_digests.intersection(selected)
        or not isinstance(evidence, Mapping)
        or not is_sha256(page_sha256)
        or page_sha256 != canonical_sha256(unsigned)
    ):
        raise ValueError("selection page is malformed")
    validate_scan_evidence(
        evidence,
        snapshot_identity_sha256_value=snapshot_identity_sha256_value,
        snapshot_rows=snapshot_rows,
        eligible_rows=eligible_rows,
        start_index=start_index,
        next_index=next_index,
        selection_exhausted=selection_exhausted,
    )
    terminal_root = bool(
        eligible_rows == 0
        and cursor == 0
        and start_index == 0
        and next_index == 0
        and page_sequence == 0
        and not committed_digests
        and evidence.get("selection_exhausted") is True
    )
    # A page may contain no solver candidates only after a non-empty
    # diagnostic tail, or at the unique root of an empty eligible prefix.
    if not selected and not (
        (
            next_index > start_index
            and evidence.get("selection_exhausted") is True
        )
        or terminal_root
    ):
        raise ValueError("empty selection page lacks terminal scan progress")
    if next_index <= start_index and not terminal_root:
        raise ValueError("selection page made no ranked-pool progress")
    return normalized


def _genesis_sha256(
    *,
    binding_sha256: str,
    snapshot_identity_sha256_value: str,
    snapshot_rows: int,
    eligible_rows: int,
    generation: int,
) -> str:
    return canonical_sha256({
        "gate": "qldpc-stage2-selection-genesis",
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": snapshot_identity_sha256_value,
        "snapshot_rows": snapshot_rows,
        "eligible_rows": eligible_rows,
        "generation": generation,
    })


def seal_selection_ledger(ledger: Mapping[str, Any]) -> dict[str, Any]:
    sealed = dict(ledger)
    sealed.pop("progress_sha256", None)
    sealed["progress_sha256"] = canonical_sha256(sealed)
    return sealed


def new_selection_ledger(
    *,
    binding_sha256: str,
    snapshot_identity_sha256_value: str,
    snapshot_rows: int,
    eligible_rows: int,
    generation: int = 0,
    generation_history: list[Mapping[str, Any]] | None = None,
    proof_config_sha256: str | None = None,
) -> dict[str, Any]:
    if (
        not is_sha256(binding_sha256)
        or not is_sha256(snapshot_identity_sha256_value)
        or isinstance(snapshot_rows, bool)
        or not isinstance(snapshot_rows, int)
        or isinstance(eligible_rows, bool)
        or not isinstance(eligible_rows, int)
        or not 0 <= eligible_rows <= snapshot_rows
        or isinstance(generation, bool)
        or not isinstance(generation, int)
        or generation < 0
    ):
        raise ValueError("selection ledger identity is malformed")
    genesis = _genesis_sha256(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=snapshot_identity_sha256_value,
        snapshot_rows=snapshot_rows,
        eligible_rows=eligible_rows,
        generation=generation,
    )
    ledger: dict[str, Any] = {
        "schema_version": SELECTION_LEDGER_SCHEMA_VERSION,
        "gate": SELECTION_LEDGER_GATE,
        "binding_sha256": binding_sha256,
        "snapshot_identity_sha256": snapshot_identity_sha256_value,
        "snapshot_rows": snapshot_rows,
        "eligible_rows": eligible_rows,
        "generation": generation,
        "generation_history": [
            dict(item) for item in (generation_history or [])
        ],
        "cursor": 0,
        "committed_digests": [],
        "completed_pages": 0,
        "ack_chain": [],
        "genesis_sha256": genesis,
        "last_ack_sha256": genesis,
        "pending": None,
        "deferred_pages": [],
    }
    if proof_config_sha256 is not None:
        ledger["proof_config_sha256"] = proof_config_sha256
    return seal_selection_ledger(ledger)


def validate_selection_ledger(
    ledger: Mapping[str, Any],
    *,
    binding_sha256: str,
    snapshot_identity_sha256_value: str,
    snapshot_rows: int,
    eligible_rows: int,
) -> dict[str, Any]:
    value = dict(ledger)
    unsigned_ledger = dict(value)
    progress_sha256 = unsigned_ledger.pop("progress_sha256", None)
    cursor = value.get("cursor")
    committed = value.get("committed_digests")
    completed_pages = value.get("completed_pages")
    ack_chain = value.get("ack_chain")
    generation = value.get("generation")
    history = value.get("generation_history")
    deferred = value.get("deferred_pages")
    if (
        value.get("schema_version") != SELECTION_LEDGER_SCHEMA_VERSION
        or value.get("gate") != SELECTION_LEDGER_GATE
        or value.get("binding_sha256") != binding_sha256
        or value.get("snapshot_identity_sha256")
        != snapshot_identity_sha256_value
        or value.get("snapshot_rows") != snapshot_rows
        or value.get("eligible_rows") != eligible_rows
        or not is_sha256(progress_sha256)
        or progress_sha256 != canonical_sha256(unsigned_ledger)
        or isinstance(cursor, bool)
        or not isinstance(cursor, int)
        or not 0 <= cursor <= eligible_rows
        or not isinstance(committed, list)
        or any(not isinstance(item, str) or not item for item in committed)
        or len(set(committed)) != len(committed)
        or isinstance(completed_pages, bool)
        or not isinstance(completed_pages, int)
        or completed_pages < 0
        or not isinstance(ack_chain, list)
        or isinstance(generation, bool)
        or not isinstance(generation, int)
        or generation < 0
        or not isinstance(history, list)
        or any(not isinstance(item, Mapping) for item in history)
        or not isinstance(deferred, list)
        or any(not isinstance(item, Mapping) for item in deferred)
    ):
        raise ValueError("selection ledger progress seal is invalid")

    expected_ack = _genesis_sha256(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=snapshot_identity_sha256_value,
        snapshot_rows=snapshot_rows,
        eligible_rows=eligible_rows,
        generation=generation,
    )
    if value.get("genesis_sha256") != expected_ack:
        raise ValueError("selection ledger genesis is invalid")
    replay_cursor = 0
    replay_committed: list[str] = []
    replay_seen: set[str] = set()
    deferred_ack_digests: list[str] = []
    for sequence, raw_ack in enumerate(ack_chain):
        if not isinstance(raw_ack, Mapping):
            raise ValueError("selection acknowledgement is malformed")
        ack = dict(raw_ack)
        unsigned_ack = dict(ack)
        ack_sha256 = unsigned_ack.pop("ack_sha256", None)
        page = ack.get("page")
        disposition = ack.get("disposition")
        deferred_entry_sha256 = ack.get("deferred_entry_sha256")
        if (
            ack.get("gate") != ACK_GATE
            or ack.get("sequence") != sequence
            or ack.get("previous_ack_sha256") != expected_ack
            or disposition not in ACK_DISPOSITIONS
            or (
                disposition == "DEFERRED"
                and not is_sha256(deferred_entry_sha256)
            )
            or (
                disposition == "COMPLETED"
                and deferred_entry_sha256 is not None
            )
            or not isinstance(page, Mapping)
            or ack.get("page_sha256") != page.get("page_sha256")
            or not is_sha256(ack_sha256)
            or ack_sha256 != canonical_sha256(unsigned_ack)
        ):
            raise ValueError("selection acknowledgement chain is invalid")
        normalized_page = validate_selection_page(
            page,
            binding_sha256=binding_sha256,
            snapshot_identity_sha256_value=snapshot_identity_sha256_value,
            snapshot_rows=snapshot_rows,
            eligible_rows=eligible_rows,
            page_sequence=sequence,
            previous_ack_sha256=expected_ack,
            cursor=replay_cursor,
            committed_digests=replay_seen,
        )
        selected = list(normalized_page["selected_digests"])
        replay_committed.extend(selected)
        replay_seen.update(selected)
        replay_cursor = int(normalized_page["next_index"])
        expected_ack = str(ack_sha256)
        if disposition == "DEFERRED":
            deferred_ack_digests.append(str(deferred_entry_sha256))
    if (
        completed_pages != len(ack_chain)
        or cursor != replay_cursor
        or committed != replay_committed
        or value.get("last_ack_sha256") != expected_ack
    ):
        raise ValueError("selection ledger replay does not match progress")
    deferred_entry_digests = [
        entry.get("entry_sha256")
        for entry in deferred
    ]
    deferred_entries_sealed = True
    for entry in deferred:
        unsigned_entry = dict(entry)
        entry_sha256 = unsigned_entry.pop("entry_sha256", None)
        if (
            not is_sha256(entry_sha256)
            or canonical_sha256(unsigned_entry) != entry_sha256
        ):
            deferred_entries_sealed = False
            break
    if (
        not deferred_entries_sealed
        or deferred_entry_digests != deferred_ack_digests
    ):
        raise ValueError(
            "selection ledger deferred acknowledgements do not match entries",
        )

    pending = value.get("pending")
    if pending is not None:
        if not isinstance(pending, Mapping):
            raise ValueError("selection ledger pending page is malformed")
        validate_selection_page(
            pending,
            binding_sha256=binding_sha256,
            snapshot_identity_sha256_value=snapshot_identity_sha256_value,
            snapshot_rows=snapshot_rows,
            eligible_rows=eligible_rows,
            page_sequence=completed_pages,
            previous_ack_sha256=expected_ack,
            cursor=cursor,
            committed_digests=set(committed),
        )
    return value


def install_pending_page(
    ledger: Mapping[str, Any],
    page: Mapping[str, Any],
) -> dict[str, Any]:
    value = validate_selection_ledger(
        ledger,
        binding_sha256=str(ledger.get("binding_sha256")),
        snapshot_identity_sha256_value=str(
            ledger.get("snapshot_identity_sha256")
        ),
        snapshot_rows=ledger.get("snapshot_rows"),  # type: ignore[arg-type]
        eligible_rows=ledger.get("eligible_rows"),  # type: ignore[arg-type]
    )
    validate_selection_page(
        page,
        binding_sha256=value["binding_sha256"],
        snapshot_identity_sha256_value=value[
            "snapshot_identity_sha256"
        ],
        snapshot_rows=value["snapshot_rows"],
        eligible_rows=value["eligible_rows"],
        page_sequence=value["completed_pages"],
        previous_ack_sha256=value["last_ack_sha256"],
        cursor=value["cursor"],
        committed_digests=set(value["committed_digests"]),
    )
    pending = value.get("pending")
    if pending is not None and dict(pending) != dict(page):
        raise ValueError("selection ledger owns a different pending page")
    value["pending"] = dict(page)
    return seal_selection_ledger(value)


def acknowledge_selection_page(
    ledger: Mapping[str, Any],
    page: Mapping[str, Any],
    *,
    disposition: str,
    deferred_entry: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    value = validate_selection_ledger(
        ledger,
        binding_sha256=str(ledger.get("binding_sha256")),
        snapshot_identity_sha256_value=str(
            ledger.get("snapshot_identity_sha256")
        ),
        snapshot_rows=ledger.get("snapshot_rows"),  # type: ignore[arg-type]
        eligible_rows=ledger.get("eligible_rows"),  # type: ignore[arg-type]
    )
    deferred_entry_sha256 = (
        deferred_entry.get("entry_sha256")
        if isinstance(deferred_entry, Mapping)
        else None
    )
    deferred_entry_replays = deferred_entry is None
    if isinstance(deferred_entry, Mapping):
        unsigned_deferred_entry = dict(deferred_entry)
        unsigned_deferred_entry.pop("entry_sha256", None)
        deferred_entry_replays = bool(
            is_sha256(deferred_entry_sha256)
            and canonical_sha256(unsigned_deferred_entry)
            == deferred_entry_sha256
        )
    if (
        disposition not in ACK_DISPOSITIONS
        or value.get("pending") != dict(page)
        or (
            disposition == "DEFERRED"
            and not deferred_entry_replays
        )
        or (
            disposition == "COMPLETED"
            and deferred_entry is not None
        )
    ):
        raise ValueError("selection acknowledgement does not match pending")
    normalized_page = validate_selection_page(
        page,
        binding_sha256=value["binding_sha256"],
        snapshot_identity_sha256_value=value[
            "snapshot_identity_sha256"
        ],
        snapshot_rows=value["snapshot_rows"],
        eligible_rows=value["eligible_rows"],
        page_sequence=value["completed_pages"],
        previous_ack_sha256=value["last_ack_sha256"],
        cursor=value["cursor"],
        committed_digests=set(value["committed_digests"]),
    )
    if value["snapshot_rows"] == 0:
        raise ValueError("zero-pool root page remains terminal and pending")
    sequence = value["completed_pages"]
    ack_payload = {
        "gate": ACK_GATE,
        "sequence": sequence,
        "previous_ack_sha256": value["last_ack_sha256"],
        "disposition": disposition,
        "deferred_entry_sha256": deferred_entry_sha256,
        "page_sha256": normalized_page["page_sha256"],
        "page": normalized_page,
    }
    ack = {
        **ack_payload,
        "ack_sha256": canonical_sha256(ack_payload),
    }
    value["cursor"] = normalized_page["next_index"]
    value["committed_digests"] = [
        *value["committed_digests"],
        *normalized_page["selected_digests"],
    ]
    value["completed_pages"] = sequence + 1
    value["ack_chain"] = [*value["ack_chain"], ack]
    value["last_ack_sha256"] = ack["ack_sha256"]
    value["pending"] = None
    if deferred_entry is not None:
        value["deferred_pages"] = [
            *value["deferred_pages"],
            dict(deferred_entry),
        ]
    return seal_selection_ledger(value)
