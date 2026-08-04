"""Tests for the versioned CSS/non-CSS known-code registry."""

import json

from evaluation.bb_code import build_bb_code
from evaluation.pbb_code import build_pbb_code
import evaluation.registry as registry_module
from evaluation.registry import (
    canonical_digest,
    canonical_json_sha256,
    check_code_novelty,
    load_registry,
)


def _write_registry(path, entries):
    value = {
        "schema_version": 1,
        "registry_version": "test-registry",
        "summary": {
            "raw_entries": len(entries),
            "deduplicated_entries": len(entries),
            "css": sum(row["code_type"] == "css" for row in entries),
            "noncss": sum(row["code_type"] == "noncss" for row in entries),
        },
        "entries": entries,
    }
    value["registry_sha256"] = canonical_json_sha256(
        value,
        omit="registry_sha256",
    )
    path.write_text(json.dumps(value))
    load_registry.cache_clear()
    return path


def test_registry_integrity_and_coverage():
    registry = load_registry()
    assert registry["summary"]["css"] >= 30
    assert registry["summary"]["noncss"] >= 300
    assert len(registry["entries"]) == 1150
    assert all(isinstance(row.get("construction"), dict) for row in registry["entries"])


def test_known_gross_code_is_in_expanded_registry():
    code = build_bb_code(
        12, 6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
    )
    audit = check_code_novelty(code, code_type="css")
    assert audit["status"] == "COMPLETE"
    assert audit["novel"] is False
    assert audit["matched_entries"]
    assert audit["replay_policy"]["digest_terminal"] is False
    replay = audit["matched_entries"][0]["replay"]
    assert replay["qubit_permutation_valid"] is True
    assert replay["x_row_permutation_valid"] is True
    assert replay["z_row_permutation_valid"] is True
    assert replay["matrix_x_replayed"] is True
    assert replay["matrix_z_replayed"] is True
    assert replay["verified"] is True


def test_known_pbb_catalog_code_is_in_expanded_registry():
    registry = load_registry()
    entry = next(row for row in registry["entries"] if row["code_type"] == "noncss")
    construction = entry["construction"]
    code = build_pbb_code(
        construction["ell"], construction["m"],
        construction["A_terms"], construction["B_terms"],
        construction["C_terms"], construction["D_terms"],
    )
    audit = check_code_novelty(code, code_type="noncss")
    assert audit["status"] == "COMPLETE"
    assert audit["novel"] is False
    assert audit["matched_entries"]
    replay = audit["matched_entries"][0]["replay"]
    assert replay["shared_row_permutation"] is True
    assert replay["matrix_x_replayed"] is True
    assert replay["matrix_z_replayed"] is True
    assert replay["verified"] is True


def test_novel_result_records_nonterminal_digest_replay_policy(tmp_path):
    code = build_bb_code(
        6,
        6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
    )
    path = _write_registry(tmp_path / "registry.json", [])

    audit = check_code_novelty(code, code_type="css", registry_path=path)

    assert audit["status"] == "COMPLETE"
    assert audit["checked"] is True
    assert audit["novel"] is True
    assert audit["matched_entries"] == []
    assert audit["replay_policy"] == {
        "schema_version": 1,
        "policy": "explicit-construction-matrix-replay",
        "digest_terminal": False,
        "index_fields": [
            "code_type",
            "n",
            "k",
            "canonical_digest",
        ],
        "entry_construction_required": True,
        "explicit_matrix_replay_required": True,
        "indexed_entries": 0,
        "verified_entries": 0,
        "complete": True,
    }


def test_digest_hit_with_inconsistent_construction_is_not_known(tmp_path):
    candidate = build_bb_code(
        12,
        6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
    )
    path = _write_registry(tmp_path / "registry.json", [{
        "id": "poisoned-index",
        "family": "test",
        "code_type": "css",
        "n": int(candidate.num_qudits),
        "k": int(candidate.dimension),
        "canonical_digest": canonical_digest(candidate),
        "construction": {
            "ell": 6,
            "m": 6,
            "A_terms": [[3, 0], [0, 1], [0, 2]],
            "B_terms": [[0, 3], [1, 0], [2, 0]],
        },
        "provenance": [{"kind": "test"}],
    }])

    audit = check_code_novelty(
        candidate,
        code_type="css",
        registry_path=path,
    )

    assert audit["status"] == "EVIDENCE_CONTRADICTION"
    assert audit["checked"] is False
    assert audit["novel"] is None
    assert audit["matched_entries"] == []
    assert audit["failure"]["terminal_candidate_rejection"] is False
    assert audit["failure"]["code"] == "REGISTRY_ENTRY_REPLAY_CONTRADICTION"


def test_digest_hit_requires_successful_explicit_matrix_replay(
    tmp_path,
    monkeypatch,
):
    registry = load_registry()
    entry = next(row for row in registry["entries"] if row["code_type"] == "css")
    code = build_bb_code(**entry["construction"])
    path = _write_registry(tmp_path / "registry.json", [entry])
    monkeypatch.setattr(
        registry_module,
        "replay_css_matrix_equivalence",
        lambda *_args: {"verified": False},
    )

    audit = check_code_novelty(code, code_type="css", registry_path=path)

    assert audit["status"] == "EVIDENCE_CONTRADICTION"
    assert audit["checked"] is False
    assert audit["novel"] is None
    assert audit["matched_entries"] == []
    assert audit["failure"]["terminal_candidate_rejection"] is False


def test_unavailable_registry_is_retryable_not_known(tmp_path):
    code = build_bb_code(
        6,
        6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
    )

    audit = check_code_novelty(
        code,
        code_type="css",
        registry_path=tmp_path / "missing.json",
    )

    assert audit["status"] == "INCOMPLETE"
    assert audit["checked"] is False
    assert audit["novel"] is None
    assert audit["failure"]["retryable"] is True
    assert audit["failure"]["terminal_candidate_rejection"] is False
