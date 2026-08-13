from __future__ import annotations

from pathlib import Path
from typing import Any

import numpy as np
import pytest

from evaluation.stratified_ladder_diagnostic import (
    decide,
    run_candidate_ladder,
    stratified_candidate_order,
)


def _row(index: int, *, volume: int, mechanism: str, twist: int) -> dict[str, Any]:
    return {
        "ell": 1,
        "m": volume,
        "A_terms": [[0, 0], [0, 1], [0, (index + 2) % volume]],
        "B_terms": [[0, 0], [0, 2], [0, (index + 3) % volume]],
        "n": 2 * volume,
        "k": 2,
        "required_distance": 4 + volume,
        "distance_lower_bound": 5,
        "relation_type": mechanism,
        "geometry": {"schema_version": 1, "family": "twisted_torus", "twist": twist},
        "triage_identity": {"canonical_digest": f"triage-{index:04d}"},
        "structural_novelty": {"canonical_digest": f"struct-{index:04d}"},
    }


def test_stratified_order_covers_rare_volumes_and_mechanisms() -> None:
    rows = [
        *[_row(i, volume=105, mechanism="shared", twist=i) for i in range(80)],
        _row(100, volume=127, mechanism="rare-a", twist=25),
        _row(101, volume=132, mechanism="rare-b", twist=7),
        _row(102, volume=170, mechanism="rare-c", twist=27),
    ]
    selected = stratified_candidate_order(rows, 48)
    assert len(selected) == 48
    assert {row["m"] for row in selected} == {105, 127, 132, 170}
    assert {row["relation_type"] for row in selected} >= {
        "shared",
        "rare-a",
        "rare-b",
        "rare-c",
    }
    assert [row["triage_identity"] for row in selected] == [
        row["triage_identity"] for row in stratified_candidate_order(rows, 48)
    ]
    assert {127, 132, 170}.issubset({row["m"] for row in selected[:6]})


def _result(
    index: int,
    *,
    rejected: bool,
    survived: bool,
    unknown: bool = False,
    lower_bound: int = 5,
    gap: int = 8,
) -> dict[str, Any]:
    return {
        "candidate_key": f"candidate-{index}",
        "rejected_by_w8": rejected,
        "survived_w8": survived,
        "unknown_fail_open": unknown,
        "final_distance_lower_bound": lower_bound,
        "target_gap": gap,
    }


def test_decision_changes_ansatz_after_concentrated_low_weight_rejections() -> None:
    results = [
        *[_result(i, rejected=True, survived=False) for i in range(44)],
        *[_result(i, rejected=False, survived=True) for i in range(44, 48)],
    ]
    decision = decide(results)
    assert decision["rejected_by_w8_fraction"] == 44 / 48
    assert decision["action"] == "change_ansatz_within_generalized_toric_family"
    assert decision["whole_family_abandonment_authorized"] is False


def test_decision_counts_unknown_as_fail_open_survivor() -> None:
    results = [
        *[_result(i, rejected=True, survived=False) for i in range(38)],
        *[
            _result(i, rejected=False, survived=True, unknown=True)
            for i in range(38, 48)
        ],
    ]
    decision = decide(results)
    assert decision["unknown_fail_open"] == 10
    assert decision["survived_w8_fraction"] >= 0.2
    assert decision["action"] == (
        "retain_generalized_toric_family_and_targeted_deep_proof"
    )


def test_decision_retains_family_on_meaningful_lower_bound() -> None:
    results = [_result(i, rejected=True, survived=False) for i in range(48)]
    results[0] = _result(
        0,
        rejected=True,
        survived=False,
        lower_bound=9,
        gap=4,
    )
    decision = decide(results)
    assert decision["meaningful_lb_ge_9"] == ["candidate-0"]
    assert decision["action"] == (
        "retain_generalized_toric_family_and_targeted_deep_proof"
    )


def test_exact_twenty_percent_overlap_resolves_toward_retention() -> None:
    results = [
        *[_result(i, rejected=True, survived=False) for i in range(40)],
        *[_result(i, rejected=False, survived=True) for i in range(40, 50)],
    ]
    decision = decide(results)
    assert decision["rejected_by_w8_fraction"] == 0.8
    assert decision["survived_w8_fraction"] == 0.2
    assert decision["action"] == (
        "retain_generalized_toric_family_and_targeted_deep_proof"
    )


def test_run_candidate_attempts_both_sectors_and_stops_on_unknown(monkeypatch) -> None:
    import evaluation.stratified_ladder_diagnostic as module

    class FakeCode:
        num_qudits = 12
        dimension = 2

    monkeypatch.setattr(module, "build_css_code_from_claim", lambda _claim: FakeCode())
    matrices = tuple(np.zeros((2, 12), dtype=np.uint8) for _ in range(4))
    monkeypatch.setattr(module, "get_code_matrices", lambda _code: matrices)
    monkeypatch.setattr(module, "verify_css_low_weight_oracle", lambda *_a, **_k: [])
    monkeypatch.setattr(module, "authoritative_candidate_digest", lambda _claim: "digest")
    monkeypatch.setattr(module, "verify_low_weight_sector_evidence", lambda *_a, **_k: [])

    calls: list[tuple[int, str]] = []

    def fake_sector(*_args, max_weight: int, sector: str, **_kwargs):
        calls.append((max_weight, sector))
        return {
            "outcome": "UNSAT" if sector == "X" else "UNKNOWN",
            "witness": None,
        }

    selected = {
        "candidate_key": "candidate",
        "structural_digest": "digest",
        "claim": {"ell": 2, "m": 3, "A_terms": [], "B_terms": []},
        "n": 12,
        "k": 2,
        "target": {"required_distance": 9},
        "strata": {},
        "initial_low_weight_oracle": {"outcome": "UNSAT", "max_weight": 4},
    }
    result = run_candidate_ladder(
        selected,
        timeouts={6: 1.0, 8: 1.0, "target": 1.0},
        sector_evaluator=fake_sector,
        isolate_sector_calls=False,
    )
    assert calls == [(6, "X"), (6, "Z")]
    assert result["unknown_fail_open"] is True
    assert result["survived_w8"] is True
    assert result["rejected_by_w8"] is False


def test_run_candidate_sat_still_attempts_both_sectors(monkeypatch) -> None:
    import evaluation.stratified_ladder_diagnostic as module

    class FakeCode:
        num_qudits = 12
        dimension = 2

    monkeypatch.setattr(module, "build_css_code_from_claim", lambda _claim: FakeCode())
    matrices = tuple(np.zeros((2, 12), dtype=np.uint8) for _ in range(4))
    monkeypatch.setattr(module, "get_code_matrices", lambda _code: matrices)
    monkeypatch.setattr(module, "verify_css_low_weight_oracle", lambda *_a, **_k: [])
    monkeypatch.setattr(module, "authoritative_candidate_digest", lambda _claim: "digest")
    monkeypatch.setattr(module, "verify_low_weight_sector_evidence", lambda *_a, **_k: [])
    calls: list[tuple[int, str]] = []

    def fake_sector(*_args, max_weight: int, sector: str, **_kwargs):
        calls.append((max_weight, sector))
        if sector == "X":
            return {"outcome": "SAT", "witness": {"weight": 6}}
        return {"outcome": "UNSAT", "witness": None}

    selected = {
        "candidate_key": "candidate",
        "structural_digest": "digest",
        "claim": {"ell": 2, "m": 3, "A_terms": [], "B_terms": []},
        "n": 12,
        "k": 2,
        "target": {"required_distance": 9},
        "strata": {},
        "initial_low_weight_oracle": {"outcome": "UNSAT", "max_weight": 4},
    }
    result = run_candidate_ladder(
        selected,
        timeouts={6: 1.0, 8: 1.0, "target": 1.0},
        sector_evaluator=fake_sector,
        isolate_sector_calls=False,
    )
    assert calls == [(6, "X"), (6, "Z")]
    assert result["rejected_by_w8"] is True
    assert result["trusted_distance_upper_bound"] == 6


def test_full_ladder_raises_lb_at_w8_before_target_witness(monkeypatch) -> None:
    import evaluation.stratified_ladder_diagnostic as module

    class FakeCode:
        num_qudits = 24
        dimension = 4

    monkeypatch.setattr(module, "build_css_code_from_claim", lambda _claim: FakeCode())
    matrices = tuple(np.zeros((2, 24), dtype=np.uint8) for _ in range(4))
    monkeypatch.setattr(module, "get_code_matrices", lambda _code: matrices)
    monkeypatch.setattr(module, "verify_css_low_weight_oracle", lambda *_a, **_k: [])
    monkeypatch.setattr(module, "authoritative_candidate_digest", lambda _claim: "digest")
    monkeypatch.setattr(module, "verify_low_weight_sector_evidence", lambda *_a, **_k: [])
    calls: list[tuple[int, str]] = []

    def fake_sector(*_args, max_weight: int, sector: str, **_kwargs):
        calls.append((max_weight, sector))
        if max_weight == 12 and sector == "X":
            return {"outcome": "SAT", "witness": {"weight": 10}}
        return {"outcome": "UNSAT", "witness": None}

    selected = {
        "candidate_key": "candidate",
        "structural_digest": "digest",
        "claim": {"ell": 3, "m": 4, "A_terms": [], "B_terms": []},
        "n": 24,
        "k": 4,
        "target": {"required_distance": 13},
        "strata": {},
        "initial_low_weight_oracle": {"outcome": "UNSAT", "max_weight": 4},
    }
    result = run_candidate_ladder(
        selected,
        timeouts={6: 1.0, 8: 1.0, "target": 1.0},
        sector_evaluator=fake_sector,
        isolate_sector_calls=False,
        contract_sha256="contract",
        selected_sha256=module._canonical_sha256(selected),
    )
    assert calls == [
        (6, "X"),
        (6, "Z"),
        (8, "X"),
        (8, "Z"),
        (12, "X"),
        (12, "Z"),
    ]
    assert result["final_distance_lower_bound"] == 9
    assert result["target_gap"] == 4
    assert result["survived_w8"] is True
    assert result["trusted_distance_upper_bound"] == 10

    replayed = module._replay_result(result, selected, "contract")
    assert replayed["final_distance_lower_bound"] == 9

    tampered = dict(result)
    tampered["final_distance_lower_bound"] = 10
    with pytest.raises(module.DiagnosticError, match="derived fields"):
        module._replay_result(tampered, selected, "contract")

    incomplete = dict(result)
    incomplete["rungs"] = [result["rungs"][0]]
    incomplete.update(
        final_distance_lower_bound=7,
        trusted_distance_upper_bound=None,
        target_gap=6,
        rejected_by_w8=False,
        survived_w8=True,
        unknown_fail_open=False,
    )
    with pytest.raises(module.DiagnosticError, match="stopped before"):
        module._replay_result(incomplete, selected, "contract")


def test_sixty_four_sample_decision_has_unambiguous_integer_boundary() -> None:
    switch = [
        *[_result(i, rejected=True, survived=False) for i in range(52)],
        *[_result(i, rejected=False, survived=True) for i in range(52, 64)],
    ]
    assert decide(switch)["action"] == "change_ansatz_within_generalized_toric_family"

    retain = [
        *[_result(i, rejected=True, survived=False) for i in range(51)],
        *[_result(i, rejected=False, survived=True) for i in range(51, 64)],
    ]
    assert decide(retain)["action"] == (
        "retain_generalized_toric_family_and_targeted_deep_proof"
    )


def test_historical_snapshot_replays_bytes_without_rotating_source_fingerprint(
    tmp_path, monkeypatch
) -> None:
    import evaluation.stratified_ladder_diagnostic as module

    input_path = tmp_path / "candidate-batch.jsonl"
    registry_path = tmp_path / "registry.json"
    ledger_path = tmp_path / "ledger.json"
    snapshot_path = Path(str(ledger_path) + ".ranked-snapshot.jsonl")
    offsets_path = Path(str(ledger_path) + ".ranked-snapshot.offsets")
    input_path.write_text("source\n", encoding="utf-8")
    registry_path.write_text("registry\n", encoding="utf-8")
    snapshot_rows = [
        {"triage_identity": {"canonical_digest": "a"}, "order": 0, "terminal": False},
        {"triage_identity": {"canonical_digest": "b"}, "order": 1, "terminal": True},
    ]
    snapshot_path.write_bytes(
        b"".join(module._canonical_bytes(row) + b"\n" for row in snapshot_rows)
    )
    offsets_path.write_bytes(b"\0" * 24)

    def historical_identity(path):
        return {
            "path": str(path.resolve()),
            "stat": module._stat_identity(path.lstat()),
            "sha256": module._file_sha256(path),
        }

    binding_unsigned = {
        "schema_version": 1,
        "gate": "qldpc-stage2-ranked-snapshot",
        "inputs": [historical_identity(input_path)],
        "source_fingerprint": "historical-source-not-current",
        "solver_runtime": {"historical": True},
        "known_code_registry": historical_identity(registry_path),
        "target_mode": module.TARGET_MODE_SCALAR,
    }
    binding = {
        **binding_unsigned,
        "binding_sha256": module._canonical_sha256(binding_unsigned),
    }
    counts = {
        "input_records": 2,
        "unique_candidates": 2,
        "duplicate_records": 0,
        "rejected_candidates": 1,
        "eligible_candidates": 1,
    }
    chunks = [{"fixture": 0}]
    identity = {
        "binding_sha256": binding["binding_sha256"],
        "snapshot_sha256": module._file_sha256(snapshot_path),
        "offsets_sha256": module._file_sha256(offsets_path),
        "chunk_index_sha256": module._canonical_sha256(chunks),
        "chunk_rows": 128,
        "rows": 2,
        "eligible_rows": 1,
        "counts_sha256": module._canonical_sha256(counts),
    }
    manifest_unsigned = {
        "schema_version": 1,
        "gate": "qldpc-stage2-ranked-snapshot",
        "binding": binding,
        "binding_sha256": binding["binding_sha256"],
        "snapshot_rows": 2,
        "chunk_rows": 128,
        "snapshot_stat": module._stat_identity(snapshot_path.lstat()),
        "offsets_stat": module._stat_identity(offsets_path.lstat()),
        "counts": counts,
        "chunks": chunks,
        "identity": identity,
    }
    manifest = {
        **manifest_unsigned,
        "manifest_sha256": module._canonical_sha256(manifest_unsigned),
    }
    monkeypatch.setattr(module, "_ranked_selection_key", lambda row: (row["order"],))
    monkeypatch.setattr(
        module,
        "_is_trusted_terminal_rejection",
        lambda row: row["terminal"],
    )
    replay = module._manifest_replays(
        manifest,
        snapshot_path=snapshot_path,
        ledger_path=ledger_path,
    )
    assert replay["historical_source_fingerprint"] == (
        "historical-source-not-current"
    )

    input_path.write_text("source changed\n", encoding="utf-8")
    with pytest.raises(module.DiagnosticError, match="input 0"):
        module._manifest_replays(
            manifest,
            snapshot_path=snapshot_path,
            ledger_path=ledger_path,
        )
