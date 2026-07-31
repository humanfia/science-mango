"""Trust-boundary tests for the search-only JSONL MILP cache."""

from __future__ import annotations

import copy
import json
import os

import pytest

import evaluation.evaluator as evaluator_module
from evaluation.bb_code import build_bb_code, get_code_params_fast
from evaluation.distance_milp import (
    get_code_matrices,
    symplectic_weight_witness,
)
from evaluation.evaluator import (
    _load_milp_cache,
    _milp_cache_key,
    _milp_cache_record,
    _milp_cache_run_parameters,
    _milp_cache_sha256,
    evaluate_candidate_milp,
    evaluate_milp_parallel,
)


_A = [(3, 0), (0, 1), (0, 2)]
_B = [(0, 3), (1, 0), (2, 0)]


def _gross_upper_bound() -> dict:
    quick = evaluate_candidate_milp(12, 6, _A, _B, quick=True)
    result = evaluate_candidate_milp(
        12,
        6,
        _A,
        _B,
        milp_early_stop=quick["d_symplectic"],
    )
    assert result["stage"] == "symplectic_low_d"
    assert result["d"] == 12
    return result


def _record(result: dict, *, timeout: int = 30, cutoff: int = 12) -> dict:
    parameters = _milp_cache_run_parameters(
        milp_timeout_per_logical=timeout,
        milp_total_timeout=120,
        milp_early_stop=cutoff,
    )
    return _milp_cache_record(
        result,
        run_parameters=parameters,
        saved_at=123.0,
    )


def _css_witness_upper_bound(side: str = "X") -> dict:
    code = build_bb_code(12, 6, _A, _B)
    n, k = get_code_params_fast(code)
    hx, hz, lx, lz = get_code_matrices(code)
    vectors, checks, duals = (
        (lx, hz, lz) if side == "X" else (lz, hx, lx)
    )
    witness = None
    for vector in vectors:
        bits = [int(value) for value in vector]
        if any(
            sum(int(a) * bit for a, bit in zip(check, bits)) % 2
            for check in checks
        ):
            continue
        index = next(
            (
                candidate
                for candidate, dual in enumerate(duals)
                if sum(
                    int(value) * bit
                    for value, bit in zip(dual, bits)
                )
                % 2
                == 1
            ),
            None,
        )
        if index is not None:
            witness = {
                "side": side,
                "index": index,
                "weight": sum(bits),
                "bits": bits,
            }
            break
    assert witness is not None
    distance = witness["weight"]
    return {
        "ell": 12,
        "m": 6,
        "A_terms": _A,
        "B_terms": _B,
        "n": n,
        "k": k,
        "d": distance,
        "d_is_exact": True,
        "distance_trusted": True,
        "fom": k * distance**2 / n,
        "score": k * distance**2 / n,
        "stage": "forged_css_exact",
        "milp_details": {
            "exact": True,
            "minimum_direction_witness": witness,
        },
    }


def _write(path, *rows: dict) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows)
    )


def _load(path, *, timeout: int = 30, cutoff: int = 12):
    return _load_milp_cache(
        str(path),
        milp_timeout_per_logical=timeout,
        milp_total_timeout=120,
        milp_early_stop=cutoff,
        requested_keys={_milp_cache_key(12, 6, _A, _B)},
    )


def test_legacy_exact_row_is_not_a_cache_proof(tmp_path):
    row = _gross_upper_bound()
    row["d_is_exact"] = True
    path = tmp_path / "legacy.jsonl"
    _write(path, row)

    assert _load(path) == {}


def test_malformed_or_non_utf8_row_does_not_discard_valid_cache(tmp_path):
    record = _record(_gross_upper_bound())
    path = tmp_path / "malformed.jsonl"
    valid = json.dumps(record, sort_keys=True).encode()
    path.write_bytes(b"\xff\xfe{not-json}\n" + valid + b"\n")

    loaded = list(_load(path).values())

    assert len(loaded) == 1
    assert loaded[0]["stage"] == "milp_cache_witness_upper_bound"


def test_deep_or_oversized_rows_cannot_block_a_valid_cache_record(tmp_path):
    record = json.dumps(_record(_gross_upper_bound()), sort_keys=True).encode()
    deep = b"[" * 2000 + b"0" + b"]" * 2000 + b"\n"
    oversized = (
        b"x" * (evaluator_module._MILP_CACHE_MAX_RECORD_BYTES + 1)
        + b"\n"
    )
    path = tmp_path / "hostile-lines.jsonl"
    path.write_bytes(deep + oversized + record + b"\n")

    loaded = list(_load(path).values())

    assert len(loaded) == 1
    assert loaded[0]["stage"] == "milp_cache_witness_upper_bound"


@pytest.mark.parametrize("kind", ("symlink", "fifo"))
def test_special_cache_path_is_ignored_without_following_or_blocking(
    tmp_path, kind
):
    path = tmp_path / "special.jsonl"
    if kind == "symlink":
        target = tmp_path / "target.jsonl"
        _write(target, _record(_gross_upper_bound()))
        path.symlink_to(target)
    else:
        os.mkfifo(path)

    assert _load(path) == {}


def test_unavailable_fingerprint_degrades_to_fresh_solve(
    tmp_path, monkeypatch
):
    path = tmp_path / "cache.jsonl"
    _write(path, _record(_gross_upper_bound()))

    def unavailable():
        raise RuntimeError("source cannot be fingerprinted")

    monkeypatch.setattr(
        evaluator_module,
        "_milp_cache_implementation_fingerprint",
        unavailable,
    )

    assert _load(path) == {}
    assert _load(tmp_path / "does-not-exist.jsonl") == {}


def test_cache_cannot_bypass_current_candidate_input_gate(tmp_path):
    a_terms = [(0, 0), (1, 0), (-1, 0)]
    b_terms = [(0, 0), (1, 0), (0, 1)]
    code = build_bb_code(3, 3, a_terms, b_terms)
    n, k = get_code_params_fast(code)
    witness = symplectic_weight_witness(code)
    assert k >= 4 and witness is not None
    invalid = {
        "ell": 3,
        "m": 3,
        "A_terms": a_terms,
        "B_terms": b_terms,
        "n": n,
        "k": k,
        "d": witness["weight"],
        "d_is_exact": True,
        "distance_trusted": True,
        "fom": k * witness["weight"] ** 2 / n,
        "score": k * witness["weight"] ** 2 / n,
        "stage": "forged_exact",
        "symplectic_weight_witness": witness,
    }
    path = tmp_path / "invalid-candidate.jsonl"
    _write(path, _record(invalid, cutoff=witness["weight"]))

    assert _load(path, cutoff=witness["weight"]) == {}


def test_bound_cache_replays_witness_but_downgrades_exact_claim(tmp_path):
    row = _gross_upper_bound()
    row["d_is_exact"] = True
    row["score"] = 999999.0
    path = tmp_path / "bound.jsonl"
    _write(path, _record(row))

    loaded = list(_load(path).values())

    assert len(loaded) == 1
    cached = loaded[0]
    assert cached["d"] == 12
    assert cached["d_is_exact"] is False
    assert cached["distance_status"] == "upper_bound"
    assert cached["score"] == 0.0
    assert (
        cached["fom_upper_bound"]
        == cached["k"] * cached["d"] ** 2 / cached["n"]
    )
    assert cached["milp_cache_replayed"] is True
    assert cached["stage"] == "milp_cache_witness_upper_bound"


def test_cache_binding_rejects_source_and_budget_changes(tmp_path):
    row = _gross_upper_bound()
    record = _record(row)
    path = tmp_path / "binding.jsonl"
    _write(path, record)

    assert _load(path, timeout=60) == {}

    tampered = copy.deepcopy(record)
    tampered["_milp_cache"]["implementation"]["cache_contract"] = "old"
    _write(path, tampered)
    assert _load(path) == {}


def test_high_upper_bound_is_recomputed_instead_of_becoming_permanent(tmp_path):
    row = _gross_upper_bound()
    path = tmp_path / "high.jsonl"
    _write(path, _record(row, cutoff=4))

    assert _load(path, cutoff=4) == {}


def test_witness_replay_rejects_forgery_even_with_recomputed_hashes(tmp_path):
    row = _gross_upper_bound()
    record = _record(row)
    forged = copy.deepcopy(record)
    witness = forged["symplectic_weight_witness"]
    witness["bits"][0] ^= 1
    body = copy.deepcopy(forged)
    metadata = body.pop("_milp_cache")
    metadata["evidence_sha256"] = _milp_cache_sha256(witness)
    metadata["result_sha256"] = _milp_cache_sha256(body)
    forged["_milp_cache"] = metadata
    path = tmp_path / "forged.jsonl"
    _write(path, forged)

    assert _load(path) == {}


def test_symplectic_witness_requires_canonical_json_types(tmp_path):
    record = _record(_gross_upper_bound())
    forged = copy.deepcopy(record)
    witness = forged["symplectic_weight_witness"]
    zero = witness["bits"].index(0)
    witness["bits"][zero] = False
    body = copy.deepcopy(forged)
    metadata = body.pop("_milp_cache")
    metadata["evidence_sha256"] = _milp_cache_sha256(witness)
    metadata["result_sha256"] = _milp_cache_sha256(body)
    forged["_milp_cache"] = metadata
    path = tmp_path / "noncanonical-witness.jsonl"
    _write(path, forged)

    assert _load(path) == {}


def test_replayed_cache_drops_untrusted_attached_claims(tmp_path):
    row = _gross_upper_bound()
    row.update(
        {
            "audit_seal": {"passed": True},
            "certificate": {"passed": True},
            "final_gate_excluded_by_upper_bound": True,
            "passed": True,
            "threshold_rejection_proven": True,
        }
    )
    path = tmp_path / "attached-claims.jsonl"
    _write(path, _record(row))

    cached = next(iter(_load(path).values()))

    for field in (
        "audit_seal",
        "certificate",
        "final_gate_excluded_by_upper_bound",
        "passed",
        "threshold_rejection_proven",
    ):
        assert field not in cached
    assert cached["d_is_exact"] is False
    assert cached["distance_status"] == "upper_bound"


@pytest.mark.parametrize("side", ("X", "Z"))
def test_css_exact_claim_is_replayed_only_as_an_upper_bound(
    tmp_path, side
):
    path = tmp_path / f"css-exact-{side}.jsonl"
    row = _css_witness_upper_bound(side)
    _write(path, _record(row, cutoff=row["d"]))

    cached = next(iter(_load(path, cutoff=row["d"]).values()))

    assert cached["stage"] == "milp_cache_witness_upper_bound"
    assert cached["d_is_exact"] is False
    assert cached["distance_status"] == "upper_bound"
    assert cached["milp_details"]["exact"] is False
    assert cached["milp_details"]["cache_replayed"] is True
    assert (
        cached["milp_details"]["minimum_direction_witness"]["side"]
        == side
    )


def test_parallel_evaluator_writes_and_reuses_only_bound_cache(tmp_path):
    path = tmp_path / "parallel.jsonl"
    path.write_bytes(b'{"torn":')
    tasks = [(12, 6, _A, _B)]
    kwargs = {
        "milp_timeout_per_logical": 30,
        "milp_total_timeout": 120,
        "milp_early_stop": 12,
        "max_workers": 1,
        "save_path": str(path),
    }

    first = evaluate_milp_parallel(tasks, **kwargs)
    persisted = json.loads(path.read_text().splitlines()[-1])
    second = evaluate_milp_parallel(tasks, **kwargs)

    assert first[0]["stage"] == "symplectic_low_d"
    assert persisted["_milp_cache"]["kind"] == (
        "qcode-milp-search-cache-record"
    )
    assert second[0]["stage"] == "milp_cache_witness_upper_bound"
    assert second[0]["d_is_exact"] is False


def test_invalid_current_task_cannot_alias_a_valid_cache_key(tmp_path):
    path = tmp_path / "strict-current-task.jsonl"
    _write(path, _record(_gross_upper_bound()))
    invalid_a = [(3, False), (0, 1), (0, 2)]
    task = [(12, 6, invalid_a, _B)]

    direct = evaluate_candidate_milp(12, 6, invalid_a, _B, quick=True)
    parallel = evaluate_milp_parallel(
        task,
        milp_timeout_per_logical=30,
        milp_total_timeout=120,
        milp_early_stop=12,
        max_workers=1,
        save_path=str(path),
    )

    assert direct["stage"] == "construction_error"
    assert parallel[0]["stage"] == "construction_error"
    assert parallel[0].get("milp_cache_replayed") is not True


def test_parallel_evaluator_does_not_append_through_cache_symlink(tmp_path):
    target = tmp_path / "outside.jsonl"
    target.write_text("must-not-change")
    path = tmp_path / "cache.jsonl"
    path.symlink_to(target)

    result = evaluate_milp_parallel(
        [(12, 6, _A, _B)],
        milp_timeout_per_logical=30,
        milp_total_timeout=120,
        milp_early_stop=12,
        max_workers=1,
        save_path=str(path),
    )

    assert result[0]["d"] == 12
    assert result[0].get("milp_cache_replayed") is not True
    assert target.read_text() == "must-not-change"
    assert path.is_symlink()
