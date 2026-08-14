"""Tests for the strict structural-novelty gate."""

import json
import os

import evaluation.structural_dedup as structural_dedup
import evaluation.tanner_equivalence as tanner_equivalence
import pytest
from evaluation.structural_dedup import (
    StructuralScreenCacheError,
    StructuralScreenIncompleteError,
    annotate_css_results_with_deferred_cache,
    check_css_static_eligibility,
    check_css_structural_novelty,
    deduplicate_css_results,
    screen_css_results_with_cache,
    screen_css_results_with_deferred_cache,
)


def test_exact_gross_code_is_known():
    result = check_css_structural_novelty(
        12, 6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
    )
    assert result["checked"] is True
    assert result["novel"] is False
    assert result["matched_reference"] == "Gross [[144,12,12]]"
    assert result["explicit_isomorphism"]["verified"] is True


def test_structural_runtime_binds_single_thread_worker_environment():
    runtime = structural_dedup.structural_screen_runtime_fingerprint()
    assert runtime["payload"]["worker_native_thread_environment"] == {
        name: "1"
        for name in structural_dedup.STRUCTURAL_SCREEN_NATIVE_THREAD_ENV
    }


def test_structural_spawn_environment_restores_parent_on_error(monkeypatch):
    first, *remaining = structural_dedup.STRUCTURAL_SCREEN_NATIVE_THREAD_ENV
    monkeypatch.setenv(first, "17")
    for name in remaining:
        monkeypatch.delenv(name, raising=False)

    with pytest.raises(RuntimeError, match="sentinel"):
        with structural_dedup._structural_screen_spawn_environment():
            assert all(
                os.environ.get(name) == "1"
                for name in structural_dedup.STRUCTURAL_SCREEN_NATIVE_THREAD_ENV
            )
            raise RuntimeError("sentinel")

    assert os.environ.get(first) == "17"
    assert all(name not in os.environ for name in remaining)


def test_idle_worker_cohort_is_signalled_before_any_join():
    processes = []
    events = []

    class FakeProcess:
        def __init__(self, index):
            self.index = index
            self.alive = True
            self.terminated = False
            processes.append(self)

        def is_alive(self):
            return self.alive

        def terminate(self):
            self.terminated = True
            events.append(("terminate", self.index))

        def join(self, timeout):
            assert timeout >= 0
            assert all(process.terminated for process in processes)
            events.append(("join", self.index))
            self.alive = False

        def kill(self):
            events.append(("kill", self.index))
            self.alive = False

    class FakeConnection:
        def __init__(self, index):
            self.index = index
            self.closed = False

        def close(self):
            self.closed = True
            events.append(("close", self.index))

    workers = [
        {
            "process": FakeProcess(index),
            "connection": FakeConnection(index),
            "closed": False,
        }
        for index in range(4)
    ]

    structural_dedup._stop_annotation_workers(workers)

    assert events[:4] == [("terminate", index) for index in range(4)]
    assert all(not worker["process"].is_alive() for worker in workers)
    assert all(worker["connection"].closed for worker in workers)
    assert not any(kind == "kill" for kind, _index in events)


def test_novelty_digest_reuses_one_bliss_canonicalization(monkeypatch):
    candidate = structural_dedup._build_css_result(_cached_candidate())
    canonical_hash = structural_dedup.canonical_hash
    observed = []

    def counted(code):
        canonical = canonical_hash(code)
        observed.append(canonical)
        return canonical

    monkeypatch.setattr(structural_dedup, "canonical_hash", counted)
    monkeypatch.setattr(
        structural_dedup,
        "known_reference_registry",
        lambda: (),
    )
    result = structural_dedup.check_css_code_structural_novelty(candidate)

    assert result["checked"] is True
    assert result["novel"] is True
    assert len(observed) == 1
    assert result["canonical_digest"] == (
        structural_dedup._canonical_digest_from_hash(observed[0])
    )


def test_annotation_reuses_static_gate_code_for_novelty_and_logical_basis(
    monkeypatch,
):
    original_build = structural_dedup.build_bb_code
    builds = []

    def counted_build(*args, **kwargs):
        code = original_build(*args, **kwargs)
        builds.append(code)
        return code

    monkeypatch.setattr(structural_dedup, "build_bb_code", counted_build)
    monkeypatch.setattr(
        structural_dedup,
        "known_reference_registry",
        lambda: (),
    )
    monkeypatch.setattr(
        structural_dedup,
        "_code_parameters",
        lambda _code: (_ for _ in ()).throw(
            AssertionError("static n/k must be reused")
        ),
    )
    monkeypatch.setattr(
        structural_dedup,
        "_logical_basis_upper_bound_report",
        lambda code: {"same_rebuilt_code": code is builds[0]},
    )

    annotated = structural_dedup.annotate_css_result(_cached_candidate())

    assert annotated["static_eligibility"]["eligible"] is True
    assert annotated["structural_novelty"]["novel"] is True
    assert annotated["static_eligibility"]["logical_basis_upper_bound"] == {
        "same_rebuilt_code": True,
    }
    assert len(builds) == 1


def test_compact_annotation_reuses_one_authoritative_rebuild(monkeypatch):
    row = {
        "construction": {
            "kind": "bb-v1",
            "ell": 6,
            "m": 6,
            "A_terms": [[0, 0], [0, 1], [1, 0]],
            "B_terms": [[0, 0], [0, 2], [2, 0]],
        },
        "n": 72,
        "k": 8,
    }
    original_build = structural_dedup._build_css_result
    builds = []

    def counted_build(result):
        code = original_build(result)
        builds.append(code)
        return code

    monkeypatch.setattr(
        structural_dedup,
        "_build_css_result",
        counted_build,
    )
    monkeypatch.setattr(
        structural_dedup,
        "known_reference_registry",
        lambda: (),
    )
    monkeypatch.setattr(
        structural_dedup,
        "_logical_basis_upper_bound_report",
        lambda code: {"same_rebuilt_code": code is builds[0]},
    )

    annotated = structural_dedup.annotate_css_result(row)

    assert annotated["static_eligibility"]["eligible"] is True
    assert annotated["structural_novelty"]["novel"] is True
    assert annotated["static_eligibility"]["logical_basis_upper_bound"] == {
        "same_rebuilt_code": True,
    }
    assert len(builds) == 1


def _dense_reference_tanner_graph(code):
    """Reproduce the pre-optimization row-major dense edge scan."""

    igraph = tanner_equivalence._require_igraph()
    matrix_x, matrix_z = tanner_equivalence._extract_check_matrices(code)
    n = matrix_x.shape[1]
    rows_x, rows_z = matrix_x.shape[0], matrix_z.shape[0]
    graph = igraph.Graph(n + rows_x + rows_z, directed=False)
    colors = [0] * n + [1] * rows_x + [2] * rows_z
    edges = []
    for row in range(rows_x):
        for column in range(n):
            if matrix_x[row, column] == 1:
                edges.append((column, n + row))
    for row in range(rows_z):
        for column in range(n):
            if matrix_z[row, column] == 1:
                edges.append((column, n + rows_x + row))
    graph.add_edges(edges)
    return graph, colors


def test_sparse_tanner_builder_preserves_edges_hash_and_concrete_mapping(
    monkeypatch,
):
    base = structural_dedup._build_css_result(_cached_candidate())
    shifted_row = _cached_candidate()
    shifted_row["A_terms"] = [[1, 0], [1, 1], [2, 0]]
    shifted_row["B_terms"] = [[1, 0], [1, 2], [3, 0]]
    shifted = structural_dedup._build_css_result(shifted_row)

    sparse_graph, sparse_colors = (
        tanner_equivalence.build_colored_tanner_graph(base)
    )
    dense_graph, dense_colors = _dense_reference_tanner_graph(base)
    assert sparse_colors == dense_colors
    assert sparse_graph.get_edgelist() == dense_graph.get_edgelist()

    sparse_hash = tanner_equivalence.canonical_hash(base)
    sparse_mapping = tanner_equivalence.extract_full_vertex_isomorphism(
        shifted,
        base,
    )
    sparse_replay = structural_dedup.replay_css_isomorphism(
        shifted,
        base,
        sparse_mapping,
    )

    monkeypatch.setattr(
        tanner_equivalence,
        "build_colored_tanner_graph",
        _dense_reference_tanner_graph,
    )
    assert tanner_equivalence.canonical_hash(base) == sparse_hash
    dense_mapping = tanner_equivalence.extract_full_vertex_isomorphism(
        shifted,
        base,
    )
    assert dense_mapping == sparse_mapping
    assert structural_dedup.replay_css_isomorphism(
        shifted,
        base,
        dense_mapping,
    ) == sparse_replay
    assert sparse_replay["verified"] is True


def test_logical_basis_upper_bound_report_is_sealed_and_tamper_closed(
    monkeypatch,
):
    witness = {
        "side": "Z",
        "index": 0,
        "dual_side": "X",
        "dual_index": 1,
        "weight": 3,
        "bits": [1, 0, 1, 0, 1],
    }
    monkeypatch.setattr(
        structural_dedup,
        "symplectic_weight_witness",
        lambda _code: witness,
    )
    report = structural_dedup._logical_basis_upper_bound_report(object())
    structural_dedup._validate_logical_basis_upper_bound_report(report)
    assert report["available"] is True
    assert report["upper_bound"] == 3

    tampered = json.loads(json.dumps(report))
    tampered["upper_bound"] = 4
    with pytest.raises(StructuralScreenCacheError, match="self-hash"):
        structural_dedup._validate_logical_basis_upper_bound_report(tampered)


def test_known_reference_dedup_carries_verified_rejection():
    row = {
        "ell": 12,
        "m": 6,
        "n": 144,
        "k": 12,
        "d": 12,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
    }
    kept, rejected = deduplicate_css_results([row])
    assert kept == []
    assert len(rejected) == 1
    assert rejected[0]["structural_rejection"] == "known_reference"
    assert (
        rejected[0]["structural_novelty"]["explicit_isomorphism"]["verified"]
        is True
    )


def test_static_gate_rebuilds_k_and_rejects_false_self_report():
    static = check_css_static_eligibility(
        12,
        6,
        [(3, 0), (0, 1), (0, 2)],
        [(0, 3), (1, 0), (2, 0)],
        reported_n=144,
        reported_k=999,
    )
    assert static["k"] == 12
    assert static["checks"]["reported_k_matches"] is False
    assert static["eligible"] is False


def test_non_diagonal_reencoding_of_bravyi_is_known():
    result = check_css_structural_novelty(
        12, 12,
        [(3, 0), (0, 1), (0, 2)],
        [(3, 3), (1, 0), (2, 0)],
    )
    assert result["novel"] is False
    assert result["matched_reference"] == "Bravyi [[288,12,18]]"
    assert result["explicit_isomorphism"]["hx_preserved"] is True
    assert result["explicit_isomorphism"]["hz_preserved"] is True


def test_different_known_parameters_are_not_false_match():
    result = check_css_structural_novelty(
        12, 6,
        [(0, 0), (0, 1), (0, 2)],
        [(0, 0), (1, 0), (2, 0)],
    )
    assert result["checked"] is True
    assert result["novel"] is True
    assert result["matched_reference"] is None


def test_within_run_reencoding_is_replayed_and_deduplicated():
    base = {
        "ell": 12, "m": 6, "n": 144, "k": 8, "d": 4,
        "A_terms": [(0, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 0), (1, 0), (2, 0)],
    }
    shifted = {
        "ell": 12, "m": 6, "n": 144, "k": 8, "d": 4,
        "A_terms": [(1, 0), (1, 1), (1, 2)],
        "B_terms": [(1, 0), (2, 0), (3, 0)],
    }
    kept, rejected = deduplicate_css_results([base, shifted])
    assert len(kept) == 1
    assert len(rejected) == 1
    audit = rejected[0]["structural_novelty"]
    assert audit["relation"] == "within_run_css_tanner_permutation_equivalent"
    assert audit["explicit_isomorphism"]["verified"] is True
    assert audit["explicit_isomorphism"]["hx_preserved"] is True
    assert audit["explicit_isomorphism"]["hz_preserved"] is True


def test_disconnected_humanize_leader_fails_tier0_before_bliss_or_milp():
    static = check_css_static_eligibility(
        12, 12,
        [(0, 0), (0, 2), (0, 4)],
        [(0, 0), (2, 0), (4, 0)],
    )
    assert static["eligible"] is False
    assert static["checks"]["connected_tanner_graph"] is False
    assert static["tanner_components"] == 4

    row = {
        "ell": 12, "m": 12, "n": 288, "k": 32, "d": 20,
        "fom": 44.44444444444444,
        "A_terms": [(0, 0), (0, 2), (0, 4)],
        "B_terms": [(0, 0), (2, 0), (4, 0)],
    }
    kept, rejected = deduplicate_css_results([row])
    assert kept == []
    assert len(rejected) == 1
    assert rejected[0]["structural_rejection"] == "static_ineligible"
    assert rejected[0]["structural_novelty"]["checked"] is False


def _cached_candidate() -> dict:
    return {
        "ell": 6,
        "m": 6,
        "n": 72,
        "k": 8,
        "d": 12,
        "fom": 16.0,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
    }


def _novel_annotation() -> dict:
    return {
        "static_eligibility": {
            "checked": True,
            "eligible": True,
            "checks": {
                "candidate_rebuild": True,
                "positive_dimension": True,
            },
            "failures": [],
            "n": 72,
            "k": 8,
        },
        "structural_novelty": {
            "checked": True,
            "novel": True,
            "relation": None,
            "canonical_digest": "a" * 64,
            "matched_reference": None,
            "reference_digest": None,
            "explicit_isomorphism": None,
        },
        "structural_rejection": None,
    }


def _identity_pair_replay(*, ell: int = 6, m: int = 6) -> dict:
    block = ell * m
    return {
        "verified": True,
        "hx_preserved": True,
        "hz_preserved": True,
        "qubit_permutation": list(range(2 * block)),
        "x_check_permutation": list(range(block)),
        "z_check_permutation": list(range(block)),
    }


def test_durable_screen_reuses_complete_content_addressed_cache(
    tmp_path,
    monkeypatch,
):
    calls = []

    def complete(
        tasks,
        *,
        max_workers,
        hard_timeout,
        on_completed=None,
        on_unresolved=None,
    ):
        del on_completed, on_unresolved
        calls.append((list(tasks), max_workers, hard_timeout))
        return {
            index: _novel_annotation() for index, _row in tasks
        }, {}

    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        complete,
    )
    row = _cached_candidate()
    kept, rejected = screen_css_results_with_cache(
        [row],
        cache_dir=tmp_path / "cache",
        max_workers=6,
        hard_timeout=17,
    )
    assert len(kept) == 1
    assert rejected == []
    assert kept[0]["static_eligibility"]["k"] == 8
    assert len(calls) == 1
    assert calls[0][1:] == (6, 17)

    def must_not_run(*_args, **_kwargs):
        raise AssertionError("complete cache entry was recomputed")

    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        must_not_run,
    )
    replayed, replay_rejected = screen_css_results_with_cache(
        [row],
        cache_dir=tmp_path / "cache",
        max_workers=2,
        hard_timeout=1,
    )
    assert replayed == kept
    assert replay_rejected == []


def test_timeout_is_durable_retryable_and_never_a_rejection(
    tmp_path,
    monkeypatch,
):
    attempts = 0

    def timeout_then_complete(
        tasks,
        *,
        max_workers,
        hard_timeout,
        on_completed=None,
        on_unresolved=None,
    ):
        del max_workers, hard_timeout, on_completed, on_unresolved
        nonlocal attempts
        attempts += 1
        index = tasks[0][0]
        if attempts == 1:
            return {}, {
                index: {
                    "kind": "hard_timeout",
                    "hard_timeout_seconds": 1.0,
                    "retryable": True,
                }
            }
        return {index: _novel_annotation()}, {}

    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        timeout_then_complete,
    )
    cache = tmp_path / "cache"
    with pytest.raises(StructuralScreenIncompleteError) as raised:
        screen_css_results_with_cache(
            [_cached_candidate()],
            cache_dir=cache,
            max_workers=1,
            hard_timeout=1,
        )
    assert raised.value.unresolved[0]["failure"]["kind"] == "hard_timeout"
    entry_path = next(cache.rglob("*.json"))
    unresolved = json.loads(entry_path.read_text())
    assert unresolved["status"] == "unresolved"
    assert unresolved["failure"]["retryable"] is True
    assert unresolved["annotation"] is None

    kept, rejected = screen_css_results_with_cache(
        [_cached_candidate()],
        cache_dir=cache,
        max_workers=1,
        hard_timeout=1,
    )
    assert len(kept) == 1
    assert rejected == []
    completed = json.loads(entry_path.read_text())
    assert completed["status"] == "complete"
    assert completed["attempt_count"] == 2


def test_permanent_timeout_is_deferred_without_blocking_or_rejection(
    tmp_path,
    monkeypatch,
):
    def always_timeout(
        tasks,
        *,
        on_unresolved=None,
        **_kwargs,
    ):
        unresolved = {}
        for index, _row in tasks:
            failure = {
                "kind": "hard_timeout",
                "hard_timeout_seconds": 1.0,
                "retryable": True,
            }
            unresolved[index] = failure
            if on_unresolved is not None:
                on_unresolved(index, failure)
        return {}, unresolved

    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        always_timeout,
    )
    cache = tmp_path / "cache"
    for expected_attempt in (1, 2):
        kept, rejected, deferred = (
            screen_css_results_with_deferred_cache(
                [_cached_candidate()],
                cache_dir=cache,
                max_workers=1,
                hard_timeout=1,
            )
        )
        assert kept == []
        assert rejected == []
        assert deferred[0]["attempt_count"] == expected_attempt
        entry = json.loads(next(cache.rglob("*.json")).read_text())
        assert entry["status"] == "unresolved"
        assert entry["failure"]["retryable"] is True


def test_cache_tamper_fails_closed_instead_of_reusing_rejection(
    tmp_path,
    monkeypatch,
):
    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        lambda tasks, **_kwargs: (
            {index: _novel_annotation() for index, _row in tasks},
            {},
        ),
    )
    cache = tmp_path / "cache"
    screen_css_results_with_cache(
        [_cached_candidate()],
        cache_dir=cache,
        max_workers=1,
    )
    entry_path = next(cache.rglob("*.json"))
    entry = json.loads(entry_path.read_text())
    entry["annotation"]["structural_rejection"] = "known_reference"
    entry_path.write_text(json.dumps(entry))

    with pytest.raises(
        StructuralScreenCacheError,
        match="integrity check failed",
    ):
        screen_css_results_with_cache(
            [_cached_candidate()],
            cache_dir=cache,
            max_workers=1,
        )


def test_completed_candidate_is_cached_before_batch_interrupt(
    tmp_path,
    monkeypatch,
):
    def complete_then_interrupt(
        tasks,
        *,
        on_completed,
        **_kwargs,
    ):
        index = tasks[0][0]
        on_completed(index, _novel_annotation())
        raise KeyboardInterrupt

    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        complete_then_interrupt,
    )
    cache = tmp_path / "cache"
    with pytest.raises(KeyboardInterrupt):
        screen_css_results_with_cache(
            [_cached_candidate()],
            cache_dir=cache,
            max_workers=1,
        )
    entry = json.loads(next(cache.rglob("*.json")).read_text())
    assert entry["status"] == "complete"

    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("durably completed candidate was recomputed")
        ),
    )
    kept, rejected = screen_css_results_with_cache(
        [_cached_candidate()],
        cache_dir=cache,
        max_workers=1,
    )
    assert len(kept) == 1
    assert rejected == []


def test_source_runtime_fingerprint_change_forces_recomputation(
    tmp_path,
    monkeypatch,
):
    runtime = {"value": "1" * 64}
    monkeypatch.setattr(
        structural_dedup,
        "structural_screen_runtime_fingerprint",
        lambda: {"payload": {}, "sha256": runtime["value"]},
    )
    calls = 0

    def complete(tasks, **_kwargs):
        nonlocal calls
        calls += 1
        return {
            index: _novel_annotation() for index, _row in tasks
        }, {}

    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        complete,
    )
    cache = tmp_path / "cache"
    screen_css_results_with_cache(
        [_cached_candidate()],
        cache_dir=cache,
        max_workers=1,
    )
    runtime["value"] = "2" * 64
    screen_css_results_with_cache(
        [_cached_candidate()],
        cache_dir=cache,
        max_workers=1,
    )
    assert calls == 2


def test_annotation_worker_has_killable_hard_wall_timeout():
    completed, unresolved = structural_dedup._run_annotation_workers(
        [(0, _cached_candidate())],
        max_workers=1,
        hard_timeout=0.001,
    )
    assert completed == {}
    assert unresolved[0]["retryable"] is True
    assert unresolved[0]["kind"] in {"hard_timeout", "worker_exit"}


def test_spawn_worker_completes_and_caches_real_structural_gate(
    tmp_path,
    monkeypatch,
):
    parent_values = {}
    for index, name in enumerate(
        structural_dedup.STRUCTURAL_SCREEN_NATIVE_THREAD_ENV,
        start=2,
    ):
        value = str(index)
        monkeypatch.setenv(name, value)
        parent_values[name] = value
    gross = {
        "ell": 12,
        "m": 6,
        "n": 144,
        "k": 12,
        "d": 12,
        "A_terms": [(3, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 3), (1, 0), (2, 0)],
    }
    kept, rejected = screen_css_results_with_cache(
        [gross],
        cache_dir=tmp_path / "cache",
        max_workers=1,
        hard_timeout=60,
    )
    assert kept == []
    assert len(rejected) == 1
    assert rejected[0]["structural_rejection"] == "known_reference"
    entry = json.loads(next((tmp_path / "cache").rglob("*.json")).read_text())
    assert entry["status"] == "complete"
    assert {
        name: os.environ.get(name)
        for name in structural_dedup.STRUCTURAL_SCREEN_NATIVE_THREAD_ENV
    } == parent_values


def test_bounded_screen_replays_real_within_pool_duplicate(tmp_path):
    base = {
        "ell": 12,
        "m": 6,
        "n": 144,
        "k": 8,
        "d": 4,
        "A_terms": [(0, 0), (0, 1), (0, 2)],
        "B_terms": [(0, 0), (1, 0), (2, 0)],
    }
    shifted = {
        "ell": 12,
        "m": 6,
        "n": 144,
        "k": 8,
        "d": 4,
        "A_terms": [(1, 0), (1, 1), (1, 2)],
        "B_terms": [(1, 0), (2, 0), (3, 0)],
    }

    kept, rejected, unresolved = screen_css_results_with_deferred_cache(
        [base, shifted],
        cache_dir=tmp_path / "cache",
        max_workers=2,
        hard_timeout=60,
    )

    assert len(kept) == 1
    assert len(rejected) == 1
    assert unresolved == []
    audit = rejected[0]["structural_novelty"]
    assert audit["relation"] == (
        "within_run_css_tanner_permutation_equivalent"
    )
    assert audit["explicit_isomorphism"]["verified"] is True
    assert audit["explicit_isomorphism"]["hx_preserved"] is True
    assert audit["explicit_isomorphism"]["hz_preserved"] is True


def test_annotation_api_has_no_unbounded_within_pool_replay(
    tmp_path,
    monkeypatch,
):
    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        lambda tasks, **_kwargs: (
            {index: _novel_annotation() for index, _row in tasks},
            {},
        ),
    )
    monkeypatch.setattr(
        structural_dedup,
        "deduplicate_annotated_css_results",
        lambda _rows: (_ for _ in ()).throw(
            AssertionError("annotation API entered unbounded pool replay")
        ),
    )
    rows = [_cached_candidate(), {**_cached_candidate(), "label": "second"}]

    annotated, unresolved = annotate_css_results_with_deferred_cache(
        rows,
        cache_dir=tmp_path / "cache",
        max_workers=2,
        hard_timeout=1,
    )

    assert [row.get("label") for row in annotated] == [None, "second"]
    assert unresolved == []


def test_within_pool_timeout_is_cached_retryable_and_never_rejected(
    tmp_path,
    monkeypatch,
):
    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        lambda tasks, **_kwargs: (
            {index: _novel_annotation() for index, _row in tasks},
            {},
        ),
    )
    attempts = 0

    def timeout_then_complete(
        tasks,
        *,
        on_unresolved=None,
        **_kwargs,
    ):
        nonlocal attempts
        attempts += 1
        index = tasks[0][0]
        if attempts == 1:
            failure = {
                "kind": "hard_timeout",
                "hard_timeout_seconds": 1.0,
                "retryable": True,
            }
            if on_unresolved is not None:
                on_unresolved(index, failure)
            return {}, {index: failure}
        return {index: _identity_pair_replay()}, {}

    monkeypatch.setattr(
        structural_dedup,
        "_run_isomorphism_workers",
        timeout_then_complete,
    )
    first = _cached_candidate()
    second = {**_cached_candidate(), "label": "duplicate"}
    cache = tmp_path / "cache"

    kept, rejected, unresolved = screen_css_results_with_deferred_cache(
        [first, second],
        cache_dir=cache,
        max_workers=2,
        hard_timeout=1,
    )

    assert [row.get("label") for row in kept] == [None]
    assert rejected == []
    assert len(unresolved) == 1
    assert unresolved[0]["operation"] == "within_pool_isomorphism"
    assert unresolved[0]["candidate_index"] == 1
    assert unresolved[0]["representative_index"] == 0
    assert unresolved[0]["failure"]["kind"] == "hard_timeout"
    pair_entry_path = next(
        (cache / "within-pool-isomorphism-v1").rglob("*.json")
    )
    pair_entry = json.loads(pair_entry_path.read_text())
    assert pair_entry["status"] == "unresolved"
    assert pair_entry["attempt_count"] == 1

    kept, rejected, unresolved = screen_css_results_with_deferred_cache(
        [first, second],
        cache_dir=cache,
        max_workers=2,
        hard_timeout=1,
    )

    assert [row.get("label") for row in kept] == [None]
    assert [row.get("label") for row in rejected] == ["duplicate"]
    assert unresolved == []
    audit = rejected[0]["structural_novelty"]
    assert audit["relation"] == (
        "within_run_css_tanner_permutation_equivalent"
    )
    assert audit["explicit_isomorphism"]["verified"] is True
    pair_entry = json.loads(pair_entry_path.read_text())
    assert pair_entry["status"] == "complete"
    assert pair_entry["attempt_count"] == 2

    monkeypatch.setattr(
        structural_dedup,
        "_run_isomorphism_workers",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("completed pair cache was recomputed")
        ),
    )
    replayed_kept, replayed_rejected, replayed_unresolved = (
        screen_css_results_with_deferred_cache(
            [first, second],
            cache_dir=cache,
            max_workers=1,
            hard_timeout=1,
        )
    )
    assert replayed_kept == kept
    assert replayed_rejected == rejected
    assert replayed_unresolved == []


def test_within_pool_worker_has_killable_hard_wall_timeout():
    row = _cached_candidate()
    completed, unresolved = structural_dedup._run_isomorphism_workers(
        [(1, {"candidate": row, "representative": row})],
        max_workers=1,
        hard_timeout=1e-9,
    )
    assert completed == {}
    assert unresolved[1]["retryable"] is True
    assert unresolved[1]["kind"] in {"hard_timeout", "worker_exit"}


def test_within_pool_cache_rejects_self_sealed_invalid_mapping(
    tmp_path,
    monkeypatch,
):
    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        lambda tasks, **_kwargs: (
            {index: _novel_annotation() for index, _row in tasks},
            {},
        ),
    )
    monkeypatch.setattr(
        structural_dedup,
        "_run_isomorphism_workers",
        lambda tasks, **_kwargs: (
            {tasks[0][0]: _identity_pair_replay()},
            {},
        ),
    )
    rows = [
        _cached_candidate(),
        {**_cached_candidate(), "label": "duplicate"},
    ]
    cache = tmp_path / "cache"
    screen_css_results_with_deferred_cache(
        rows,
        cache_dir=cache,
        max_workers=1,
        hard_timeout=1,
    )
    path = next(
        (cache / "within-pool-isomorphism-v1").rglob("*.json")
    )
    entry = json.loads(path.read_text())
    entry["replay"]["qubit_permutation"][0] = 1
    entry["seal_sha256"] = structural_dedup._cache_entry_seal(entry)
    path.write_text(json.dumps(entry))

    with pytest.raises(
        StructuralScreenCacheError,
        match="violates color partitions",
    ):
        screen_css_results_with_deferred_cache(
            rows,
            cache_dir=cache,
            max_workers=1,
            hard_timeout=1,
        )


def test_screen_wrapper_never_calls_parent_process_pair_replay(
    tmp_path,
    monkeypatch,
):
    monkeypatch.setattr(
        structural_dedup,
        "_run_annotation_workers",
        lambda tasks, **_kwargs: (
            {index: _novel_annotation() for index, _row in tasks},
            {},
        ),
    )
    monkeypatch.setattr(
        structural_dedup,
        "deduplicate_annotated_css_results",
        lambda _rows: (_ for _ in ()).throw(
            AssertionError("screen wrapper entered parent-process replay")
        ),
    )

    kept, rejected, unresolved = screen_css_results_with_deferred_cache(
        [_cached_candidate()],
        cache_dir=tmp_path / "cache",
        max_workers=1,
        hard_timeout=1,
    )

    assert len(kept) == 1
    assert rejected == []
    assert unresolved == []
