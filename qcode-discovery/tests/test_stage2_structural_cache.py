from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from evaluation import structural_dedup as structural
from scripts import audit_candidate_pool as candidate_pool
from scripts import stage2_structural_cache as packed_cache

RUNTIME_A = "a" * 64
RUNTIME_B = "b" * 64


def _row(marker: int = 0) -> dict:
    return {
        "source": f"candidate-{marker}",
        "ell": 3,
        "m": 3,
        "A_terms": [[0, 0], [1 + marker, 0]],
        "B_terms": [[0, 0], [0, 1]],
    }


def _annotation(
    *,
    n: int = 18,
    k: int = 2,
    reported_checks: bool = False,
) -> dict:
    checks = {
        "candidate_rebuild": True,
        "css_commutation": True,
    }
    if reported_checks:
        checks.update(
            {
                "reported_n_matches": True,
                "reported_k_matches": True,
            }
        )
    return {
        "static_eligibility": {
            "checked": True,
            "eligible": True,
            "checks": checks,
            "failures": [],
            "n": n,
            "k": k,
        },
        "structural_novelty": {
            "checked": True,
            "novel": True,
            "relation": None,
            "canonical_digest": "c" * 64,
            "matched_reference": None,
            "reference_digest": None,
            "explicit_isomorphism": None,
        },
        "structural_rejection": None,
    }


def _input_file(tmp_path: Path) -> Path:
    path = tmp_path / "candidate-batch.jsonl"
    path.write_text("{}\n")
    return path


def _annotation_binding(row: dict) -> tuple[dict, str]:
    screen_input = structural._normalized_screen_input(row)
    return screen_input, packed_cache._sha256_json(screen_input)


def _write_v1_annotation(
    cache_dir: Path,
    row: dict,
    *,
    runtime: str,
    annotation: dict | None = None,
) -> Path:
    screen_input, input_sha256 = _annotation_binding(row)
    path = cache_dir / input_sha256[:2] / f"{input_sha256}.json"
    structural._write_cache_entry(
        path,
        screen_input=screen_input,
        input_sha256=input_sha256,
        runtime_sha256=runtime,
        status="complete",
        annotation=annotation or _annotation(),
        failure=None,
        attempt_count=1,
    )
    return path


def _read_v1_annotation(
    cache_dir: Path,
    row: dict,
    *,
    runtime: str,
):
    screen_input, input_sha256 = _annotation_binding(row)
    path = cache_dir / input_sha256[:2] / f"{input_sha256}.json"
    return structural._read_cache_entry(
        path,
        screen_input=screen_input,
        input_sha256=input_sha256,
        runtime_sha256=runtime,
    )


def test_pack_round_trip_is_manifest_last_and_does_not_write_v1(tmp_path):
    input_path = _input_file(tmp_path)
    cache_dir = tmp_path / "cache"
    row = _row()
    screen_input, input_sha256 = _annotation_binding(row)
    v1_path = cache_dir / input_sha256[:2] / f"{input_sha256}.json"

    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
        chunk_rows=1,
    ):
        structural._write_cache_entry(
            v1_path,
            screen_input=screen_input,
            input_sha256=input_sha256,
            runtime_sha256=RUNTIME_A,
            status="complete",
            annotation=_annotation(),
            failure=None,
            attempt_count=1,
        )

    assert not v1_path.exists()
    manifest_path = cache_dir / packed_cache.PACK_DIRECTORY / packed_cache.PACK_MANIFEST
    manifest = json.loads(manifest_path.read_text())
    assert manifest["record_count"] == 1
    assert manifest["manifest_sha256"] == packed_cache._manifest_seal(manifest)
    assert (
        manifest["adapter_source_sha256"]
        == hashlib.sha256(Path(packed_cache.__file__).read_bytes()).hexdigest()
    )

    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
    ):
        restored = _read_v1_annotation(cache_dir, row, runtime=RUNTIME_A)
    assert restored is not None
    assert restored["annotation"] == _annotation()


def test_flushed_shard_is_immediately_readable_and_not_duplicated(tmp_path):
    input_path = _input_file(tmp_path)
    cache_dir = tmp_path / "cache"
    row = _row()
    screen_input, input_sha256 = _annotation_binding(row)
    path = cache_dir / input_sha256[:2] / f"{input_sha256}.json"

    def write_entry() -> None:
        structural._write_cache_entry(
            path,
            screen_input=screen_input,
            input_sha256=input_sha256,
            runtime_sha256=RUNTIME_A,
            status="complete",
            annotation=_annotation(),
            failure=None,
            attempt_count=1,
        )

    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
        chunk_rows=1,
    ):
        write_entry()
        assert _read_v1_annotation(cache_dir, row, runtime=RUNTIME_A)
        write_entry()

    manifest_path = cache_dir / packed_cache.PACK_DIRECTORY / packed_cache.PACK_MANIFEST
    manifest = json.loads(manifest_path.read_text())
    assert manifest["record_count"] == 1
    assert len(manifest["chunks"]) == 1
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
    ):
        assert _read_v1_annotation(cache_dir, row, runtime=RUNTIME_A)


def test_shard_replacement_after_manifest_load_fails_closed(tmp_path):
    input_path = _input_file(tmp_path)
    cache_dir = tmp_path / "cache"
    row = _row()
    screen_input, input_sha256 = _annotation_binding(row)
    path = cache_dir / input_sha256[:2] / f"{input_sha256}.json"
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
        chunk_rows=1,
    ):
        structural._write_cache_entry(
            path,
            screen_input=screen_input,
            input_sha256=input_sha256,
            runtime_sha256=RUNTIME_A,
            status="complete",
            annotation=_annotation(),
            failure=None,
            attempt_count=1,
        )

    pack_dir = cache_dir / packed_cache.PACK_DIRECTORY
    manifest = json.loads((pack_dir / packed_cache.PACK_MANIFEST).read_text())
    shard = pack_dir / "shards" / manifest["chunks"][0]["name"]
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
    ):
        original = shard.read_bytes()
        replacement = original.replace(b'"stage2_computed"', b'"stage2_xomputed"', 1)
        assert replacement != original
        assert len(replacement) == len(original)
        shard.write_bytes(replacement)
        with pytest.raises(
            packed_cache.Stage2StructuralPackError,
            match="changed after manifest load",
        ):
            _read_v1_annotation(cache_dir, row, runtime=RUNTIME_A)


def test_existing_v1_import_then_pack_hit_needs_no_annotation_worker(
    tmp_path, monkeypatch
):
    input_path = _input_file(tmp_path)
    cache_dir = tmp_path / "cache"
    row = _row()
    runtime = structural.structural_screen_runtime_fingerprint()["sha256"]
    v1_path = _write_v1_annotation(cache_dir, row, runtime=runtime)

    def no_worker(*_args, **_kwargs):
        raise AssertionError("annotation worker must not run on a cache hit")

    monkeypatch.setattr(structural, "_run_annotation_workers", no_worker)
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=runtime,
        input_paths=[input_path],
        stage1_aliases={},
        chunk_rows=1,
    ):
        kept, rejected, unresolved = structural.screen_css_results_with_deferred_cache(
            [row], cache_dir=cache_dir, max_workers=1, hard_timeout=1
        )
    assert len(kept) == 1
    assert not rejected
    assert not unresolved

    v1_path.unlink()
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=runtime,
        input_paths=[input_path],
        stage1_aliases={},
    ):
        kept_again, rejected_again, unresolved_again = (
            structural.screen_css_results_with_deferred_cache(
                [row], cache_dir=cache_dir, max_workers=1, hard_timeout=1
            )
        )
    assert kept_again == kept
    assert rejected_again == rejected
    assert unresolved_again == unresolved


def test_current_pack_tamper_fails_closed_but_stale_runtime_ignores_shard(
    tmp_path,
):
    input_path = _input_file(tmp_path)
    cache_dir = tmp_path / "cache"
    row = _row()
    screen_input, input_sha256 = _annotation_binding(row)
    path = cache_dir / input_sha256[:2] / f"{input_sha256}.json"
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
        chunk_rows=1,
    ):
        structural._write_cache_entry(
            path,
            screen_input=screen_input,
            input_sha256=input_sha256,
            runtime_sha256=RUNTIME_A,
            status="complete",
            annotation=_annotation(),
            failure=None,
            attempt_count=1,
        )

    pack_dir = cache_dir / packed_cache.PACK_DIRECTORY
    manifest = json.loads((pack_dir / packed_cache.PACK_MANIFEST).read_text())
    shard = pack_dir / "shards" / manifest["chunks"][0]["name"]
    payload = bytearray(shard.read_bytes())
    payload[0] ^= 1
    shard.write_bytes(payload)

    # A clean manifest for another runtime is stale and its shards are ignored.
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_B,
        input_paths=[input_path],
        stage1_aliases={},
    ):
        pass

    with pytest.raises(packed_cache.Stage2StructuralPackError):
        with packed_cache.packed_structural_cache(
            cache_dir=cache_dir,
            runtime_sha256=RUNTIME_A,
            input_paths=[input_path],
            stage1_aliases={},
        ):
            pass


def test_full_shard_survives_interruption_and_partial_batch_is_ignored(
    tmp_path,
):
    input_path = _input_file(tmp_path)
    cache_dir = tmp_path / "cache"
    rows = [_row(index) for index in range(3)]
    with pytest.raises(RuntimeError, match="simulated interruption"):
        with packed_cache.packed_structural_cache(
            cache_dir=cache_dir,
            runtime_sha256=RUNTIME_A,
            input_paths=[input_path],
            stage1_aliases={},
            chunk_rows=2,
        ):
            for index, row in enumerate(rows):
                screen_input, input_sha256 = _annotation_binding(row)
                structural._write_cache_entry(
                    cache_dir / input_sha256[:2] / f"{input_sha256}.json",
                    screen_input=screen_input,
                    input_sha256=input_sha256,
                    runtime_sha256=RUNTIME_A,
                    status="complete",
                    annotation=_annotation(),
                    failure=None,
                    attempt_count=1,
                )
                if index == 2:
                    raise RuntimeError("simulated interruption")

    manifest = json.loads(
        (
            cache_dir / packed_cache.PACK_DIRECTORY / packed_cache.PACK_MANIFEST
        ).read_text()
    )
    assert manifest["record_count"] == 2
    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
    ):
        assert _read_v1_annotation(cache_dir, rows[0], runtime=RUNTIME_A)
        assert _read_v1_annotation(cache_dir, rows[1], runtime=RUNTIME_A)
        assert _read_v1_annotation(cache_dir, rows[2], runtime=RUNTIME_A) is None


def test_unmanifested_orphan_shard_is_ignored(tmp_path):
    input_path = _input_file(tmp_path)
    cache_dir = tmp_path / "cache"
    shards = cache_dir / packed_cache.PACK_DIRECTORY / "shards"
    shards.mkdir(parents=True)
    payload = b"interrupted shard\n"
    digest = hashlib.sha256(payload).hexdigest()
    orphan = shards / f"{digest}.jsonl"
    orphan.write_bytes(payload)

    with packed_cache.packed_structural_cache(
        cache_dir=cache_dir,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases={},
    ):
        pass
    assert orphan.read_bytes() == payload
    assert not (
        cache_dir / packed_cache.PACK_DIRECTORY / packed_cache.PACK_MANIFEST
    ).exists()


def _stage1_layout(tmp_path: Path) -> tuple[Path, Path]:
    run_root = tmp_path / "run"
    candidate_batch = run_root / "rounds" / "round-001" / "candidate-batch.jsonl"
    candidate_batch.parent.mkdir(parents=True)
    candidate_batch.write_text("{}\n")
    return candidate_batch, run_root / "structural-screen-cache-v1"


def _write_stage1_alias(
    stage1_cache: Path,
    alias: dict,
    *,
    annotation: dict,
) -> None:
    alias_sha256 = packed_cache._sha256_json(alias)
    structural._write_cache_entry(
        stage1_cache / alias_sha256[:2] / f"{alias_sha256}.json",
        screen_input=alias,
        input_sha256=alias_sha256,
        runtime_sha256=RUNTIME_A,
        status="complete",
        annotation=annotation,
        failure=None,
        attempt_count=1,
    )


def test_stage1_derivation_is_opt_in_and_removes_only_true_report_checks(
    tmp_path,
):
    input_path, stage1_cache = _stage1_layout(tmp_path)
    row = _row()
    target, target_sha256 = _annotation_binding(row)
    aliases = packed_cache.make_stage1_annotation_aliases([row], [(18, 2)])
    alias = aliases[target_sha256][0]
    _write_stage1_alias(
        stage1_cache,
        alias,
        annotation=_annotation(reported_checks=True),
    )
    stage2_cache = tmp_path / "stage2-cache"
    target_path = stage2_cache / target_sha256[:2] / f"{target_sha256}.json"

    with packed_cache.packed_structural_cache(
        cache_dir=stage2_cache,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases=aliases,
    ):
        assert (
            structural._read_cache_entry(
                target_path,
                screen_input=target,
                input_sha256=target_sha256,
                runtime_sha256=RUNTIME_A,
            )
            is None
        )

    with packed_cache.packed_structural_cache(
        cache_dir=tmp_path / "enabled-stage2-cache",
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases=aliases,
        enable_stage1_import=True,
        chunk_rows=1,
    ):
        derived = structural._read_cache_entry(
            tmp_path / "missing-v1" / f"{target_sha256}.json",
            screen_input=target,
            input_sha256=target_sha256,
            runtime_sha256=RUNTIME_A,
        )
    assert derived is not None
    checks = derived["annotation"]["static_eligibility"]["checks"]
    assert checks == {
        "candidate_rebuild": True,
        "css_commutation": True,
    }


def test_stage1_derivation_rejects_reported_parameter_mismatch(tmp_path):
    input_path, stage1_cache = _stage1_layout(tmp_path)
    row = _row()
    target, target_sha256 = _annotation_binding(row)
    aliases = packed_cache.make_stage1_annotation_aliases([row], [(18, 2)])
    _write_stage1_alias(
        stage1_cache,
        aliases[target_sha256][0],
        annotation=_annotation(n=20, k=2, reported_checks=True),
    )
    stage2_cache = tmp_path / "stage2-cache"
    with packed_cache.packed_structural_cache(
        cache_dir=stage2_cache,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases=aliases,
        enable_stage1_import=True,
    ):
        assert (
            structural._read_cache_entry(
                stage2_cache / target_sha256[:2] / f"{target_sha256}.json",
                screen_input=target,
                input_sha256=target_sha256,
                runtime_sha256=RUNTIME_A,
            )
            is None
        )


def test_stage1_pair_import_requires_exact_ordered_alias(tmp_path):
    input_path, stage1_cache = _stage1_layout(tmp_path)
    candidate = structural._normalized_screen_input(_row(0))
    representative = structural._normalized_screen_input(_row(1))
    aliases = packed_cache.make_stage1_annotation_aliases(
        [_row(0), _row(1)], [(18, 2), (18, 2)]
    )
    pair_input = {
        "candidate": candidate,
        "representative": representative,
        "recomputed_n": 18,
        "recomputed_k": 2,
        "recomputed_x_checks": 9,
        "recomputed_z_checks": 9,
        "canonical_digest": "d" * 64,
    }
    alias_pair = copy.deepcopy(pair_input)
    alias_pair["candidate"] = aliases[packed_cache._sha256_json(candidate)][0]
    alias_pair["representative"] = aliases[packed_cache._sha256_json(representative)][0]
    alias_sha256 = packed_cache._sha256_json(alias_pair)
    replay = {
        "verified": True,
        "hx_preserved": True,
        "hz_preserved": True,
        "qubit_permutation": list(range(18)),
        "x_check_permutation": list(range(9)),
        "z_check_permutation": list(range(9)),
    }
    structural._write_pair_cache_entry(
        stage1_cache
        / "within-pool-isomorphism-v1"
        / alias_sha256[:2]
        / f"{alias_sha256}.json",
        pair_input=alias_pair,
        input_sha256=alias_sha256,
        runtime_sha256=RUNTIME_A,
        status="complete",
        replay=replay,
        failure=None,
        attempt_count=1,
    )

    stage2_cache = tmp_path / "stage2-cache"
    target_sha256 = packed_cache._sha256_json(pair_input)
    with packed_cache.packed_structural_cache(
        cache_dir=stage2_cache,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases=aliases,
        enable_stage1_import=True,
    ):
        derived = structural._read_pair_cache_entry(
            stage2_cache
            / "within-pool-isomorphism-v1"
            / target_sha256[:2]
            / f"{target_sha256}.json",
            pair_input=pair_input,
            input_sha256=target_sha256,
            runtime_sha256=RUNTIME_A,
        )
        swapped = copy.deepcopy(pair_input)
        swapped["candidate"], swapped["representative"] = (
            swapped["representative"],
            swapped["candidate"],
        )
        swapped_sha256 = packed_cache._sha256_json(swapped)
        assert (
            structural._read_pair_cache_entry(
                stage2_cache
                / "within-pool-isomorphism-v1"
                / swapped_sha256[:2]
                / f"{swapped_sha256}.json",
                pair_input=swapped,
                input_sha256=swapped_sha256,
                runtime_sha256=RUNTIME_A,
            )
            is None
        )
    assert derived is not None
    assert derived["replay"] == replay


def test_stage1_pair_import_rejects_intermediate_symlink(tmp_path):
    input_path, stage1_cache = _stage1_layout(tmp_path)
    stage1_cache.mkdir(parents=True)
    outside = tmp_path / "outside-pair-cache"
    outside.mkdir()
    (stage1_cache / "within-pool-isomorphism-v1").symlink_to(
        outside, target_is_directory=True
    )
    candidate = structural._normalized_screen_input(_row(0))
    representative = structural._normalized_screen_input(_row(1))
    aliases = packed_cache.make_stage1_annotation_aliases(
        [_row(0), _row(1)], [(18, 2), (18, 2)]
    )
    pair_input = {
        "candidate": candidate,
        "representative": representative,
        "recomputed_n": 18,
        "recomputed_k": 2,
        "recomputed_x_checks": 9,
        "recomputed_z_checks": 9,
        "canonical_digest": "d" * 64,
    }
    target_sha256 = packed_cache._sha256_json(pair_input)
    stage2_cache = tmp_path / "stage2-cache"

    with packed_cache.packed_structural_cache(
        cache_dir=stage2_cache,
        runtime_sha256=RUNTIME_A,
        input_paths=[input_path],
        stage1_aliases=aliases,
        enable_stage1_import=True,
    ):
        with pytest.raises(
            packed_cache.Stage2StructuralPackError,
            match="path contains a symlink",
        ):
            structural._read_pair_cache_entry(
                stage2_cache
                / "within-pool-isomorphism-v1"
                / target_sha256[:2]
                / f"{target_sha256}.json",
                pair_input=pair_input,
                input_sha256=target_sha256,
                runtime_sha256=RUNTIME_A,
            )


def test_symlink_ancestor_fails_closed(tmp_path):
    input_path = _input_file(tmp_path)
    real = tmp_path / "real-cache"
    real.mkdir()
    linked = tmp_path / "linked-cache"
    linked.symlink_to(real, target_is_directory=True)
    with pytest.raises(packed_cache.Stage2StructuralPackError):
        with packed_cache.packed_structural_cache(
            cache_dir=linked,
            runtime_sha256=RUNTIME_A,
            input_paths=[input_path],
            stage1_aliases={},
        ):
            pass


def test_helper_bytes_participate_in_stage2_source_fingerprints(monkeypatch):
    certificate_before = candidate_pool.certificate_source_fingerprint()
    novelty_before = candidate_pool._novelty_source_fingerprint()
    original = Path.read_bytes

    def altered(path: Path):
        payload = original(path)
        if path.name == "stage2_structural_cache.py":
            return payload + b"changed"
        return payload

    monkeypatch.setattr(Path, "read_bytes", altered)
    assert candidate_pool.certificate_source_fingerprint() != certificate_before
    assert candidate_pool._novelty_source_fingerprint() != novelty_before
