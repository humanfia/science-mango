from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from evaluation import cube_and_conquer_smoke_v1 as smoke


CADICAL = Path("/root/cadical-rel-1.9.5-standalone-audit/build/cadical")
DRAT_TRIM = Path("/root/qcode-proof-tools/bin/drat-trim")
LRAT_CHECK = Path("/root/qcode-proof-tools/bin/lrat-check")
TOY = b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"


def _require_tools() -> None:
    if not all(path.is_file() for path in (CADICAL, DRAT_TRIM, LRAT_CHECK)):
        pytest.skip("pinned proof toolchain is not installed")


def _write_toy(path: Path) -> None:
    path.write_bytes(TOY)


def _run(tmp_path: Path) -> Path:
    _require_tools()
    source = tmp_path / "toy.cnf"
    root = tmp_path / "bundle"
    _write_toy(source)
    aggregate = smoke.run_bundle(
        input_cnf=source,
        output_root=root,
        split_variables=(1, 2),
        workers=2,
        cadical=CADICAL,
        drat_trim=DRAT_TRIM,
        lrat_check=LRAT_CHECK,
        timeout_s=10,
    )
    assert aggregate["classification"] == smoke.CLASSIFICATION
    return root


def test_binary_tree_replay_is_exact_disjoint_and_exhaustive() -> None:
    tree, generated = smoke.build_split_tree((1, 2))
    replay = smoke.replay_split_tree(tree, num_variables=2)
    assert replay["valid"] is True
    assert replay["mutually_exclusive"] is True
    assert replay["exhaustive"] is True
    assert replay["leaf_count"] == 4
    assert replay["pair_count_checked"] == 6
    assert replay["leaves"] == generated
    assert [leaf["assumptions"] for leaf in generated] == [
        [-1, -2], [-1, 2], [1, -2], [1, 2]
    ]


def test_two_worker_end_to_end_proofs_and_fresh_replay(tmp_path: Path) -> None:
    root = _run(tmp_path)
    cover = json.loads((root / "cover.json").read_text(encoding="utf-8"))
    assert cover["execution"] == {
        "workers": 2,
        "model": "independent-single-process-leaf-solvers-v1",
        "clause_sharing": False,
        "shared_proof_stream": False,
    }
    commits = sorted((root / "leaves").glob("*/COMMIT.json"))
    assert len(commits) == 4
    solver_pids = {
        json.loads(path.read_text(encoding="utf-8"))["solver"]["pid"]
        for path in commits
    }
    assert len(solver_pids) == 4
    verification = smoke.verify_bundle(
        root,
        cadical=CADICAL,
        drat_trim=DRAT_TRIM,
        lrat_check=LRAT_CHECK,
        timeout_s=10,
        report_path=Path("verification.json"),
    )
    assert verification["fresh_aggregate_replay_equal"] is True
    assert verification["classification"] == smoke.CLASSIFICATION


def test_missing_leaf_certificate_fails_closed(tmp_path: Path) -> None:
    root = _run(tmp_path)
    (root / "leaves" / "leaf-0002" / "COMMIT.json").unlink()
    with pytest.raises(smoke.CubeAndConquerSmokeError, match="missing or extra"):
        smoke.compute_aggregate(
            root,
            cadical=CADICAL,
            drat_trim=DRAT_TRIM,
            lrat_check=LRAT_CHECK,
            timeout_s=10,
        )


def test_resealed_bad_tree_and_proof_tamper_fail_closed(tmp_path: Path) -> None:
    root = _run(tmp_path)
    cover_path = root / "cover.json"
    cover = json.loads(cover_path.read_text(encoding="utf-8"))
    changed = copy.deepcopy(cover)
    changed["tree"]["nodes"][0]["true_child"] = changed["tree"]["nodes"][0]["false_child"]
    changed = smoke.seal(changed, "manifest_sha256")
    cover_path.write_text(json.dumps(changed, sort_keys=True), encoding="utf-8")
    with pytest.raises(smoke.CubeAndConquerSmokeError, match="share a child"):
        smoke.compute_aggregate(
            root,
            cadical=CADICAL,
            drat_trim=DRAT_TRIM,
            lrat_check=LRAT_CHECK,
            timeout_s=10,
        )

    cover_path.write_text(json.dumps(cover, sort_keys=True), encoding="utf-8")
    proof = root / "leaves" / "leaf-0000" / "proof.drat"
    tampered = bytearray(proof.read_bytes())
    tampered[-1] ^= 1
    proof.write_bytes(tampered)
    with pytest.raises(smoke.CubeAndConquerSmokeError, match="SHA-256 mismatch"):
        smoke.compute_aggregate(
            root,
            cadical=CADICAL,
            drat_trim=DRAT_TRIM,
            lrat_check=LRAT_CHECK,
            timeout_s=10,
        )
