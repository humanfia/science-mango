from __future__ import annotations

import argparse
import copy
import json
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pytest

from evaluation.target_policy import TARGET_MODE_SCALAR_13_INCLUSIVE
from scripts import merge_distqldpc_stage3 as merge


CANONICAL_DIGEST = "1" * 64
MTO_EVIDENCE_SHA256 = "8" * 64
UPPER_EVIDENCE_SHA256 = "9" * 64
UPPER_OPERATOR_SHA256 = "a" * 64


def _arguments(
    *,
    candidate: Path,
    mto: Path,
    upper: Path,
    output_root: Path,
    check_only: bool,
) -> argparse.Namespace:
    return argparse.Namespace(
        candidate=None,
        stage2_ranked=candidate,
        candidate_index=0,
        expected_canonical_digest=CANONICAL_DIGEST,
        mto_checkpoint=mto,
        anchored_upper_checkpoint=upper,
        output_root=output_root,
        cardinality_mode="mto",
        coverage_mode="first-nonzero",
        target_mode=TARGET_MODE_SCALAR_13_INCLUSIVE,
        check_only=check_only,
    )


def _write_inputs(tmp_path: Path) -> tuple[Path, Path, Path]:
    candidate = tmp_path / "stage2-ranked.jsonl"
    mto = tmp_path / "mto.json"
    upper = tmp_path / "upper.json"
    candidate.write_text("{}\n", encoding="utf-8")
    mto.write_text(
        json.dumps({
            "evidence_sha256": MTO_EVIDENCE_SHA256,
            "exact_distance": 16,
        }),
        encoding="utf-8",
    )
    upper.write_text(
        json.dumps({
            "evidence_sha256": UPPER_EVIDENCE_SHA256,
            "operator": {"sha256": UPPER_OPERATOR_SHA256},
            "objective": 16,
        }),
        encoding="utf-8",
    )
    return candidate, mto, upper


def _patch_verified_boundaries(
    monkeypatch: pytest.MonkeyPatch,
    *,
    candidate_path: Path,
) -> tuple[dict[str, Any], dict[str, str]]:
    candidate = {
        "canonical_digest": CANONICAL_DIGEST,
        "required_distance": 16,
        "target_mode": TARGET_MODE_SCALAR_13_INCLUSIVE,
    }
    candidate_input = {
        "kind": "stage2-ranked",
        "path": str(candidate_path.resolve()),
        "file_sha256": merge._file_sha256(candidate_path),
        "row_index": 0,
        "row_sha256": "2" * 64,
        "rows": 1,
    }
    context = {
        "geometry": {"n": 2, "k": 1},
        "matrices": tuple(
            np.zeros((1, 2), dtype=np.uint8) for _ in range(4)
        ),
        "detector": {"report_sha256": "3" * 64},
        "symmetry": {
            "verified": True,
            "orbit_representatives": [0],
        },
        "isometry": {"report_sha256": "4" * 64},
        "anchors": (0,),
        "anchor_cover_cubes": [{"cube_sha256": "5" * 64}],
        "plan": [
            ("lower-distqldpc-mto", "XZ", None, None),
            ("upper", "X", None, None),
        ],
        "matrix_binding": {"Hx": {"shape": [1, 2]}},
    }
    runtime = {
        "schema_version": 2,
        "python": {"sealed": True},
        "packages": {"sealed": True},
        "package_artifacts": {"sealed": True},
        "interpreter": {"sealed": True},
    }
    source_files = {
        "scripts/merge_distqldpc_stage3.py": "6" * 64,
        "evaluation/distance_distqldpc.py": "7" * 64,
    }

    def candidate_from_input(
        path: Path,
        *,
        index: int,
        stage2_ranked: bool,
        target_mode: str,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        assert path == candidate_path.resolve()
        assert index == 0
        assert stage2_ranked is True
        assert target_mode == TARGET_MODE_SCALAR_13_INCLUSIVE
        return copy.deepcopy(candidate), copy.deepcopy(candidate_input)

    def fresh_context(
        supplied: dict[str, Any],
        *,
        expected_digest: str | None,
        coverage_mode: str,
    ) -> dict[str, Any]:
        assert supplied == candidate
        assert expected_digest == CANONICAL_DIGEST
        assert coverage_mode == "first-nonzero"
        return copy.deepcopy(context)

    def verify_distqldpc(
        evidence: dict[str, Any],
        *_args: Any,
        **_kwargs: Any,
    ) -> dict[str, str]:
        if (
            evidence.get("evidence_sha256") != MTO_EVIDENCE_SHA256
            or evidence.get("exact_distance") != 16
        ):
            raise ValueError("MTO evidence binding mismatch")
        return {"checkpoint": "fresh"}

    def verify_upper(
        evidence: dict[str, Any],
        *_args: Any,
        **_kwargs: Any,
    ) -> None:
        operator = evidence.get("operator")
        if (
            evidence.get("evidence_sha256") != UPPER_EVIDENCE_SHA256
            or evidence.get("objective") != 16
            or not isinstance(operator, dict)
            or operator.get("sha256") != UPPER_OPERATOR_SHA256
        ):
            raise ValueError("upper evidence binding mismatch")

    def artifact(
        supplied: dict[str, Any],
        **kwargs: Any,
    ) -> dict[str, Any]:
        assert supplied == candidate
        assert kwargs["lower_backend"] == "distqldpc"
        value = {
            "status": "EXACT_PROVEN",
            "lower_bound_backend": "distqldpc",
            "distqldpc_exact_distances": [16],
        }
        value["artifact_sha256"] = merge._canonical_sha256(value)
        return value

    def claim_from_artifact(value: dict[str, Any]) -> dict[str, Any]:
        return {
            merge.SECTOR_REQUEST_FIELD: {
                "stage3_status": "EXACT_PROVEN",
                "lower_bound_backend": "distqldpc",
                "stage3_artifact_sha256": merge._canonical_sha256(value),
            },
        }

    monkeypatch.setattr(merge, "_candidate_from_input", candidate_from_input)
    monkeypatch.setattr(merge, "_fresh_context", fresh_context)
    monkeypatch.setattr(merge, "_verify_distqldpc", verify_distqldpc)
    monkeypatch.setattr(merge, "_verify_upper", verify_upper)
    monkeypatch.setattr(merge, "_artifact", artifact)
    monkeypatch.setattr(
        merge,
        "claim_from_sector_sat_artifact",
        claim_from_artifact,
    )
    monkeypatch.setattr(
        merge,
        "proof_runtime_fingerprint",
        lambda: copy.deepcopy(runtime),
    )
    monkeypatch.setattr(
        merge,
        "validate_proof_runtime_fingerprint",
        lambda value: copy.deepcopy(value),
    )
    monkeypatch.setattr(
        merge,
        "_loaded_project_source_hashes",
        lambda: copy.deepcopy(source_files),
    )
    return runtime, source_files


def test_sourcebound_check_only_and_complete_manifest(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate, mto, upper = _write_inputs(tmp_path)
    output_root = tmp_path / "merged"
    runtime, source_files = _patch_verified_boundaries(
        monkeypatch,
        candidate_path=candidate,
    )
    sealed_argv = [
        "scripts/merge_distqldpc_stage3.py",
        "--stage2-ranked",
        str(candidate),
        "--output-root",
        str(output_root),
    ]
    monkeypatch.setattr(sys, "argv", sealed_argv)
    args = _arguments(
        candidate=candidate,
        mto=mto,
        upper=upper,
        output_root=output_root,
        check_only=True,
    )

    checked = merge._run(args)
    assert checked["status"] == "CHECKED"
    assert checked["solver_invoked"] is False
    assert not output_root.exists()

    args.check_only = False
    complete = merge._run(args)
    assert complete["status"] == "COMPLETE"
    assert complete["solver_invoked"] is False
    manifest_path = output_root / "input/merge-handoff.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest["solver_invoked"] is False
    assert manifest["source_provenance"]["argv"] == sealed_argv
    assert manifest["source_provenance"]["source_files"] == source_files
    assert manifest["source_provenance"]["proof_runtime"] == runtime
    assert manifest["candidate_input"]["file_sha256"] == merge._file_sha256(
        candidate,
    )
    assert manifest["mto"]["file_sha256"] == merge._file_sha256(mto)
    assert manifest["mto"]["evidence_sha256"] == MTO_EVIDENCE_SHA256
    assert manifest["mto"]["exact_distance"] == 16
    assert manifest["anchored_upper"]["file_sha256"] == merge._file_sha256(
        upper,
    )
    assert manifest["anchored_upper"]["evidence_sha256"] == (
        UPPER_EVIDENCE_SHA256
    )
    assert manifest["anchored_upper"]["operator_sha256"] == (
        UPPER_OPERATOR_SHA256
    )
    assert manifest["anchored_upper"]["objective"] == 16
    assert manifest["manifest_sha256"] == merge._canonical_sha256(
        manifest,
        omit="manifest_sha256",
    )

    with pytest.raises(ValueError, match="output root already exists"):
        merge._run(args)


@pytest.mark.parametrize("target", ["mto", "upper"])
def test_sourcebound_merge_rejects_key_hash_tampering(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    target: str,
) -> None:
    candidate, mto, upper = _write_inputs(tmp_path)
    _patch_verified_boundaries(monkeypatch, candidate_path=candidate)
    path = mto if target == "mto" else upper
    value = json.loads(path.read_text(encoding="utf-8"))
    if target == "mto":
        value["evidence_sha256"] = "0" * 64
        expected = "MTO evidence binding mismatch"
    else:
        value["operator"]["sha256"] = "0" * 64
        expected = "upper evidence binding mismatch"
    path.write_text(json.dumps(value), encoding="utf-8")

    with pytest.raises(ValueError, match=expected):
        merge._run(
            _arguments(
                candidate=candidate,
                mto=mto,
                upper=upper,
                output_root=tmp_path / "merged",
                check_only=True,
            ),
        )
