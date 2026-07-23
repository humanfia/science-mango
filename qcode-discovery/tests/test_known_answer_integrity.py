"""Tests for pinned known-answer integrity modes."""

import json

from evaluation.known_answer_integrity import (
    check_fast,
    file_sha256,
    semantic_sha256,
)


def test_repository_pinned_known_answer_passes_fast_mode():
    result = check_fast(
        "results/known_answer_gate.json",
        "results/known_answer_trust.json",
    )
    assert result["passed"] is True


def test_fast_mode_rejects_tampered_artifact(tmp_path):
    source = json.loads(open("results/known_answer_gate.json").read())
    source["baselines"][0]["observed"]["d"] += 1
    artifact = tmp_path / "known.json"
    artifact.write_text(json.dumps(source))
    result = check_fast(artifact, "results/known_answer_trust.json")
    assert result["passed"] is False
    assert any("SHA-256" in failure for failure in result["failures"])


def test_semantic_hash_ignores_runtime_only_fields():
    artifact = json.loads(open("results/known_answer_gate.json").read())
    changed = json.loads(json.dumps(artifact))
    changed["generated_at"] = "different"
    changed["baselines"][0]["milp"]["time_s"] = 999999
    assert semantic_sha256(artifact) == semantic_sha256(changed)
    assert file_sha256("results/known_answer_gate.json")
