"""Focused regressions for the two-lane Stage 2 evidence funnel."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import replace

import pytest

import scripts.audit_candidate_pool as candidate_pool


def _selected(*digests: str) -> list[dict]:
    return [
        {
            "source": f"candidate-{index}",
            "triage_identity": {"canonical_digest": digest},
        }
        for index, digest in enumerate(digests)
    ]


def _result(digest: str, status: str, **extra) -> dict:
    return {
        "canonical_digest": digest,
        "status": status,
        **extra,
    }


def _config(tmp_path, **overrides) -> candidate_pool.AuditConfig:
    values = {
        "state_dir": tmp_path,
        "solver_timeout_s": 600,
        "solver_workers": 4,
        "candidate_hard_timeout_s": 999,
        "resume": True,
        "certify": False,
    }
    values.update(overrides)
    return candidate_pool.AuditConfig(**values)


def test_adaptive_machine_policy_reallocates_without_oversubscription(tmp_path):
    config = _config(tmp_path)

    policy, cheap, cheap_workers = (
        candidate_pool._adaptive_stage2_machine_policy(
            config,
            candidate_workers=3,
            max_total_workers=12,
        )
    )

    assert cheap_workers == 12
    assert cheap.solver_workers == 1
    assert cheap.solver_timeout_s == 30
    assert cheap.candidate_hard_timeout_s is None
    assert cheap.resume is True
    assert policy["cheap_lane"] == {
        "candidate_workers": 12,
        "solver_workers_per_candidate": 1,
        "configured_solver_workers": 12,
        "solver_timeout_s": 30.0,
        "candidate_hard_timeout_s": 65.0,
    }
    assert policy["strong_lane"]["candidate_workers"] == 3
    assert policy["strong_lane"]["solver_workers_per_candidate"] == 4
    assert policy["strong_lane"]["candidate_hard_timeout_s"] == 999
    assert policy["pool_truncation"] is False
    assert policy["unknown_semantics"] == "fail_closed"
    assert policy["unknown_action"] == "escalate_to_strong_proof"
    assert policy["bp_osd_positive_credit"] is False
    assert policy["terminal_retry_conflict"] == "fail_closed"
    assert policy["retain_statuses"] == [
        "EXACT_PROVEN",
        "REJECTED",
        "THRESHOLD_PROVEN",
        "UNSUPPORTED",
    ]


def test_adaptive_escalates_only_retryable_results_and_restores_order(
    tmp_path,
    monkeypatch,
):
    selected = _selected(*"abcdef")
    cheap = [
        _result("a", "REJECTED", witness_weight=3),
        _result("b", "UNRESOLVED"),
        _result("c", "THRESHOLD_PROVEN"),
        _result("d", "ERROR", error="cheap worker failed"),
        _result("e", "UNSUPPORTED"),
        _result("f", "EXACT_PROVEN"),
    ]
    strong = [
        _result("b", "UNRESOLVED", retry_required=True),
        _result("d", "THRESHOLD_PROVEN"),
    ]
    calls: list[tuple[tuple[str, ...], candidate_pool.AuditConfig, int]] = []

    def managed(rows, config, *, candidate_workers):
        calls.append((
            tuple(
                row["triage_identity"]["canonical_digest"] for row in rows
            ),
            config,
            candidate_workers,
        ))
        return cheap if len(calls) == 1 else strong

    monkeypatch.setattr(candidate_pool, "audit_selected_candidates", managed)
    config = _config(tmp_path)

    merged, diagnostics = candidate_pool.audit_selected_candidates_adaptive(
        selected,
        config,
        candidate_workers=3,
        max_total_workers=12,
    )

    assert calls[0][0] == tuple("abcdef")
    assert calls[0][1].solver_workers == 1
    assert calls[0][1].solver_timeout_s == 30
    assert calls[0][1].candidate_hard_timeout_s is None
    assert calls[0][2] == 12
    assert calls[1] == (("b", "d"), config, 3)
    assert [item["canonical_digest"] for item in merged] == list("abcdef")
    assert [item["status"] for item in merged] == [
        "REJECTED",
        "UNRESOLVED",
        "THRESHOLD_PROVEN",
        "THRESHOLD_PROVEN",
        "UNSUPPORTED",
        "EXACT_PROVEN",
    ]
    assert merged[1]["retry_required"] is True
    assert diagnostics["cheap_status_counts"] == {
        "REJECTED": 1,
        "UNRESOLVED": 1,
        "THRESHOLD_PROVEN": 1,
        "ERROR": 1,
        "UNSUPPORTED": 1,
        "EXACT_PROVEN": 1,
    }
    assert diagnostics["strong_status_counts"] == {
        "UNRESOLVED": 1,
        "THRESHOLD_PROVEN": 1,
    }
    assert diagnostics["escalated_to_strong"] == 2
    assert diagnostics["retained_after_cheap"] == 4
    assert diagnostics["adaptive_machine_policy_sha256"] == (
        candidate_pool._json_sha256(diagnostics["machine_policy"])
    )
    assert diagnostics["escalated_digests_sha256"] == (
        candidate_pool._json_sha256({"canonical_digests": ["b", "d"]})
    )
    assert diagnostics[
        "unsupported_candidates_remain_globally_incomplete"
    ] == 1


@pytest.mark.parametrize(
    "bad_results",
    [
        [_result("a", "REJECTED")],
        [_result("b", "REJECTED"), _result("a", "REJECTED")],
        [_result("a", "REJECTED"), _result("c", "REJECTED")],
        [_result("a", "REJECTED"), _result("a", "REJECTED")],
    ],
)
def test_adaptive_rejects_incomplete_reordered_or_substituted_cheap_results(
    tmp_path,
    monkeypatch,
    bad_results,
):
    monkeypatch.setattr(
        candidate_pool,
        "audit_selected_candidates",
        lambda rows, config, *, candidate_workers: bad_results,
    )

    with pytest.raises(ValueError, match="do not exactly match managed work"):
        candidate_pool.audit_selected_candidates_adaptive(
            _selected("a", "b"),
            _config(tmp_path),
            candidate_workers=3,
            max_total_workers=12,
        )


def test_adaptive_rejects_incomplete_strong_results(tmp_path, monkeypatch):
    calls = 0

    def managed(rows, config, *, candidate_workers):
        nonlocal calls
        calls += 1
        if calls == 1:
            return [
                _result("a", "UNRESOLVED"),
                _result("b", "ERROR"),
            ]
        return [_result("a", "REJECTED")]

    monkeypatch.setattr(candidate_pool, "audit_selected_candidates", managed)

    with pytest.raises(ValueError, match="do not exactly match managed work"):
        candidate_pool.audit_selected_candidates_adaptive(
            _selected("a", "b"),
            _config(tmp_path),
            candidate_workers=3,
            max_total_workers=12,
        )


def test_adaptive_strong_unknown_is_never_promoted(tmp_path, monkeypatch):
    calls = 0

    def managed(rows, config, *, candidate_workers):
        nonlocal calls
        calls += 1
        if calls == 1:
            return [_result("a", "UNRESOLVED")]
        return [_result("a", "UNRESOLVED", retry_required=True)]

    monkeypatch.setattr(candidate_pool, "audit_selected_candidates", managed)
    merged, diagnostics = candidate_pool.audit_selected_candidates_adaptive(
        _selected("a"),
        _config(tmp_path),
        candidate_workers=3,
        max_total_workers=12,
    )

    assert merged == [
        _result("a", "UNRESOLVED", retry_required=True)
    ]
    assert diagnostics["final_status_counts"] == {"UNRESOLVED": 1}
    assert diagnostics["machine_policy"]["unknown_semantics"] == (
        "fail_closed"
    )


def test_adaptive_terminal_results_skip_the_strong_lane(tmp_path, monkeypatch):
    calls = 0

    def managed(rows, config, *, candidate_workers):
        nonlocal calls
        calls += 1
        return [
            _result("a", "REJECTED"),
            _result("b", "THRESHOLD_PROVEN"),
        ]

    monkeypatch.setattr(candidate_pool, "audit_selected_candidates", managed)
    merged, diagnostics = candidate_pool.audit_selected_candidates_adaptive(
        _selected("a", "b"),
        _config(tmp_path),
        candidate_workers=3,
        max_total_workers=12,
    )

    assert calls == 1
    assert [item["status"] for item in merged] == [
        "REJECTED",
        "THRESHOLD_PROVEN",
    ]
    assert diagnostics["escalated_to_strong"] == 0


def test_adaptive_preserves_explicit_no_resume_in_both_lanes(
    tmp_path,
    monkeypatch,
):
    configs: list[candidate_pool.AuditConfig] = []

    def managed(rows, config, *, candidate_workers):
        configs.append(config)
        return [_result("a", "UNRESOLVED", retry_required=True)]

    monkeypatch.setattr(candidate_pool, "audit_selected_candidates", managed)
    config = _config(tmp_path, resume=False)
    merged, _ = candidate_pool.audit_selected_candidates_adaptive(
        _selected("a"),
        config,
        candidate_workers=3,
        max_total_workers=12,
    )

    assert len(configs) == 2
    assert configs[0].resume is False
    assert configs[1] == config
    assert merged[0]["retry_required"] is True


def test_terminal_retry_conflict_fails_closed(tmp_path, monkeypatch):
    monkeypatch.setattr(
        candidate_pool,
        "audit_selected_candidates",
        lambda rows, config, *, candidate_workers: [
            _result("a", "REJECTED", retry_required=True)
        ],
    )

    with pytest.raises(ValueError, match="cannot request retry"):
        candidate_pool.audit_selected_candidates_adaptive(
            _selected("a"),
            _config(tmp_path),
            candidate_workers=3,
            max_total_workers=12,
        )


def test_adaptive_cli_is_default_on_and_can_be_disabled():
    parser = candidate_pool.build_parser()
    required = [
        "input.jsonl",
        "--state-dir",
        "state",
        "--ranked-output",
        "ranked.jsonl",
        "--summary-output",
        "summary.json",
    ]

    assert parser.parse_args(required).adaptive_stage2 is True
    assert parser.parse_args([*required, "--no-adaptive-stage2"]).adaptive_stage2 is False


def test_cheap_lane_never_inherits_a_strong_hard_wall_or_enables_resume(
    tmp_path,
):
    strong = _config(
        tmp_path,
        solver_timeout_s=12.5,
        solver_workers=2,
        candidate_hard_timeout_s=500,
        resume=False,
    )
    _, cheap, workers = candidate_pool._adaptive_stage2_machine_policy(
        strong,
        candidate_workers=4,
        max_total_workers=8,
    )

    assert workers == 8
    assert cheap == replace(
        strong,
        solver_timeout_s=12.5,
        solver_workers=1,
        candidate_hard_timeout_s=None,
    )
    assert cheap.resume is False


def test_native_thread_caps_apply_only_to_cli_subprocess():
    names = candidate_pool.STAGE2_NATIVE_THREAD_CAP_ENV
    sentinels = {
        name: str(index) for index, name in enumerate(names, start=2)
    }
    child_env = {**os.environ, **sentinels}
    script = str(
        (candidate_pool.PROJECT / "scripts" / "audit_candidate_pool.py")
        .resolve()
    )
    marker = "NATIVE_CAP_PROBE="
    parent_before = {name: os.environ.get(name) for name in names}

    cli_source = f"""\
import contextlib, io, json, os, runpy, sys
names = {names!r}
sys.argv = [{script!r}, "--help"]
try:
    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
        runpy.run_path({script!r}, run_name="__main__")
except SystemExit as exc:
    assert exc.code == 0
print({marker!r} + json.dumps({{name: os.environ.get(name) for name in names}}, sort_keys=True))
"""
    cli = subprocess.run(
        [sys.executable, "-c", cli_source],
        cwd=candidate_pool.PROJECT,
        env=child_env,
        text=True,
        capture_output=True,
        check=True,
    )
    cli_caps = json.loads(cli.stdout.split(marker, 1)[1])
    assert cli_caps == {name: "1" for name in names}

    import_source = f"""\
import json, os
names = {names!r}
before = {{name: os.environ.get(name) for name in names}}
import scripts.audit_candidate_pool
print({marker!r} + json.dumps({{"before": before, "after": {{name: os.environ.get(name) for name in names}}}}, sort_keys=True))
"""
    imported = subprocess.run(
        [sys.executable, "-c", import_source],
        cwd=candidate_pool.PROJECT,
        env=child_env,
        text=True,
        capture_output=True,
        check=True,
    )
    import_caps = json.loads(imported.stdout.split(marker, 1)[1])
    assert import_caps == {"before": sentinels, "after": sentinels}
    assert {name: os.environ.get(name) for name in names} == parent_before


def test_main_certifies_only_merged_threshold_results(
    tmp_path,
    monkeypatch,
    capsys,
):
    from humanize.pipeline import FiveStagePipeline

    candidate_input = tmp_path / "candidates.jsonl"
    candidate_input.write_text("{}\n")
    ranked_output = tmp_path / "ranked.jsonl"
    summary_output = tmp_path / "summary.json"
    selected = _selected("a", "b", "c")
    counts = {
        "input_candidates": 3,
        "unique_candidates": 3,
        "eligible_candidates": 3,
        "rejected_candidates": 0,
    }

    monkeypatch.setattr(
        candidate_pool,
        "rank_candidate_files",
        lambda paths, *, target_mode: (selected, counts),
    )
    monkeypatch.setattr(
        candidate_pool,
        "select_audit_candidates",
        lambda ranked, top, *, canonicalizer: (
            ranked,
            {"selection_exhausted": True},
        ),
    )

    lane_calls = []

    def managed(rows, config, *, candidate_workers):
        digests = tuple(
            row["triage_identity"]["canonical_digest"] for row in rows
        )
        lane_calls.append(
            (digests, candidate_workers, config.solver_workers)
        )
        if len(lane_calls) == 1:
            return [
                _result("a", "THRESHOLD_PROVEN"),
                _result("b", "UNRESOLVED"),
                _result("c", "UNRESOLVED"),
            ]
        return [
            _result("b", "REJECTED"),
            _result("c", "THRESHOLD_PROVEN"),
        ]

    monkeypatch.setattr(
        candidate_pool,
        "audit_selected_candidates",
        managed,
    )
    certified_digests = []

    def certify(
        items,
        config,
        *,
        certificate_workers,
        max_total_workers,
    ):
        del config, certificate_workers, max_total_workers
        certified_digests.extend(
            item["triage_identity"]["canonical_digest"] for item in items
        )
        return {
            digest: {
                "attempted": True,
                "certificate_passed": True,
                "verification_passed": True,
            }
            for digest in certified_digests
        }

    monkeypatch.setattr(
        candidate_pool,
        "certify_selected_candidates",
        certify,
    )

    assert candidate_pool.main([
        str(candidate_input),
        "--top", "3",
        "--state-dir", str(tmp_path / "state"),
        "--ranked-output", str(ranked_output),
        "--summary-output", str(summary_output),
        "--candidate-workers", "2",
        "--solver-workers", "4",
        "--max-total-workers", "8",
    ]) == 0
    capsys.readouterr()

    assert lane_calls == [
        (("a", "b", "c"), 8, 1),
        (("b", "c"), 2, 4),
    ]
    assert certified_digests == ["a", "c"]
    summary = json.loads(summary_output.read_text())
    assert [result["canonical_digest"] for result in summary["results"]] == [
        "a", "b", "c",
    ]
    assert [result["status"] for result in summary["results"]] == [
        "THRESHOLD_PROVEN", "REJECTED", "THRESHOLD_PROVEN",
    ]
    assert summary["status_counts"] == {
        "THRESHOLD_PROVEN": 2,
        "REJECTED": 1,
    }
    assert summary["certified_wins"] == 2
    assert summary["retry_required"] is False
    assert summary["adaptive_stage2"]["escalated_to_strong"] == 2
    ranked_rows = [
        json.loads(line) for line in ranked_output.read_text().splitlines()
    ]
    assert [
        row["campaign_audit"]["canonical_digest"] for row in ranked_rows
    ] == ["a", "b", "c"]
    assert all(row["campaign_selected"] is True for row in ranked_rows)
    validated = FiveStagePipeline._validate_pool_summary(
        summary_output,
        ranked_output,
        "qldpc-proof-oriented-candidate-pool",
        expected_target_mode=candidate_pool.DEFAULT_TARGET_MODE,
    )
    assert validated == summary
