from __future__ import annotations

import hashlib
import json
import subprocess
from collections import Counter
from dataclasses import replace
from pathlib import Path

import pytest
from humanize.pipeline import (
    STAGE_ORDER,
    FiveStagePipeline,
    PipelineConfig,
    PipelineError,
    PipelinePaths,
)


def _argument(command: list[str], name: str) -> Path:
    return Path(command[command.index(name) + 1])


def _write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))


def _plan(
    results: list[dict] | None = None,
    *,
    returncode: int = 0,
    operational_errors: int = 0,
    write_outputs: bool = True,
    gate_passed: bool = True,
) -> dict:
    return {
        "results": list(results or []),
        "returncode": returncode,
        "operational_errors": operational_errors,
        "write_outputs": write_outputs,
        "gate_passed": gate_passed,
    }


class ScenarioRunner:
    """A stage-aware command runner that materializes the real CLI contracts."""

    def __init__(
        self,
        *,
        stage2: list[dict] | None = None,
        stage3: list[dict] | None = None,
        strict: list[dict] | None = None,
    ):
        self.plans = {
            "stage2": stage2 or [_plan()],
            "stage3": stage3 or [_plan()],
            "strict": strict or [_plan()],
        }
        self.calls: list[tuple[str, list[str]]] = []
        self.counts: Counter[str] = Counter()

    def _next(self, stage: str) -> dict:
        index = self.counts[stage]
        self.counts[stage] += 1
        plans = self.plans[stage]
        return plans[min(index, len(plans) - 1)]

    def __call__(
        self, command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        assert cwd.is_dir()
        script = Path(command[1]).name
        if script == "audit_candidate_pool.py":
            stage = "stage2"
            expected_gate = "qldpc-proof-oriented-candidate-pool"
        elif script == "audit_direction_pool.py":
            stage = "stage3"
            expected_gate = "qldpc-direction-candidate-pool"
        elif script == "finalize_challenge.py":
            stage = "strict"
            expected_gate = "qldpc-challenge-final-batch"
        else:
            raise AssertionError(f"unexpected pipeline command: {command}")
        self.calls.append((stage, list(command)))
        plan = self._next(stage)

        if plan["write_outputs"] and stage in {"stage2", "stage3"}:
            results = plan["results"]
            annotation_key = (
                "campaign_audit" if stage == "stage2" else "campaign_direction_audit"
            )
            selection_key = (
                "campaign_selected"
                if stage == "stage2"
                else "campaign_direction_selected"
            )
            ranked_rows = [
                {
                    "triage_identity": {
                        "canonical_digest": result.get(
                            "canonical_digest", f"{stage}-{index}"
                        )
                    },
                    selection_key: True,
                    annotation_key: dict(result),
                }
                for index, result in enumerate(results)
            ]
            _write_jsonl(_argument(command, "--ranked-output"), ranked_rows)
            status_counts = dict(Counter(str(result["status"]) for result in results))
            summary = {
                "schema_version": 1,
                "gate": expected_gate,
                "results": results,
                "status_counts": status_counts,
                "selected_candidates": len(results),
            }
            if stage == "stage2":
                summary["certificate_operational_errors"] = plan["operational_errors"]
                summary["unique_candidates"] = len(results)
            else:
                summary["operational_errors"] = plan["operational_errors"]
                _write_jsonl(_argument(command, "--stage4-manifest"), [])
            _write_json(_argument(command, "--summary-output"), summary)
        elif plan["write_outputs"] and stage == "strict":
            _write_json(
                _argument(command, "--output"),
                {
                    "schema_version": 1,
                    "gate": expected_gate,
                    "passed": plan["gate_passed"],
                    "known_answer_integrity": {
                        "mode": "strict",
                        "passed": plan["gate_passed"],
                    },
                    "summary": {
                        "accepted": int(plan["gate_passed"]),
                        "rejected": int(not plan["gate_passed"]),
                        "total": 1,
                    },
                    "evaluations": [{"result": {"passed": plan["gate_passed"]}}],
                },
            )
        return subprocess.CompletedProcess(
            command,
            plan["returncode"],
            stdout=f"{stage} stdout\n",
            stderr="" if plan["returncode"] == 0 else f"{stage} failed\n",
        )

    def commands(self, stage: str) -> list[list[str]]:
        return [command for name, command in self.calls if name == stage]


class RecordingReviewer:
    def __init__(
        self,
        *,
        verdict: str = "continue",
        fail_once: set[str] | None = None,
    ):
        self.verdict = verdict
        self.fail_once = set(fail_once or ())
        self.calls: list[str] = []

    def review(self, stage: str, prompt: str, stage_dir: Path) -> dict:
        self.calls.append(stage)
        assert stage in prompt
        assert "cannot alter routing" in prompt
        assert stage_dir.name == stage
        if stage in self.fail_once:
            self.fail_once.remove(stage)
            raise RuntimeError(f"simulated {stage} reviewer outage")
        return {
            "verdict": self.verdict,
            "summary": f"Advisory review for {stage}.",
            "risks": [],
            "recommended_focus": [],
            "lessons": [],
        }


def _repo(tmp_path: Path) -> tuple[Path, Path]:
    repo = tmp_path / "qcode"
    scripts = repo / "scripts"
    scripts.mkdir(parents=True)
    for name in (
        "audit_candidate_pool.py",
        "audit_direction_pool.py",
        "finalize_challenge.py",
        "screen_frontier_candidate.py",
        "screen_frontier_xor.py",
    ):
        (scripts / name).write_text(f"# fake {name}\n")
    evaluation = repo / "evaluation"
    evaluation.mkdir()
    (evaluation / "verifier.py").write_text("# fake imported verifier\n")
    results = repo / "results"
    results.mkdir()
    (results / "known_answer_gate.json").write_text('{"passed": true}\n')
    (results / "known_answer_trust.json").write_text('{"schema_version": 1}\n')
    candidates = repo / "candidate-pool.jsonl"
    candidates.write_text('{"candidate": 1}\n')
    return repo, candidates


def _config(
    repo: Path,
    candidates: Path,
    *,
    run_id: str = "pipeline-test",
) -> PipelineConfig:
    return PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_inputs=(candidates,),
        stage_review=True,
    )


def _certificate(
    config: PipelineConfig,
    digest: str,
    *,
    artifact_passed: bool = True,
    certificate_passed: bool = True,
    verification_passed: bool = True,
) -> tuple[dict, Path]:
    paths = PipelinePaths(config.root)
    certificate_path = paths.solver_state / "certificates" / f"{digest}.json"
    verification_path = paths.solver_state / "verifications" / f"{digest}.json"
    certificate = {
        "schema_version": 1,
        "certificate_type": "qldpc-css-bb-exact",
        "passed": artifact_passed,
        "claim": {
            "canonical_digest": digest,
            "n": 72,
            "k": 12,
            "d": 7,
        },
        "milp": {
            "exact": True,
            "expected_directions": 2,
            "completed_directions": 2,
        },
    }
    certificate_sha = hashlib.sha256(
        json.dumps(
            certificate,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    certificate["certificate_sha256"] = certificate_sha
    _write_json(certificate_path, certificate)
    known_answer_sha = hashlib.sha256(
        Path(config.known_answer_artifact).read_bytes()
    ).hexdigest()
    payload_sha = hashlib.sha256(
        json.dumps(
            certificate,
            sort_keys=True,
            separators=(",", ":"),
        ).encode()
    ).hexdigest()
    _write_json(
        verification_path,
        {
            "schema_version": 2,
            "kind": "qldpc-certificate-verification-cache",
            "canonical_digest": digest,
            "known_answer_sha256": known_answer_sha,
            "candidate_payload_sha256": hashlib.sha256(digest.encode()).hexdigest(),
            "certificate_sha256": certificate_sha,
            "certificate_payload_sha256": payload_sha,
            "verification": {"passed": verification_passed},
        },
    )
    return {
        "canonical_digest": digest,
        "status": "THRESHOLD_PROVEN",
        "certificate": {
            "attempted": True,
            "certificate_path": str(certificate_path),
            "verification_path": str(verification_path),
            "certificate_sha256": certificate_sha,
            "certificate_exact": True,
            "certificate_passed": certificate_passed,
            "verification_passed": verification_passed,
        },
    }, certificate_path


def test_stage2_proof_bypasses_stage3_solver_and_reaches_strict_gate(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates)
    proven, _ = _certificate(config, "direct")
    runner = ScenarioRunner(stage2=[_plan([proven])])
    reviewer = RecordingReviewer(verdict="stop")

    state = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "strict": 1}
    assert state["stages"]["stage3_direction_audit"]["machine_status"] == "SKIPPED"
    assert reviewer.calls == list(STAGE_ORDER)
    for stage in STAGE_ORDER:
        review = config.root / "reviews" / stage / "review.json"
        assert review.is_file()
    strict = runner.commands("strict")[0]
    assert Path(strict[1]).name == "finalize_challenge.py"
    assert "fast" not in strict
    assert "--known-answer-trust" in strict
    assert (
        json.loads((config.root / "artifacts" / "stage4-summary.json").read_text())[
            "verified_certificates"
        ]
        == 1
    )


def test_unresolved_stage2_routes_through_stage3_then_joins_stage4(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="via-stage3")
    unresolved = {
        "canonical_digest": "needs-directions",
        "status": "UNRESOLVED",
    }
    proven, _ = _certificate(config, "direction-proof")
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([proven])],
    )

    state = FiveStagePipeline(
        config, command_runner=runner, reviewer=RecordingReviewer()
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "stage3": 1, "strict": 1}
    summary = json.loads(
        (config.root / "artifacts" / "stage4-summary.json").read_text()
    )
    assert summary["verified_certificates"] == 1
    assert summary["entries"][0]["source_stage"] == "stage3_direction_audit"


def test_stage2_and_stage3_verified_certificates_merge_and_deduplicate(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="merge")
    direct, _ = _certificate(config, "same")
    duplicate, _ = _certificate(config, "same")
    second, _ = _certificate(config, "other")
    unresolved = {"canonical_digest": "route-stage3", "status": "UNRESOLVED"}
    runner = ScenarioRunner(
        stage2=[_plan([direct, unresolved])],
        stage3=[_plan([duplicate, second])],
    )

    state = FiveStagePipeline(
        config, command_runner=runner, reviewer=RecordingReviewer()
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    summary = json.loads(
        (config.root / "artifacts" / "stage4-summary.json").read_text()
    )
    assert summary["verified_certificates"] == 2
    assert [entry["canonical_digest"] for entry in summary["entries"]] == [
        "same",
        "other",
    ]
    claims = [
        json.loads(line)
        for line in (config.root / "artifacts" / "stage4-certificates.jsonl")
        .read_text()
        .splitlines()
    ]
    assert len(claims) == 2


def test_no_verified_certificate_completes_no_win_without_strict_solver(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="no-win")
    unresolved = {"canonical_digest": "still-open", "status": "UNRESOLVED"}
    unverified, _ = _certificate(config, "not-independent", verification_passed=False)
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unverified])],
    )
    # Even an advisory "promote" is not allowed to waive certificate flags.
    reviewer = RecordingReviewer(verdict="promote")

    state = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()

    assert state["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": 1, "stage3": 1}
    assert state["stages"]["stage5_strict_gate"]["machine_status"] == "SKIPPED"
    assert reviewer.calls == list(STAGE_ORDER)
    terminal = json.loads(
        (config.root / "artifacts" / "stage5-no-win.json").read_text()
    )
    assert terminal["status"] == "COMPLETED_NO_WIN"


def test_reviewer_failure_is_fail_closed_and_resume_retries_only_review(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="review-resume")
    runner = ScenarioRunner(stage2=[_plan([])])
    flaky = RecordingReviewer(fail_once={"stage2_sector_audit"})

    failed = FiveStagePipeline(config, command_runner=runner, reviewer=flaky).run()
    assert failed["status"] == "FAILED"
    assert failed["failure"]["classification"] == "REVIEW_FAILED"
    stage2 = failed["stages"]["stage2_sector_audit"]
    assert stage2["machine_status"] == "COMPLETED"
    assert stage2["review_status"] == "FAILED"
    assert runner.counts["stage2"] == 1

    completed = FiveStagePipeline(config, command_runner=runner, reviewer=flaky).run()
    assert completed["status"] == "COMPLETED_NO_WIN"
    assert runner.counts["stage2"] == 1
    assert flaky.calls.count("stage2_sector_audit") == 2
    assert completed["stages"]["stage2_sector_audit"]["attempt"] == 1


def test_nonzero_stage_is_not_cached_and_blocks_downstream_until_resume(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="command-resume")
    unresolved = {"canonical_digest": "retry", "status": "UNRESOLVED"}
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[
            _plan([unresolved], returncode=2),
            _plan([]),
        ],
    )
    reviewer = RecordingReviewer()

    failed = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert failed["status"] == "FAILED"
    assert failed["failure"]["classification"] == "STAGE_EXIT_NONZERO"
    assert failed["failure"]["stage"] == "stage3_direction_audit"
    assert runner.counts == {"stage2": 1, "stage3": 1}

    completed = FiveStagePipeline(
        config, command_runner=runner, reviewer=reviewer
    ).run()
    assert completed["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": 1, "stage3": 2}
    assert completed["stages"]["stage2_sector_audit"]["attempt"] == 1
    assert completed["stages"]["stage3_direction_audit"]["attempt"] == 2


def test_rc_zero_operational_error_is_fail_closed(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="bad-summary")
    runner = ScenarioRunner(
        stage2=[_plan([], operational_errors=1)],
    )

    state = FiveStagePipeline(
        config, command_runner=runner, reviewer=RecordingReviewer()
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OPERATIONAL_ERROR"
    assert state["failure"]["stage"] == "stage2_sector_audit"
    assert runner.counts == {"stage2": 1}


def test_passed_flags_cannot_hide_a_failed_certificate_artifact(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="bad-certificate")
    dishonest, _ = _certificate(config, "dishonest", artifact_passed=False)
    runner = ScenarioRunner(stage2=[_plan([dishonest])])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(verdict="promote"),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage4_certificate_merge"
    assert runner.counts == {"stage2": 1}


def test_stage2_budget_change_reuses_stage1_and_reruns_all_downstream(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="stage2-budget")
    proven, _ = _certificate(config, "budget")
    runner = ScenarioRunner(stage2=[_plan([proven])])
    reviewer = RecordingReviewer()
    first = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert first["status"] == "COMPLETED_WIN"

    changed = replace(config, stage2_timeout=config.stage2_timeout + 1)
    second = FiveStagePipeline(changed, command_runner=runner, reviewer=reviewer).run()

    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 2}
    assert second["stages"]["stage1_search"]["attempt"] == 1
    for stage in STAGE_ORDER[1:]:
        assert second["stages"][stage]["attempt"] == 2


def test_stage3_budget_change_reuses_stage1_and_stage2_then_reruns_tail(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="stage3-budget")
    unresolved = {"canonical_digest": "open", "status": "UNRESOLVED"}
    proven, _ = _certificate(config, "stage3-budget")
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([proven])],
    )
    reviewer = RecordingReviewer()
    first = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert first["status"] == "COMPLETED_WIN"

    changed = replace(config, stage3_timeout=config.stage3_timeout + 1)
    second = FiveStagePipeline(changed, command_runner=runner, reviewer=reviewer).run()

    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "stage3": 2, "strict": 2}
    assert second["stages"]["stage1_search"]["attempt"] == 1
    assert second["stages"]["stage2_sector_audit"]["attempt"] == 1
    for stage in STAGE_ORDER[2:]:
        assert second["stages"][stage]["attempt"] == 2


def test_stage1_candidate_identity_change_requires_new_run_id(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="immutable-search")
    runner = ScenarioRunner()
    reviewer = RecordingReviewer()
    assert (
        FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()[
            "status"
        ]
        == "COMPLETED_NO_WIN"
    )
    previous_calls = list(runner.calls)

    candidates.write_text('{"candidate": 2}\n')
    with pytest.raises(ValueError, match="Stage 1 search identity"):
        FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert runner.calls == previous_calls


def test_completed_run_is_idempotent(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="idempotent")
    runner = ScenarioRunner()
    reviewer = RecordingReviewer()
    pipeline = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer)
    first = pipeline.run()
    first_calls = list(runner.calls)
    first_reviews = list(reviewer.calls)

    second = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()

    assert first["status"] == second["status"] == "COMPLETED_NO_WIN"
    assert runner.calls == first_calls
    assert reviewer.calls == first_reviews


def test_reviewer_config_change_reuses_machine_work_but_refreshes_reviews(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="review-fingerprint")
    runner = ScenarioRunner()
    first_reviewer = RecordingReviewer()
    first = FiveStagePipeline(
        config, command_runner=runner, reviewer=first_reviewer
    ).run()
    assert first["status"] == "COMPLETED_NO_WIN"
    assert first_reviewer.calls == list(STAGE_ORDER)

    changed = replace(config, reviewer_model="independent-review-model")
    second_reviewer = RecordingReviewer()
    second = FiveStagePipeline(
        changed, command_runner=runner, reviewer=second_reviewer
    ).run()

    assert second["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": 1}
    assert second_reviewer.calls == list(STAGE_ORDER)
    for stage in STAGE_ORDER:
        assert second["stages"][stage]["attempt"] == 1
        assert second["stages"][stage]["review_attempt"] == 2


def test_strict_gate_rejection_is_fail_closed_and_retried_on_resume(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-retry")
    proven, _ = _certificate(config, "strict-retry")
    runner = ScenarioRunner(
        stage2=[_plan([proven])],
        strict=[
            _plan(returncode=1, gate_passed=False),
            _plan(gate_passed=True),
        ],
    )
    reviewer = RecordingReviewer()

    failed = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert failed["status"] == "FAILED"
    assert failed["failure"]["classification"] == "STRICT_GATE_REJECTED"
    assert failed["failure"]["stage"] == "stage5_strict_gate"
    assert runner.counts == {"stage2": 1, "strict": 1}

    completed = FiveStagePipeline(
        config, command_runner=runner, reviewer=reviewer
    ).run()
    assert completed["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "strict": 2}
    assert completed["stages"]["stage2_sector_audit"]["attempt"] == 1
    assert completed["stages"]["stage5_strict_gate"]["attempt"] == 2


def test_pipeline_run_id_cannot_escape_pipeline_root(tmp_path):
    repo, candidates = _repo(tmp_path)
    for run_id in ("..", ".", "../escape", "/absolute", "space name"):
        with pytest.raises(ValueError):
            _config(repo, candidates, run_id=run_id)


def test_stage4_rejects_failed_verification_sidecar_despite_summary_flags(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="sidecar-failed")
    dishonest, _ = _certificate(config, "sidecar-failed")
    sidecar_path = Path(dishonest["certificate"]["verification_path"])
    sidecar = json.loads(sidecar_path.read_text())
    sidecar["verification"]["passed"] = False
    _write_json(sidecar_path, sidecar)

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(stage2=[_plan([dishonest])]),
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage4_certificate_merge"


def test_stage4_rejects_certificate_payload_changed_after_verification(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="payload-tamper")
    dishonest, certificate_path = _certificate(config, "payload-tamper")
    certificate = json.loads(certificate_path.read_text())
    certificate["claim"]["n"] = 73
    unsigned = dict(certificate)
    unsigned.pop("certificate_sha256")
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            unsigned,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    _write_json(certificate_path, certificate)
    # Real audit metadata does not carry this optional field. Stage 4 must
    # still detect the stale sidecar through its bound payload hash.
    dishonest["certificate"].pop("certificate_sha256")

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(stage2=[_plan([dishonest])]),
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage4_certificate_merge"


def test_stage4_rejects_verification_path_outside_solver_state(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="sidecar-escape")
    dishonest, _ = _certificate(config, "sidecar-escape")
    dishonest["certificate"]["verification_path"] = str(
        tmp_path / "outside-verification.json"
    )

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(stage2=[_plan([dishonest])]),
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage4_certificate_merge"


def test_corrupt_pool_result_cannot_route_to_completed_no_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="corrupt-pool")

    def corrupt_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        assert Path(command[1]).name == "audit_candidate_pool.py"
        _write_jsonl(_argument(command, "--ranked-output"), [])
        _write_json(
            _argument(command, "--summary-output"),
            {
                "schema_version": 1,
                "gate": "qldpc-proof-oriented-candidate-pool",
                "status_counts": {},
                "certificate_operational_errors": 0,
                "results": [None],
            },
        )
        return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

    state = FiveStagePipeline(
        config,
        command_runner=corrupt_runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage2_sector_audit"


def test_cache_miss_cannot_reuse_stale_strict_gate_output(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="stale-strict-output")
    proven, _ = _certificate(config, "stale-strict-output")
    runner = ScenarioRunner(
        stage2=[_plan([proven])],
        strict=[_plan(), _plan(write_outputs=False)],
    )
    reviewer = RecordingReviewer()

    first = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert first["status"] == "COMPLETED_WIN"

    changed = replace(
        config,
        known_answer_total_timeout=config.known_answer_total_timeout + 1,
    )
    second = FiveStagePipeline(changed, command_runner=runner, reviewer=reviewer).run()

    assert second["status"] == "FAILED"
    assert second["failure"]["classification"] == "OUTPUT_INVALID"
    assert second["failure"]["stage"] == "stage5_strict_gate"
    assert "result" not in second
    assert "completed_at" not in second
    assert second["result_history"][-1]["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "strict": 2}


def test_imported_verifier_source_change_invalidates_proof_stages(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="source-change")
    runner = ScenarioRunner()
    reviewer = RecordingReviewer()

    first = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert first["status"] == "COMPLETED_NO_WIN"
    (repo / "evaluation" / "verifier.py").write_text("# changed imported verifier\n")

    second = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()

    assert second["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": 2}
    assert second["stages"]["stage1_search"]["attempt"] == 1
    for stage in STAGE_ORDER[1:]:
        assert second["stages"][stage]["attempt"] == 2


def test_strict_gate_rejects_passed_flag_without_strict_evaluations(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="weak-strict-evidence")
    proven, _ = _certificate(config, "weak-strict-evidence")
    underlying = ScenarioRunner(stage2=[_plan([proven])])

    def weak_strict_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        result = underlying(command, cwd=cwd)
        if Path(command[1]).name == "finalize_challenge.py":
            output = _argument(command, "--output")
            artifact = json.loads(output.read_text())
            artifact["evaluations"] = []
            _write_json(output, artifact)
        return result

    state = FiveStagePipeline(
        config,
        command_runner=weak_strict_runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "STRICT_GATE_REJECTED"
    assert state["failure"]["stage"] == "stage5_strict_gate"


def test_stage4_rejects_inconsistent_exact_certificate_flags(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="inconsistent-proof-flags")
    dishonest, _ = _certificate(config, "inconsistent-proof-flags")
    dishonest["certificate"]["certificate_exact"] = False

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(stage2=[_plan([dishonest])]),
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage4_certificate_merge"


def test_certificate_solver_workers_rejects_unsupported_highs_thread_count(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="worker-limit")

    with pytest.raises(ValueError, match="between 1 and 8"):
        replace(
            config,
            certificate_solver_workers=9,
            max_total_workers=9,
        )


def test_selected_candidate_without_audit_annotation_fails_closed(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="missing-selected-audit")

    def missing_annotation_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        assert Path(command[1]).name == "audit_candidate_pool.py"
        _write_jsonl(
            _argument(command, "--ranked-output"),
            [
                {
                    "triage_identity": {"canonical_digest": "selected"},
                    "campaign_selected": True,
                }
            ],
        )
        _write_json(
            _argument(command, "--summary-output"),
            {
                "schema_version": 1,
                "gate": "qldpc-proof-oriented-candidate-pool",
                "status_counts": {},
                "selected_candidates": 1,
                "certificate_operational_errors": 0,
                "results": [],
            },
        )
        return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

    state = FiveStagePipeline(
        config,
        command_runner=missing_annotation_runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage2_sector_audit"


def test_solver_state_symlink_cannot_escape_pipeline_root(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="solver-state-escape")
    config.root.mkdir(parents=True)
    outside = tmp_path / "outside-solver-state"
    outside.mkdir()
    (config.root / "solver-state").symlink_to(outside, target_is_directory=True)

    with pytest.raises(PipelineError, match="may not be a symlink"):
        FiveStagePipeline(
            config,
            command_runner=ScenarioRunner(),
            reviewer=RecordingReviewer(),
        ).run()
    assert list(outside.iterdir()) == []


def test_nested_solver_state_symlink_cannot_escape_pipeline_root(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="nested-solver-state-escape")
    solver_state = config.root / "solver-state"
    solver_state.mkdir(parents=True)
    outside = tmp_path / "outside-nested-solver-state"
    outside.mkdir()
    (solver_state / "certificates").symlink_to(
        outside,
        target_is_directory=True,
    )

    with pytest.raises(PipelineError, match="entry may not be a symlink"):
        FiveStagePipeline(
            config,
            command_runner=ScenarioRunner(),
            reviewer=RecordingReviewer(),
        ).run()
    assert list(outside.iterdir()) == []
