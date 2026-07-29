from __future__ import annotations

import hashlib
import importlib.util
import json
import marshal
import os
import py_compile
import subprocess
import sys
from collections import Counter
from dataclasses import replace
from pathlib import Path

import pytest

import humanize.pipeline as pipeline_module
from evaluation.final_gate import classify_win
from humanize.flow import (
    FlowConfig,
    HumanizeFlow,
    HumanizeRunAlreadyActiveError,
    UnresolvedAuditError,
    _acquire_humanize_run_lease,
)
from humanize.pipeline import (
    STAGE_ORDER,
    FiveStagePipeline,
    PipelineBusyError,
    PipelineConfig,
    PipelineError,
    PipelinePaths,
)
from humanize.release_export import export_release


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
    strict_dispositions: list[str] | None = None,
    selection_exhausted: bool = True,
    selection_page: tuple[int, int] | None = None,
    canonicalization_errors: int = 0,
) -> dict:
    return {
        "results": list(results or []),
        "returncode": returncode,
        "operational_errors": operational_errors,
        "write_outputs": write_outputs,
        "gate_passed": gate_passed,
        "strict_dispositions": strict_dispositions,
        "selection_exhausted": selection_exhausted,
        "selection_page": selection_page,
        "canonicalization_errors": canonicalization_errors,
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
                "selection_exhausted": plan["selection_exhausted"],
            }
            if stage == "stage2":
                summary["certificate_operational_errors"] = plan["operational_errors"]
                summary["canonicalization_errors"] = plan[
                    "canonicalization_errors"
                ]
                summary["unique_candidates"] = len(results)
                if plan["selection_page"] is not None:
                    start_index, next_index = plan["selection_page"]
                    selected_digests = [
                        str(result["canonical_digest"])
                        for result in results
                    ]
                    binding = "a" * 64
                    page_payload = {
                        "binding_sha256": binding,
                        "start_index": start_index,
                        "next_index": next_index,
                        "selected_digests": selected_digests,
                    }
                    page = {
                        **page_payload,
                        "page_sha256": hashlib.sha256(
                            json.dumps(
                                page_payload,
                                sort_keys=True,
                                separators=(",", ":"),
                            ).encode()
                        ).hexdigest(),
                    }
                    summary["selection_page"] = page
                    ledger_path = _argument(command, "--selection-ledger")
                    if ledger_path.is_file():
                        ledger = json.loads(ledger_path.read_text())
                    else:
                        ledger = {
                            "schema_version": 1,
                            "gate": "qldpc-stage2-selection-ledger",
                            "binding_sha256": binding,
                            "cursor": start_index,
                            "committed_digests": [],
                            "completed_pages": 0,
                            "pending": None,
                        }
                    assert ledger["cursor"] == start_index
                    assert ledger["pending"] is None or ledger["pending"] == page
                    ledger["pending"] = page
                    _write_json(ledger_path, ledger)
            else:
                summary["operational_errors"] = plan["operational_errors"]
                _write_jsonl(_argument(command, "--stage4-manifest"), [])
            _write_json(_argument(command, "--summary-output"), summary)
        elif plan["write_outputs"] and stage == "strict":
            certificates = [
                json.loads(line)
                for line in Path(command[2]).read_text().splitlines()
                if line.strip()
            ]
            trust = json.loads(_argument(command, "--known-answer-trust").read_text())
            dispositions = plan["strict_dispositions"]
            if dispositions is None:
                dispositions = [
                    "ACCEPTED" if plan["gate_passed"] else "REJECTED"
                    for _certificate in certificates
                ]
            assert len(dispositions) == len(certificates)
            evaluations = [
                {
                    "source_index": index,
                    "claim": certificate.get("claim"),
                    "certificate_sha256": certificate.get("certificate_sha256"),
                    "disposition": disposition,
                    "result": {
                        "passed": disposition == "ACCEPTED",
                        "replay_complete": disposition != "INCOMPLETE",
                        "checks": {
                            "schema": disposition == "ACCEPTED",
                            "certificate_sha256": disposition == "ACCEPTED",
                            "known_answer_sha256": disposition == "ACCEPTED",
                            "matrix_sha256": disposition == "ACCEPTED",
                            "direction_count": disposition == "ACCEPTED",
                            "stored_direction_evidence": disposition == "ACCEPTED",
                            "milp_rerun": disposition == "ACCEPTED",
                            "distance_recomputed": disposition == "ACCEPTED",
                            "final_gate": disposition == "ACCEPTED",
                            "certificate_passed_flag": disposition == "ACCEPTED",
                        },
                        "failures": (
                            []
                            if disposition == "ACCEPTED"
                            else [
                                "strict replay timeout"
                                if disposition == "INCOMPLETE"
                                else "final_gate"
                            ]
                        ),
                        "distance": certificate["claim"]["d"],
                        "directions_verified": 2 * certificate["claim"]["k"],
                        "directions_total": 2 * certificate["claim"]["k"],
                        "final_gate": (
                            certificate["final_gate"]
                            if disposition == "ACCEPTED"
                            else {"accepted": False}
                        ),
                    },
                }
                for index, (certificate, disposition) in enumerate(
                    zip(certificates, dispositions, strict=True)
                )
            ]
            accepted = sum(
                item["disposition"] == "ACCEPTED" for item in evaluations
            )
            rejected = sum(
                item["disposition"] == "REJECTED" for item in evaluations
            )
            incomplete = sum(
                item["disposition"] == "INCOMPLETE" for item in evaluations
            )
            outcome = (
                "WIN"
                if accepted
                else "INCOMPLETE"
                if incomplete
                else "NO_WIN"
            )
            _write_json(
                _argument(command, "--output"),
                {
                    "schema_version": 1,
                    "gate": expected_gate,
                    "passed": outcome == "WIN",
                    "outcome": outcome,
                    "known_answer_integrity": {
                        "mode": "strict",
                        "passed": True,
                        "artifact_sha256": trust["artifact_sha256"],
                        "semantic_sha256": trust["semantic_sha256"],
                        "rerun_semantic_sha256": trust["semantic_sha256"],
                        "environment": trust["environment"],
                        "failures": [],
                    },
                    "summary": {
                        "accepted": accepted,
                        "rejected": rejected,
                        "incomplete": incomplete,
                        "total": len(evaluations),
                    },
                    "evaluations": evaluations,
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


class SharedLeaseProbeReviewer(RecordingReviewer):
    def __init__(self, repo: Path, candidates: Path, run_id: str):
        super().__init__()
        self.repo = repo
        self.candidates = candidates
        self.run_id = run_id
        self.blocked_stages: list[str] = []

    def review(self, stage: str, prompt: str, stage_dir: Path) -> dict:
        direct = HumanizeFlow(
            FlowConfig(
                repo_dir=self.repo,
                run_id=self.run_id,
                max_rounds=1,
                candidate_file=self.candidates,
            ),
            reviewer=self,
        )
        with pytest.raises(
            HumanizeRunAlreadyActiveError,
            match="already active",
        ):
            direct.run()
        self.blocked_stages.append(stage)
        return super().review(stage, prompt, stage_dir)


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
    humanize = repo / "humanize"
    humanize.mkdir()
    for name in ("pipeline.py", "audit_state.py", "state.py"):
        (humanize / name).write_text(f"# fake humanize/{name}\n")
    tests = repo / "tests"
    tests.mkdir()
    (tests / "verify_known_answer_gate.py").write_text(
        "# fake strict known-answer runner\n"
    )
    results = repo / "results"
    results.mkdir()
    (results / "known_code_registry.json").write_text(
        '{"schema_version": 1, "registry_sha256": "test"}\n'
    )
    known_answer = results / "known_answer_gate.json"
    known_answer.write_text('{"passed": true}\n')
    (results / "known_answer_trust.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "artifact_sha256": hashlib.sha256(
                    known_answer.read_bytes()
                ).hexdigest(),
                "semantic_sha256": "a" * 64,
                "environment": {"python": "test"},
            }
        )
        + "\n"
    )
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
        proof_retry_max_attempts=1,
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
    known_answer_sha = hashlib.sha256(
        Path(config.known_answer_artifact).read_bytes()
    ).hexdigest()
    n, k, d = 72, 16, 8
    fom = k * d * d / n
    claim = {
        "canonical_digest": digest,
        "n": n,
        "k": k,
        "d": d,
        "fom": fom,
    }
    win = classify_win(n, k, d)
    assert win["passed"] is True
    certificate = {
        "schema_version": 1,
        "certificate_type": "qldpc-css-bb-exact",
        "passed": artifact_passed,
        "known_answer": {"artifact_sha256": known_answer_sha},
        "claim": claim,
        "milp": {
            "exact": True,
            "expected_directions": 2 * k,
            "completed_directions": 2 * k,
            "distance": d,
            "directions": [{"objective": d} for _ in range(2 * k)],
        },
        "final_gate": {
            "accepted": True,
            "checks": {
                "challenge_win": True,
                "reported_fom_matches": True,
            },
            "failures": [],
            "candidate": {"n": n, "k": k, "d": d, "fom": fom},
            "win": win,
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


def test_shared_run_lease_blocks_direct_humanize_through_all_five_stages(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    run_id = "shared-five-stage-lease"
    config = _config(repo, candidates, run_id=run_id)
    unresolved = {
        "canonical_digest": "route-under-shared-lease",
        "status": "UNRESOLVED",
    }
    proven, _ = _certificate(config, "shared-lease-proof")
    reviewer = SharedLeaseProbeReviewer(repo, candidates, run_id)

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(
            stage2=[_plan([unresolved])],
            stage3=[_plan([proven])],
        ),
        reviewer=reviewer,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert reviewer.calls == list(STAGE_ORDER)
    assert reviewer.blocked_stages == list(STAGE_ORDER)


def test_pipeline_refuses_to_start_while_direct_humanize_owns_run(tmp_path):
    repo, candidates = _repo(tmp_path)
    run_id = "direct-owner-blocks-pipeline"
    config = _config(repo, candidates, run_id=run_id)
    direct = HumanizeFlow(
        FlowConfig(
            repo_dir=repo,
            run_id=run_id,
            candidate_file=candidates,
        ),
        reviewer=RecordingReviewer(),
    )
    pipeline = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(),
        reviewer=RecordingReviewer(),
    )

    with _acquire_humanize_run_lease(direct.store):
        with pytest.raises(PipelineBusyError) as failure:
            pipeline.run()

    assert failure.value.classification == "PIPELINE_BUSY"
    assert pipeline._humanize_run_lease is None
    assert pipeline.run()["status"] == "COMPLETED_NO_WIN"


def test_completed_win_writer_is_exporter_compatible(tmp_path):
    repo, candidates = _repo(tmp_path)
    run_id = "writer-export-contract"
    config = _config(repo, candidates, run_id=run_id)
    proven, _ = _certificate(config, run_id)

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(stage2=[_plan([proven])]),
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert (
        json.loads((config.root / "artifacts" / "stage4-summary.json").read_text())[
            "routing"
        ]
        == "STRICT_GATE"
    )
    assert (
        json.loads((config.root / "artifacts" / "stage5-final-gate.json").read_text())[
            "passed"
        ]
        is True
    )

    destination = repo / "results" / "runs" / run_id
    destination.mkdir(parents=True)
    evaluations = destination / "evaluations.jsonl"
    evaluations.write_text('{"source":"humanize"}\n')

    result = export_release(repo_dir=repo, run_id=run_id)

    assert result["status"] == "exported"
    assert result["certificates"] == 1
    assert Path(result["manifest"]).is_file()
    assert evaluations.read_text() == '{"source":"humanize"}\n'
    assert export_release(repo_dir=repo, run_id=run_id)["status"] == "already-exported"


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


def test_stage3_audits_entire_bounded_stage2_page_and_finds_second_win(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="stage3-entire-stage2-page"),
        stage2_top=2,
        stage3_top=0,
    )
    first_digest = "stage3-first-loser"
    second_digest = "stage3-second-winner"
    stage2_results = [
        {"canonical_digest": first_digest, "status": "UNRESOLVED"},
        {"canonical_digest": second_digest, "status": "UNRESOLVED"},
    ]
    first_loser, _ = _certificate(
        config,
        first_digest,
        certificate_passed=False,
        verification_passed=False,
    )
    second_winner, _ = _certificate(config, second_digest)
    runner = ScenarioRunner(
        stage2=[_plan(stage2_results)],
        stage3=[_plan([first_loser, second_winner])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "stage3": 1, "strict": 1}
    stage3_command = runner.commands("stage3")[0]
    assert stage3_command[stage3_command.index("--top") + 1] == "0"
    stage4 = json.loads(
        (config.root / "artifacts" / "stage4-summary.json").read_text()
    )
    assert [entry["canonical_digest"] for entry in stage4["entries"]] == [
        second_digest
    ]


def test_stage3_incomplete_page_is_pinned_and_replayed_before_later_work(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="stage3-pinned-page-resume"),
        stage2_top=2,
        stage3_top=0,
    )
    first_digest = "stage3-pinned-loser"
    second_digest = "stage3-pinned-winner"
    unresolved = [
        {"canonical_digest": first_digest, "status": "UNRESOLVED"},
        {"canonical_digest": second_digest, "status": "UNRESOLVED"},
    ]
    first_loser, _ = _certificate(
        config,
        first_digest,
        certificate_passed=False,
        verification_passed=False,
    )
    incomplete, _ = _certificate(
        config,
        second_digest,
        verification_passed=False,
    )
    winner, _ = _certificate(config, second_digest)
    runner = ScenarioRunner(
        stage2=[
            _plan(
                unresolved,
                selection_exhausted=False,
                selection_page=(0, 2),
            ),
            _plan(
                unresolved,
                selection_exhausted=False,
                selection_page=(0, 2),
            ),
        ],
        stage3=[
            _plan([first_loser, incomplete]),
            _plan([first_loser, winner]),
        ],
    )

    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert first["status"] == "INCOMPLETE"
    ledger_path = config.root / "solver-state" / "stage2-selection-ledger.json"
    pending_before_resume = json.loads(ledger_path.read_text())["pending"]
    assert pending_before_resume["start_index"] == 0
    assert pending_before_resume["selected_digests"] == [
        first_digest,
        second_digest,
    ]

    resumed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert resumed["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "stage3": 2, "strict": 1}
    assert json.loads(ledger_path.read_text())["pending"] == pending_before_resume
    assert all(
        command[command.index("--top") + 1] == "0"
        for command in runner.commands("stage3")
    )


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


def test_unverified_certificate_is_incomplete_and_same_config_resume_retries(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="no-win")
    unresolved = {"canonical_digest": "still-open", "status": "UNRESOLVED"}
    unverified, _ = _certificate(config, "not-independent", verification_passed=False)
    verified, _ = _certificate(config, "not-independent")
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unverified]), _plan([verified])],
    )
    # Even an advisory "promote" is not allowed to waive certificate flags.
    reviewer = RecordingReviewer(verdict="promote")

    first = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()

    assert first["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 1, "stage3": 1}
    assert first["stages"]["stage3_direction_audit"]["machine_status"] == "INCOMPLETE"
    assert first["stages"]["stage5_strict_gate"]["machine_status"] == "SKIPPED"
    assert reviewer.calls == list(STAGE_ORDER)
    terminal = json.loads(
        (config.root / "artifacts" / "stage5-incomplete.json").read_text()
    )
    assert terminal["status"] == "INCOMPLETE"

    second = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "stage3": 2, "strict": 1}
    assert second["stages"]["stage2_sector_audit"]["attempt"] == 1
    assert second["stages"]["stage3_direction_audit"]["attempt"] == 2


def test_partial_stage2_certificate_is_incomplete_and_retried(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="partial-stage2")
    partial, _ = _certificate(config, "partial-stage2")
    partial["certificate"]["certificate_exact"] = False
    partial["certificate"]["certificate_passed"] = False
    partial["certificate"]["verification_passed"] = False
    verified, _ = _certificate(config, "partial-stage2")
    runner = ScenarioRunner(stage2=[_plan([partial]), _plan([verified])])
    reviewer = RecordingReviewer()

    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()
    second = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert first["status"] == "INCOMPLETE"
    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 1}
    assert second["stages"]["stage2_sector_audit"]["attempt"] == 2


def test_proof_retry_controller_escalates_1x_2x_4x_then_caps(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-escalation"),
        proof_retry_max_attempts=6,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {"canonical_digest": "retry-me", "status": "UNRESOLVED"}
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=False,
                selection_page=(0, 1),
            )
        ],
        stage3=[_plan([unresolved])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 3, "stage3": 3}
    stage2_commands = [
        command for stage, command in runner.calls if stage == "stage2"
    ]
    assert [
        float(command[command.index("--timeout") + 1])
        for command in stage2_commands
    ] == [300, 600, 1200]
    assert [
        int(command[command.index("--max-total-workers") + 1])
        for command in stage2_commands
    ] == [config.max_total_workers] * 3
    controller = json.loads(
        (config.root / "solver-state" / "proof-retry-controller.json").read_text()
    )
    active = controller["active"]
    assert active["status"] == "CAPPED"
    assert active["cap_reason"] == "NO_PROGRESS_AT_MAX_MULTIPLIER"
    assert [item["multiplier"] for item in active["attempts"]] == [1, 2, 4]
    assert active["binding"]["selected_digests"] == ["retry-me"]
    assert active["binding"]["page_sha256"]
    assert active["binding"]["source_fingerprint"]
    assert active["binding"]["proof_config_sha256"]
    assert state["proof_retry"]["resume_required"] is True


def test_proof_retry_max_attempts_caps_before_next_budget(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-max-attempts"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {"canonical_digest": "attempt-cap", "status": "UNRESOLVED"}
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unresolved])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 2, "stage3": 2}
    assert state["proof_retry"]["cap_reason"] == "MAX_ATTEMPTS_REACHED"
    controller = json.loads(
        (config.root / "solver-state" / "proof-retry-controller.json").read_text()
    )
    assert [item["multiplier"] for item in controller["active"]["attempts"]] == [
        1,
        2,
    ]


def test_proof_retry_does_not_spin_on_non_solver_input_errors(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-bad-input"),
        proof_retry_max_attempts=6,
        proof_retry_backoff_seconds=0,
    )
    runner = ScenarioRunner(
        stage2=[_plan([], canonicalization_errors=1)],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 1}
    assert not (
        config.root / "solver-state" / "proof-retry-controller.json"
    ).exists()


def test_proof_retry_direction_progress_holds_budget_before_escalating(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-progress"),
        proof_retry_max_attempts=6,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {"canonical_digest": "progressing", "status": "UNRESOLVED"}
    underlying = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unresolved])],
    )

    def progress_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        completed = underlying(command, cwd=cwd)
        if (
            Path(command[1]).name == "audit_direction_pool.py"
            and underlying.counts["stage3"] == 2
        ):
            _write_json(
                config.root
                / "solver-state"
                / "directions"
                / "progress.json",
                {
                    "completed_directions": 1,
                    "directions": [{"objective": 9}],
                },
            )
        return completed

    state = FiveStagePipeline(
        config,
        command_runner=progress_runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "INCOMPLETE"
    stage2_commands = [
        command for stage, command in underlying.calls if stage == "stage2"
    ]
    assert [
        float(command[command.index("--timeout") + 1])
        for command in stage2_commands
    ] == [300, 600, 1200]
    stage3_commands = [
        command for stage, command in underlying.calls if stage == "stage3"
    ]
    assert [
        float(command[command.index("--timeout") + 1])
        for command in stage3_commands
    ] == [300, 600, 600, 1200]
    controller = json.loads(
        (config.root / "solver-state" / "proof-retry-controller.json").read_text()
    )
    attempts = controller["active"]["attempts"]
    assert [item["multiplier"] for item in attempts] == [1, 2, 2, 4]
    assert attempts[1]["made_progress"] is True
    assert attempts[1]["progress_after"]["completed_units"] == 1


def test_proof_retry_prepared_attempt_survives_crash_and_resumes(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-crash"),
        proof_retry_max_attempts=4,
        proof_retry_backoff_seconds=1,
    )
    unresolved = {"canonical_digest": "crash-retry", "status": "UNRESOLVED"}
    winner, _ = _certificate(config, "crash-retry")
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unresolved]), _plan([winner])],
    )

    def interrupt_backoff(_seconds: float) -> None:
        raise KeyboardInterrupt

    with pytest.raises(KeyboardInterrupt):
        FiveStagePipeline(
            config,
            command_runner=runner,
            reviewer=RecordingReviewer(),
            sleeper=interrupt_backoff,
        ).run()

    controller_path = (
        config.root / "solver-state" / "proof-retry-controller.json"
    )
    interrupted = json.loads(controller_path.read_text())
    assert [item["status"] for item in interrupted["active"]["attempts"]] == [
        "COMPLETED_INCOMPLETE",
        "PREPARED",
    ]
    assert interrupted["active"]["attempts"][-1]["multiplier"] == 2
    assert runner.counts == {"stage2": 1, "stage3": 1}

    sleeps: list[float] = []
    resumed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=sleeps.append,
    ).run()

    assert resumed["status"] == "COMPLETED_WIN"
    assert sleeps == [1]
    assert runner.counts == {"stage2": 2, "stage3": 2, "strict": 1}
    completed = json.loads(controller_path.read_text())["active"]
    assert [item["attempt"] for item in completed["attempts"]] == [1, 2]
    assert completed["attempts"][-1]["status"] == "COMPLETED_WIN"


def test_proof_retry_campaign_total_timeout_caps_after_current_attempt(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-total-timeout"),
        proof_retry_max_attempts=6,
        proof_retry_campaign_total_timeout=0.5,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {"canonical_digest": "total-timeout", "status": "UNRESOLVED"}
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unresolved])],
    )
    clock = iter([0.0, 1.0])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
        monotonic=lambda: next(clock),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 1, "stage3": 1}
    assert state["proof_retry"]["cap_reason"] == (
        "CAMPAIGN_TOTAL_TIMEOUT_REACHED"
    )


def test_proof_retry_win_stops_before_later_budgets(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-win"),
        proof_retry_max_attempts=6,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {"canonical_digest": "retry-win", "status": "UNRESOLVED"}
    winner, _ = _certificate(config, "retry-win")
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unresolved]), _plan([winner])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "stage3": 2, "strict": 1}
    stage2_commands = [
        command for stage, command in runner.calls if stage == "stage2"
    ]
    assert [
        float(command[command.index("--timeout") + 1])
        for command in stage2_commands
    ] == [300, 600]
    controller = json.loads(
        (config.root / "solver-state" / "proof-retry-controller.json").read_text()
    )
    assert controller["active"]["status"] == "COMPLETED_WIN"
    assert [item["multiplier"] for item in controller["active"]["attempts"]] == [
        1,
        2,
    ]


def test_proof_retry_retries_hard_wall_error_then_stops_on_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-hard-wall"),
        proof_retry_max_attempts=6,
        proof_retry_backoff_seconds=0,
    )
    hard_wall_error = {
        "canonical_digest": "hard-wall-retry",
        "status": "ERROR",
        "error": "TimeoutError: candidate process hard-wall timeout",
        "hard_wall": {
            "timed_out": True,
            "candidate_timeout_s": 300,
        },
    }
    winner, _ = _certificate(config, "hard-wall-retry")
    runner = ScenarioRunner(
        stage2=[
            _plan([hard_wall_error], returncode=2),
            _plan([winner]),
        ],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 1}
    stage2_commands = runner.commands("stage2")
    assert [
        float(command[command.index("--timeout") + 1])
        for command in stage2_commands
    ] == [300, 600]
    assert [
        int(command[command.index("--max-total-workers") + 1])
        for command in stage2_commands
    ] == [config.max_total_workers, config.max_total_workers]
    controller = json.loads(
        (config.root / "solver-state" / "proof-retry-controller.json").read_text()
    )
    assert controller["active"]["status"] == "COMPLETED_WIN"
    assert [item["multiplier"] for item in controller["active"]["attempts"]] == [
        1,
        2,
    ]


def test_verified_win_survives_peer_certificate_hard_wall(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-peer-hard-wall"),
        proof_retry_max_attempts=6,
        proof_retry_backoff_seconds=0,
    )
    winner, _ = _certificate(config, "hard-wall-surviving-win")
    timed_out_peer = {
        "canonical_digest": "hard-wall-certificate-peer",
        "status": "THRESHOLD_PROVEN",
        "certificate": {
            "attempted": True,
            "certificate_passed": False,
            "verification_passed": False,
            "error": "certificate/verification candidate hard-wall timeout",
            "hard_wall": {
                "timed_out": True,
                "candidate_timeout_s": 600,
            },
        },
    }
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [winner, timed_out_peer],
                operational_errors=1,
                returncode=2,
            )
        ],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "strict": 1}
    assert state["result"]["verified_certificates"] == 1
    assert state["stages"]["stage2_sector_audit"][
        "accepted_nonzero_output"
    ] is True
    assert not (
        config.root / "solver-state" / "proof-retry-controller.json"
    ).exists()


def test_exact_certificate_loser_is_terminal_no_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="exact-loser")
    loser, _ = _certificate(
        config,
        "exact-loser",
        certificate_passed=False,
        verification_passed=False,
    )
    runner = ScenarioRunner(stage2=[_plan([loser])])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": 1}
    assert state["stages"]["stage2_sector_audit"]["machine_status"] == "COMPLETED"


@pytest.mark.parametrize("with_certificate", [False, True])
def test_truncated_selection_is_incomplete_unless_verified_certificate_wins(
    tmp_path,
    with_certificate,
):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"truncated-{'win' if with_certificate else 'empty'}",
    )
    results = []
    if with_certificate:
        proven, _ = _certificate(config, "truncated-win")
        results.append(proven)
    runner = ScenarioRunner(
        stage2=[_plan(results, selection_exhausted=False)],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    expected = "COMPLETED_WIN" if with_certificate else "INCOMPLETE"
    assert state["status"] == expected
    assert runner.counts["strict"] == int(with_certificate)
    assert (
        json.loads(
            (config.root / "artifacts" / "stage4-summary.json").read_text()
        )["routing"]
        == ("STRICT_GATE" if with_certificate else "INCOMPLETE")
    )


def test_paginated_stage2_automatically_reaches_win_on_second_page(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="paginated-second-page-win")
    loser, _ = _certificate(
        config,
        "page-one-loser",
        certificate_passed=False,
        verification_passed=False,
    )
    winner, _ = _certificate(config, "page-two-winner")
    runner = ScenarioRunner(stage2=[
        _plan(
            [loser],
            selection_exhausted=False,
            selection_page=(0, 1),
        ),
        _plan(
            [winner],
            selection_exhausted=True,
            selection_page=(1, 2),
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 1}
    ledger = json.loads(
        (config.root / "solver-state" / "stage2-selection-ledger.json").read_text()
    )
    assert ledger["cursor"] == 1
    assert ledger["committed_digests"] == ["page-one-loser"]
    assert ledger["pending"]["selected_digests"] == ["page-two-winner"]
    assert state["stage2_pagination"]["completed_pages"] == 1


def test_paginated_terminal_page_advances_past_global_input_diagnostic(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="paginated-global-diagnostic-win"),
        stage2_top=1,
    )
    loser, _ = _certificate(
        config,
        "global-diagnostic-loser",
        certificate_passed=False,
        verification_passed=False,
    )
    winner, _ = _certificate(config, "global-diagnostic-winner")
    runner = ScenarioRunner(stage2=[
        _plan(
            [loser],
            selection_exhausted=False,
            selection_page=(0, 1),
            canonicalization_errors=1,
        ),
        _plan(
            [winner],
            selection_exhausted=True,
            selection_page=(1, 2),
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 1}
    assert state["stage2_pagination"]["cursor"] == 1
    assert state["stage2_pagination"]["global_input_incompleteness"] == [
        {
            "stage": "stage2_sector_audit",
            "reason": (
                "Stage 2 candidates failed authoritative canonicalization: 1"
            ),
            "code": "STAGE2_CANONICALIZATION_ERRORS",
        }
    ]


def test_paginated_global_input_diagnostic_still_blocks_final_no_win(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="paginated-global-diagnostic-no-win"),
        stage2_top=1,
    )
    first, _ = _certificate(
        config,
        "global-diagnostic-first-loser",
        certificate_passed=False,
        verification_passed=False,
    )
    second, _ = _certificate(
        config,
        "global-diagnostic-second-loser",
        certificate_passed=False,
        verification_passed=False,
    )
    runner = ScenarioRunner(stage2=[
        _plan(
            [first],
            selection_exhausted=False,
            selection_page=(0, 1),
            canonicalization_errors=1,
        ),
        _plan(
            [second],
            selection_exhausted=True,
            selection_page=(1, 2),
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 2}
    reasons = state["result"]["proof_incompleteness"]["reasons"]
    assert {
        reason["code"] for reason in reasons
    } == {"STAGE2_CANONICALIZATION_ERRORS"}


def test_paginated_stage2_interruption_replays_pending_second_page(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="paginated-interrupt-resume")
    loser, _ = _certificate(
        config,
        "interrupt-page-one",
        certificate_passed=False,
        verification_passed=False,
    )
    winner, _ = _certificate(config, "interrupt-page-two")
    underlying = ScenarioRunner(stage2=[
        _plan(
            [loser],
            selection_exhausted=False,
            selection_page=(0, 1),
        ),
        _plan(
            [winner],
            selection_exhausted=True,
            selection_page=(1, 2),
        ),
    ])
    interrupted = False

    def interrupt_second_page(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        nonlocal interrupted
        completed = underlying(command, cwd=cwd)
        if (
            Path(command[1]).name == "audit_candidate_pool.py"
            and underlying.counts["stage2"] == 2
            and not interrupted
        ):
            interrupted = True
            raise KeyboardInterrupt
        return completed

    with pytest.raises(KeyboardInterrupt):
        FiveStagePipeline(
            config,
            command_runner=interrupt_second_page,
            reviewer=RecordingReviewer(),
        ).run()

    ledger_path = (
        config.root / "solver-state" / "stage2-selection-ledger.json"
    )
    interrupted_ledger = json.loads(ledger_path.read_text())
    assert interrupted_ledger["cursor"] == 1
    assert interrupted_ledger["pending"]["start_index"] == 1

    resumed = FiveStagePipeline(
        config,
        command_runner=interrupt_second_page,
        reviewer=RecordingReviewer(),
    ).run()

    assert resumed["status"] == "COMPLETED_WIN"
    assert underlying.counts == {"stage2": 3, "strict": 1}
    assert resumed["stages"]["stage2_sector_audit"]["attempt"] == 3
    resumed_ledger = json.loads(ledger_path.read_text())
    assert resumed_ledger["cursor"] == 1
    assert resumed_ledger["pending"] == interrupted_ledger["pending"]


def test_paginated_stage2_stops_when_cursor_makes_no_progress(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="pagination-no-progress")
    runner = ScenarioRunner(stage2=[
        _plan(
            [],
            selection_exhausted=False,
            selection_page=(0, 0),
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 1}
    assert state["stage2_pagination"]["no_progress"] is True
    assert state["stage2_pagination"]["cursor"] == 0


def test_paginated_page_advances_after_stage3_rejects_unresolved(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="pagination-stage3-reject")
    unresolved = {
        "canonical_digest": "stage3-page-one",
        "status": "UNRESOLVED",
    }
    rejected = {
        "canonical_digest": "stage3-page-one",
        "status": "REJECTED",
    }
    winner, _ = _certificate(config, "stage3-page-two-winner")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=False,
                selection_page=(0, 1),
            ),
            _plan(
                [winner],
                selection_exhausted=True,
                selection_page=(1, 2),
            ),
        ],
        stage3=[_plan([rejected])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "stage3": 1, "strict": 1}
    assert state["stage2_pagination"]["cursor"] == 1
    assert state["stage2_pagination"]["completed_pages"] == 1


def test_paginated_page_digest_order_must_match_results(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="pagination-order-binding")
    first, _ = _certificate(
        config,
        "pagination-order-first",
        certificate_passed=False,
        verification_passed=False,
    )
    second, _ = _certificate(
        config,
        "pagination-order-second",
        certificate_passed=False,
        verification_passed=False,
    )
    underlying = ScenarioRunner(stage2=[
        _plan(
            [first, second],
            selection_exhausted=False,
            selection_page=(0, 2),
        ),
    ])

    def reordered_page_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        completed = underlying(command, cwd=cwd)
        if Path(command[1]).name == "audit_candidate_pool.py":
            summary_path = _argument(command, "--summary-output")
            summary = json.loads(summary_path.read_text())
            page = summary["selection_page"]
            page["selected_digests"].reverse()
            page["page_sha256"] = hashlib.sha256(
                json.dumps(
                    {
                        key: page[key]
                        for key in (
                            "binding_sha256",
                            "start_index",
                            "next_index",
                            "selected_digests",
                        )
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest()
            _write_json(summary_path, summary)
        return completed

    state = FiveStagePipeline(
        config,
        command_runner=reordered_page_runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert state["failure"]["stage"] == "stage2_sector_audit"


def test_proof_reviewer_failure_is_advisory_and_resume_retries_only_review(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="review-resume")
    runner = ScenarioRunner(stage2=[_plan([])])
    flaky = RecordingReviewer(fail_once={"stage2_sector_audit"})

    first = FiveStagePipeline(config, command_runner=runner, reviewer=flaky).run()
    assert first["status"] == "COMPLETED_NO_WIN"
    assert "failure" not in first
    stage2 = first["stages"]["stage2_sector_audit"]
    assert stage2["machine_status"] == "COMPLETED"
    assert stage2["status"] == "COMPLETED"
    assert stage2["review_status"] == "ADVISORY_FAILED"
    assert stage2["advisory_failure"] == {
        "classification": "ADVISORY_FAILED",
        "error": (
            "RuntimeError: simulated stage2_sector_audit reviewer outage"
        ),
        "attempt": 1,
        "timestamp": stage2["review_finished_at"],
    }
    assert not (config.root / "reviews" / "stage2_sector_audit" / "review.json").exists()
    assert runner.counts["stage2"] == 1

    completed = FiveStagePipeline(config, command_runner=runner, reviewer=flaky).run()
    assert completed["status"] == "COMPLETED_NO_WIN"
    assert runner.counts["stage2"] == 1
    assert flaky.calls.count("stage2_sector_audit") == 2
    assert completed["stages"]["stage2_sector_audit"]["attempt"] == 1
    assert (
        completed["stages"]["stage2_sector_audit"]["review_attempt"]
        == 2
    )
    assert (
        completed["stages"]["stage2_sector_audit"]["review_status"]
        == "COMPLETED"
    )
    assert (
        "advisory_failure"
        not in completed["stages"]["stage2_sector_audit"]
    )


def test_stage2_through_stage4_advisory_failures_preserve_machine_routing(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="proof-advisory-routing")
    unresolved = {
        "canonical_digest": "advisory-route",
        "status": "UNRESOLVED",
    }
    proven, _ = _certificate(config, "advisory-proof")
    runner = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([proven])],
    )
    failed_reviews = {
        "stage2_sector_audit",
        "stage3_direction_audit",
        "stage4_certificate_merge",
    }
    reviewer = RecordingReviewer(fail_once=failed_reviews)

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert "failure" not in state
    assert runner.counts == {"stage2": 1, "stage3": 1, "strict": 1}
    for stage in failed_reviews:
        record = state["stages"][stage]
        assert record["review_status"] == "ADVISORY_FAILED"
        assert record["status"] == record["machine_status"]
        assert record["advisory_failure"]["classification"] == "ADVISORY_FAILED"
        assert record["advisory_failure"]["attempt"] == 1
        assert not (config.root / "reviews" / stage / "review.json").exists()


def test_stage5_strict_win_survives_advisory_reviewer_failure(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-win-advisory")
    proven, _ = _certificate(config, "strict-win-advisory")
    runner = ScenarioRunner(stage2=[_plan([proven])])
    reviewer = RecordingReviewer(fail_once={"stage5_strict_gate"})

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert "failure" not in state
    assert runner.counts == {"stage2": 1, "strict": 1}
    strict = state["stages"]["stage5_strict_gate"]
    assert strict["machine_status"] == "COMPLETED"
    assert strict["status"] == "COMPLETED"
    assert strict["review_status"] == "ADVISORY_FAILED"
    assert strict["advisory_failure"]["classification"] == "ADVISORY_FAILED"
    assert (config.root / "artifacts" / "stage5-final-gate.json").is_file()
    assert not (config.root / "reviews" / "stage5_strict_gate" / "review.json").exists()


def test_proof_reviewer_schema_error_is_advisory(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="proof-review-schema-error")

    class MalformedReviewer(RecordingReviewer):
        def review(self, stage: str, prompt: str, stage_dir: Path) -> dict:
            if stage == "stage4_certificate_merge":
                self.calls.append(stage)
                return {"verdict": "continue"}
            return super().review(stage, prompt, stage_dir)

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(),
        reviewer=MalformedReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_NO_WIN"
    stage4 = state["stages"]["stage4_certificate_merge"]
    assert stage4["review_status"] == "ADVISORY_FAILED"
    assert stage4["advisory_failure"]["classification"] == "ADVISORY_FAILED"
    assert stage4["advisory_failure"]["error"].startswith("ReviewError:")


def test_stage1_reviewer_failure_remains_fail_closed(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="stage1-review-fail-closed")
    runner = ScenarioRunner()
    reviewer = RecordingReviewer(fail_once={"stage1_search"})

    failed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert failed["status"] == "FAILED"
    assert failed["failure"]["classification"] == "REVIEW_FAILED"
    stage1 = failed["stages"]["stage1_search"]
    assert stage1["machine_status"] == "COMPLETED"
    assert stage1["review_status"] == "FAILED"
    assert runner.counts == {}


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
            _plan([{"canonical_digest": "retry", "status": "REJECTED"}]),
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


def test_stage2_poison_does_not_mask_replay_verified_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="poison-plus-win")
    poison = {
        "canonical_digest": "poison",
        "status": "ERROR",
        "error": "solver worker crashed",
    }
    winner, _ = _certificate(config, "surviving-win")
    runner = ScenarioRunner(
        stage2=[_plan([poison, winner], returncode=2)],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "strict": 1}
    stage2 = state["stages"]["stage2_sector_audit"]
    assert stage2["exit_code"] == 2
    assert stage2["accepted_nonzero_output"] is True


def test_stage2_poison_only_is_incomplete_and_fail_closed(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="poison-only")
    poison = {
        "canonical_digest": "only-poison",
        "status": "ERROR",
        "error": "solver worker crashed",
    }
    runner = ScenarioRunner(
        stage2=[_plan([poison], returncode=2)],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 1}
    assert (
        state["stages"]["stage2_sector_audit"]["machine_status"]
        == "INCOMPLETE"
    )
    assert {
        reason["code"]
        for reason in state["result"]["proof_incompleteness"]["reasons"]
    } >= {"STAGE2_OPERATIONAL_ERROR"}


def test_stage3_nonzero_poison_does_not_mask_replay_verified_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="stage3-poison-plus-win")
    stage2_results = [
        {"canonical_digest": "stage3-poison", "status": "UNRESOLVED"},
        {"canonical_digest": "stage3-surviving-win", "status": "UNRESOLVED"},
    ]
    poison = {
        "canonical_digest": "stage3-poison",
        "status": "ERROR",
        "error": "direction worker crashed",
    }
    winner, _ = _certificate(config, "stage3-surviving-win")
    runner = ScenarioRunner(
        stage2=[_plan(stage2_results)],
        stage3=[_plan([poison, winner], returncode=2)],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "stage3": 1, "strict": 1}
    stage3 = state["stages"]["stage3_direction_audit"]
    assert stage3["exit_code"] == 2
    assert stage3["accepted_nonzero_output"] is True


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


def test_stage5_winner_survives_peer_timeout(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-existential-win")
    winner, _ = _certificate(config, "strict-winner")
    peer, _ = _certificate(config, "strict-timeout-peer")
    runner = ScenarioRunner(
        stage2=[_plan([winner, peer])],
        strict=[
            _plan(strict_dispositions=["ACCEPTED", "INCOMPLETE"]),
        ],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    gate = json.loads(
        (config.root / "artifacts" / "stage5-final-gate.json").read_text()
    )
    assert gate["outcome"] == "WIN"
    assert gate["summary"] == {
        "accepted": 1,
        "rejected": 0,
        "incomplete": 1,
        "total": 2,
    }


def test_stage5_all_terminal_rejections_are_no_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-all-rejected")
    first, _ = _certificate(config, "strict-rejected-1")
    second, _ = _certificate(config, "strict-rejected-2")
    runner = ScenarioRunner(
        stage2=[_plan([first, second])],
        strict=[_plan(strict_dispositions=["REJECTED", "REJECTED"])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_NO_WIN"
    assert state["stages"]["stage5_strict_gate"]["machine_status"] == "COMPLETED"


def test_stage5_without_winner_and_with_timeout_is_retryable(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-no-winner-timeout")
    rejected, _ = _certificate(config, "strict-terminal-reject")
    timeout, _ = _certificate(config, "strict-incomplete-peer")
    runner = ScenarioRunner(
        stage2=[_plan([rejected, timeout])],
        strict=[_plan(strict_dispositions=["REJECTED", "INCOMPLETE"])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert state["result"]["incomplete"] == str(
        config.root / "artifacts" / "stage5-final-gate.json"
    )
    assert state["stages"]["stage5_strict_gate"]["machine_status"] == "INCOMPLETE"


def test_stage5_timeout_keeps_current_proof_page_pending(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-timeout-pins-page")
    rejected, _ = _certificate(config, "strict-page-reject")
    timeout, _ = _certificate(config, "strict-page-timeout")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [rejected, timeout],
                selection_exhausted=False,
                selection_page=(0, 2),
            )
        ],
        strict=[_plan(strict_dispositions=["REJECTED", "INCOMPLETE"])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert state["result"]["stage5_outcome"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 1, "strict": 1}
    ledger = json.loads(
        (config.root / "solver-state" / "stage2-selection-ledger.json").read_text()
    )
    assert ledger["cursor"] == 0
    assert ledger["pending"] is not None


def test_stage5_incomplete_automatically_retries_with_scaled_strict_budget(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    run_id = "strict-timeout-auto-retry"
    config = replace(
        _config(repo, candidates, run_id=run_id),
        proof_retry_max_attempts=4,
        proof_retry_backoff_seconds=0,
    )
    winner, _ = _certificate(config, "strict-timeout-eventual-win")
    runner = ScenarioRunner(
        stage2=[_plan([winner])],
        strict=[
            _plan(strict_dispositions=["INCOMPLETE"]),
            _plan(strict_dispositions=["ACCEPTED"]),
        ],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 2}
    strict_commands = runner.commands("strict")
    assert [
        float(command[command.index("--verification-timeout-per-logical") + 1])
        for command in strict_commands
    ] == [300, 600]
    assert [
        float(command[command.index("--verification-total-timeout") + 1])
        for command in strict_commands
    ] == [7200, 14400]
    assert [
        int(command[command.index("--known-answer-timeout-per-logical") + 1])
        for command in strict_commands
    ] == [300, 600]
    assert [
        int(command[command.index("--known-answer-total-timeout") + 1])
        for command in strict_commands
    ] == [7200, 14400]
    controller = json.loads(
        (config.root / "solver-state" / "proof-retry-controller.json").read_text()
    )
    active = controller["active"]
    assert active["status"] == "COMPLETED_WIN"
    assert [attempt["multiplier"] for attempt in active["attempts"]] == [1, 2]
    assert active["binding"]["strict_source_fingerprint"]
    assert active["binding"]["strict_runner_sha256"]
    assert active["binding"]["strict_inputs"][str(
        config.root / "artifacts" / "stage4-certificates.jsonl"
    )]

    exported = export_release(repo_dir=repo, run_id=run_id)
    assert exported["status"] == "exported"
    assert exported["certificates"] == 1


def test_stage5_prepared_retry_survives_restart_and_keeps_pending_page(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="strict-timeout-prepared-resume"),
        proof_retry_max_attempts=4,
        proof_retry_backoff_seconds=1,
    )
    winner, _ = _certificate(config, "strict-timeout-resumed-win")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [winner],
                selection_exhausted=False,
                selection_page=(0, 1),
            )
        ],
        strict=[
            _plan(strict_dispositions=["INCOMPLETE"]),
            _plan(strict_dispositions=["ACCEPTED"]),
        ],
    )

    def interrupt_backoff(_seconds: float) -> None:
        raise KeyboardInterrupt

    with pytest.raises(KeyboardInterrupt):
        FiveStagePipeline(
            config,
            command_runner=runner,
            reviewer=RecordingReviewer(),
            sleeper=interrupt_backoff,
        ).run()

    ledger_path = (
        config.root / "solver-state" / "stage2-selection-ledger.json"
    )
    pending_before = json.loads(ledger_path.read_text())["pending"]
    controller_path = (
        config.root / "solver-state" / "proof-retry-controller.json"
    )
    interrupted = json.loads(controller_path.read_text())["active"]
    assert [attempt["status"] for attempt in interrupted["attempts"]] == [
        "COMPLETED_INCOMPLETE",
        "PREPARED",
    ]
    assert interrupted["attempts"][-1]["multiplier"] == 2
    assert runner.counts == {"stage2": 1, "strict": 1}

    sleeps: list[float] = []
    resumed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=sleeps.append,
    ).run()

    assert resumed["status"] == "COMPLETED_WIN"
    assert sleeps == [1]
    assert runner.counts == {"stage2": 2, "strict": 2}
    assert json.loads(ledger_path.read_text())["pending"] == pending_before
    strict_commands = runner.commands("strict")
    assert [
        float(command[command.index("--verification-total-timeout") + 1])
        for command in strict_commands
    ] == [7200, 14400]
    completed = json.loads(controller_path.read_text())["active"]
    assert completed["attempts"][-1]["status"] == "COMPLETED_WIN"


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


@pytest.mark.parametrize("dependency", ["audit_state.py", "state.py"])
def test_humanize_audit_dependency_change_invalidates_proof_stages(
    tmp_path,
    dependency,
):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"humanize-source-change-{dependency}",
    )
    runner = ScenarioRunner()
    reviewer = RecordingReviewer()

    first = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()
    assert first["status"] == "COMPLETED_NO_WIN"
    source = repo / "humanize" / dependency
    source.write_text(source.read_text() + "# changed audit dependency\n")

    second = FiveStagePipeline(config, command_runner=runner, reviewer=reviewer).run()

    assert second["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": 2}
    assert second["stages"]["stage1_search"]["attempt"] == 1
    for stage in STAGE_ORDER[1:]:
        assert second["stages"][stage]["attempt"] == 2


def test_registry_change_invalidates_every_proof_and_strict_stage(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="registry-change")
    proven, _ = _certificate(config, "registry-change")
    runner = ScenarioRunner(stage2=[_plan([proven]), _plan([proven])])
    reviewer = RecordingReviewer()

    first = FiveStagePipeline(
        config, command_runner=runner, reviewer=reviewer,
    ).run()
    assert first["status"] == "COMPLETED_WIN"

    (repo / "results" / "known_code_registry.json").write_text(
        '{"schema_version": 1, "registry_sha256": "changed"}\n'
    )
    second = FiveStagePipeline(
        config, command_runner=runner, reviewer=reviewer,
    ).run()

    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 2}
    assert second["stages"]["stage1_search"]["attempt"] == 1
    for stage in STAGE_ORDER[1:]:
        assert second["stages"][stage]["attempt"] == 2


def test_registry_is_recorded_for_live_stage3_and_strict_inputs(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="registry-stage3-input")
    proven, _ = _certificate(config, "registry-stage3-input")
    unresolved = {
        "canonical_digest": "registry-stage3-input",
        "status": "UNRESOLVED",
    }

    state = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(
            stage2=[_plan([unresolved])],
            stage3=[_plan([proven])],
        ),
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    registry = str((repo / "results" / "known_code_registry.json").resolve())
    strict_runner = str((repo / "tests" / "verify_known_answer_gate.py").resolve())
    assert registry in state["stages"]["stage2_sector_audit"]["input_hashes"]
    assert registry in state["stages"]["stage3_direction_audit"]["input_hashes"]
    stage5_inputs = state["stages"]["stage5_strict_gate"]["input_hashes"]
    assert registry in stage5_inputs
    assert strict_runner in stage5_inputs


def test_strict_runner_change_invalidates_only_strict_stage(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-runner-change")
    proven, _ = _certificate(config, "strict-runner-change")
    runner = ScenarioRunner(stage2=[_plan([proven])])
    reviewer = RecordingReviewer()

    first = FiveStagePipeline(
        config, command_runner=runner, reviewer=reviewer,
    ).run()
    assert first["status"] == "COMPLETED_WIN"

    (repo / "tests" / "verify_known_answer_gate.py").write_text(
        "# changed strict known-answer runner\n"
    )
    second = FiveStagePipeline(
        config, command_runner=runner, reviewer=reviewer,
    ).run()

    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 1, "strict": 2}
    for stage in STAGE_ORDER[:-1]:
        assert second["stages"][stage]["attempt"] == 1
    assert second["stages"]["stage5_strict_gate"]["attempt"] == 2


def test_missing_registry_fails_closed_before_proof_stages(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="missing-registry")
    (repo / "results" / "known_code_registry.json").unlink()
    runner = ScenarioRunner()

    state = FiveStagePipeline(
        config, command_runner=runner, reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "INPUT_MISSING"
    assert runner.counts == {}


def test_missing_strict_runner_fails_closed_before_proof_stages(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="missing-strict-runner")
    (repo / "tests" / "verify_known_answer_gate.py").unlink()
    runner = ScenarioRunner()

    state = FiveStagePipeline(
        config, command_runner=runner, reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "INPUT_MISSING"
    assert runner.counts == {}


@pytest.mark.parametrize(
    "relative_path",
    [
        "results/known_code_registry.json",
        "tests/verify_known_answer_gate.py",
    ],
    ids=["known-code-registry", "strict-runner"],
)
def test_proof_dependency_symlink_escape_fails_closed(tmp_path, relative_path):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"dependency-symlink-{Path(relative_path).stem}",
    )
    dependency = repo / relative_path
    outside = tmp_path / f"outside-{dependency.name}"
    outside.write_bytes(dependency.read_bytes())
    dependency.unlink()
    dependency.symlink_to(outside)
    runner = ScenarioRunner()

    state = FiveStagePipeline(
        config, command_runner=runner, reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "UNSAFE_SOURCE_PATH"
    assert runner.counts == {}


@pytest.mark.parametrize(
    "relative_path",
    [
        "results/known_code_registry.json",
        "tests/verify_known_answer_gate.py",
    ],
    ids=["known-code-registry", "strict-runner"],
)
def test_internal_proof_dependency_symlink_fails_before_commands(
    tmp_path, relative_path
):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"internal-symlink-{Path(relative_path).stem}",
    )
    dependency = repo / relative_path
    target = repo / f"internal-{dependency.name}"
    target.write_bytes(dependency.read_bytes())
    dependency.unlink()
    dependency.symlink_to(target)
    runner = ScenarioRunner()

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "UNSAFE_SOURCE_PATH"
    assert runner.counts == {}


def test_non_python_symlink_inside_source_tree_fails_before_commands(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="source-tree-nonpy-symlink")
    target = repo / "source-metadata.txt"
    target.write_text("trusted-looking metadata\n")
    (repo / "evaluation" / "metadata.txt").symlink_to(target)
    runner = ScenarioRunner()

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "UNSAFE_SOURCE_PATH"
    assert runner.counts == {}


@pytest.mark.parametrize("suffix", [".so", ".pyc"])
def test_unhashed_import_artifact_inside_source_tree_fails_before_commands(
    tmp_path, suffix
):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"source-tree-import-artifact-{suffix[1:]}",
    )
    (repo / "evaluation" / f"verifier{suffix}").write_bytes(b"executable")
    runner = ScenarioRunner()

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "UNSAFE_SOURCE_PATH"
    assert runner.counts == {}


def test_sourceless_module_inside_pycache_fails_before_commands(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="source-tree-pycache-sourceless")
    cache = repo / "evaluation" / "__pycache__"
    cache.mkdir()
    (cache / "evil.pyc").write_bytes(b"executable")
    runner = ScenarioRunner()

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "UNSAFE_SOURCE_PATH"
    assert runner.counts == {}


def test_pep3147_cache_must_be_inert_or_match_current_source(tmp_path):
    source = tmp_path / "evaluation" / "verifier.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(importlib.util.cache_from_source(str(source)))
    py_compile.compile(
        str(source),
        cfile=str(cache),
        doraise=True,
        invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP,
    )

    assert not pipeline_module._is_untrusted_import_artifact(cache)

    # A normal stale timestamp cache is inert: CPython recompiles this source.
    source.write_text("VALUE = 222\n")
    assert not pipeline_module._is_untrusted_import_artifact(cache)

    # A cache with a current header but different executable code is unsafe.
    py_compile.compile(
        str(source),
        cfile=str(cache),
        doraise=True,
        invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP,
    )
    header = cache.read_bytes()[:16]
    forged = compile("VALUE = 'forged'\n", str(source), "exec")
    cache.write_bytes(header + marshal.dumps(forged))
    assert pipeline_module._is_untrusted_import_artifact(cache)


@pytest.mark.parametrize("optimisation", [0, 1, 2])
def test_dotted_source_name_pep3147_cache_is_accepted(
    tmp_path, optimisation
):
    source = tmp_path / "evaluation" / "verifier.extra.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(
        importlib.util.cache_from_source(
            str(source),
            optimization=None if optimisation == 0 else optimisation,
        )
    )
    py_compile.compile(
        str(source),
        cfile=str(cache),
        doraise=True,
        optimize=optimisation,
    )

    assert not pipeline_module._is_untrusted_import_artifact(cache)


def test_different_magic_pep3147_cache_fails_closed(tmp_path):
    source = tmp_path / "evaluation" / "verifier.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(importlib.util.cache_from_source(str(source)))
    py_compile.compile(str(source), cfile=str(cache), doraise=True)
    raw = bytearray(cache.read_bytes())
    raw[0] ^= 0xFF
    cache.write_bytes(raw)

    assert pipeline_module._is_untrusted_import_artifact(cache)


def test_foreign_tag_and_magic_pep3147_cache_is_inert(tmp_path):
    source = tmp_path / "evaluation" / "verifier.py"
    source.parent.mkdir()
    source.write_text("VALUE = 1\n")
    cache = Path(importlib.util.cache_from_source(str(source)))
    py_compile.compile(str(source), cfile=str(cache), doraise=True)
    current_tag = sys.implementation.cache_tag
    assert current_tag is not None
    foreign = cache.with_name(
        cache.name.replace(current_tag, "cpython-999")
    )
    raw = bytearray(cache.read_bytes())
    raw[0] ^= 0xFF
    foreign.write_bytes(raw)
    cache.unlink()

    assert not pipeline_module._is_untrusted_import_artifact(foreign)


def test_stage1_real_humanize_inherits_campaign_lease_without_relocking(
    tmp_path,
    monkeypatch,
):
    repo, candidates = _repo(tmp_path)
    for name in ("flow.py", "audit_state.py", "state.py", "reviewer.py"):
        (repo / "humanize" / name).write_text(f"# fake {name}\n")
    evolve = repo / "evolve"
    evolve.mkdir()
    (evolve / "engine.py").write_text("# fake evolution engine\n")
    (repo / "main.py").write_text("# fake main\n")
    run_id = "stage1-inherited-lease"
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=FlowConfig(
            repo_dir=repo,
            run_id=run_id,
            candidate_file=candidates,
        ),
        stage_review=False,
    )
    observed = {}

    def fake_locked(flow):
        observed["run_id"] = flow.store.run_id
        return {
            "status": "search-complete",
            "candidate_inputs": [str(candidates)],
        }

    monkeypatch.setattr(HumanizeFlow, "_run_locked", fake_locked)
    pipeline = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(),
        reviewer=RecordingReviewer(),
    )

    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()
        assert pipeline._stage1_inputs() == [candidates.resolve()]

    assert observed == {"run_id": run_id}


def test_stage1_unresolved_exhaustion_hands_candidates_to_proof_stages(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    for name in ("flow.py", "audit_state.py", "state.py", "reviewer.py"):
        (repo / "humanize" / name).write_text(f"# fake {name}\n")
    evolve = repo / "evolve"
    evolve.mkdir()
    (evolve / "engine.py").write_text("# fake evolution engine\n")
    (repo / "main.py").write_text("# fake main\n")
    run_id = "stage1-unresolved-handoff"
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=FlowConfig(
            repo_dir=repo,
            run_id=run_id,
            candidate_file=candidates,
        ),
        stage_review=False,
    )

    class DurableStore:
        @staticmethod
        def load_state():
            return {
                "status": "incomplete-unresolved",
                "unresolved_candidates": {"candidate": {}},
            }

    class ExhaustedFlow:
        store = DurableStore()
        pipeline_candidate_inputs = (candidates,)

        @staticmethod
        def run():
            raise UnresolvedAuditError("exhausted max_rounds")

    pipeline = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(),
        reviewer=RecordingReviewer(),
        flow_factory=lambda _config: ExhaustedFlow(),
    )

    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()
        assert pipeline._stage1_inputs() == [candidates.resolve()]

    stage1 = pipeline.state["stages"]["stage1_search"]
    assert stage1["machine_status"] == "COMPLETED"
    assert stage1["candidate_inputs"] == [str(candidates.resolve())]


def test_stage1_pycache_prefix_reaches_spawned_interpreters_and_restores(
    tmp_path, monkeypatch
):
    repo, candidates = _repo(tmp_path)
    for name in ("flow.py", "audit_state.py", "state.py", "reviewer.py"):
        (repo / "humanize" / name).write_text(f"# fake {name}\n")
    evolve = repo / "evolve"
    evolve.mkdir()
    (evolve / "engine.py").write_text("# fake evolution engine\n")
    (repo / "main.py").write_text("# fake main\n")
    run_id = "stage1-pycache-prefix"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        candidate_file=candidates,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
    )
    original_environment = str(tmp_path / "original-pycache")
    monkeypatch.setenv("PYTHONPYCACHEPREFIX", original_environment)
    original_runtime = sys.pycache_prefix
    observed = {}

    class CapturingFlow:
        def run(self):
            observed["runtime"] = sys.pycache_prefix
            observed["environment"] = os.environ.get("PYTHONPYCACHEPREFIX")
            child = subprocess.run(
                [
                    sys.executable,
                    "-c",
                    (
                        "import os,sys;"
                        "print(sys.pycache_prefix);"
                        "print(os.environ.get('PYTHONPYCACHEPREFIX'))"
                    ),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            observed["child"] = child.stdout.splitlines()
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidates)],
            }

    pipeline = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(),
        reviewer=RecordingReviewer(),
        flow_factory=lambda _config: CapturingFlow(),
    )
    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()
        assert pipeline._stage1_inputs() == [candidates.resolve()]

    assert observed["runtime"] == observed["environment"]
    assert observed["runtime"] != original_environment
    assert observed["child"] == [
        observed["runtime"],
        observed["runtime"],
    ]
    assert sys.pycache_prefix == original_runtime
    assert os.environ["PYTHONPYCACHEPREFIX"] == original_environment


@pytest.mark.parametrize(
    ("stage_script", "relative_source", "expected_stage"),
    [
        (
            "audit_candidate_pool.py",
            "evaluation/verifier.py",
            "stage2_sector_audit",
        ),
        (
            "finalize_challenge.py",
            "humanize/pipeline.py",
            "stage5_strict_gate",
        ),
    ],
    ids=["stage2-evaluation-source", "stage5-controller-source"],
)
def test_restored_source_mutation_during_stage_fails_closed(
    tmp_path, stage_script, relative_source, expected_stage
):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"restored-source-{expected_stage}",
    )
    proven, _ = _certificate(config, f"restored-source-{expected_stage}")
    underlying = ScenarioRunner(stage2=[_plan([proven])])
    source = repo / relative_source
    original = source.read_bytes()

    def mutating_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        completed = underlying(command, cwd=cwd)
        if Path(command[1]).name == stage_script:
            source.write_bytes(original + b"# temporary replacement\n")
            source.write_bytes(original)
        return completed

    state = FiveStagePipeline(
        config,
        command_runner=mutating_runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "INPUT_CHANGED_DURING_STAGE"
    assert state["failure"]["stage"] == expected_stage


def test_pipeline_rejects_symlinked_control_root_before_lock(tmp_path):
    repo, candidates = _repo(tmp_path)
    humanize_root = repo / "results" / "humanize"
    humanize_root.mkdir(parents=True)
    target = repo / "internal-pipeline-control"
    target.mkdir()
    (humanize_root / "pipelines").symlink_to(target)

    with pytest.raises(PipelineError) as failure:
        _config(repo, candidates, run_id="linked-control-root")

    assert failure.value.classification == "UNSAFE_CONTROL_PATH"


def test_legacy_cache_without_stage_config_is_never_reused(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="legacy-cache-no-stage-config")
    runner = ScenarioRunner()
    reviewer = RecordingReviewer()

    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()
    assert first["status"] == "COMPLETED_NO_WIN"
    state_path = config.root / "state.json"
    state = json.loads(state_path.read_text())
    state["stages"]["stage2_sector_audit"].pop("stage_config")
    _write_json(state_path, state)

    second = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert second["status"] == "COMPLETED_NO_WIN"
    assert runner.counts["stage2"] == 2
    assert second["stages"]["stage2_sector_audit"]["attempt"] == 2
    assert "stage_config" in second["stages"]["stage2_sector_audit"]


@pytest.mark.parametrize(
    "relative_path",
    [
        "results/known_code_registry.json",
        "tests/verify_known_answer_gate.py",
    ],
    ids=["known-code-registry", "strict-runner"],
)
def test_stage5_dependency_change_during_command_fails_closed(
    tmp_path, relative_path
):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"stage5-live-mutation-{Path(relative_path).stem}",
    )
    proven, _ = _certificate(config, f"stage5-live-{Path(relative_path).stem}")
    underlying = ScenarioRunner(stage2=[_plan([proven])])

    def mutating_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        completed = underlying(command, cwd=cwd)
        if Path(command[1]).name == "finalize_challenge.py":
            dependency = repo / relative_path
            dependency.write_bytes(dependency.read_bytes() + b"# mutated in Stage 5\n")
        return completed

    state = FiveStagePipeline(
        config,
        command_runner=mutating_runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "INPUT_CHANGED_DURING_STAGE"
    assert state["failure"]["stage"] == "stage5_strict_gate"
    assert "completed_at" not in state
    assert state["stages"]["stage5_strict_gate"]["machine_status"] == "FAILED"


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


def test_strict_gate_rejects_evaluation_bound_to_wrong_certificate(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-certificate-mismatch")
    proven, _ = _certificate(config, "strict-certificate-mismatch")
    underlying = ScenarioRunner(stage2=[_plan([proven])])

    def mismatched_strict_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        result = underlying(command, cwd=cwd)
        if Path(command[1]).name == "finalize_challenge.py":
            output = _argument(command, "--output")
            artifact = json.loads(output.read_text())
            artifact["evaluations"][0]["certificate_sha256"] = "0" * 64
            _write_json(output, artifact)
        return result

    state = FiveStagePipeline(
        config,
        command_runner=mismatched_strict_runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "STRICT_GATE_REJECTED"
    assert state["failure"]["stage"] == "stage5_strict_gate"


def test_strict_gate_rejects_incomplete_replay_checks(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id="strict-incomplete-replay-checks",
    )
    proven, _ = _certificate(config, "strict-incomplete-replay-checks")
    underlying = ScenarioRunner(stage2=[_plan([proven])])

    def incomplete_strict_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        result = underlying(command, cwd=cwd)
        if Path(command[1]).name == "finalize_challenge.py":
            output = _argument(command, "--output")
            artifact = json.loads(output.read_text())
            artifact["evaluations"][0]["result"]["checks"].pop("milp_rerun")
            _write_json(output, artifact)
        return result

    state = FiveStagePipeline(
        config,
        command_runner=incomplete_strict_runner,
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



def test_pipeline_injects_one_shared_stage1_worker_budget(tmp_path):
    repo, _candidates = _repo(tmp_path)
    flow = FlowConfig(repo_dir=repo, run_id="shared-worker-budget")
    legacy_identity = flow.serializable()
    config = PipelineConfig(
        repo_dir=repo,
        run_id="shared-worker-budget",
        flow_config=flow,
        max_total_workers=4,
        stage2_candidate_workers=1,
    )

    assert config.flow_config is not None
    assert config.flow_config.max_total_workers == 4
    assert config.flow_config.serializable() == legacy_identity

    with pytest.raises(ValueError, match="conflicts"):
        PipelineConfig(
            repo_dir=repo,
            run_id="shared-worker-budget",
            flow_config=replace(flow, max_total_workers=2),
            max_total_workers=4,
            stage2_candidate_workers=1,
        )


def test_production_proof_page_bounds_are_live_and_stage3_is_exhaustive(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="proof-page-bounds")

    compatible = replace(config, stage2_top=1, stage3_top=0)
    assert compatible.stage2_top == 1
    assert compatible.stage3_top == 0

    with pytest.raises(ValueError, match="stage2_top must be a positive integer"):
        replace(config, stage2_top=0)
    with pytest.raises(ValueError, match="stage2_top must be a positive integer"):
        replace(config, stage2_top=True)
    with pytest.raises(
        ValueError,
        match="stage3_top must be 0",
    ):
        replace(config, stage3_top=1)


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
