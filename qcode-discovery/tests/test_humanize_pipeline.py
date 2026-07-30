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
import humanize.release_export as release_export_module
from evaluation.final_gate import classify_win
from evaluation.proof_runtime import (
    known_answer_environment,
    probe_python_runtime,
    proof_runtime_fingerprint,
)
from evaluation.selection_ledger import (
    install_pending_page,
    make_scan_evidence,
    make_selection_page,
    new_selection_ledger,
    seal_selection_ledger,
)
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


@pytest.fixture(scope="session")
def _stable_runtime_identity():
    return proof_runtime_fingerprint()


@pytest.fixture(autouse=True)
def _stable_worker_runtime_probe(monkeypatch, _stable_runtime_identity):
    """Keep orchestration tests fast; runtime hashing has dedicated tests."""

    runtime = json.loads(json.dumps(_stable_runtime_identity))
    provenance = {
        "runtime": runtime,
        "interpreter": runtime["interpreter"],
    }
    probe = lambda *_args, **_kwargs: provenance
    monkeypatch.setattr(
        pipeline_module,
        "proof_runtime_fingerprint",
        lambda: runtime,
    )
    monkeypatch.setattr(pipeline_module, "probe_python_runtime", probe)
    monkeypatch.setattr(release_export_module, "probe_python_runtime", probe)


def _argument(command: list[str], name: str) -> Path:
    return Path(command[command.index(name) + 1])


def _stage_script(command: list[str]) -> str:
    return next(
        Path(value).name
        for value in command[1:]
        if str(value).endswith(".py")
    )


def _stage_positional(command: list[str], offset: int = 1) -> Path:
    script_index = next(
        index
        for index, value in enumerate(command)
        if str(value).endswith(".py")
    )
    return Path(command[script_index + offset])


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
    structural_unresolved_candidates: int = 0,
    snapshot_rows: int | None = None,
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
        "structural_unresolved_candidates": (
            structural_unresolved_candidates
        ),
        "snapshot_rows": snapshot_rows,
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
        script = _stage_script(command)
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
                summary["structural_unresolved_candidates"] = plan[
                    "structural_unresolved_candidates"
                ]
                summary["unique_candidates"] = len(results)
                if plan["selection_page"] is not None:
                    start_index, next_index = plan["selection_page"]
                    selected_digests = [
                        str(result["canonical_digest"])
                        for result in results
                    ]
                    binding = "a" * 64
                    snapshot_identity = "b" * 64
                    terminal_ends = [
                        int(candidate["selection_page"][1])
                        for candidate in self.plans["stage2"]
                        if (
                            candidate["selection_page"] is not None
                            and candidate["selection_exhausted"] is True
                        )
                    ]
                    observed_ends = [
                        int(candidate["selection_page"][1])
                        for candidate in self.plans["stage2"]
                        if candidate["selection_page"] is not None
                    ]
                    eligible_rows = (
                        max(terminal_ends)
                        if terminal_ends
                        else max(observed_ends, default=next_index) + 1
                    )
                    configured_snapshot_rows = [
                        int(candidate["snapshot_rows"])
                        for candidate in self.plans["stage2"]
                        if candidate["snapshot_rows"] is not None
                    ]
                    snapshot_rows = (
                        max(configured_snapshot_rows)
                        if configured_snapshot_rows
                        else eligible_rows
                    )
                    ledger_path = _argument(command, "--selection-ledger")
                    if ledger_path.is_file():
                        ledger = json.loads(ledger_path.read_text())
                    else:
                        ledger = {}
                    if (
                        ledger.get("schema_version") != 2
                        or ledger.get("gate")
                        != "qldpc-stage2-selection-ledger"
                        or ledger.get("binding_sha256") != binding
                        or ledger.get("snapshot_identity_sha256")
                        != snapshot_identity
                        or ledger.get("snapshot_rows") != snapshot_rows
                        or ledger.get("eligible_rows") != eligible_rows
                    ):
                        ledger = new_selection_ledger(
                            binding_sha256=binding,
                            snapshot_identity_sha256_value=(
                                snapshot_identity
                            ),
                            snapshot_rows=snapshot_rows,
                            eligible_rows=eligible_rows,
                        )
                    scan_evidence = make_scan_evidence(
                        snapshot_identity_sha256_value=snapshot_identity,
                        start_index=start_index,
                        next_index=next_index,
                        snapshot_rows=snapshot_rows,
                        eligible_rows=eligible_rows,
                        selection_exhausted=plan["selection_exhausted"],
                    )
                    page = make_selection_page(
                        binding_sha256=binding,
                        snapshot_identity_sha256_value=snapshot_identity,
                        page_sequence=ledger["completed_pages"],
                        previous_ack_sha256=ledger["last_ack_sha256"],
                        start_index=start_index,
                        next_index=next_index,
                        selected_digests=selected_digests,
                        scan_evidence=scan_evidence,
                    )
                    summary["selection_page"] = page
                    assert ledger["cursor"] == start_index
                    assert ledger["pending"] is None or ledger["pending"] == page
                    try:
                        ledger = install_pending_page(ledger, page)
                    except ValueError:
                        # Malformed-page tests still need the fake machine to
                        # materialize an artifact for Humanize to reject.
                        ledger["pending"] = page
                        ledger = seal_selection_ledger(ledger)
                    _write_json(ledger_path, ledger)
            else:
                summary["operational_errors"] = plan["operational_errors"]
                _write_jsonl(_argument(command, "--stage4-manifest"), [])
            _write_json(_argument(command, "--summary-output"), summary)
        elif plan["write_outputs"] and stage == "strict":
            certificates = [
                json.loads(line)
                for line in _stage_positional(command).read_text().splitlines()
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
            evaluations = []
            for index, (certificate, requested_disposition) in enumerate(
                zip(certificates, dispositions, strict=True)
            ):
                contradiction = (
                    requested_disposition == "EVIDENCE_CONTRADICTION"
                )
                disposition = (
                    "INCOMPLETE" if contradiction else requested_disposition
                )
                if disposition == "INCOMPLETE":
                    failure_disposition = {
                        "schema_version": 1,
                        "status": (
                            "EVIDENCE_CONTRADICTION"
                            if contradiction
                            else "INCOMPLETE"
                        ),
                        "domain": "evidence" if contradiction else "solver",
                        "codes": [
                            "STRICT_REPLAY_CONTRADICTION"
                            if contradiction
                            else "STRICT_REPLAY_TIMEOUT"
                        ],
                    }
                elif disposition == "REJECTED":
                    failure_disposition = {
                        "schema_version": 1,
                        "status": "CANDIDATE_REJECTED",
                        "domain": "candidate",
                        "codes": ["GATE_CHALLENGE_WIN"],
                    }
                else:
                    failure_disposition = None
                result = {
                    "passed": disposition == "ACCEPTED",
                    "replay_complete": (
                        disposition != "INCOMPLETE" or contradiction
                    ),
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
                            "strict replay contradiction"
                            if contradiction
                            else "strict replay timeout"
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
                }
                if failure_disposition is not None:
                    result["failure_disposition"] = failure_disposition
                evaluations.append({
                    "source_index": index,
                    "claim": certificate.get("claim"),
                    "certificate_sha256": certificate.get("certificate_sha256"),
                    "certificate_payload_sha256": hashlib.sha256(
                        json.dumps(
                            certificate,
                            sort_keys=True,
                            separators=(",", ":"),
                            ensure_ascii=False,
                            allow_nan=False,
                        ).encode()
                    ).hexdigest(),
                    "disposition": disposition,
                    "result": result,
                })
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
                "environment": known_answer_environment(),
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


def test_proof_stage_outer_walls_cover_stage3_and_stage5(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = PipelineConfig(
        repo_dir=repo,
        run_id="outer-wall-budget",
        candidate_inputs=(candidates,),
        stage2_candidate_workers=1,
        stage2_solver_workers=1,
        stage3_timeout=2,
        stage3_candidate_workers=1,
        stage3_direction_workers=2,
        certificate_workers=1,
        certificate_solver_workers=1,
        certificate_total_timeout=3,
        verification_total_timeout=4,
        known_answer_total_timeout=1,
        max_total_workers=6,
        stage_review=False,
    )
    pipeline = FiveStagePipeline(config)
    _write_jsonl(
        pipeline.paths.stage2_ranked,
        [
            {
                "k": 2,
                "triage_identity": {"canonical_digest": "candidate"},
                "campaign_audit": {"status": "UNRESOLVED"},
            }
        ],
    )

    # Stage 3: candidate wall 2 directions * (2 + 5) + 5, one
    # termination second, certificate wall 3 + 4 + 5, one termination
    # second, and the stage-level 60 second controller cushion.
    assert pipeline._stage_outer_hard_timeout(
        "stage3_direction_audit"
    ) == pytest.approx(93)
    assert pipeline._stage_outer_hard_timeout(
        "stage5_strict_gate"
    ) == pytest.approx(102)
    assert pipeline._stage_outer_hard_timeout("stage2_sector_audit") is None


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
            "schema_version": 3,
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


def _terminal_negative_certificate(
    config: PipelineConfig,
    digest: str,
) -> tuple[dict, Path]:
    paths = PipelinePaths(config.root)
    token = hashlib.sha256(digest.encode()).hexdigest()
    certificate_path = (
        paths.solver_state / "certificates" / f"{token}.json"
    )
    known_answer_sha = hashlib.sha256(
        Path(config.known_answer_artifact).read_bytes()
    ).hexdigest()
    failure_disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }
    checks = {
        "known_answer_gate": True,
        "css_bb_candidate": True,
        "candidate_rebuild": True,
        "css_commutation": True,
        "weight_and_degree_at_most_6": True,
        "connected_tanner_graph": True,
        "reported_n_matches": True,
        "reported_k_matches": True,
        "qldpc_k_crosscheck": True,
        "positive_reported_distance": True,
        "all_2k_milp_directions_optimal": True,
        "structural_audit_present": True,
        "structural_audit_reproduced": True,
        "expanded_registry_novel": True,
        "challenge_win": False,
        "reported_fom_matches": True,
    }
    certificate = {
        "schema_version": 1,
        "certificate_type": "qldpc-css-bb-exact",
        "formulation": "css-logical-anticommutation-milp-v1",
        "passed": False,
        "known_answer": {"artifact_sha256": known_answer_sha},
        "claim": {"canonical_digest": digest, "n": 72, "k": 12, "d": 6},
        "milp": {
            "exact": True,
            "expected_directions": 24,
            "completed_directions": 24,
            "directions": [{} for _ in range(24)],
        },
        "final_gate": {
            "schema_version": 1,
            "gate": "qldpc-challenge-final",
            "accepted": False,
            "checks": checks,
            "failures": ["challenge_win"],
            "win": {"passed": False},
        },
        "failure_disposition": failure_disposition,
    }
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            certificate,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    _write_json(certificate_path, certificate)
    _write_json(
        certificate_path.with_name(f"{token}.cache.json"),
        {
            "schema_version": 3,
            "kind": "qldpc-certificate-cache",
            "canonical_digest": digest,
            "known_answer_sha256": known_answer_sha,
            "certificate_sha256": certificate["certificate_sha256"],
            "certificate_payload_sha256": hashlib.sha256(
                json.dumps(
                    certificate,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest(),
            "exact": True,
            "passed": False,
        },
    )
    return {
        "canonical_digest": digest,
        "status": "THRESHOLD_PROVEN",
        "certificate": {
            "attempted": True,
            "certificate_path": str(certificate_path),
            "certificate_sha256": certificate["certificate_sha256"],
            "certificate_exact": True,
            "certificate_passed": False,
            "verification_passed": False,
            "failure_disposition": failure_disposition,
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
    assert _stage_script(strict) == "finalize_challenge.py"
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
    assert [
        float(command[command.index("--structural-hard-timeout") + 1])
        for command in stage2_commands
    ] == [300, 600, 1200]
    assert all(
        Path(command[command.index("--structural-cache-dir") + 1])
        == config.root
        / "solver-state"
        / "stage2-structural-screen-cache-v1"
        for command in stage2_commands
    )
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
    assert active["binding"]["proof_runtime"] == proof_runtime_fingerprint()
    assert (
        active["binding"]["proof_interpreter"]
        == proof_runtime_fingerprint()["interpreter"]
    )
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
            _stage_script(command) == "audit_direction_pool.py"
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


def test_prepared_attempt_at_attempt_cap_executes_after_crash(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-prepared-at-cap"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=1,
    )
    digest = "prepared-last-chance-win"
    unresolved = {"canonical_digest": digest, "status": "UNRESOLVED"}
    winner, _ = _certificate(config, digest)
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=True,
                selection_page=(0, 1),
            )
        ],
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
    interrupted_controller = json.loads(controller_path.read_text())
    interrupted = interrupted_controller["active"]
    assert [attempt["status"] for attempt in interrupted["attempts"]] == [
        "COMPLETED_INCOMPLETE",
        "PREPARED",
    ]
    assert interrupted["attempts"][-1]["attempt"] == (
        config.proof_retry_max_attempts
    )
    assert runner.counts == {"stage2": 1, "stage3": 1}
    # PREPARE already committed this bounded attempt.  Even a recovered
    # controller at the campaign wall must execute it exactly once.
    interrupted["elapsed_seconds"] = (
        config.proof_retry_campaign_total_timeout
    )
    _write_json(controller_path, interrupted_controller)

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
    assert completed["status"] == "COMPLETED_WIN"
    assert [attempt["attempt"] for attempt in completed["attempts"]] == [1, 2]
    assert completed["attempts"][-1]["status"] == "COMPLETED_WIN"
    ledger = json.loads(
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_text()
    )
    assert ledger["cursor"] == 0
    assert ledger["deferred_pages"] == []


def test_checkpoint_progress_can_exceed_attempt_cap_and_reach_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-progress-past-cap"),
        proof_retry_max_attempts=3,
        proof_retry_campaign_total_timeout=10_000,
        proof_retry_backoff_seconds=0,
    )
    digest = "progress-past-cap-win"
    unresolved = {"canonical_digest": digest, "status": "UNRESOLVED"}
    winner, _ = _certificate(config, digest)
    underlying = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=True,
                selection_page=(0, 1),
            )
        ],
        stage3=[
            _plan([unresolved]),
            _plan([unresolved]),
            _plan([unresolved]),
            _plan([unresolved]),
            _plan([winner]),
        ],
    )

    def progress_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        completed = underlying(command, cwd=cwd)
        if _stage_script(command) == "audit_direction_pool.py":
            count = underlying.counts["stage3"]
            _write_json(
                config.root
                / "solver-state"
                / "directions"
                / "progress.json",
                {
                    "completed_directions": count,
                    "directions": [{"objective": 9}] * count,
                },
            )
        return completed

    state = FiveStagePipeline(
        config,
        command_runner=progress_runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert underlying.counts["stage3"] == 5
    controller = json.loads(
        (
            config.root
            / "solver-state"
            / "proof-retry-controller.json"
        ).read_text()
    )["active"]
    assert len(controller["attempts"]) == 5
    assert len(controller["attempts"]) > config.proof_retry_max_attempts
    assert [attempt["multiplier"] for attempt in controller["attempts"]] == [
        1,
        1,
        1,
        1,
        1,
    ]
    assert all(
        attempt["made_progress"] is True
        for attempt in controller["attempts"][:-1]
    )
    assert controller["attempts"][-1]["status"] == "COMPLETED_WIN"
    ledger = json.loads(
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_text()
    )
    assert ledger["cursor"] == 0
    assert ledger["deferred_pages"] == []


def test_proof_retry_campaign_total_timeout_caps_after_current_attempt(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="proof-retry-total-timeout"),
        proof_retry_max_attempts=6,
        proof_retry_campaign_total_timeout=0.5,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {"canonical_digest": "total-timeout", "status": "UNRESOLVED"}
    underlying = ScenarioRunner(
        stage2=[_plan([unresolved])],
        stage3=[_plan([unresolved])],
    )

    def progress_runner(
        command: list[str], *, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        completed = underlying(command, cwd=cwd)
        if _stage_script(command) == "audit_direction_pool.py":
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

    clock = iter([0.0, 1.0])

    state = FiveStagePipeline(
        config,
        command_runner=progress_runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
        monotonic=lambda: next(clock),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert underlying.counts == {"stage2": 1, "stage3": 1}
    assert state["proof_retry"]["cap_reason"] == (
        "CAMPAIGN_TOTAL_TIMEOUT_REACHED"
    )
    controller = json.loads(
        (
            config.root
            / "solver-state"
            / "proof-retry-controller.json"
        ).read_text()
    )["active"]
    assert controller["attempts"][-1]["made_progress"] is True


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
    loser, _ = _terminal_negative_certificate(config, "exact-loser")
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
    loser, _ = _terminal_negative_certificate(
        config,
        "page-one-loser",
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


def test_empty_nonterminal_stage2_page_advances_to_later_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id="empty-progress-page-then-win",
    )
    winner, _ = _certificate(config, "after-empty-progress-winner")
    runner = ScenarioRunner(stage2=[
        _plan(
            [],
            selection_exhausted=False,
            selection_page=(0, 1),
            structural_unresolved_candidates=1,
            snapshot_rows=2,
        ),
        _plan(
            [winner],
            selection_exhausted=True,
            selection_page=(1, 2),
            snapshot_rows=2,
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
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_text()
    )
    assert ledger["cursor"] == 1
    assert ledger["committed_digests"] == []
    assert len(ledger["ack_chain"]) == 1
    assert ledger["ack_chain"][0]["page"]["selected_digests"] == []
    assert ledger["pending"]["selected_digests"] == [
        "after-empty-progress-winner"
    ]


def test_max_attempts_one_binds_cache_to_acknowledged_ledger_prestate(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="page-cache-ledger-prestate")
    first = {
        "canonical_digest": "cache-page-one-rejected",
        "status": "REJECTED",
    }
    winner, _ = _certificate(config, "cache-page-two-winner")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [first],
                selection_exhausted=False,
                selection_page=(0, 1),
            ),
            _plan(
                [winner],
                selection_exhausted=True,
                selection_page=(1, 2),
            ),
        ]
    )
    pipeline = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    )
    acknowledge = pipeline._acknowledge_completed_stage2_page

    def force_cache_eligible_after_ack(state):
        advanced = acknowledge(state)
        if advanced:
            # Reproduce the dangerous cache shape directly: all ordinary
            # command/config/input/output fields still describe page zero,
            # while only the transaction-owned ledger moved to page one.
            record = pipeline.state["stages"]["stage2_sector_audit"]
            record["status"] = "COMPLETED"
            record["machine_status"] = "COMPLETED"
            pipeline._write_state()
        return advanced

    pipeline._acknowledge_completed_stage2_page = (
        force_cache_eligible_after_ack
    )
    state = pipeline.run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 1}
    stage2 = state["stages"]["stage2_sector_audit"]
    ledger_digest = hashlib.sha256(
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_bytes()
    ).hexdigest()
    # The latest cache key captured the acknowledged prestate before page two
    # itself installed a new pending page.
    assert stage2["stage_config"][
        "selection_ledger_prestate_sha256"
    ] != ledger_digest


def test_paginated_terminal_page_advances_past_global_input_diagnostic(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="paginated-global-diagnostic-win"),
        stage2_top=1,
    )
    loser, _ = _terminal_negative_certificate(
        config,
        "global-diagnostic-loser",
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
    first, _ = _terminal_negative_certificate(
        config,
        "global-diagnostic-first-loser",
    )
    second, _ = _terminal_negative_certificate(
        config,
        "global-diagnostic-second-loser",
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


def test_diagnostic_only_terminal_page_stays_pending_across_resume(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="diagnostic-only-terminal-page"),
        stage2_top=1,
    )
    first = {
        "canonical_digest": "diagnostic-tail-first",
        "status": "REJECTED",
    }
    runner = ScenarioRunner(stage2=[
        _plan(
            [first],
            selection_exhausted=False,
            selection_page=(0, 1),
        ),
        _plan(
            [],
            selection_exhausted=True,
            selection_page=(1, 2),
            canonicalization_errors=1,
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 2}
    ledger_path = (
        config.root
        / "solver-state"
        / "stage2-selection-ledger.json"
    )
    ledger_bytes = ledger_path.read_bytes()
    ledger = json.loads(ledger_bytes)
    assert ledger["cursor"] == 1
    assert ledger["pending"]["selected_digests"] == []
    assert (
        ledger["pending"]["scan_evidence"]["selection_exhausted"]
        is True
    )
    assert ledger["committed_digests"] == ["diagnostic-tail-first"]
    assert len(ledger["ack_chain"]) == 1
    assert ledger["ack_chain"][0]["page"]["selected_digests"] == [
        "diagnostic-tail-first"
    ]
    assert state["stage2_pagination"]["selection_exhausted"] is True
    assert state["stage2_pagination"]["terminal_pending"] is True
    reasons = state["result"]["proof_incompleteness"]["reasons"]
    assert {
        reason["code"] for reason in reasons
    } == {"STAGE2_CANONICALIZATION_ERRORS"}

    resumed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert resumed["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 2}
    assert ledger_path.read_bytes() == ledger_bytes


def test_zero_pool_terminal_root_page_is_incomplete_not_no_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="zero-pool-terminal-root")
    runner = ScenarioRunner(stage2=[
        _plan(
            [],
            selection_exhausted=True,
            selection_page=(0, 0),
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    reasons = state["result"]["proof_incompleteness"]["reasons"]
    assert any(
        reason["code"] == "STAGE2_EMPTY_CANDIDATE_POOL"
        for reason in reasons
    )
    ledger = json.loads(
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_text()
    )
    assert ledger["cursor"] == 0
    assert ledger["ack_chain"] == []
    assert ledger["pending"]["start_index"] == 0
    assert ledger["pending"]["next_index"] == 0


def test_nonempty_all_rejected_snapshot_can_complete_no_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="all-rejected-snapshot")
    runner = ScenarioRunner(stage2=[
        _plan(
            [],
            selection_exhausted=True,
            selection_page=(0, 0),
            snapshot_rows=1,
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_NO_WIN"
    ledger = json.loads(
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_text()
    )
    assert ledger["snapshot_rows"] == 1
    assert ledger["eligible_rows"] == 0
    assert ledger["pending"]["scan_evidence"]["snapshot_rows"] == 1


@pytest.mark.parametrize("unsupported_stage", ("stage2", "stage3"))
def test_unsupported_result_blocks_exhaustive_no_win(
    tmp_path,
    unsupported_stage,
):
    repo, candidates = _repo(tmp_path)
    config = _config(
        repo,
        candidates,
        run_id=f"unsupported-{unsupported_stage}",
    )
    digest = f"{unsupported_stage}-unsupported"
    if unsupported_stage == "stage2":
        stage2_result = {
            "canonical_digest": digest,
            "status": "UNSUPPORTED",
        }
        stage3_plans = None
        expected_code = "STAGE2_UNSUPPORTED_RESULT"
    else:
        stage2_result = {
            "canonical_digest": digest,
            "status": "UNRESOLVED",
        }
        stage3_plans = [[{
            "canonical_digest": digest,
            "status": "UNSUPPORTED",
        }]]
        expected_code = "STAGE3_UNSUPPORTED_RESULT"
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [stage2_result],
                selection_exhausted=True,
                selection_page=(0, 1),
            ),
        ],
        stage3=(
            None
            if stage3_plans is None
            else [_plan(stage3_plans[0])]
        ),
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    codes = {
        reason["code"]
        for reason in state["result"]["proof_incompleteness"]["reasons"]
    }
    assert expected_code in codes


def test_paginated_stage2_interruption_replays_pending_second_page(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="paginated-interrupt-resume")
    loser, _ = _terminal_negative_certificate(
        config,
        "interrupt-page-one",
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
            _stage_script(command) == "audit_candidate_pool.py"
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

    assert state["status"] == "FAILED"
    assert runner.counts == {"stage2": 1}
    assert state["failure"]["classification"] == "OUTPUT_INVALID"


@pytest.mark.parametrize("forgery", ("cursor", "committed"))
def test_forged_selection_progress_cannot_reach_no_win(
    tmp_path,
    forgery,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id=f"forged-ledger-{forgery}")

    class ForgingRunner(ScenarioRunner):
        def __call__(self, command, *, cwd):
            result = super().__call__(command, cwd=cwd)
            if _stage_script(command) == "audit_candidate_pool.py":
                ledger_path = _argument(command, "--selection-ledger")
                ledger = json.loads(ledger_path.read_text())
                if forgery == "cursor":
                    ledger["cursor"] = ledger["eligible_rows"]
                else:
                    ledger["committed_digests"].append("forged-skip")
                _write_json(ledger_path, seal_selection_ledger(ledger))
            return result

    runner = ForgingRunner(stage2=[
        _plan(
            [{
                "canonical_digest": "would-be-no-win",
                "status": "REJECTED",
            }],
            selection_exhausted=True,
            selection_page=(0, 1),
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "OUTPUT_INVALID"
    assert runner.counts == {"stage2": 1}


def test_legacy_selection_ledger_is_reset_before_terminal_page(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="legacy-ledger-reset")
    ledger_path = (
        config.root
        / "solver-state"
        / "stage2-selection-ledger.json"
    )
    _write_json(ledger_path, {
        "schema_version": 1,
        "gate": "qldpc-stage2-selection-ledger",
        "binding_sha256": "a" * 64,
        "cursor": 999,
        "committed_digests": ["forged-legacy-skip"],
        "completed_pages": 999,
        "pending": None,
    })
    runner = ScenarioRunner(stage2=[
        _plan(
            [{
                "canonical_digest": "legacy-reset-rejected",
                "status": "REJECTED",
            }],
            selection_exhausted=True,
            selection_page=(0, 1),
        ),
    ])

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_NO_WIN"
    ledger = json.loads(ledger_path.read_text())
    assert ledger["schema_version"] == 2
    assert ledger["cursor"] == 0
    assert ledger["committed_digests"] == []
    assert ledger["pending"]["start_index"] == 0


def test_capped_first_page_is_deferred_and_later_page_can_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="deferred-page-later-win"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {
        "canonical_digest": "deferred-page-zero",
        "status": "UNRESOLVED",
    }
    winner, _ = _certificate(config, "later-page-winner")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=False,
                selection_page=(0, 1),
            ),
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
        stage3=[_plan([unresolved]), _plan([unresolved])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 3, "stage3": 2, "strict": 1}
    ledger = json.loads(
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_text()
    )
    assert ledger["cursor"] == 1
    assert ledger["pending"]["selected_digests"] == ["later-page-winner"]
    assert ledger["committed_digests"] == ["deferred-page-zero"]
    assert len(ledger["deferred_pages"]) == 1
    deferred = ledger["deferred_pages"][0]
    assert deferred["selected_digests"] == ["deferred-page-zero"]
    assert deferred["cap_reason"] == "MAX_ATTEMPTS_REACHED"
    manifest = (
        config.root / "solver-state" / deferred["manifest_path"]
    )
    assert hashlib.sha256(manifest.read_bytes()).hexdigest() == deferred[
        "manifest_sha256"
    ]


def test_no_win_with_deferred_backlog_remains_incomplete(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="deferred-page-no-win"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {
        "canonical_digest": "deferred-no-win-zero",
        "status": "UNRESOLVED",
    }
    rejected = {
        "canonical_digest": "terminal-rejected-one",
        "status": "REJECTED",
    }
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=False,
                selection_page=(0, 1),
            ),
            _plan(
                [unresolved],
                selection_exhausted=False,
                selection_page=(0, 1),
            ),
            _plan(
                [rejected],
                selection_exhausted=True,
                selection_page=(1, 2),
            ),
        ],
        stage3=[_plan([unresolved]), _plan([unresolved])],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert runner.counts == {"stage2": 3, "stage3": 2}
    reasons = state["result"]["proof_incompleteness"]["reasons"]
    assert "STAGE2_DEFERRED_PROOF_PAGE" in {
        reason["code"] for reason in reasons
    }
    assert not (
        config.root / "artifacts" / "stage5-no-win.json"
    ).exists()
    ledger = json.loads(
        (
            config.root
            / "solver-state"
            / "stage2-selection-ledger.json"
        ).read_text()
    )
    assert ledger["cursor"] == 1
    assert ledger["committed_digests"] == ["deferred-no-win-zero"]
    assert ledger["pending"]["start_index"] == 1
    assert ledger["pending"]["next_index"] == 2
    assert ledger["pending"]["selected_digests"] == [
        "terminal-rejected-one"
    ]
    assert (
        ledger["pending"]["scan_evidence"]["selection_exhausted"]
        is True
    )
    assert len(ledger["ack_chain"]) == 1
    assert ledger["ack_chain"][0]["disposition"] == "DEFERRED"
    assert (
        ledger["ack_chain"][0]["deferred_entry_sha256"]
        == ledger["deferred_pages"][0]["entry_sha256"]
    )


def test_higher_base_budget_rotates_deferred_generation_and_retries(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    first_config = replace(
        _config(repo, candidates, run_id="deferred-budget-generation"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=0,
        stage2_timeout=100,
    )
    digest = "terminal-poison-then-win"
    unresolved = {"canonical_digest": digest, "status": "UNRESOLVED"}
    winner, _ = _certificate(first_config, digest)
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=True,
                selection_page=(0, 1),
            ),
            _plan(
                [unresolved],
                selection_exhausted=True,
                selection_page=(0, 1),
            ),
            _plan(
                [winner],
                selection_exhausted=True,
                selection_page=(0, 1),
            ),
        ],
        stage3=[_plan([unresolved]), _plan([unresolved])],
    )

    first_state = FiveStagePipeline(
        first_config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert first_state["status"] == "INCOMPLETE"
    ledger_path = (
        first_config.root
        / "solver-state"
        / "stage2-selection-ledger.json"
    )
    first_ledger = json.loads(ledger_path.read_text())
    assert first_ledger["cursor"] == 1
    assert first_ledger.get("generation", 0) == 0
    assert first_ledger["deferred_pages"][0]["selected_digests"] == [
        digest
    ]
    deferred_manifest = (
        first_config.root
        / "solver-state"
        / first_ledger["deferred_pages"][0]["manifest_path"]
    )
    deferred_manifest_sha256 = hashlib.sha256(
        deferred_manifest.read_bytes()
    ).hexdigest()

    second_config = replace(first_config, stage2_timeout=400)
    second_state = FiveStagePipeline(
        second_config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert second_state["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 3, "stage3": 2, "strict": 1}
    second_ledger = json.loads(ledger_path.read_text())
    assert second_ledger["generation"] == 1
    assert second_ledger["cursor"] == 0
    assert second_ledger["committed_digests"] == []
    assert second_ledger["deferred_pages"] == []
    assert second_ledger["pending"]["selected_digests"] == [digest]
    assert len(second_ledger["generation_history"]) == 1
    generation = second_ledger["generation_history"][0]
    archived_ledger = (
        second_config.root
        / "solver-state"
        / generation["ledger_path"]
    )
    assert hashlib.sha256(archived_ledger.read_bytes()).hexdigest() == (
        generation["ledger_sha256"]
    )
    archived_value = json.loads(archived_ledger.read_text())
    assert archived_value["deferred_pages"] == first_ledger[
        "deferred_pages"
    ]
    assert hashlib.sha256(deferred_manifest.read_bytes()).hexdigest() == (
        deferred_manifest_sha256
    )


def test_registry_change_rotates_terminal_deferred_generation_and_retries(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="deferred-registry-generation"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=0,
    )
    digest = "registry-change-then-win"
    unresolved = {"canonical_digest": digest, "status": "UNRESOLVED"}
    winner, _ = _certificate(config, digest)
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=True,
                selection_page=(0, 1),
            ),
            _plan(
                [unresolved],
                selection_exhausted=True,
                selection_page=(0, 1),
            ),
            _plan(
                [winner],
                selection_exhausted=True,
                selection_page=(0, 1),
            ),
        ],
        stage3=[_plan([unresolved]), _plan([unresolved])],
    )

    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()
    assert first["status"] == "INCOMPLETE"
    ledger_path = (
        config.root / "solver-state" / "stage2-selection-ledger.json"
    )
    first_ledger = json.loads(ledger_path.read_text())
    assert first_ledger["pending"] is None
    assert first_ledger["deferred_pages"][0]["selection_exhausted"] is True

    registry = repo / "results" / "known_code_registry.json"
    registry.write_text(
        '{"schema_version": 1, "registry_sha256": "changed"}\n'
    )
    second = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 3, "stage3": 2, "strict": 1}
    second_ledger = json.loads(ledger_path.read_text())
    assert second_ledger["generation"] == 1
    assert second_ledger["deferred_pages"] == []
    assert second_ledger["pending"]["selected_digests"] == [digest]
    generation = second_ledger["generation_history"][0]
    assert "DEPENDENCY_BINDING_CHANGED" in generation["rotation_reasons"]
    assert generation["replacement_environment_binding_sha256"]


def test_deferred_page_atomic_commit_resumes_without_skipping_digest(
    tmp_path, monkeypatch
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="deferred-page-crash-resume"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {
        "canonical_digest": "deferred-before-crash",
        "status": "UNRESOLVED",
    }
    winner, _ = _certificate(config, "winner-after-crash")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=False,
                selection_page=(0, 1),
            ),
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
        stage3=[_plan([unresolved]), _plan([unresolved])],
    )
    ledger_path = (
        config.root / "solver-state" / "stage2-selection-ledger.json"
    )
    original_atomic_write_json = pipeline_module.atomic_write_json
    interrupted = False

    def interrupt_after_ledger_commit(path: Path, value: dict) -> None:
        nonlocal interrupted
        original_atomic_write_json(path, value)
        if (
            path == ledger_path
            and value.get("deferred_pages")
            and not interrupted
        ):
            interrupted = True
            raise KeyboardInterrupt

    monkeypatch.setattr(
        pipeline_module, "atomic_write_json", interrupt_after_ledger_commit
    )
    with pytest.raises(KeyboardInterrupt):
        FiveStagePipeline(
            config,
            command_runner=runner,
            reviewer=RecordingReviewer(),
        ).run()

    committed = json.loads(ledger_path.read_text())
    assert committed["cursor"] == 1
    assert committed["pending"] is None
    assert committed["committed_digests"] == ["deferred-before-crash"]
    assert committed["deferred_pages"][0]["selected_digests"] == [
        "deferred-before-crash"
    ]
    assert committed["ack_chain"][-1]["disposition"] == "DEFERRED"
    assert (
        committed["ack_chain"][-1]["deferred_entry_sha256"]
        == committed["deferred_pages"][0]["entry_sha256"]
    )

    monkeypatch.setattr(
        pipeline_module, "atomic_write_json", original_atomic_write_json
    )
    resumed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert resumed["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 3, "stage3": 2, "strict": 1}
    replayed = json.loads(ledger_path.read_text())
    assert replayed["deferred_pages"] == committed["deferred_pages"]
    assert replayed["pending"]["selected_digests"] == [
        "winner-after-crash"
    ]


def test_deferred_page_prepare_replays_after_crash_before_ledger_commit(
    tmp_path, monkeypatch
):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="deferred-prepare-crash"),
        proof_retry_max_attempts=2,
        proof_retry_backoff_seconds=0,
    )
    unresolved = {
        "canonical_digest": "prepared-before-crash",
        "status": "UNRESOLVED",
    }
    winner, _ = _certificate(config, "winner-after-prepare-replay")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [unresolved],
                selection_exhausted=False,
                selection_page=(0, 1),
            ),
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
        stage3=[_plan([unresolved]), _plan([unresolved])],
    )
    ledger_path = (
        config.root / "solver-state" / "stage2-selection-ledger.json"
    )
    original_atomic_write_json = pipeline_module.atomic_write_json
    interrupted = False

    def interrupt_before_ledger_commit(path: Path, value: dict) -> None:
        nonlocal interrupted
        if (
            path == ledger_path
            and value.get("deferred_pages")
            and not interrupted
        ):
            interrupted = True
            raise KeyboardInterrupt
        original_atomic_write_json(path, value)

    monkeypatch.setattr(
        pipeline_module, "atomic_write_json", interrupt_before_ledger_commit
    )
    with pytest.raises(KeyboardInterrupt):
        FiveStagePipeline(
            config,
            command_runner=runner,
            reviewer=RecordingReviewer(),
        ).run()

    prepared = json.loads(ledger_path.read_text())
    assert prepared["cursor"] == 0
    assert prepared["pending"]["selected_digests"] == [
        "prepared-before-crash"
    ]
    assert not prepared.get("deferred_pages")
    manifests = list(
        (config.root / "solver-state" / "deferred-pages").glob(
            "*/manifest.json"
        )
    )
    assert len(manifests) == 1
    prepared_manifest_sha256 = hashlib.sha256(
        manifests[0].read_bytes()
    ).hexdigest()

    monkeypatch.setattr(
        pipeline_module, "atomic_write_json", original_atomic_write_json
    )
    resumed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert resumed["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 3, "stage3": 2, "strict": 1}
    committed = json.loads(ledger_path.read_text())
    assert committed["committed_digests"] == ["prepared-before-crash"]
    assert committed["deferred_pages"][0]["selected_digests"] == [
        "prepared-before-crash"
    ]
    assert (
        hashlib.sha256(manifests[0].read_bytes()).hexdigest()
        == prepared_manifest_sha256
    )


def test_paginated_stage2_scans_more_than_64_pages_without_resume(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="pagination-more-than-64-pages"),
        stage_review=False,
    )
    page_count = 66
    plans = [
        _plan(
            [
                {
                    "canonical_digest": f"terminal-reject-{index}",
                    "status": "REJECTED",
                }
            ],
            selection_exhausted=index == page_count - 1,
            selection_page=(index, index + 1),
        )
        for index in range(page_count)
    ]
    runner = ScenarioRunner(stage2=plans)

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "COMPLETED_NO_WIN"
    assert runner.counts == {"stage2": page_count}
    assert state["execution_attempt"] == page_count
    assert state["stage2_pagination"]["automatic_passes"] == page_count - 1
    assert "automatic_pass_limit" not in state["stage2_pagination"]


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
        if _stage_script(command) == "audit_candidate_pool.py":
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


def test_existing_input_stage1_reviewer_failure_is_advisory_and_resume_only_retries_review(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="stage1-existing-review-advisory")
    proven, _ = _certificate(config, "stage1-review-advisory-win")
    runner = ScenarioRunner(stage2=[_plan([proven])])
    reviewer = RecordingReviewer(fail_once={"stage1_search"})

    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert first["status"] == "COMPLETED_WIN"
    assert "failure" not in first
    stage1 = first["stages"]["stage1_search"]
    assert stage1["machine_status"] == "COMPLETED"
    assert stage1["status"] == "COMPLETED"
    assert stage1["review_status"] == "ADVISORY_FAILED"
    assert stage1["advisory_failure"]["classification"] == "ADVISORY_FAILED"
    assert stage1["attempt"] == 1
    assert runner.counts == {"stage2": 1, "strict": 1}

    completed = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=reviewer,
    ).run()

    assert completed["status"] == "COMPLETED_WIN"
    assert completed["stages"]["stage1_search"]["attempt"] == 1
    assert completed["stages"]["stage1_search"]["resumed_machine"] is True
    assert completed["stages"]["stage1_search"]["review_attempt"] == 2
    assert completed["stages"]["stage1_search"]["review_status"] == "COMPLETED"
    assert reviewer.calls.count("stage1_search") == 2
    assert runner.counts == {"stage2": 1, "strict": 1}


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


def test_stage1_monotonic_round_extension_reruns_search_and_downstream(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    for name in ("flow.py", "reviewer.py"):
        (repo / "humanize" / name).write_text(f"# fake {name}\n")
    evolve = repo / "evolve"
    evolve.mkdir()
    (evolve / "engine.py").write_text("# fake evolution engine\n")
    (repo / "main.py").write_text("# fake main\n")
    run_id = "pipeline-round-extension"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        max_rounds=1,
        candidate_file=candidates,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
        proof_retry_max_attempts=1,
    )
    flow_calls = []

    class SearchFlow:
        pipeline_candidate_inputs = (candidates,)

        def __init__(self, received):
            self.received = received

        def run(self):
            flow_calls.append(self.received.max_rounds)
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidates)],
            }

    runner = ScenarioRunner()
    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        flow_factory=SearchFlow,
    ).run()
    assert first["status"] == "COMPLETED_NO_WIN"

    # Model a state written before the structured identity migration.  The
    # fingerprint and the previous serialized PipelineConfig must suffice to
    # authorize this one compatible extension.
    legacy = json.loads(config.root.joinpath("state.json").read_text())
    legacy.pop("stage1_identity")
    _write_json(config.root / "state.json", legacy)

    extended = replace(
        config,
        flow_config=replace(config.flow_config, max_rounds=3),
    )
    second = FiveStagePipeline(
        extended,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        flow_factory=SearchFlow,
    ).run()

    assert second["status"] == "COMPLETED_NO_WIN"
    assert flow_calls == [1, 3]
    assert runner.counts == {"stage2": 2}
    for stage in STAGE_ORDER:
        assert second["stages"][stage]["attempt"] == 2
    assert (
        second["stages"]["stage1_search"]["stage_config"]["flow_config"][
            "max_rounds"
        ]
        == 3
    )
    assert second["stage1_identity"]["flow_config"]["max_rounds"] == 3
    assert second["stage1_identity_fingerprint"] == hashlib.sha256(
        json.dumps(
            second["stage1_identity"],
            sort_keys=True,
            separators=(",", ":"),
        ).encode()
    ).hexdigest()
    assert len(second["config_history"]) == 1
    assert second["config_history"][0]["config"]["flow_config"][
        "max_rounds"
    ] == 1


@pytest.mark.parametrize(
    ("change", "value"),
    [
        ("max_rounds", 1),
        ("model", "different-search-model"),
        ("candidate_file", "replacement"),
        ("milp_total_timeout", 7201),
    ],
)
def test_stage1_round_extension_rejects_every_other_identity_change(
    tmp_path,
    change,
    value,
):
    repo, candidates = _repo(tmp_path)
    replacement = repo / "replacement-candidates.jsonl"
    replacement.write_text('{"candidate": 2}\n')
    run_id = f"reject-round-extension-{change}"
    flow_config = FlowConfig(
        repo_dir=repo,
        run_id=run_id,
        max_rounds=2,
        candidate_file=candidates,
    )
    config = PipelineConfig(
        repo_dir=repo,
        run_id=run_id,
        flow_config=flow_config,
        stage_review=False,
    )
    pipeline = FiveStagePipeline(config)
    with pipeline._exclusive_lock():
        original = pipeline._load_or_initialize_state()
    original_fingerprint = original["stage1_identity_fingerprint"]

    updates = {"max_rounds": 3}
    updates[change] = replacement if value == "replacement" else value
    changed = replace(
        config,
        flow_config=replace(config.flow_config, **updates),
    )
    with pytest.raises(ValueError, match="only a strict max_rounds increase"):
        rejected = FiveStagePipeline(changed)
        with rejected._exclusive_lock():
            rejected._load_or_initialize_state()

    durable = json.loads(config.root.joinpath("state.json").read_text())
    assert durable["config"]["flow_config"]["max_rounds"] == 2
    assert durable["stage1_identity_fingerprint"] == original_fingerprint
    assert durable["config_history"] == []


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


def test_summary_disposition_without_bound_certificate_always_retries(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="summary-only-rejection")
    pipeline = FiveStagePipeline(config, reviewer=RecordingReviewer())
    result = {
        "canonical_digest": "summary-only",
        "status": "THRESHOLD_PROVEN",
        "certificate": {
            "attempted": True,
            "certificate_exact": True,
            "certificate_passed": False,
            "verification_passed": False,
            "failure_disposition": {
                "schema_version": 1,
                "status": "CANDIDATE_REJECTED",
                "domain": "candidate",
                "codes": ["GATE_CHALLENGE_WIN"],
            },
        },
    }

    assert pipeline._certificate_requires_retry(result) is True


def test_bound_recomputed_candidate_rejection_terminates_retry(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="bound-terminal-rejection")
    pipeline = FiveStagePipeline(config, reviewer=RecordingReviewer())
    digest = "terminal-negative"
    token = hashlib.sha256(digest.encode()).hexdigest()
    certificate_path = (
        pipeline.paths.solver_state
        / "certificates"
        / f"{token}.json"
    )
    known_answer_sha = hashlib.sha256(
        Path(config.known_answer_artifact).read_bytes()
    ).hexdigest()
    failure_disposition = {
        "schema_version": 1,
        "status": "CANDIDATE_REJECTED",
        "domain": "candidate",
        "codes": ["GATE_CHALLENGE_WIN"],
    }
    checks = {
        "known_answer_gate": True,
        "css_bb_candidate": True,
        "candidate_rebuild": True,
        "css_commutation": True,
        "weight_and_degree_at_most_6": True,
        "connected_tanner_graph": True,
        "reported_n_matches": True,
        "reported_k_matches": True,
        "qldpc_k_crosscheck": True,
        "positive_reported_distance": True,
        "all_2k_milp_directions_optimal": True,
        "structural_audit_present": True,
        "structural_audit_reproduced": True,
        "expanded_registry_novel": True,
        "challenge_win": False,
        "reported_fom_matches": True,
    }
    certificate = {
        "schema_version": 1,
        "certificate_type": "qldpc-css-bb-exact",
        "formulation": "css-logical-anticommutation-milp-v1",
        "passed": False,
        "known_answer": {"artifact_sha256": known_answer_sha},
        "claim": {"n": 72, "k": 12, "d": 6},
        "milp": {
            "exact": True,
            "expected_directions": 24,
            "completed_directions": 24,
            "directions": [{} for _ in range(24)],
        },
        "final_gate": {
            "schema_version": 1,
            "gate": "qldpc-challenge-final",
            "accepted": False,
            "checks": checks,
            "failures": ["challenge_win"],
            "win": {"passed": False},
        },
        "failure_disposition": failure_disposition,
    }
    certificate["certificate_sha256"] = hashlib.sha256(
        json.dumps(
            certificate,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()
    _write_json(certificate_path, certificate)
    _write_json(
        certificate_path.with_name(f"{token}.cache.json"),
        {
            "schema_version": 3,
            "kind": "qldpc-certificate-cache",
            "canonical_digest": digest,
            "known_answer_sha256": known_answer_sha,
            "certificate_sha256": certificate["certificate_sha256"],
            "certificate_payload_sha256": hashlib.sha256(
                json.dumps(
                    certificate,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest(),
            "exact": True,
            "passed": False,
        },
    )
    result = {
        "canonical_digest": digest,
        "status": "THRESHOLD_PROVEN",
        "certificate": {
            "attempted": True,
            "certificate_path": str(certificate_path),
            "certificate_sha256": certificate["certificate_sha256"],
            "certificate_exact": True,
            "certificate_passed": False,
            "verification_passed": False,
            "failure_disposition": failure_disposition,
        },
    }

    assert pipeline._certificate_requires_retry(result) is False


def test_stage5_all_passed_certificate_contradictions_are_retryable(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-all-rejected")
    first, _ = _certificate(config, "strict-rejected-1")
    second, _ = _certificate(config, "strict-rejected-2")
    runner = ScenarioRunner(
        stage2=[_plan([first, second])],
        strict=[
            _plan(
                strict_dispositions=[
                    "EVIDENCE_CONTRADICTION",
                    "EVIDENCE_CONTRADICTION",
                ],
            )
        ],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert state["status"] == "INCOMPLETE"
    assert state["result"]["stage5_outcome"] == "INCOMPLETE"
    assert state["stages"]["stage5_strict_gate"]["machine_status"] == "INCOMPLETE"


def test_stage5_without_winner_and_with_timeout_is_retryable(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="strict-no-winner-timeout")
    rejected, _ = _certificate(config, "strict-terminal-reject")
    timeout, _ = _certificate(config, "strict-incomplete-peer")
    runner = ScenarioRunner(
        stage2=[_plan([rejected, timeout])],
        strict=[
            _plan(
                strict_dispositions=[
                    "EVIDENCE_CONTRADICTION",
                    "INCOMPLETE",
                ],
            )
        ],
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
        strict=[
            _plan(
                strict_dispositions=[
                    "EVIDENCE_CONTRADICTION",
                    "INCOMPLETE",
                ],
            )
        ],
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


def test_stage5_retry_reaches_later_winner_and_exports_accepted_subset(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    run_id = "strict-timeout-auto-retry"
    config = replace(
        _config(repo, candidates, run_id=run_id),
        proof_retry_max_attempts=4,
        proof_retry_backoff_seconds=0,
    )
    blocker, _ = _certificate(config, "strict-timeout-blocker")
    winner, _ = _certificate(config, "strict-timeout-eventual-win")
    runner = ScenarioRunner(
        stage2=[_plan([blocker, winner])],
        strict=[
            _plan(strict_dispositions=["INCOMPLETE", "INCOMPLETE"]),
            _plan(strict_dispositions=["INCOMPLETE", "ACCEPTED"]),
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
        assert _stage_script(command) == "audit_candidate_pool.py"
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


@pytest.mark.parametrize(
    "runtime_mutation",
    ["version", "installed-content", "transitive-content"],
)
def test_worker_runtime_change_invalidates_stage1_and_all_proof_caches(
    tmp_path,
    monkeypatch,
    runtime_mutation,
):
    repo, candidates = _repo(tmp_path)
    config = _config(repo, candidates, run_id="proof-runtime-change")
    winner, _ = _certificate(config, "proof-runtime-change-win")
    runner = ScenarioRunner(
        stage2=[_plan([winner]), _plan([winner])],
        strict=[_plan(), _plan()],
    )
    runtime = {
        "current": probe_python_runtime(
            config.python_executable,
            cwd=repo,
        )
    }
    monkeypatch.setattr(
        pipeline_module,
        "probe_python_runtime",
        lambda *_args, **_kwargs: runtime["current"],
    )

    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()
    assert first["status"] == "COMPLETED_WIN"

    runtime["current"] = json.loads(json.dumps(runtime["current"]))
    if runtime_mutation == "version":
        runtime["current"]["runtime"]["packages"]["ortools"] = (
            "runtime-changed"
        )
        runtime["current"]["runtime"]["package_artifacts"]["ortools"][
            "version"
        ] = "runtime-changed"
    else:
        package = (
            "ortools"
            if runtime_mutation == "installed-content"
            else "llvmlite"
        )
        runtime["current"]["runtime"]["package_artifacts"][package][
            "files_sha256"
        ] = "f" * 64
    second = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
    ).run()

    assert second["status"] == "COMPLETED_WIN"
    assert runner.counts == {"stage2": 2, "strict": 2}
    for stage in STAGE_ORDER:
        assert second["stages"][stage]["attempt"] == 2
    assert (
        second["stages"]["stage2_sector_audit"]["stage_config"][
            "proof_runtime"
        ]
        == runtime["current"]["runtime"]
    )
    assert (
        second["stages"]["stage5_strict_gate"]["stage_config"][
            "proof_runtime"
        ]
        == runtime["current"]["runtime"]
    )


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


def test_stage1_humanize_cache_is_invalidated_by_proof_runtime_change(
    tmp_path,
    monkeypatch,
):
    repo, candidates = _repo(tmp_path)
    for name in ("flow.py", "reviewer.py"):
        (repo / "humanize" / name).write_text(f"# fake {name}\n")
    evolve = repo / "evolve"
    evolve.mkdir()
    (evolve / "engine.py").write_text("# fake evolution engine\n")
    (repo / "main.py").write_text("# fake main\n")
    run_id = "stage1-runtime-change"
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
    runtime = {"current": proof_runtime_fingerprint()}
    monkeypatch.setattr(
        pipeline_module,
        "proof_runtime_fingerprint",
        lambda: runtime["current"],
    )
    flow_calls = []

    class SearchFlow:
        pipeline_candidate_inputs = (candidates,)

        def run(self):
            flow_calls.append(runtime["current"])
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidates)],
            }

    runner = ScenarioRunner()
    first = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        flow_factory=lambda _config: SearchFlow(),
    ).run()
    assert first["status"] == "COMPLETED_NO_WIN"

    runtime["current"] = json.loads(json.dumps(runtime["current"]))
    runtime["current"]["packages"]["highspy"] = "runtime-changed"
    runtime["current"]["package_artifacts"]["highspy"]["version"] = (
        "runtime-changed"
    )
    second = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        flow_factory=lambda _config: SearchFlow(),
    ).run()

    assert second["status"] == "COMPLETED_NO_WIN"
    assert len(flow_calls) == 2
    assert second["stages"]["stage1_search"]["attempt"] == 2
    assert (
        second["stages"]["stage1_search"]["stage_config"]["controller_runtime"]
        == runtime["current"]
    )


def test_stage1_new_attempt_clears_stale_terminal_monitoring_fields(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    for name in ("flow.py", "reviewer.py"):
        (repo / "humanize" / name).write_text(
            f"# fake humanize/{name}\n"
        )
    evolve = repo / "evolve"
    evolve.mkdir()
    (evolve / "engine.py").write_text("# fake evolution engine\n")
    (repo / "main.py").write_text("# fake main\n")
    run_id = "stage1-clear-stale-terminal-fields"
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

    class SearchFlow:
        @staticmethod
        def run():
            persisted = json.loads(config.root.joinpath("state.json").read_text())
            observed.update(persisted["stages"]["stage1_search"])
            return {
                "status": "search-complete",
                "candidate_inputs": [str(candidates)],
            }

    pipeline = FiveStagePipeline(
        config,
        command_runner=ScenarioRunner(),
        reviewer=RecordingReviewer(),
        flow_factory=lambda _config: SearchFlow(),
    )
    with pipeline._exclusive_lock():
        pipeline._load_or_initialize_state()
        stage1 = pipeline.state["stages"]["stage1_search"]
        stage1.update(
            {
                "status": "FAILED",
                "machine_status": "FAILED",
                "review_status": "COMPLETED",
                "review_attempt": 3,
                "finished_at": "2026-07-30T02:37:36+00:00",
                "machine_completed_at": "2026-07-30T02:30:00+00:00",
                "machine_summary": {"winner": "stale"},
                "output_hashes": {"stale.jsonl": "a" * 64},
                "candidate_inputs": ["stale.jsonl"],
                "resumed_machine": True,
                "review_started_at": "2026-07-30T02:31:00+00:00",
                "review_finished_at": "2026-07-30T02:32:00+00:00",
                "review_path": "reviews/stale.json",
                "review_fingerprint": "b" * 64,
                "review_machine_output_hashes": {
                    "stale.jsonl": "a" * 64,
                },
                "review_error": "stale review error",
                "advisory_failure": {"error": "stale advisory failure"},
                "bitlesson_ids": ["stale-lesson"],
                "failure": {
                    "classification": "INTERRUPTED",
                    "message": "pipeline interrupted",
                },
            }
        )
        pipeline._write_state()
        assert pipeline._stage1_inputs() == [candidates.resolve()]

    assert observed["status"] == "RUNNING"
    assert observed["machine_status"] == "RUNNING"
    assert observed["review_status"] == "PENDING"
    assert observed["attempt"] == 1
    assert observed["review_attempt"] == 3
    for field_name in (
        "advisory_failure",
        "bitlesson_ids",
        "candidate_inputs",
        "failure",
        "finished_at",
        "machine_completed_at",
        "machine_summary",
        "output_hashes",
        "resumed_machine",
        "review_error",
        "review_fingerprint",
        "review_finished_at",
        "review_machine_output_hashes",
        "review_path",
        "review_started_at",
    ):
        assert field_name not in observed


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
        if _stage_script(command) == stage_script:
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
        if _stage_script(command) == "finalize_challenge.py":
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
        if _stage_script(command) == "finalize_challenge.py":
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
        if _stage_script(command) == "finalize_challenge.py":
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
        if _stage_script(command) == "finalize_challenge.py":
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
        assert _stage_script(command) == "audit_candidate_pool.py"
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


def test_structural_timeout_is_global_retryable_stage2_incompleteness(
    tmp_path,
):
    repo, candidates = _repo(tmp_path)
    pipeline = FiveStagePipeline(
        _config(repo, candidates, run_id="structural-incomplete"),
        command_runner=ScenarioRunner(),
        reviewer=RecordingReviewer(),
    )
    incompleteness = pipeline._proof_incompleteness(
        {
            "selection_exhausted": False,
            "structural_unresolved_candidates": 1,
            "results": [],
        },
        {
            "selection_exhausted": True,
            "results": [],
        },
    )

    codes = {
        reason["code"] for reason in incompleteness["reasons"]
    }
    assert "STAGE2_SELECTION_TRUNCATED" in codes
    assert "STAGE2_STRUCTURAL_UNRESOLVED_CANDIDATES" in codes
    assert (
        "STAGE2_STRUCTURAL_UNRESOLVED_CANDIDATES"
        not in pipeline_module.STAGE2_GLOBAL_INPUT_INCOMPLETENESS_CODES
    )
    assert incompleteness["retry_stages"] == ["stage2_sector_audit"]


def test_zero_page_structural_barrier_escalates_and_reaches_win(tmp_path):
    repo, candidates = _repo(tmp_path)
    config = replace(
        _config(repo, candidates, run_id="structural-zero-page-retry"),
        proof_retry_max_attempts=3,
        proof_retry_max_multiplier=4,
        proof_retry_backoff_seconds=0,
    )
    winner, _ = _certificate(config, "structural-late-win")
    runner = ScenarioRunner(
        stage2=[
            _plan(
                [],
                selection_exhausted=False,
                structural_unresolved_candidates=1,
            ),
            _plan(
                [],
                selection_exhausted=False,
                structural_unresolved_candidates=1,
            ),
            _plan(
                [winner],
                selection_exhausted=True,
                selection_page=(0, 1),
                snapshot_rows=1,
            ),
        ],
        stage3=[_plan()],
    )

    state = FiveStagePipeline(
        config,
        command_runner=runner,
        reviewer=RecordingReviewer(),
        sleeper=lambda _seconds: None,
    ).run()

    assert state["status"] == "COMPLETED_WIN"
    stage2_commands = runner.commands("stage2")
    assert len(stage2_commands) == 3
    assert [
        float(command[command.index("--structural-hard-timeout") + 1])
        for command in stage2_commands
    ] == [300, 600, 1200]
    controller = json.loads(
        (
            config.root
            / "solver-state"
            / "proof-retry-controller.json"
        ).read_text()
    )["active"]
    assert [attempt["multiplier"] for attempt in controller["attempts"]] == [
        1,
        2,
        4,
    ]
    assert controller["attempts"][-1]["status"] == "COMPLETED_WIN"
    assert controller["binding"]["selected_digests"] == []


def test_unexpected_pipeline_exception_is_recorded_as_internal_error(
    tmp_path,
    monkeypatch,
):
    repo, candidates = _repo(tmp_path)
    pipeline = FiveStagePipeline(
        _config(repo, candidates, run_id="unexpected-internal-error"),
        command_runner=ScenarioRunner(),
        reviewer=RecordingReviewer(),
    )

    def fail_stage1_inputs():
        raise RuntimeError("unexpected stage-1 handoff failure")

    monkeypatch.setattr(pipeline, "_stage1_inputs", fail_stage1_inputs)

    state = pipeline.run()

    assert state["status"] == "FAILED"
    assert state["failure"]["classification"] == "INTERNAL_ERROR"
    assert state["failure"]["message"] == (
        "RuntimeError: unexpected stage-1 handoff failure"
    )
