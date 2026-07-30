from __future__ import annotations

import argparse
import json
from pathlib import Path

import pytest

from evaluation.certificate import _certificate_sha256
from scripts import finalize_challenge as finalizer


def _certificate(index: int = 0) -> dict:
    return {
        "certificate_type": "qldpc-css-bb-exact",
        "certificate_sha256": f"certificate-{index}",
        "passed": True,
        "claim": {"n": 72 + index, "k": 12, "d": 7},
    }


def _terminal_negative(index: int = 0) -> dict:
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
        "claim": {"n": 72 + index, "k": 12, "d": 6},
        "milp": {
            "exact": True,
            "completed_directions": 24,
            "expected_directions": 24,
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
        "failure_disposition": {
            "schema_version": 1,
            "status": "CANDIDATE_REJECTED",
            "domain": "candidate",
            "codes": ["GATE_CHALLENGE_WIN"],
        },
    }
    certificate["certificate_sha256"] = _certificate_sha256(certificate)
    return certificate


def _args(tmp_path: Path, rows: list[dict] | None = None) -> argparse.Namespace:
    claims = tmp_path / "claims.json"
    claims.write_text(json.dumps(rows or [_certificate()]) + "\n")
    known_answer = tmp_path / "known-answer.json"
    known_answer.write_text('{"passed": true}\n')
    trust = tmp_path / "known-answer-trust.json"
    trust.write_text('{"schema_version": 1}\n')
    return argparse.Namespace(
        claims=claims,
        known_answer_artifact=known_answer,
        known_answer_trust=trust,
        known_answer_timeout_per_logical=101,
        known_answer_total_timeout=202,
        verification_timeout_per_logical=11.0,
        verification_total_timeout=40.0,
        verification_solver_workers=3,
        verification_state_dir=tmp_path / "verification-state",
        resume=True,
        output=tmp_path / "final-gate.json",
    )


def _strict_integrity(*_args, **_kwargs) -> dict:
    return {"mode": "strict", "passed": True, "failures": []}


def _bypass_strict_hard_wall(monkeypatch) -> None:
    monkeypatch.setattr(
        finalizer,
        "_strict_integrity_with_hard_wall",
        lambda _args: _strict_integrity(),
    )


def test_main_forwards_strict_replay_budget_and_checkpoint(tmp_path, monkeypatch):
    args = _args(tmp_path)
    calls = []
    clock = iter((100.0, 102.0))
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: next(clock))

    def verify(certificate, **kwargs):
        calls.append((certificate, kwargs))
        return {"passed": True, "accepted": True, "failures": []}

    monkeypatch.setattr(finalizer, "_verify_certificate_with_hard_wall", verify)

    assert finalizer.main() == 0
    assert len(calls) == 1
    certificate, controls = calls[0]
    assert certificate == _certificate()
    assert controls["timeout_per_logical"] == 11.0
    assert controls["total_timeout"] == 38.0
    assert controls["solver_workers"] == 3
    assert controls["resume"] is True
    checkpoint = Path(controls["checkpoint_path"])
    assert checkpoint.parent == args.verification_state_dir
    assert checkpoint.name == (
        f"{finalizer._payload_sha256(_certificate())}.json"
    )

    artifact = json.loads(args.output.read_text())
    assert artifact["passed"] is True
    assert artifact["known_answer_integrity"]["mode"] == "strict"
    assert artifact["verification_budget"] == {
        "timeout_per_logical": 11.0,
        "total_timeout": 40.0,
        "solver_workers": 3,
        "resume": True,
        "state_dir": str(args.verification_state_dir),
    }


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("verification_timeout_per_logical", 0),
        ("verification_total_timeout", float("inf")),
        ("verification_solver_workers", 0),
        ("verification_solver_workers", 9),
        ("verification_solver_workers", True),
    ],
)
def test_invalid_verification_budget_fails_before_replay(
    tmp_path, monkeypatch, field, value
):
    args = _args(tmp_path)
    setattr(args, field, value)
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    monkeypatch.setattr(
        finalizer,
        "_verify_certificate_with_hard_wall",
        lambda *_args, **_kwargs: pytest.fail("invalid budget reached replay"),
    )

    assert finalizer.main() == 2
    assert not args.output.exists()


def test_batch_timeout_rotates_to_later_certificate_after_restart(
    tmp_path,
    monkeypatch,
):
    certificates = [_certificate(0), _certificate(1)]
    args = _args(tmp_path, certificates)
    args.verification_total_timeout = 10.0
    calls = []
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)

    def verify(certificate, **kwargs):
        calls.append((certificate, kwargs))
        if certificate == certificates[0]:
            return {
                "passed": False,
                "replay_complete": False,
                "failures": ["first certificate exhausted its budget"],
            }
        return {"passed": True, "accepted": True, "failures": []}

    monkeypatch.setattr(finalizer, "_verify_certificate_with_hard_wall", verify)

    first_clock = iter((0.0, 1.0, 11.0))
    monkeypatch.setattr(
        finalizer.time,
        "monotonic",
        lambda: next(first_clock),
    )
    assert finalizer.main() == 0
    assert len(calls) == 1
    assert calls[0][1]["total_timeout"] == 4.5
    first = json.loads(args.output.read_text())
    assert first["passed"] is False
    assert first["outcome"] == "INCOMPLETE"
    assert first["summary"] == {
        "accepted": 0,
        "rejected": 0,
        "incomplete": 2,
        "total": 2,
    }
    scheduler_path = (
        args.verification_state_dir / finalizer.SCHEDULER_FILENAME
    )
    scheduler = json.loads(scheduler_path.read_text())
    assert scheduler["next_payload_sha256"] == finalizer._payload_sha256(
        certificates[1]
    )

    reordered = [certificates[1], certificates[0]]
    args.claims.write_text(json.dumps(reordered) + "\n")
    second_clock = iter((0.0, 1.0))
    monkeypatch.setattr(
        finalizer.time,
        "monotonic",
        lambda: next(second_clock),
    )
    assert finalizer.main() == 0

    assert [certificate for certificate, _ in calls] == certificates
    assert calls[1][1]["total_timeout"] == 4.5
    assert Path(calls[1][1]["checkpoint_path"]).name == (
        f"{finalizer._payload_sha256(certificates[1])}.json"
    )
    second = json.loads(args.output.read_text())
    assert second["passed"] is True
    assert second["outcome"] == "WIN"
    assert second["summary"] == {
        "accepted": 1,
        "rejected": 0,
        "incomplete": 1,
        "total": 2,
    }
    assert second["evaluations"][0]["claim"] == reordered[0]["claim"]
    assert second["evaluations"][0]["disposition"] == "ACCEPTED"
    assert second["evaluations"][1]["claim"] == reordered[1]["claim"]
    assert second["evaluations"][1]["disposition"] == "INCOMPLETE"
    assert second["evaluations"][1]["result"]["failures"] == [
        "strict replay deferred by fair batch scheduler"
    ]


def test_scheduler_advances_before_crashed_verifier_and_resumes_peer(
    tmp_path,
    monkeypatch,
):
    certificates = [_certificate(0), _certificate(1)]
    args = _args(tmp_path, certificates)
    calls = []
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: 0.0)

    def crash(certificate, **kwargs):
        calls.append((certificate, kwargs))
        raise KeyboardInterrupt

    monkeypatch.setattr(finalizer, "_verify_certificate_with_hard_wall", crash)
    with pytest.raises(KeyboardInterrupt):
        finalizer.main()

    scheduler = json.loads(
        (
            args.verification_state_dir / finalizer.SCHEDULER_FILENAME
        ).read_text()
    )
    assert scheduler["last_started_payload_sha256"] == (
        finalizer._payload_sha256(certificates[0])
    )
    assert scheduler["next_payload_sha256"] == finalizer._payload_sha256(
        certificates[1]
    )

    def accept(certificate, **kwargs):
        calls.append((certificate, kwargs))
        return {"passed": True, "accepted": True, "failures": []}

    monkeypatch.setattr(finalizer, "_verify_certificate_with_hard_wall", accept)
    assert finalizer.main() == 0

    assert [certificate for certificate, _ in calls] == certificates
    artifact = json.loads(args.output.read_text())
    assert artifact["outcome"] == "WIN"
    assert artifact["evaluations"][0]["disposition"] == "INCOMPLETE"
    assert artifact["evaluations"][1]["disposition"] == "ACCEPTED"


def test_verifier_runtime_error_is_persisted_fail_closed(tmp_path, monkeypatch):
    args = _args(tmp_path)
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(
        finalizer,
        "_verify_certificate_with_hard_wall",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(RuntimeError("solver died")),
    )

    assert finalizer.main() == 0
    artifact = json.loads(args.output.read_text())
    assert artifact["outcome"] == "INCOMPLETE"
    assert artifact["evaluations"][0]["disposition"] == "INCOMPLETE"
    result = artifact["evaluations"][0]["result"]
    assert result["passed"] is False
    assert "RuntimeError: solver died" in result["failures"][0]


def test_missing_replay_completeness_is_incomplete(tmp_path, monkeypatch):
    args = _args(tmp_path)
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(
        finalizer,
        "_verify_certificate_with_hard_wall",
        lambda *_args, **_kwargs: {
            "passed": False,
            "failures": ["verifier omitted replay completion"],
        },
    )

    assert finalizer.main() == 0
    artifact = json.loads(args.output.read_text())
    assert artifact["outcome"] == "INCOMPLETE"
    assert artifact["evaluations"][0]["disposition"] == "INCOMPLETE"
    assert artifact["evaluations"][0]["result"]["replay_complete"] is False


def test_passed_certificate_replay_mismatch_is_incomplete(tmp_path, monkeypatch):
    args = _args(tmp_path, [_certificate(0), _certificate(1)])
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: 0.0)
    monkeypatch.setattr(
        finalizer,
        "_verify_certificate_with_hard_wall",
        lambda *_args, **_kwargs: {
            "passed": False,
            "replay_complete": True,
            "failures": ["certificate_sha256"],
        },
    )

    assert finalizer.main() == 0
    artifact = json.loads(args.output.read_text())
    assert artifact["passed"] is False
    assert artifact["outcome"] == "INCOMPLETE"
    assert artifact["summary"] == {
        "accepted": 0,
        "rejected": 0,
        "incomplete": 2,
        "total": 2,
    }
    assert {
        evaluation["disposition"] for evaluation in artifact["evaluations"]
    } == {"INCOMPLETE"}
    assert {
        evaluation["result"]["failure_disposition"]["status"]
        for evaluation in artifact["evaluations"]
    } == {"EVIDENCE_CONTRADICTION"}


def test_typed_raw_candidate_rejections_remain_no_win(tmp_path, monkeypatch):
    rejected = [_terminal_negative(index) for index in range(2)]
    args = _args(tmp_path, rejected)
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: 0.0)
    monkeypatch.setattr(
        finalizer,
        "_verify_certificate_with_hard_wall",
        lambda *_args, **_kwargs: {
            "passed": False,
            "replay_complete": True,
            "checks": {
                "schema": True,
                "certificate_sha256": True,
                "known_answer_sha256": True,
                "matrix_sha256": True,
                "direction_count": True,
                "stored_direction_evidence": True,
                "milp_rerun": True,
                "distance_recomputed": True,
                "final_gate": False,
                "certificate_passed_flag": False,
            },
            "failures": ["final_gate", "certificate_passed_flag"],
            "final_gate": rejected[0]["final_gate"],
        },
    )

    assert finalizer.main() == 0
    artifact = json.loads(args.output.read_text())
    assert artifact["outcome"] == "NO_WIN"
    assert artifact["summary"] == {
        "accepted": 0,
        "rejected": 2,
        "incomplete": 0,
        "total": 2,
    }


def test_negative_certificate_cannot_override_replay_contradiction(
    tmp_path,
    monkeypatch,
):
    certificate = _terminal_negative(0)
    args = _args(tmp_path, [certificate])
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: 0.0)
    monkeypatch.setattr(
        finalizer,
        "_verify_certificate_with_hard_wall",
        lambda *_args, **_kwargs: {
            "passed": False,
            "replay_complete": True,
            "checks": {
                "schema": False,
                "certificate_sha256": False,
                "known_answer_sha256": True,
                "matrix_sha256": True,
                "direction_count": True,
                "stored_direction_evidence": True,
                "milp_rerun": True,
                "distance_recomputed": True,
                "final_gate": False,
                "certificate_passed_flag": False,
            },
            "failures": [
                "schema",
                "certificate_sha256",
                "final_gate",
                "certificate_passed_flag",
            ],
            "final_gate": certificate["final_gate"],
        },
    )

    assert finalizer.main() == 0
    artifact = json.loads(args.output.read_text())
    assert artifact["outcome"] == "INCOMPLETE"
    result = artifact["evaluations"][0]["result"]
    assert result["failure_disposition"]["status"] == "EVIDENCE_CONTRADICTION"
    assert result["replay_complete"] is True


def test_no_winner_with_timeout_is_incomplete(tmp_path, monkeypatch):
    args = _args(tmp_path, [_certificate(0), _certificate(1)])
    args.verification_total_timeout = 10.0
    clock = iter((0.0, 11.0, 12.0))
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    _bypass_strict_hard_wall(monkeypatch)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: next(clock))
    monkeypatch.setattr(
        finalizer,
        "_verify_certificate_with_hard_wall",
        lambda *_args, **_kwargs: pytest.fail("expired batch reached verifier"),
    )

    assert finalizer.main() == 0
    artifact = json.loads(args.output.read_text())
    assert artifact["passed"] is False
    assert artifact["outcome"] == "INCOMPLETE"
    assert artifact["summary"] == {
        "accepted": 0,
        "rejected": 0,
        "incomplete": 2,
        "total": 2,
    }
