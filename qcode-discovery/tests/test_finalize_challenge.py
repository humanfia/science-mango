from __future__ import annotations

import argparse
import json
from pathlib import Path

import pytest

from scripts import finalize_challenge as finalizer


def _certificate(index: int = 0) -> dict:
    return {
        "certificate_type": "qldpc-css-bb-exact",
        "certificate_sha256": f"certificate-{index}",
        "claim": {"n": 72 + index, "k": 12, "d": 7},
    }


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


def test_main_forwards_strict_replay_budget_and_checkpoint(tmp_path, monkeypatch):
    args = _args(tmp_path)
    calls = []
    clock = iter((100.0, 102.0))
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    monkeypatch.setattr(finalizer, "check_known_answer_integrity", _strict_integrity)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: next(clock))

    def verify(certificate, **kwargs):
        calls.append((certificate, kwargs))
        return {"passed": True, "accepted": True, "failures": []}

    monkeypatch.setattr(finalizer, "verify_certificate", verify)

    assert finalizer.main() == 0
    assert len(calls) == 1
    certificate, controls = calls[0]
    assert certificate == _certificate()
    assert controls["rerun_milp"] is True
    assert controls["timeout_per_logical"] == 11.0
    assert controls["total_timeout"] == 38.0
    assert controls["solver_workers"] == 3
    assert controls["resume"] is True
    checkpoint = Path(controls["checkpoint_path"])
    assert checkpoint.parent == args.verification_state_dir
    assert checkpoint.name.startswith("0000-")

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
        "verify_certificate",
        lambda *_args, **_kwargs: pytest.fail("invalid budget reached replay"),
    )

    assert finalizer.main() == 2
    assert not args.output.exists()


def test_batch_timeout_stops_later_certificate_replay(tmp_path, monkeypatch):
    args = _args(tmp_path, [_certificate(0), _certificate(1)])
    args.verification_total_timeout = 10.0
    calls = []
    clock = iter((0.0, 1.0, 11.0))
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    monkeypatch.setattr(finalizer, "check_known_answer_integrity", _strict_integrity)
    monkeypatch.setattr(finalizer.time, "monotonic", lambda: next(clock))

    def verify(certificate, **kwargs):
        calls.append((certificate, kwargs))
        return {"passed": True, "accepted": True, "failures": []}

    monkeypatch.setattr(finalizer, "verify_certificate", verify)

    assert finalizer.main() == 1
    assert len(calls) == 1
    assert calls[0][1]["total_timeout"] == 9.0
    artifact = json.loads(args.output.read_text())
    assert artifact["summary"] == {"accepted": 1, "rejected": 1, "total": 2}
    assert artifact["evaluations"][1]["result"]["failures"] == [
        "strict replay batch timeout exhausted"
    ]


def test_verifier_runtime_error_is_persisted_fail_closed(tmp_path, monkeypatch):
    args = _args(tmp_path)
    monkeypatch.setattr(finalizer, "parse_args", lambda: args)
    monkeypatch.setattr(finalizer, "check_known_answer_integrity", _strict_integrity)
    monkeypatch.setattr(
        finalizer,
        "verify_certificate",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(RuntimeError("solver died")),
    )

    assert finalizer.main() == 1
    artifact = json.loads(args.output.read_text())
    result = artifact["evaluations"][0]["result"]
    assert result["passed"] is False
    assert "RuntimeError: solver died" in result["failures"][0]
