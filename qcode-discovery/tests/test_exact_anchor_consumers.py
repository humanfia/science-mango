from __future__ import annotations

import json
import sys

import pytest

import verify as verify_cli
from evaluation.certificate_dispatch import EXACT_ANCHOR_CSS_TYPE
from scripts import build_certificate as build_cli
from scripts import finalize_challenge as finalizer
from scripts import verify_release


def _calibration_stub():
    return {
        "certificate_type": EXACT_ANCHOR_CSS_TYPE,
        "parameters": {"n": 224, "k": 12, "d": 16},
    }


def test_verify_cli_reports_valid_calibration_without_treating_it_as_passed(
    tmp_path,
    monkeypatch,
    capsys,
):
    certificate_path = tmp_path / "certificate.json"
    certificate_path.write_text(json.dumps(_calibration_stub()))
    policy_path = tmp_path / "policy.json"
    policy_path.write_text("{}")
    artifact_root = tmp_path / "artifacts"
    artifact_root.mkdir()
    calls = {}

    def forbidden_known_answer(*_args, **_kwargs):
        raise AssertionError("calibration verification must not run known-answer solver")

    def fake_verify(certificate, **kwargs):
        calls["certificate"] = certificate
        calls["kwargs"] = kwargs
        return {
            "calibration_valid": True,
            "passed": False,
            "failures": [],
        }

    monkeypatch.setattr(verify_cli, "check_known_answer_integrity", forbidden_known_answer)
    monkeypatch.setattr(
        verify_cli,
        "load_trusted_checker_policy",
        lambda path: {"pinned": {"policy": str(path)}},
    )
    monkeypatch.setattr(verify_cli, "verify_certificate", fake_verify)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "verify.py",
            str(certificate_path),
            "--artifact-root",
            str(artifact_root),
            "--trusted-checker-policy",
            str(policy_path),
            "--checker-timeout",
            "17.5",
        ],
    )

    assert verify_cli.main() == 0
    output = capsys.readouterr()
    assert "CALIBRATION VERIFIED / NOT A WIN" in output.out
    assert calls["kwargs"]["artifact_root"] == artifact_root
    assert calls["kwargs"]["checker_timeout_s"] == 17.5
    assert "rerun_milp" not in calls["kwargs"]


@pytest.mark.parametrize(
    ("missing_args", "fragment"),
    [
        (["--trusted-checker-policy", "policy.json", "--checker-timeout", "5"], "artifact-root"),
        (["--artifact-root", "artifacts", "--checker-timeout", "5"], "trusted-checker-policy"),
        (
            ["--artifact-root", "artifacts", "--trusted-checker-policy", "policy.json"],
            "checker-timeout",
        ),
    ],
)
def test_verify_cli_requires_all_explicit_calibration_trust_inputs(
    tmp_path,
    monkeypatch,
    capsys,
    missing_args,
    fragment,
):
    certificate_path = tmp_path / "certificate.json"
    certificate_path.write_text(json.dumps(_calibration_stub()))
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(
        verify_cli,
        "check_known_answer_integrity",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(
            AssertionError("must not run known-answer replay")
        ),
    )
    monkeypatch.setattr(sys, "argv", ["verify.py", str(certificate_path), *missing_args])

    assert verify_cli.main() == 2
    assert fragment in capsys.readouterr().err


def test_build_cli_packages_calibration_without_milp_or_final_gate_access(
    tmp_path,
    monkeypatch,
    capsys,
):
    source = tmp_path / "source.json"
    source.write_text(json.dumps(_calibration_stub()))
    output = tmp_path / "packaged.json"
    built = _calibration_stub()

    monkeypatch.setattr(build_cli, "build_certificate", lambda *_args, **_kwargs: built)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "build_certificate.py",
            str(source),
            "--output",
            str(output),
        ],
    )

    assert build_cli.main() == 0
    assert json.loads(output.read_text()) == built
    captured = capsys.readouterr()
    assert "VERIFICATION REQUIRED" in captured.out
    assert "NOT A WIN" in captured.out


def test_release_consumer_explicitly_rejects_calibration():
    failure = verify_release.calibration_release_failure(_calibration_stub())
    assert failure is not None
    assert "ineligible" in failure
    assert verify_release.calibration_release_failure(
        {"certificate_type": "qldpc-css-bb-exact"}
    ) is None


def test_finalizer_rejects_calibration_before_known_answer_or_solver(
    tmp_path,
    monkeypatch,
    capsys,
):
    claims = tmp_path / "claims.json"
    claims.write_text(json.dumps([_calibration_stub()]))

    def forbidden_integrity(_args):
        raise AssertionError("calibration must be rejected before known-answer replay")

    monkeypatch.setattr(finalizer, "_strict_integrity_with_hard_wall", forbidden_integrity)
    monkeypatch.setattr(sys, "argv", ["finalize_challenge.py", str(claims)])

    assert finalizer.main() == 2
    assert "ineligible for challenge finalization" in capsys.readouterr().err
