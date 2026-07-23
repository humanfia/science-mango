import json
from pathlib import Path

from archon.commands import qcode_formalize
from archon.commands.qcode_formalize import distance_is_exact, prepare_catalogs


def _row(**updates):
    row = {
        "ell": 6,
        "m": 6,
        "A_terms": [[0, 0], [0, 1], [1, 0]],
        "B_terms": [[0, 0], [0, 2], [2, 0]],
        "n": 72,
        "k": 12,
        "d": 6,
        "score": 6.0,
        "stage": "milp_exact",
        "d_is_exact": True,
        "milp_details": {
            "exact": True,
            "total_logicals": 24,
            "num_logicals_checked": 24,
            "logicals_optimal": 24,
        },
    }
    row.update(updates)
    return row


def test_milp_exact_requires_full_optimal_coverage():
    assert distance_is_exact(_row())
    assert not distance_is_exact(_row(milp_details={
        "exact": True,
        "total_logicals": 24,
        "num_logicals_checked": 7,
        "logicals_optimal": 7,
    }))


def test_prepare_catalogs_separates_exact_and_upper_and_deduplicates():
    exact = _row(score=10, milp_attempted=True)
    duplicate = _row(score=1)
    partial = _row(
        ell=12,
        m=6,
        n=144,
        score=9,
        milp_attempted=True,
        d=14,
        milp_details={
            "exact": True,
            "total_logicals": 24,
            "num_logicals_checked": 7,
            "logicals_optimal": 7,
        },
    )
    exact_catalog, upper_catalog = prepare_catalogs([duplicate, partial, exact], 0)
    assert [r["label"] for r in exact_catalog["archon-qcode-exact"]] == ["[[72,12,6]]"]
    assert [r["label"] for r in upper_catalog["archon-qcode-upper"]] == ["[[144,12,<=14]]"]


def test_prepare_catalogs_prefers_milp_audited_rows():
    unaudited = _row(score=100, d_is_exact=False, stage="quick_estimate")
    audited = _row(score=1, milp_attempted=True)
    exact_catalog, upper_catalog = prepare_catalogs([unaudited, audited], 1)
    assert len(exact_catalog["archon-qcode-exact"]) == 1
    assert not upper_catalog["archon-qcode-upper"]


def test_formalize_routes_generic_certificate_only_to_universal(
    tmp_path, monkeypatch,
):
    repo = tmp_path / "qcode"
    run_root = repo / "results" / "runs" / "route-test"
    certificate_dir = run_root / "certificates"
    certificate_dir.mkdir(parents=True)
    certificate = {
        "certificate_type": "qldpc-css-matrix-exact",
        "passed": True,
        "claim": {"n": 2, "k": 1, "d": 1},
    }
    (certificate_dir / "candidate.json").write_text(json.dumps(certificate))
    manifest = {
        "certificates": [{
            "file": "certificates/candidate.json",
            "verification": {"passed": True},
        }],
    }
    (run_root / "challenge_manifest.json").write_text(json.dumps(manifest))
    calls = []

    def record_run(cmd, cwd):
        calls.append([str(part) for part in cmd])

    monkeypatch.setattr(qcode_formalize, "_run", record_run)
    output = qcode_formalize.formalize_qcode_run(
        lean_project=tmp_path / "lean",
        repo_dir=repo,
        bridge_dir=tmp_path / "bridges",
        run_id="route-test",
        python="python",
        top=0,
        witness_timeout=10,
        sat_timeout=30,
        skip_missing=False,
    )
    invoked = [Path(call[1]).name for call in calls]
    assert invoked == [
        "check_release_manifest.py",
        "verify_release.py",
        "bridge_universal.py",
    ]
    result = json.loads((output / "manifest.json").read_text())
    assert result["universal_exact_claims"] == 1
    assert result["exact_claims"] == result["upper_bound_claims"] == 0
