import hashlib
import json
from pathlib import Path


def test_search_summary_counts_and_artifact_hashes():
    results = Path(__file__).resolve().parent.parent / "results"
    summary = json.loads((results / "real_win_search_summary.json").read_text())
    assert summary["status"] == "no_certified_win"
    assert summary["aggregate"] == {
        "sampled": 115000,
        "commuting": 560,
        "static_pass": 77,
        "basis_bound_pass": 16,
        "milp_attempted": 16,
        "certified_wins": 0,
    }
    for run in summary["runs"]:
        if "artifact" not in run:
            continue
        payload = (results / run["artifact"]).read_bytes()
        assert hashlib.sha256(payload).hexdigest() == run["artifact_sha256"]
    legacy = summary["legacy_high_score_recheck"]
    payload = (results / legacy["artifact"]).read_bytes()
    assert hashlib.sha256(payload).hexdigest() == legacy["artifact_sha256"]
