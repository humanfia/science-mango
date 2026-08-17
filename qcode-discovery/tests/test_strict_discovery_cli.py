from __future__ import annotations

import ast
import json
from argparse import Namespace
from pathlib import Path
from types import SimpleNamespace

import pytest

from evaluation.selection_ledger import (
    acknowledge_selection_page,
    install_pending_page,
    make_scan_evidence,
    make_selection_page,
    new_selection_ledger,
)
from humanize import strict_discovery_cli as cli


_REAL_VALIDATE_LIVE = cli.validate_live_portfolio_source


def _paths(tmp_path: Path) -> cli.SidecarPaths:
    repo = tmp_path / "repo"
    run = repo / "results" / "humanize" / "pipelines" / "run"
    root = run / "sidecars" / cli.SIDECAR_NAME
    root.mkdir(parents=True)
    (repo / "scripts").mkdir()
    return cli.SidecarPaths(
        repo=repo,
        run_root=run,
        root=root,
        process=root / "process.json",
        lock=root / "process.lock",
        log=root / "worker.log",
        progress=root / "progress.json",
        batches=root / "batches",
    )


def _jsonl(path: Path, rows: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(
            json.dumps({
                "rank": index,
                "canonical_digest": f"{index + 1:064x}",
            }) + "\n"
            for index in range(rows)
        ),
        encoding="utf-8",
    )


def _portfolio_manifest(paths: cli.SidecarPaths, ranked: Path) -> Path:
    path = paths.root / "portfolio.json"
    if path.exists():
        return path
    rows = sum(1 for _ in ranked.open("rb"))
    ledger = paths.run_root / "solver-state" / "stage2-selection-ledger.json"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text("{}\n", encoding="utf-8")
    snapshot_manifest = ledger.with_name(
        ledger.name + ".ranked-snapshot.manifest.json"
    )
    snapshot_manifest.write_text(
        json.dumps({"manifest_sha256": "d" * 64}) + "\n",
        encoding="utf-8",
    )
    items = []
    for index in range(rows):
        digest = f"{index + 1:064x}"
        items.append({
            "canonical_digest": digest,
            "portfolio_rank": index + 1,
            "scheduling_only": True,
            "n": 12,
            "k": 1,
            "d_req": 13,
            "required_distance": 13,
            "cutoff": 12,
        })
    batches = []
    cursor = 0
    for limit in (100, 400):
        selected = items[cursor : cursor + limit]
        if selected:
            batches.append({
                "sequence": len(batches),
                "count": len(selected),
                "digests": [item["canonical_digest"] for item in selected],
            })
            cursor += len(selected)
    while cursor < len(items):
        selected = items[cursor : cursor + 500]
        batches.append({
            "sequence": len(batches),
            "count": len(selected),
            "digests": [item["canonical_digest"] for item in selected],
        })
        cursor += len(selected)
    manifest = {
        "schema_version": cli.PORTFOLIO_SCHEMA_VERSION,
        "gate": cli.PORTFOLIO_GATE,
        "producer": {
            "module": "humanize.strict_discovery_ranking",
            "source_sha256": cli._file_sha256(
                Path(cli.__file__).resolve().with_name(
                    "strict_discovery_ranking.py"
                )
            ),
        },
        "publication_certificate": False,
        "pipeline_promotion": False,
        "target_mode": cli.TARGET_MODE,
        "source": {
            "ledger_path": str(ledger.resolve()),
            "ledger_generation": 0,
            "ledger_cursor": 0,
            "portfolio_cursor": 0,
            "snapshot_identity_sha256": "e" * 64,
            "manifest_path": str(snapshot_manifest.resolve()),
            "manifest_file_sha256": cli._file_sha256(snapshot_manifest),
            "manifest_sha256": "d" * 64,
        },
        "items": items,
        "batches": batches,
        "ranked_input": {
            "path": str(ranked.resolve()),
            "bytes": ranked.stat().st_size,
            "rows": rows,
            "sha256": cli._file_sha256(ranked),
            "payload_kind": cli.PORTFOLIO_PAYLOAD_KIND,
        },
    }
    manifest["portfolio_sha256"] = cli._sha256(manifest)
    path.write_text(json.dumps(manifest) + "\n", encoding="utf-8")
    return path


@pytest.fixture(autouse=True)
def _no_live_overlap(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        cli,
        "validate_live_portfolio_source",
        lambda *args, **kwargs: {
            "overlap": False,
            "blocked_digests": [],
            "check_scope": "test",
        },
    )


def _value(argv: list[str], option: str) -> str:
    return argv[argv.index(option) + 1]


def _write_complete_no_win(
    argv: list[str],
    *,
    statuses: list[str] | None = None,
) -> None:
    count = int(_value(argv, "--top"))
    values = statuses or ["REJECTED"] * count
    assert len(values) == count
    input_rows = [
        json.loads(line)
        for line in Path(argv[2]).read_text(encoding="utf-8").splitlines()
    ]
    digests = [str(row["canonical_digest"]) for row in input_rows]
    assert len(digests) == count
    ranked = Path(_value(argv, "--ranked-output"))
    summary = Path(_value(argv, "--summary-output"))
    ranked.parent.mkdir(parents=True, exist_ok=True)
    ranked.write_text(
        "".join(
            json.dumps({
                "campaign_selected": True,
                "campaign_audit": {
                    "canonical_digest": digest,
                    "status": status,
                },
            }) + "\n"
            for digest, status in zip(digests, values, strict=True)
        ),
        encoding="utf-8",
    )
    summary.write_text(
        json.dumps({
            "target_mode": cli.TARGET_MODE,
            "selected_candidates": count,
            "top": count,
            "canonical_duplicates_skipped": 0,
            "known_codes_skipped": 0,
            "unsupported_candidates_skipped": 0,
            "canonicalization_errors": 0,
            "structural_unresolved_candidates": 0,
            "unscanned_eligible_candidates": 0,
            "selection_exhausted": True,
            "certificate_operational_errors": 0,
        }),
        encoding="utf-8",
    )
    ledger_path = Path(_value(argv, "--selection-ledger"))
    binding = "b" * 64
    identity = "d" * 64
    ledger = new_selection_ledger(
        binding_sha256=binding,
        snapshot_identity_sha256_value=identity,
        snapshot_rows=count,
        eligible_rows=count,
    )
    scan = make_scan_evidence(
        snapshot_identity_sha256_value=identity,
        start_index=0,
        next_index=count,
        snapshot_rows=count,
        eligible_rows=count,
        selection_exhausted=True,
    )
    page = make_selection_page(
        binding_sha256=binding,
        snapshot_identity_sha256_value=identity,
        page_sequence=0,
        previous_ack_sha256=str(ledger["last_ack_sha256"]),
        start_index=0,
        next_index=count,
        selected_digests=digests,
        scan_evidence=scan,
    )
    ledger = acknowledge_selection_page(
        install_pending_page(ledger, page),
        page,
        disposition="COMPLETED",
    )
    ledger_path.write_text(json.dumps(ledger) + "\n", encoding="utf-8")


def _write_complete_win(
    argv: list[str],
    *,
    digest: str | None = None,
    certificate_sha256: str = "c" * 64,
) -> None:
    count = int(_value(argv, "--top"))
    _write_complete_no_win(
        argv,
        statuses=["THRESHOLD_PROVEN", *(["REJECTED"] * (count - 1))],
    )
    ranked = Path(_value(argv, "--ranked-output"))
    rows = [json.loads(line) for line in ranked.read_text().splitlines()]
    rows[0]["campaign_audit"].update({
        "canonical_digest": digest or rows[0]["campaign_audit"]["canonical_digest"],
        "certificate": {
            "attempted": True,
            "certificate_exact": True,
            "certificate_passed": True,
            "verification_attempted": True,
            "verification_passed": True,
            "certificate_sha256": certificate_sha256,
        },
    })
    ranked.write_text(
        "".join(json.dumps(row) + "\n" for row in rows),
        encoding="utf-8",
    )


def test_parser_config_and_backend_argv_are_strict_and_bounded(tmp_path: Path) -> None:
    parser = cli.build_parser()
    for command in ("run", "start", "status", "cancel", "_worker"):
        assert command in parser._subparsers._group_actions[0].choices
    cancel = parser.parse_args(["cancel", "--run-id", "r"])
    assert cancel.grace_seconds == 180.0

    config = cli.DiscoveryConfig(
        cpu_list=tuple(range(12, 31)) + tuple(range(44, 63)),
    ).validate()
    assert len(config.cpu_list or ()) == 38
    paths = _paths(tmp_path)
    argv = cli.build_audit_argv(
        python_executable="/usr/bin/python3",
        paths=paths,
        config=config,
        batch_index=0,
        count=100,
    )
    assert _value(argv, "--target-mode") == "scalar-fom-strict-v1"
    assert _value(argv, "--candidate-workers") == "6"
    assert _value(argv, "--solver-workers") == "4"
    assert _value(argv, "--max-total-workers") == "24"
    assert _value(argv, "--certificate-workers") == "2"
    assert _value(argv, "--certificate-solver-workers") == "6"
    assert _value(argv, "--hard-wall-termination-grace") == "180.0"
    assert "--resume" in argv and "--certify" in argv


def test_progressive_100_then_400_stops_on_proof_even_exit_two(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 900)
    calls: list[list[str]] = []

    def fake_run(argv: list[str], **kwargs: object) -> SimpleNamespace:
        assert kwargs == {"cwd": paths.repo, "shell": False, "check": False}
        calls.append(argv)
        ranked = Path(_value(argv, "--ranked-output"))
        ranked.parent.mkdir(parents=True, exist_ok=True)
        if len(calls) == 1:
            _write_complete_no_win(argv)
            return SimpleNamespace(returncode=0)
        _write_complete_win(argv)
        return SimpleNamespace(returncode=2)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=fake_run,
    )
    assert result["status"] == "STRICT_THRESHOLD_PROVEN"
    assert result["next_row"] == 500
    assert [batch["rows"] for batch in result["batches"]] == [100, 400]
    assert [_value(call, "--top") for call in calls] == ["100", "400"]
    assert len(result["wins"]) == 1
    assert result["wins"][0]["status"] == "STRICT_THRESHOLD_PROVEN"
    assert result["wins"][0]["publication_certificate"] is False
    assert result["wins"][0]["pipeline_promotion"] is False
    cli.validate_progress(json.loads(paths.progress.read_text()))


def test_failed_batch_does_not_advance_and_reuses_exact_input(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 5)

    failed = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=lambda *args, **kwargs: SimpleNamespace(returncode=1),
    )
    assert failed["status"] == "FAILED"
    assert failed["next_row"] == 0
    assert failed["batches"] == []
    batch_input = paths.batches / "batch-0000" / "input.jsonl"
    before = (batch_input.stat().st_ino, batch_input.stat().st_mtime_ns)

    def succeed(argv: list[str], **_: object) -> SimpleNamespace:
        _write_complete_no_win(argv)
        return SimpleNamespace(returncode=0)

    resumed = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=succeed,
    )
    after = (batch_input.stat().st_ino, batch_input.stat().st_mtime_ns)
    assert before == after
    assert resumed["status"] == "EXHAUSTED"
    assert resumed["next_row"] == 5
    assert [batch["batch_index"] for batch in resumed["batches"]] == [0]



def test_complete_unresolved_exit_two_is_deferred_and_widens(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 2)

    def unresolved(argv: list[str], **_: object) -> SimpleNamespace:
        _write_complete_no_win(
            argv, statuses=["REJECTED", "UNRESOLVED"],
        )
        return SimpleNamespace(returncode=2)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=unresolved,
    )
    assert result["status"] == "INCOMPLETE"
    assert result["next_row"] == 2
    assert result["batches"][0]["disposition"] == "DEFERRED"
    assert result["batches"][0]["status_counts"] == {
        "REJECTED": 1,
        "UNRESOLVED": 1,
    }


    ranked = paths.root / "all-rejected.jsonl"
    summary = paths.root / "all-rejected-summary.json"
    ranked.write_text(json.dumps({
        "campaign_selected": True,
        "campaign_audit": {
            "canonical_digest": "a" * 64,
            "status": "REJECTED",
        },
    }) + "\n", encoding="utf-8")
    summary.write_text(json.dumps({
        "target_mode": cli.TARGET_MODE,
        "selected_candidates": 1,
        "top": 1,
        "canonical_duplicates_skipped": 0,
        "known_codes_skipped": 0,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "structural_unresolved_candidates": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
        "certificate_operational_errors": 0,
    }), encoding="utf-8")
    complete, has_unresolved, counts = cli._complete_unresolved_batch(
        ranked,
        summary,
        expected_rows=1,
    )
    assert complete is True
    assert has_unresolved is False
    assert counts == {"REJECTED": 1}

def test_progress_and_source_tampering_fail_closed(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 1)
    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=lambda *args, **kwargs: SimpleNamespace(returncode=1),
    )
    result["next_row"] = 99
    paths.progress.write_text(json.dumps(result), encoding="utf-8")
    with pytest.raises(ValueError, match="progress seal"):
        cli._load_progress(paths.progress)


def test_capacity_uses_original_affinity_before_applying_selected(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 1)
    config_path = tmp_path / "config.json"
    config_path.write_text(json.dumps({"discovery": cli.DiscoveryConfig().as_dict()}))
    args = Namespace(
        config=config_path,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        python_executable="python",
        cpu_list=None,
        nice=None,
        run_id="run",
    )
    order: list[object] = []

    class Lease:
        def release(self) -> None:
            order.append("release")

    class Heartbeat:
        def __init__(self, *args: object) -> None:
            pass

        def start(self) -> None:
            order.append("heartbeat-start")

        def stop(self) -> None:
            order.append("heartbeat-stop")

    control = SimpleNamespace(
        _acquire_lock=lambda path: 91,
        _capacity_lease=lambda policy, affinity: (
            order.append(("lease", tuple(affinity))) or Lease()
        ),
        ResourcePolicy=lambda **kwargs: SimpleNamespace(**kwargs),
        _proc_identity=lambda pid: {
            "pid": pid,
            "proc_starttime": 1,
            "pgid": pid,
            "session_id": pid,
            "uid": 0,
            "cmdline_sha256": "b" * 64,
        },
        read_process_record=lambda path: None,
        write_process_record=lambda path, value: value,
        _update_record=lambda *args, **kwargs: True,
        _Heartbeat=Heartbeat,
        utc_now=lambda: "now",
        PROCESS_SCHEMA_VERSION=1,
    )
    monkeypatch.setattr(cli, "_install_control_namespace", lambda: control)
    monkeypatch.setattr(cli, "_select_cpus", lambda config: (tuple(range(64)), tuple(range(24))))
    monkeypatch.setattr(cli, "_apply_resources", lambda config, cpus: order.append(("apply", tuple(cpus))))
    monkeypatch.setattr(cli, "run_discovery", lambda **kwargs: {"status": "EXHAUSTED"})
    monkeypatch.setattr(cli.os, "close", lambda fd: None)

    result = cli._execute_worker(args, paths)
    assert result["status"] == "EXHAUSTED"
    lease_index = order.index(("lease", tuple(range(64))))
    apply_index = order.index(("apply", tuple(range(24))))
    assert lease_index < apply_index
    assert "heartbeat-start" in order and "heartbeat-stop" in order


def test_start_uses_list_argv_shell_false_and_isolated_session(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 1)
    config_path = tmp_path / "config.json"
    config_path.write_text(json.dumps({"discovery": cli.DiscoveryConfig().as_dict()}))
    args = Namespace(
        repo_dir=paths.repo,
        run_id="run",
        ranked_input=source,
        portfolio_manifest=_portfolio_manifest(paths, source),
        config=config_path,
        python_executable="/usr/bin/python3",
        cpu_list=None,
        nice=None,
    )
    captured: dict[str, object] = {}

    class FakeProcess:
        pid = 4242

        def poll(self) -> None:
            return None

        def terminate(self) -> None:
            pass

        def wait(self, timeout: float) -> int:
            return 0

        def kill(self) -> None:
            pass

    def fake_popen(argv: list[str], **kwargs: object) -> FakeProcess:
        captured.update(argv=argv, kwargs=kwargs)
        return FakeProcess()

    control = cli._install_control_namespace()
    monkeypatch.setattr(control, "_proc_identity", lambda pid: {
        "pid": pid,
        "proc_starttime": 7,
        "pgid": pid,
        "session_id": pid,
        "uid": 0,
        "cmdline_sha256": "c" * 64,
    })
    monkeypatch.setattr(cli.subprocess, "Popen", fake_popen)
    monkeypatch.setattr(cli.os, "write", lambda fd, data: len(data))
    record = cli.start_background(args, paths)
    argv = captured["argv"]
    kwargs = captured["kwargs"]
    assert isinstance(argv, list)
    assert argv[1:4] == ["-m", "humanize.strict_discovery_cli", "_worker"]
    assert kwargs["shell"] is False
    assert kwargs["start_new_session"] is True
    assert record["kind"] == cli.PROCESS_KIND


def test_module_has_no_top_level_scientific_import() -> None:
    tree = ast.parse(Path(cli.__file__).read_text(encoding="utf-8"))
    imported: set[str] = set()
    for node in tree.body:
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module)
    assert "numpy" not in imported
    assert "evaluation.distance_sat" not in imported
    assert "scripts.audit_candidate_pool" not in imported


def test_overlap_is_skipped_and_second_batch_is_backfilled(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 510)
    manifest_path = _portfolio_manifest(paths, source)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    blocked = [
        manifest["items"][index]["canonical_digest"]
        for index in (100, 101, 102)
    ]
    checks = 0
    calls = 0

    def live_check(*args: object, **kwargs: object) -> dict[str, object]:
        nonlocal checks
        checks += 1
        requested = set(kwargs["candidate_digests"])
        owned = set(blocked) if checks >= 4 else set()
        overlap = sorted(requested.intersection(owned))
        return {
            "overlap": bool(overlap),
            "blocked_digests": overlap,
            "check_scope": "test",
        }

    def backend(argv: list[str], **_: object) -> SimpleNamespace:
        nonlocal calls
        calls += 1
        if calls == 1:
            _write_complete_no_win(argv)
            return SimpleNamespace(returncode=0)
        _write_complete_win(argv, certificate_sha256="b" * 64)
        return SimpleNamespace(returncode=2)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=manifest_path,
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=backend,
        live_source_validator=live_check,
    )
    assert result["status"] == "STRICT_THRESHOLD_PROVEN"
    assert result["next_row"] == 503
    second = result["batches"][1]
    assert second["manifest_start_row"] == 100
    assert second["manifest_next_row"] == 503
    assert second["selected_portfolio_ranks"][0] == 104
    assert second["selected_portfolio_ranks"][-1] == 503
    assert second["rows"] == 400
    assert second["skipped_foreground_owned_count"] == 3
    assert second["skipped_foreground_owned_digests"] == blocked
    assert second["skipped_foreground_owned_sha256"] == cli._sha256(blocked)


def test_failed_active_batch_replays_with_live_refencing(
    tmp_path: Path,
) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 5)
    manifest_path = _portfolio_manifest(paths, source)
    checks = 0

    def live_check(*args: object, **kwargs: object) -> dict[str, object]:
        nonlocal checks
        checks += 1
        return {"overlap": False, "blocked_digests": [], "check_scope": "test"}

    failed = cli.run_discovery(
        paths=paths,
        portfolio_manifest=manifest_path,
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=lambda *args, **kwargs: SimpleNamespace(returncode=1),
        live_source_validator=live_check,
    )
    active = failed["active_batch"]
    batch_input = Path(active["input_path"])
    identity = (batch_input.stat().st_ino, active["input_sha256"])

    def succeed(argv: list[str], **_: object) -> SimpleNamespace:
        _write_complete_no_win(argv)
        return SimpleNamespace(returncode=0)

    resumed = cli.run_discovery(
        paths=paths,
        portfolio_manifest=manifest_path,
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=succeed,
        live_source_validator=live_check,
    )
    completed = resumed["batches"][0]
    assert checks == 5
    assert identity == (batch_input.stat().st_ino, completed["input_sha256"])
    for field in (
        "selected_source_rows",
        "selected_portfolio_ranks",
        "selected_digests",
        "argv",
        "manifest_start_row",
        "manifest_next_row",
    ):
        assert completed[field] == active[field]


def test_partial_exit_zero_fails_without_advancing(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 2)

    def partial(argv: list[str], **_: object) -> SimpleNamespace:
        ranked = Path(_value(argv, "--ranked-output"))
        summary = Path(_value(argv, "--summary-output"))
        ranked.write_text(json.dumps({
            "campaign_selected": True,
            "campaign_audit": {"status": "REJECTED"},
        }) + "\n", encoding="utf-8")
        summary.write_text(json.dumps({
            "target_mode": cli.TARGET_MODE,
            "selected_candidates": 1,
            "top": 2,
            "canonical_duplicates_skipped": 0,
            "known_codes_skipped": 0,
            "unsupported_candidates_skipped": 0,
            "canonicalization_errors": 0,
            "structural_unresolved_candidates": 0,
            "unscanned_eligible_candidates": 0,
            "selection_exhausted": True,
            "certificate_operational_errors": 0,
        }), encoding="utf-8")
        return SimpleNamespace(returncode=0)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=partial,
    )
    assert result["status"] == "FAILED"
    assert result["next_row"] == 0
    assert result["batches"] == []


def test_uncertified_threshold_status_never_stops_as_win(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 1)

    def uncertified(argv: list[str], **_: object) -> SimpleNamespace:
        ranked = Path(_value(argv, "--ranked-output"))
        ranked.write_text(json.dumps({
            "campaign_selected": True,
            "campaign_audit": {
                "status": "THRESHOLD_PROVEN",
                "certificate": {
                    "attempted": True,
                    "certificate_exact": True,
                    "certificate_passed": False,
                    "verification_attempted": True,
                    "verification_passed": False,
                },
            },
        }) + "\n", encoding="utf-8")
        return SimpleNamespace(returncode=2)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=uncertified,
    )
    assert result["status"] == "FAILED"
    assert result["wins"] == []
    assert result["next_row"] == 0


def test_live_source_reports_committed_and_pending_as_blocked(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 3)
    manifest_path = _portfolio_manifest(paths, source)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    digests = [item["canonical_digest"] for item in manifest["items"]]
    import evaluation.selection_ledger as selection_ledger

    monkeypatch.setattr(
        selection_ledger,
        "validate_selection_ledger",
        lambda *args, **kwargs: {
            "snapshot_identity_sha256": "e" * 64,
            "generation": 0,
            "cursor": 7,
            "committed_digests": [digests[0]],
            "pending": {
                "page_sha256": "f" * 64,
                "page": {"selected_digests": [digests[1]]},
            },
            "progress_sha256": "1" * 64,
            "last_ack_sha256": "2" * 64,
        },
    )
    result = _REAL_VALIDATE_LIVE(
        manifest,
        paths=paths,
        candidate_digests=digests,
    )
    assert result["blocked_digests"] == digests[:2]
    assert result["overlap"] is True
    assert result["ledger_cursor"] == 7


def test_production_config_seals_resource_policy() -> None:
    config_path = (
        Path(cli.__file__).resolve().parents[1]
        / "configs"
        / "stage2_strict_discovery_v1.json"
    )
    config = cli.DiscoveryConfig.from_json(config_path)
    assert config.nice == 10
    assert config.cpu_list == (
        tuple(range(12, 31)) + tuple(range(44, 63))
    )
    assert len(config.cpu_list) == 38


def test_known_registry_skip_is_only_accepted_when_exactly_accounted(
    tmp_path: Path,
) -> None:
    paths = _paths(tmp_path)
    ranked = paths.root / "known-skip-ranked.jsonl"
    summary = paths.root / "known-skip-summary.json"
    ranked.write_text(json.dumps({
        "campaign_selected": True,
        "campaign_audit": {
            "canonical_digest": "a" * 64,
            "status": "REJECTED",
        },
    }) + "\n", encoding="utf-8")
    base = {
        "target_mode": cli.TARGET_MODE,
        "top": 2,
        "selected_candidates": 1,
        "canonical_duplicates_skipped": 0,
        "known_codes_skipped": 1,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "structural_unresolved_candidates": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
        "certificate_operational_errors": 0,
    }
    summary.write_text(json.dumps(base), encoding="utf-8")
    complete, unresolved, counts = cli._complete_unresolved_batch(
        ranked,
        summary,
        expected_rows=2,
    )
    assert complete is True
    assert unresolved is False
    assert counts == {"REJECTED": 1}

    summary.write_text(
        json.dumps({**base, "known_codes_skipped": 0}),
        encoding="utf-8",
    )
    assert cli._complete_unresolved_batch(
        ranked,
        summary,
        expected_rows=2,
    )[0] is False


def test_portfolio_producer_and_authority_tampering_fail_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 1)
    manifest_path = _portfolio_manifest(paths, source)
    original = json.loads(manifest_path.read_text(encoding="utf-8"))

    changed_producer = json.loads(json.dumps(original))
    changed_producer["producer"]["source_sha256"] = "0" * 64
    changed_producer.pop("portfolio_sha256")
    changed_producer["portfolio_sha256"] = cli._sha256(changed_producer)
    manifest_path.write_text(json.dumps(changed_producer), encoding="utf-8")
    with pytest.raises(ValueError, match="seal/schema"):
        cli.load_portfolio_manifest(manifest_path, paths=paths)

    changed_authority = json.loads(json.dumps(original))
    changed_authority["pipeline_promotion"] = True
    changed_authority.pop("portfolio_sha256")
    changed_authority["portfolio_sha256"] = cli._sha256(changed_authority)
    manifest_path.write_text(json.dumps(changed_authority), encoding="utf-8")
    with pytest.raises(ValueError, match="seal/schema"):
        cli.load_portfolio_manifest(manifest_path, paths=paths)

    manifest_path.write_text(json.dumps(original), encoding="utf-8")
    monkeypatch.setattr(cli, "_CLI_SOURCE_SHA256", "0" * 64)
    with pytest.raises(cli.StrictDiscoveryError, match="CLI source changed"):
        cli.load_portfolio_manifest(manifest_path, paths=paths)



def test_prelaunch_overlap_fails_without_invoking_backend(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 2)
    manifest_path = _portfolio_manifest(paths, source)
    manifest = json.loads(manifest_path.read_text())
    blocked = manifest["items"][0]["canonical_digest"]
    checks = 0
    backend_called = False

    def live_check(*args: object, **kwargs: object) -> dict[str, object]:
        nonlocal checks
        checks += 1
        requested = set(kwargs["candidate_digests"])
        overlap = [blocked] if checks == 2 and blocked in requested else []
        return {
            "overlap": bool(overlap),
            "blocked_digests": overlap,
            "check_scope": "test",
        }

    def backend(*args: object, **kwargs: object) -> SimpleNamespace:
        nonlocal backend_called
        backend_called = True
        return SimpleNamespace(returncode=0)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=manifest_path,
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=backend,
        live_source_validator=live_check,
    )
    assert result["status"] == "FAILED"
    assert result["next_row"] == 0
    assert result["batches"] == []
    assert result["active_batch"]["ownership_conflict"]["phase"] == "pre-launch"
    assert backend_called is False


def test_postrun_overlap_fails_without_committing_batch(tmp_path: Path) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 2)
    manifest_path = _portfolio_manifest(paths, source)
    manifest = json.loads(manifest_path.read_text())
    blocked = manifest["items"][0]["canonical_digest"]
    checks = 0

    def live_check(*args: object, **kwargs: object) -> dict[str, object]:
        nonlocal checks
        checks += 1
        requested = set(kwargs["candidate_digests"])
        overlap = [blocked] if checks == 3 and blocked in requested else []
        return {
            "overlap": bool(overlap),
            "blocked_digests": overlap,
            "check_scope": "test",
        }

    def backend(argv: list[str], **_: object) -> SimpleNamespace:
        _write_complete_no_win(argv)
        return SimpleNamespace(returncode=0)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=manifest_path,
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=backend,
        live_source_validator=live_check,
    )
    assert result["status"] == "FAILED"
    assert result["next_row"] == 0
    assert result["batches"] == []
    conflict = result["active_batch"]["ownership_conflict"]
    assert conflict["phase"] == "post-run"
    assert conflict["blocked_digests"] == [blocked]

@pytest.mark.parametrize(
    "tamper",
    ["nonselected", "digest", "summary", "missing_ledger", "ledger_digest"],
)
def test_runtime_rejects_proof_before_progress_when_batch_evidence_diverges(
    tmp_path: Path,
    tamper: str,
) -> None:
    paths = _paths(tmp_path)
    source = paths.run_root / "ranked-input.jsonl"
    _jsonl(source, 1)

    def backend(argv: list[str], **_: object) -> SimpleNamespace:
        _write_complete_win(argv)
        ranked = Path(_value(argv, "--ranked-output"))
        summary = Path(_value(argv, "--summary-output"))
        ledger = Path(_value(argv, "--selection-ledger"))
        if tamper in {"nonselected", "digest"}:
            rows = [json.loads(line) for line in ranked.read_text().splitlines()]
            if tamper == "nonselected":
                rows[0]["campaign_selected"] = False
            else:
                rows[0]["campaign_audit"]["canonical_digest"] = "f" * 64
            ranked.write_text(
                "".join(json.dumps(row) + "\n" for row in rows),
                encoding="utf-8",
            )
        elif tamper == "summary":
            value = json.loads(summary.read_text())
            value["selected_candidates"] = 0
            summary.write_text(json.dumps(value) + "\n", encoding="utf-8")
        elif tamper == "missing_ledger":
            ledger.unlink()
        else:
            value = json.loads(ledger.read_text())
            value["committed_digests"] = ["f" * 64]
            unsigned = dict(value)
            unsigned.pop("progress_sha256", None)
            value["progress_sha256"] = cli._sha256(unsigned)
            ledger.write_text(json.dumps(value) + "\n", encoding="utf-8")
        return SimpleNamespace(returncode=2)

    result = cli.run_discovery(
        paths=paths,
        portfolio_manifest=_portfolio_manifest(paths, source),
        ranked_input=source,
        config=cli.DiscoveryConfig(),
        run_command=backend,
    )
    assert result["status"] == "FAILED"
    assert result["wins"] == []
    assert result["next_row"] == 0
    assert result["batches"] == []
    assert result["active_batch"]["manifest_start_row"] == 0
