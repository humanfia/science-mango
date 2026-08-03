from __future__ import annotations

from pathlib import Path

import pytest

from evaluation.solver_budget import (
    CpuBudget,
    ProcessRecord,
    SolverBudgetError,
    SolverBudgetUnavailable,
    acquire_solver_budget,
    detect_cpu_budget,
    estimate_unmanaged_qcode_usage,
)


def _budget(capacity: int) -> CpuBudget:
    return CpuBudget(
        capacity=capacity,
        affinity_cpus=64,
        cpuset_cpus=64,
        quota_cores=float(capacity),
        cgroup_path="/test",
        limiting_source="cgroup_cpu_quota",
        inspected_files=(),
    )


def _process(
    pid: int,
    *,
    ppid: int = 1,
    pgid: int | None = None,
    comm: str = "python",
    argv: tuple[str, ...] = (),
    state: str = "S",
) -> ProcessRecord:
    return ProcessRecord(
        pid=pid,
        ppid=ppid,
        pgid=pid if pgid is None else pgid,
        state=state,
        comm=comm,
        argv=argv,
        cwd="/workspace/qcode-discovery",
    )


def test_detect_cpu_budget_uses_nested_quota_cpuset_and_affinity(
    tmp_path: Path,
) -> None:
    cgroup_root = tmp_path / "cgroup"
    leaf = cgroup_root / "campaign" / "worker"
    leaf.mkdir(parents=True)
    (cgroup_root / "cpu.max").write_text("max 100000\n")
    (cgroup_root / "cpuset.cpus.effective").write_text("0-63\n")
    (cgroup_root / "campaign" / "cpu.max").write_text("1600000 100000\n")
    (leaf / "cpu.max").write_text("max 100000\n")
    (leaf / "cpuset.cpus.effective").write_text("0-31\n")
    membership = tmp_path / "self.cgroup"
    membership.write_text("0::/campaign/worker\n")

    budget = detect_cpu_budget(
        cgroup_root=cgroup_root,
        proc_self_cgroup=membership,
        affinity=range(48),
    )

    assert budget.capacity == 16
    assert budget.quota_cores == 16.0
    assert budget.cpuset_cpus == 32
    assert budget.affinity_cpus == 48
    assert budget.limiting_source == "cgroup_cpu_quota"


def test_detect_cpu_budget_fails_closed_on_malformed_quota(
    tmp_path: Path,
) -> None:
    cgroup_root = tmp_path / "cgroup"
    cgroup_root.mkdir()
    (cgroup_root / "cpu.max").write_text("broken\n")
    membership = tmp_path / "self.cgroup"
    membership.write_text("0::/\n")

    with pytest.raises(SolverBudgetError, match="cannot parse"):
        detect_cpu_budget(
            cgroup_root=cgroup_root,
            proc_self_cgroup=membership,
            affinity=range(8),
        )


@pytest.mark.parametrize("requested", [True, 0, -1, 1.5, "2"])
def test_global_slots_reject_non_positive_or_non_integer_requests(
    tmp_path: Path,
    requested: object,
) -> None:
    with pytest.raises(ValueError, match="positive integer"):
        acquire_solver_budget(
            requested,  # type: ignore[arg-type]
            cpu_budget=_budget(4),
            lock_root=tmp_path / "locks",
            processes=(),
            current_pid=999,
        )


def test_unmanaged_scan_counts_campaign_peak_and_distqldpc_groups_only() -> None:
    audit_argv = (
        "python", "scripts/audit_direction_pool.py", "ranked.jsonl",
        "--candidate-workers", "2", "--direction-workers", "6",
        "--certify", "--certificate-workers", "2",
        "--certificate-solver-workers", "3",
    )
    processes = [
        _process(100, argv=audit_argv),
        _process(
            101,
            ppid=100,
            pgid=100,
            argv=("python", "-c", "multiprocessing.spawn_main"),
        ),
        # Wrapper and worker share a PGID and consume one CPU slot.
        _process(
            200,
            pgid=200,
            comm="distqldpc",
            argv=("/tools/DistQLDPC/bin/distqldpc", "matrix-a"),
        ),
        _process(
            201,
            ppid=200,
            pgid=200,
            comm="distqldpc",
            argv=("/tools/DistQLDPC/bin/distqldpc", "matrix-a"),
        ),
        _process(
            300,
            comm="cadical",
            argv=("/tools/cadical", "/tmp/ipho-archon/problem.cnf"),
        ),
        _process(
            400,
            comm="cadical",
            argv=("/tools/cadical", "/tmp/qcode-proof-tools/proof.cnf"),
        ),
    ]

    usage = estimate_unmanaged_qcode_usage(processes, current_pid=999)

    assert usage.workers == 14
    assert usage.campaigns == ({
        "pid": 100,
        "entrypoint": "audit_direction_pool",
        "reserved_workers": 12,
        "cwd": "/workspace/qcode-discovery",
    },)
    assert {item["solver"] for item in usage.external_solvers} == {
        "distqldpc", "cadical",
    }


def test_global_slots_coordinate_independent_leases(tmp_path: Path) -> None:
    budget = _budget(4)
    first = acquire_solver_budget(
        2,
        cpu_budget=budget,
        lock_root=tmp_path / "locks",
        processes=(),
        current_pid=999,
    )
    try:
        with pytest.raises(SolverBudgetUnavailable, match="requested=3"):
            acquire_solver_budget(
                3,
                cpu_budget=budget,
                lock_root=tmp_path / "locks",
                processes=(),
                current_pid=999,
            )
        second = acquire_solver_budget(
            2,
            cpu_budget=budget,
            lock_root=tmp_path / "locks",
            processes=(),
            current_pid=999,
        )
        assert second.cooperative_slots_before == 2
        second.release()
    finally:
        first.release()

    replacement = acquire_solver_budget(
        4,
        cpu_budget=budget,
        lock_root=tmp_path / "locks",
        processes=(),
        current_pid=999,
    )
    replacement.release()


def test_unmanaged_qcode_processes_reduce_available_capacity(
    tmp_path: Path,
) -> None:
    processes = (
        _process(
            100,
            argv=(
                "python", "scripts/audit_direction_pool.py", "input.jsonl",
                "--candidate-workers", "1", "--direction-workers", "4",
            ),
        ),
    )
    with pytest.raises(
        SolverBudgetUnavailable,
        match="unmanaged_qcode_workers=4",
    ):
        acquire_solver_budget(
            1,
            cpu_budget=_budget(4),
            lock_root=tmp_path / "locks",
            processes=processes,
            current_pid=999,
        )


def test_cooperative_owner_descendants_are_not_double_counted(
    tmp_path: Path,
) -> None:
    # The first lease metadata names this process.  Its synthetic child audit
    # must be excluded from the unmanaged-process estimate by the next lease.
    first = acquire_solver_budget(
        1,
        cpu_budget=_budget(3),
        lock_root=tmp_path / "locks",
        processes=(),
        current_pid=999,
    )
    try:
        processes = (
            _process(
                100,
                ppid=__import__("os").getpid(),
                argv=(
                    "python", "scripts/audit_direction_pool.py", "input",
                    "--candidate-workers", "1", "--direction-workers", "8",
                ),
            ),
        )
        second = acquire_solver_budget(
            2,
            cpu_budget=_budget(3),
            lock_root=tmp_path / "locks",
            processes=processes,
            current_pid=999,
        )
        assert second.unmanaged_usage.workers == 0
        second.release()
    finally:
        first.release()
