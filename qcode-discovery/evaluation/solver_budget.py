"""Host-wide solver-worker admission control for qcode proof campaigns.

The per-command ``max_total_workers`` checks are necessary but not sufficient:
two independently launched campaigns can each obey their local limit while
oversubscribing the same cgroup.  This module provides a small, fail-closed
advisory semaphore.  Cooperating qcode processes reserve one ``flock`` slot per
solver worker for their complete lifetime.  A startup scan also accounts for
older qcode proof processes which predate the semaphore.

The lock namespace is scoped to the current cgroup and uid.  It deliberately
does not inspect, signal, or otherwise manage unrelated workloads (including
IPhO and Archon jobs).
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import math
import os
import stat
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Mapping, Sequence


class SolverBudgetError(RuntimeError):
    """Base class for global solver-budget failures."""


class SolverBudgetUnavailable(SolverBudgetError):
    """The requested solver slots do not fit in the effective CPU budget."""


@dataclass(frozen=True)
class CpuBudget:
    """Effective integral solver capacity for the current process."""

    capacity: int
    affinity_cpus: int
    cpuset_cpus: int | None
    quota_cores: float | None
    cgroup_path: str
    limiting_source: str
    inspected_files: tuple[str, ...]

    def as_dict(self) -> dict[str, object]:
        return {
            "capacity": self.capacity,
            "affinity_cpus": self.affinity_cpus,
            "cpuset_cpus": self.cpuset_cpus,
            "quota_cores": self.quota_cores,
            "cgroup_path": self.cgroup_path,
            "limiting_source": self.limiting_source,
            "inspected_files": list(self.inspected_files),
        }


@dataclass(frozen=True)
class ProcessRecord:
    pid: int
    ppid: int
    pgid: int
    state: str
    comm: str
    argv: tuple[str, ...]
    cwd: str | None = None


@dataclass(frozen=True)
class UnmanagedUsage:
    workers: int
    campaigns: tuple[Mapping[str, object], ...]
    external_solvers: tuple[Mapping[str, object], ...]

    def as_dict(self) -> dict[str, object]:
        return {
            "workers": self.workers,
            "campaigns": [dict(value) for value in self.campaigns],
            "external_solvers": [
                dict(value) for value in self.external_solvers
            ],
        }


def _parse_cpu_list(value: str) -> int:
    cpus: set[int] = set()
    for raw_part in value.strip().split(","):
        part = raw_part.strip()
        if not part:
            continue
        if "-" in part:
            lower_text, upper_text = part.split("-", 1)
            lower = int(lower_text)
            upper = int(upper_text)
            if lower < 0 or upper < lower:
                raise ValueError("invalid cpuset range")
            cpus.update(range(lower, upper + 1))
        else:
            cpu = int(part)
            if cpu < 0:
                raise ValueError("invalid cpuset CPU")
            cpus.add(cpu)
    return len(cpus)


def _read_self_cgroup(proc_self_cgroup: Path) -> tuple[str, bool]:
    try:
        lines = proc_self_cgroup.read_text().splitlines()
    except OSError as exc:
        raise SolverBudgetError(
            f"cannot read cgroup membership {proc_self_cgroup}: {exc}"
        ) from exc
    for line in lines:
        fields = line.split(":", 2)
        if len(fields) == 3 and fields[0] == "0" and fields[1] == "":
            return fields[2] or "/", True
    for line in lines:
        fields = line.split(":", 2)
        if len(fields) != 3:
            continue
        controllers = set(fields[1].split(","))
        if "cpu" in controllers or "cpuacct" in controllers:
            return fields[2] or "/", False
    # A host without a CPU controller can still be bounded by affinity.
    return "/", (Path("/sys/fs/cgroup/cgroup.controllers").exists())


def _safe_cgroup_relative(path: str) -> Path:
    value = Path(path.lstrip("/"))
    if any(part == ".." for part in value.parts):
        raise SolverBudgetError(f"unsafe cgroup path: {path!r}")
    return value


def _ancestry(current: Path, root: Path) -> Iterable[Path]:
    try:
        current.relative_to(root)
    except ValueError as exc:
        raise SolverBudgetError(
            f"cgroup path {current} escapes cgroup root {root}"
        ) from exc
    value = current
    while True:
        yield value
        if value == root:
            break
        value = value.parent


def detect_cpu_budget(
    *,
    cgroup_root: Path = Path("/sys/fs/cgroup"),
    proc_self_cgroup: Path = Path("/proc/self/cgroup"),
    affinity: Sequence[int] | None = None,
) -> CpuBudget:
    """Return the strictest integral capacity from quota/cpuset/affinity.

    All nested cgroup-v2 ``cpu.max`` files are considered because a parent can
    impose a tighter quota than the leaf.  Fractional quotas are rounded down
    to avoid admitting more whole single-threaded solvers than the allocation.
    A positive sub-CPU quota still admits one worker.
    """

    if affinity is None:
        try:
            affinity_values = os.sched_getaffinity(0)
        except (AttributeError, OSError):
            count = os.cpu_count()
            if not isinstance(count, int) or count < 1:
                raise SolverBudgetError("cannot determine CPU affinity")
            affinity_values = range(count)
    else:
        affinity_values = affinity
    affinity_count = len(set(int(cpu) for cpu in affinity_values))
    if affinity_count < 1:
        raise SolverBudgetError("CPU affinity is empty")

    cgroup_path, unified = _read_self_cgroup(proc_self_cgroup)
    relative = _safe_cgroup_relative(cgroup_path)
    inspected: list[str] = []
    quotas: list[float] = []
    cpusets: list[int] = []

    if unified:
        leaf = cgroup_root / relative
        for directory in _ancestry(leaf, cgroup_root):
            cpu_max = directory / "cpu.max"
            if cpu_max.exists():
                inspected.append(str(cpu_max))
                try:
                    fields = cpu_max.read_text().strip().split()
                    if len(fields) != 2:
                        raise ValueError("expected two fields")
                    if fields[0] != "max":
                        quota = int(fields[0])
                        period = int(fields[1])
                        if quota <= 0 or period <= 0:
                            raise ValueError("quota and period must be positive")
                        quotas.append(quota / period)
                except (OSError, ValueError) as exc:
                    raise SolverBudgetError(
                        f"cannot parse cgroup CPU quota {cpu_max}: {exc}"
                    ) from exc
            cpuset = directory / "cpuset.cpus.effective"
            if cpuset.exists():
                inspected.append(str(cpuset))
                try:
                    count = _parse_cpu_list(cpuset.read_text())
                except (OSError, ValueError) as exc:
                    raise SolverBudgetError(
                        f"cannot parse cgroup cpuset {cpuset}: {exc}"
                    ) from exc
                if count:
                    cpusets.append(count)
    else:
        candidates = (
            cgroup_root / "cpu" / relative,
            cgroup_root / relative,
        )
        leaf = next(
            (
                candidate for candidate in candidates
                if (candidate / "cpu.cfs_quota_us").exists()
            ),
            None,
        )
        if leaf is not None:
            quota_path = leaf / "cpu.cfs_quota_us"
            period_path = leaf / "cpu.cfs_period_us"
            inspected.extend((str(quota_path), str(period_path)))
            try:
                quota = int(quota_path.read_text().strip())
                period = int(period_path.read_text().strip())
            except (OSError, ValueError) as exc:
                raise SolverBudgetError(
                    f"cannot parse cgroup-v1 CPU quota: {exc}"
                ) from exc
            if quota > 0:
                if period <= 0:
                    raise SolverBudgetError("invalid cgroup-v1 CPU period")
                quotas.append(quota / period)

    quota_cores = min(quotas) if quotas else None
    cpuset_count = min(cpusets) if cpusets else None
    limits: list[tuple[str, int]] = [("sched_affinity", affinity_count)]
    if cpuset_count is not None:
        limits.append(("cgroup_cpuset", cpuset_count))
    if quota_cores is not None:
        limits.append((
            "cgroup_cpu_quota",
            max(1, math.floor(quota_cores + 1e-12)),
        ))
    limiting_source, capacity = min(limits, key=lambda item: item[1])
    return CpuBudget(
        capacity=capacity,
        affinity_cpus=affinity_count,
        cpuset_cpus=cpuset_count,
        quota_cores=quota_cores,
        cgroup_path=cgroup_path,
        limiting_source=limiting_source,
        inspected_files=tuple(inspected),
    )


def _read_processes(proc_root: Path = Path("/proc")) -> list[ProcessRecord]:
    records: list[ProcessRecord] = []
    try:
        entries = list(proc_root.iterdir())
    except OSError as exc:
        raise SolverBudgetError(f"cannot inspect process table: {exc}") from exc
    for entry in entries:
        if not entry.name.isdigit():
            continue
        pid = int(entry.name)
        try:
            # stat's command name may contain spaces and parentheses.  Split
            # only after its final closing parenthesis.
            raw_stat = (entry / "stat").read_text()
            right = raw_stat.rfind(")")
            if right < 0:
                continue
            prefix = raw_stat[: right + 1]
            suffix = raw_stat[right + 2 :].split()
            if len(suffix) < 3:
                continue
            comm = prefix[prefix.find("(") + 1 : -1]
            state = suffix[0]
            ppid = int(suffix[1])
            pgid = int(suffix[2])
            raw_cmdline = (entry / "cmdline").read_bytes()
            argv = tuple(
                part.decode(errors="replace")
                for part in raw_cmdline.split(b"\0") if part
            )
            try:
                cwd = os.readlink(entry / "cwd")
            except OSError:
                cwd = None
        except (OSError, ValueError):
            continue
        records.append(ProcessRecord(
            pid=pid,
            ppid=ppid,
            pgid=pgid,
            state=state,
            comm=comm,
            argv=argv,
            cwd=cwd,
        ))
    return records


def _option_int(argv: Sequence[str], name: str, default: int) -> int:
    try:
        index = argv.index(name)
    except ValueError:
        return default
    if index + 1 >= len(argv):
        return default
    try:
        value = int(argv[index + 1])
    except ValueError:
        return default
    return value if value > 0 else default


def _descendants(
    root_pid: int,
    children: Mapping[int, Sequence[int]],
) -> set[int]:
    found: set[int] = set()
    pending = list(children.get(root_pid, ()))
    while pending:
        pid = pending.pop()
        if pid in found:
            continue
        found.add(pid)
        pending.extend(children.get(pid, ()))
    return found


def estimate_unmanaged_qcode_usage(
    processes: Sequence[ProcessRecord],
    *,
    cooperative_owner_pids: Iterable[int] = (),
    current_pid: int | None = None,
) -> UnmanagedUsage:
    """Conservatively reserve workers used by pre-semaphore qcode runs.

    Matching is intentionally narrow: only qcode audit entry points and known
    proof-solver binaries are counted.  Generic Python, Java, Archon, IPhO and
    other user processes are ignored.
    """

    children: dict[int, list[int]] = {}
    for record in processes:
        children.setdefault(record.ppid, []).append(record.pid)
    excluded: set[int] = set()
    for owner in cooperative_owner_pids:
        excluded.add(owner)
        excluded.update(_descendants(owner, children))
    if current_pid is not None:
        excluded.add(current_pid)
        excluded.update(_descendants(current_pid, children))

    campaigns: list[Mapping[str, object]] = []
    covered: set[int] = set()
    for record in processes:
        if record.pid in excluded or record.state == "Z":
            continue
        command = " ".join(record.argv)
        entrypoint: str | None = None
        if "scripts/audit_direction_pool.py" in command:
            entrypoint = "audit_direction_pool"
            stage3 = (
                _option_int(record.argv, "--candidate-workers", 1)
                * _option_int(record.argv, "--direction-workers", 4)
            )
            certification = 0
            if "--certify" in record.argv:
                certification = (
                    _option_int(record.argv, "--certificate-workers", 1)
                    * _option_int(
                        record.argv, "--certificate-solver-workers", 1,
                    )
                )
            workers = max(stage3, certification)
        elif "scripts/audit_candidate_pool.py" in command:
            entrypoint = "audit_candidate_pool"
            workers = max(
                _option_int(record.argv, "--candidate-workers", 2)
                * _option_int(record.argv, "--solver-workers", 4),
                _option_int(record.argv, "--certificate-workers", 1)
                * _option_int(
                    record.argv, "--certificate-solver-workers", 1,
                ),
            )
        else:
            continue
        descendants = _descendants(record.pid, children)
        covered.add(record.pid)
        covered.update(descendants)
        campaigns.append({
            "pid": record.pid,
            "entrypoint": entrypoint,
            "reserved_workers": workers,
            "cwd": record.cwd,
        })

    # DistQLDPC commonly has one wrapper and one worker in the same process
    # group.  Count a PGID once.  Other known standalone proof solvers count
    # once per PID.  Restrict the match to exact executable/comm names so this
    # cannot absorb unrelated qcode-adjacent workloads.
    distqldpc_groups: dict[int, ProcessRecord] = {}
    standalone: list[ProcessRecord] = []
    known_standalone = {
        "cadical", "kissat", "cryptominisat5", "glucose", "minisat",
        "highs",
    }
    for record in processes:
        if (
            record.pid in excluded
            or record.pid in covered
            or record.state == "Z"
        ):
            continue
        executable = Path(record.argv[0]).name if record.argv else ""
        name = executable or record.comm
        if name == "distqldpc" or record.comm == "distqldpc":
            distqldpc_groups.setdefault(record.pgid, record)
        elif name in known_standalone or record.comm in known_standalone:
            command = " ".join(record.argv).lower()
            if (
                "qcode-discovery" in command
                or "qcode-proof-tools" in command
                or "/qcode-" in command
            ):
                standalone.append(record)

    external: list[Mapping[str, object]] = [
        {
            "solver": "distqldpc",
            "pid": record.pid,
            "pgid": pgid,
            "reserved_workers": 1,
        }
        for pgid, record in sorted(distqldpc_groups.items())
    ]
    external.extend({
        "solver": Path(record.argv[0]).name if record.argv else record.comm,
        "pid": record.pid,
        "pgid": record.pgid,
        "reserved_workers": 1,
    } for record in standalone)
    workers = sum(int(value["reserved_workers"]) for value in campaigns)
    workers += len(external)
    return UnmanagedUsage(
        workers=workers,
        campaigns=tuple(campaigns),
        external_solvers=tuple(external),
    )


def _default_lock_root(cgroup_path: str) -> Path:
    override = os.environ.get("QCODE_SOLVER_BUDGET_DIR")
    if override:
        path = Path(override)
        if not path.is_absolute():
            raise SolverBudgetError(
                "QCODE_SOLVER_BUDGET_DIR must be an absolute path"
            )
        return path
    identity = hashlib.sha256(cgroup_path.encode()).hexdigest()[:16]
    return Path(tempfile.gettempdir()) / (
        f"qcode-discovery-solver-budget-v1-{os.getuid()}-{identity}"
    )


def _prepare_lock_root(path: Path) -> None:
    path.mkdir(mode=0o700, parents=True, exist_ok=True)
    info = path.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid():
        raise SolverBudgetError(
            f"unsafe solver-budget directory ownership/type: {path}"
        )
    # Do not allow another uid to inject lock files or metadata.
    path.chmod(0o700)


def _open_lock(path: Path) -> int:
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        return os.open(path, flags, 0o600)
    except OSError as exc:
        raise SolverBudgetError(
            f"cannot open solver-budget lock {path}: {exc}"
        ) from exc


def _locked_owner_pid(fd: int) -> int | None:
    try:
        os.lseek(fd, 0, os.SEEK_SET)
        raw = os.read(fd, 65536)
        value = json.loads(raw.decode())
        pid = value.get("owner_pid") if isinstance(value, dict) else None
        return pid if isinstance(pid, int) and pid > 0 else None
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None


class SolverBudgetLease:
    """A set of process-lifetime global solver slots."""

    def __init__(
        self,
        *,
        fds: Sequence[int],
        paths: Sequence[Path],
        requested_slots: int,
        cpu_budget: CpuBudget,
        unmanaged_usage: UnmanagedUsage,
        cooperative_slots_before: int,
        lock_root: Path,
    ) -> None:
        self._fds = list(fds)
        self._paths = tuple(paths)
        self.requested_slots = requested_slots
        self.cpu_budget = cpu_budget
        self.unmanaged_usage = unmanaged_usage
        self.cooperative_slots_before = cooperative_slots_before
        self.lock_root = lock_root

    @property
    def released(self) -> bool:
        return not self._fds

    def as_dict(self) -> dict[str, object]:
        return {
            "enforced": True,
            "requested_slots": self.requested_slots,
            "cooperative_slots_before": self.cooperative_slots_before,
            "unmanaged_usage": self.unmanaged_usage.as_dict(),
            "cpu_budget": self.cpu_budget.as_dict(),
            "lock_root": str(self.lock_root),
            "slot_files": [path.name for path in self._paths],
        }

    def release(self) -> None:
        while self._fds:
            fd = self._fds.pop()
            try:
                fcntl.flock(fd, fcntl.LOCK_UN)
            finally:
                os.close(fd)

    def __enter__(self) -> "SolverBudgetLease":
        return self

    def __exit__(self, *_: object) -> None:
        self.release()

    def __del__(self) -> None:
        try:
            self.release()
        except Exception:
            pass


def acquire_solver_budget(
    requested_slots: int,
    *,
    cpu_budget: CpuBudget | None = None,
    lock_root: Path | None = None,
    processes: Sequence[ProcessRecord] | None = None,
    proc_root: Path = Path("/proc"),
    current_pid: int | None = None,
) -> SolverBudgetLease:
    """Atomically reserve ``requested_slots`` or raise with diagnostics."""

    if (
        isinstance(requested_slots, bool)
        or not isinstance(requested_slots, int)
        or requested_slots < 1
    ):
        raise ValueError("requested solver slots must be a positive integer")
    budget = cpu_budget or detect_cpu_budget()
    if budget.capacity < 1:
        raise SolverBudgetError("effective CPU capacity is zero")
    root = lock_root or _default_lock_root(budget.cgroup_path)
    _prepare_lock_root(root)
    allocator_fd = _open_lock(root / "allocator.lock")
    slot_fds: list[int] = []
    slot_paths: list[Path] = []
    free: list[tuple[int, Path]] = []
    try:
        fcntl.flock(allocator_fd, fcntl.LOCK_EX)
        existing_indices = []
        for path in root.glob("slot-*.lock"):
            try:
                existing_indices.append(int(path.stem.split("-", 1)[1]))
            except (ValueError, IndexError):
                continue
        slot_count = max(
            budget.capacity,
            max(existing_indices, default=-1) + 1,
        )
        cooperative_busy = 0
        cooperative_owners: set[int] = set()
        for index in range(slot_count):
            path = root / f"slot-{index:04d}.lock"
            fd = _open_lock(path)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                cooperative_busy += 1
                owner = _locked_owner_pid(fd)
                if owner is not None:
                    cooperative_owners.add(owner)
                os.close(fd)
            else:
                free.append((fd, path))

        snapshot = (
            list(processes)
            if processes is not None
            else _read_processes(proc_root)
        )
        unmanaged = estimate_unmanaged_qcode_usage(
            snapshot,
            cooperative_owner_pids=cooperative_owners,
            current_pid=os.getpid() if current_pid is None else current_pid,
        )
        available = budget.capacity - cooperative_busy - unmanaged.workers
        if requested_slots > available:
            blockers = [
                f"{value['entrypoint']}:pid={value['pid']}"
                for value in unmanaged.campaigns
            ]
            blockers.extend(
                f"{value['solver']}:pid={value['pid']}"
                for value in unmanaged.external_solvers
            )
            blocker_text = ",".join(blockers[:8]) or "cooperative leases"
            raise SolverBudgetUnavailable(
                "global qcode solver budget unavailable: "
                f"requested={requested_slots}, capacity={budget.capacity}, "
                f"cooperative_busy={cooperative_busy}, "
                f"unmanaged_qcode_workers={unmanaged.workers}, "
                f"available={max(0, available)}, blockers={blocker_text}; "
                "finish or explicitly stop the other qcode proof campaign "
                "before retrying (unrelated IPhO/Archon jobs were not counted)"
            )
        usable = [
            item for item in free
            if int(item[1].stem.split("-", 1)[1]) < budget.capacity
        ]
        if len(usable) < requested_slots:
            raise SolverBudgetUnavailable(
                "global qcode solver slot files are inconsistent with the "
                f"effective capacity: requested={requested_slots}, "
                f"free_slots={len(usable)}, capacity={budget.capacity}"
            )
        selected = usable[:requested_slots]
        selected_fds = {fd for fd, _ in selected}
        metadata = json.dumps({
            "schema_version": 1,
            "owner_pid": os.getpid(),
            "owner_start_ticks": _self_start_ticks(),
            "requested_slots": requested_slots,
            "acquired_utc": datetime.now(timezone.utc).isoformat(),
            # Do not persist arbitrary command arguments: launch commands can
            # contain credentials or other unrelated sensitive values.
            "entrypoint": os.path.basename(os.sys.argv[0]),
            "cpu_budget": budget.as_dict(),
        }, sort_keys=True).encode()
        for fd, path in selected:
            os.ftruncate(fd, 0)
            os.lseek(fd, 0, os.SEEK_SET)
            if os.write(fd, metadata) != len(metadata):
                raise SolverBudgetError(
                    f"short write to solver-budget lock metadata: {path}"
                )
            os.fsync(fd)
            slot_fds.append(fd)
            slot_paths.append(path)
        for fd, _ in free:
            if fd not in selected_fds:
                fcntl.flock(fd, fcntl.LOCK_UN)
                os.close(fd)
        free.clear()
        return SolverBudgetLease(
            fds=slot_fds,
            paths=slot_paths,
            requested_slots=requested_slots,
            cpu_budget=budget,
            unmanaged_usage=unmanaged,
            cooperative_slots_before=cooperative_busy,
            lock_root=root,
        )
    except Exception:
        cleanup_fds = {fd for fd, _ in free}
        cleanup_fds.update(slot_fds)
        for fd in cleanup_fds:
            try:
                fcntl.flock(fd, fcntl.LOCK_UN)
            finally:
                os.close(fd)
        raise
    finally:
        try:
            fcntl.flock(allocator_fd, fcntl.LOCK_UN)
        finally:
            os.close(allocator_fd)


def _self_start_ticks() -> int | None:
    try:
        raw = Path("/proc/self/stat").read_text()
        right = raw.rfind(")")
        fields = raw[right + 2 :].split()
        # Field 22 overall, or index 19 after state (field 3).
        return int(fields[19])
    except (OSError, ValueError, IndexError):
        return None


__all__ = [
    "CpuBudget",
    "ProcessRecord",
    "SolverBudgetError",
    "SolverBudgetLease",
    "SolverBudgetUnavailable",
    "UnmanagedUsage",
    "acquire_solver_budget",
    "detect_cpu_budget",
    "estimate_unmanaged_qcode_usage",
]
