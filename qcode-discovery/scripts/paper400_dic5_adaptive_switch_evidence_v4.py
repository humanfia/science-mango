#!/usr/bin/env python3
"""One-shot, incident-bound retry of the paper400 adaptive handoff.

The failed v3 attempt published intent and PREPARED records, then restored all
nine legacy lock entry points before any target was prepared or worker was
started.  Those five v3 artifacts are immutable incident evidence; this module
never removes, renames, or reuses them.  It admits exactly that state before
creating a disjoint v4 namespace or renaming any lock.

All JSON remains evidence-only.  Launch authority exists only in the
non-serializable, owner-process/thread-bound ``AtomicSwitchLease``.
"""

from __future__ import annotations

import contextlib
import fcntl
import hashlib
import importlib
import importlib.abc
import importlib.util
import json
import os
import stat
import sys
import threading
import types
import uuid
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any


PROJECT = Path(__file__).resolve().parent.parent
BASE_RELATIVE = Path("scripts/paper400_dic5_adaptive_switch_evidence_v2.py")
V3_RELATIVE = Path("scripts/paper400_dic5_adaptive_switch_evidence_v3.py")
OVERLAY_RELATIVE = Path(
    "investigations/paper400_dic5_adaptive_leaf_overlay_v2.py"
)
FIXED_REPLAY_PROJECT = Path(
    "/root/paper400-adaptive-prod-20260827-mHCpDT/source-b6058b8/"
    "qcode-discovery"
)
FIXED_REPLAY_V3_SOURCE = (
    FIXED_REPLAY_PROJECT / "scripts/paper400_dic5_adaptive_switch_evidence_v3.py"
)
FIXED_REPLAY_V2_SOURCE = FIXED_REPLAY_PROJECT / BASE_RELATIVE
FIXED_REPLAY_OVERLAY_SOURCE = FIXED_REPLAY_PROJECT / OVERLAY_RELATIVE
MAX_SOURCE_BYTES = 16 << 20
MAX_PROOF_BYTES = 1 << 40
SCHEMA_VERSION = 4
LANE_COUNT = 4
DESCENDANT_COUNT = 2
TARGET_COUNT = LANE_COUNT * DESCENDANT_COUNT
MAX_LIVE_WORKERS = 4
TARGET_KEYS = tuple(
    (lane, descendant)
    for descendant in range(DESCENDANT_COUNT)
    for lane in range(LANE_COUNT)
)
GATE = "paper400-dic5-adaptive-switch-evidence-v4"
PREPARED_KIND = "paper400-dic5-adaptive-retirement-prepared-v4"
HANDOFF_KIND = "paper400-dic5-adaptive-batch-handoff-v4"
HANDOFF_VERIFY_KIND = "paper400-dic5-adaptive-batch-handoff-check-v4"
ROLLBACK_KIND = "paper400-dic5-adaptive-handoff-rollback-v4"
QUIESCENCE_INPUT_KIND = (
    "paper400-adaptive-new-root-quiescence-observation-v5"
)
QUIESCENCE_KIND = "paper400-adaptive-new-root-quiescence-v4"

ATTEMPT_ID = (
    "6bef308b48b6469d5232347e20a7b08d78a63fa08b0c63fcc96d9156da6e26ca"
)
ATTEMPT_ROOT = Path(f"adaptive-handoff-v4-attempt-{ATTEMPT_ID}")
INCIDENT_PRECONDITION = ATTEMPT_ROOT / "00-incident-precondition.json"
RETIREMENT_INTENT = ATTEMPT_ROOT / "10-retirement-intent.json"
PREPARED_COMMIT = ATTEMPT_ROOT / "20-prepared.json"
TARGET_DIRECTORY = ATTEMPT_ROOT / "targets"
STARTED_DIRECTORY = ATTEMPT_ROOT / "started"
QUIESCENCE_DIRECTORY = ATTEMPT_ROOT / "quiescence"
HANDOFF_COMMIT = ATTEMPT_ROOT / "90-handoff.json"
ROLLBACK_COMMIT = ATTEMPT_ROOT / "90-rollback.json"
COMPENSATION_COMMIT = ATTEMPT_ROOT / "95-compensation.json"

FAILED_V3_INTENT = Path("adaptive-handoff-v3.retirement-intent.json")
FAILED_V3_PREPARED = Path("adaptive-handoff-v3.prepared.json")
FAILED_V3_TARGET_DIRECTORY = Path("adaptive-handoff-v3.targets")
FAILED_V3_STARTED_DIRECTORY = Path("adaptive-handoff-v3.started")
FAILED_V3_QUIESCENCE_DIRECTORY = Path("adaptive-handoff-v3.quiescence")
FAILED_V3_HANDOFF = Path("adaptive-handoff-v3.json")
FAILED_V3_ROLLBACK = Path("adaptive-handoff-v3.rollback.json")

EXPECTED_BATCH_ROOT = Path(
    "/tmp/paper400-dic5-width10-parent000-batch000-v3-b59cfbe9-20260827T054227Z"
)
EXPECTED_BATCH_MANIFEST_SHA256 = (
    "3228c3dab9464efd656eda26301ea200074085c08eedfb6abd19d2f683cfe40f"
)
EXPECTED_SWITCH_EVIDENCE_SHA256 = (
    "2ac95f8d035f0edf604077a2cd1d0db837b1d457704eb18e0777c09f33e80c7b"
)
EXPECTED_HARD_EVIDENCE_SHA256S = (
    "4b44152fa91e706dadc1b5b573618e0e724d896bca81f3a352fb5f1559b7b95c",
    "40672627b9c5cde9e4fdd356b96bbcd3fcd3ec0e16833700ec9bb3d479376a9f",
    "713ad0246f567e5cb83ef7a38b6bbb0d6239e2bf2dfd6190c715111d0bcad40a",
    "67dcd4ab6bc9f11f7e49bd89b74413e0ecf38c295cdbe3948892343bc896cbe5",
)
EXPECTED_OLD_LANE_TUPLES = (
    (
        0,
        "68eaec2b0f7b10e1f38b4604c7801d935546ef977f8a9e515542ec355f5b4f0b",
        "148cb68f8078c6f51ec3b47c3a9fd1d1c87c33616b90c66898d15372aea38f14",
        16701861888,
        EXPECTED_HARD_EVIDENCE_SHA256S[0],
    ),
    (
        64,
        "04c437281f0b68faec6fc6995948f6f371449c4b5c47567509b891c07a246427",
        "20a4a8cb69501d49e262100cc792c08191c0f72771c7159055f6ca4f75bb5bef",
        15216906240,
        EXPECTED_HARD_EVIDENCE_SHA256S[1],
    ),
    (
        128,
        "35c0e5279041dc187bdfe9fc252613d8a73a959a5c095c9481cefb58c0bbd360",
        "f789a7565e073273fda862a71c72d419f3386d6537cc125dcc432bacb756fac3",
        16716435456,
        EXPECTED_HARD_EVIDENCE_SHA256S[2],
    ),
    (
        192,
        "bfaffc88e425935ed75f8c41a93e78a8206fb386b5682c82fbbb53fd118847a1",
        "887994e6cabcb4cc5418da8d82abe0c8d1b5600f030cf3bd5e90bc17d0a2d8ca",
        15743700992,
        EXPECTED_HARD_EVIDENCE_SHA256S[3],
    ),
)
EXPECTED_OLD_PROOF_PHYSICAL_TUPLES = (
    (58, 60729374, 0, 0o600, 1, 16701861888),
    (58, 60729391, 0, 0o600, 1, 15216906240),
    (58, 60729408, 0, 0o600, 1, 16716435456),
    (58, 60729426, 0, 0o600, 1, 15743700992),
)
FAILED_V3_INTENT_RECORD_SHA256 = (
    "5d85fdc5775e315053f3dce89d1a021fb41e01451befede1ac93cac8807411b6"
)
FAILED_V3_PREPARED_RECORD_SHA256 = (
    "d431fbf48ba4a76ae87475f848e7026cd410e1147831dcecb27a454cce82de58"
)
FAILED_V3_INTENT_PHYSICAL_SHA256 = (
    "7e2b13855d78ecd4721e27b21e9a7ccebcc06ca00335fc5df4e9cc42b72596ed"
)
FAILED_V3_PREPARED_PHYSICAL_SHA256 = (
    "e41c6a8b3f0cfa6b223304145f8f9ebb0d3cc7910af2269e62f2232543c623ef"
)
FAILED_V3_SOURCE_SHA256 = (
    "bbaed5af10dc390a9b1b87b480a5bf3ce2c5a2004338154d77743bae6f8172fd"
)
FAILED_V3_SOURCE_BYTES = 128600
EXPECTED_V2_SOURCE_SHA256 = (
    "f4f6b7fbed84f5daf5a98a48d33b73299b3fd135ff92b3119b6fe1e241225da2"
)
EXPECTED_V2_SOURCE_BYTES = 82701
FIXED_REPLAY_OVERLAY_SOURCE_SHA256 = (
    "f4c485d94616c464c7b240407a4d69b9d49a5dac55966d4cb5cbc4431558436d"
)
FIXED_REPLAY_OVERLAY_SOURCE_BYTES = 72189
FIXED_REPLAY_STATIC_SOURCE_BINDING_SHA256 = (
    "199bd785ab31bdcc1881d9b3733ff5a41164be68745b3e91d12ec207f3bb747e"
)
FIXED_REPLAY_DYNAMIC_SOURCE_BINDING_SHA256 = (
    "993c2fdbcd56c82093fff7aee4d9e83e9ecec45c28e80b248d4b4f655e0db362"
)


class AdaptiveSwitchEvidenceV4Error(RuntimeError):
    """A source, retirement, target, process, or rollback invariant failed."""


def _read_source_bytes(path: Path) -> bytes:
    candidate = Path(path)
    lexical = candidate.lstat()
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_nlink != 1 or lexical.st_size > MAX_SOURCE_BYTES
    ):
        raise AdaptiveSwitchEvidenceV4Error("unsafe source file")
    fd = os.open(candidate, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    chunks: list[bytes] = []
    try:
        before = os.fstat(fd)
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            chunks.append(chunk)
            if sum(map(len, chunks)) > MAX_SOURCE_BYTES:
                raise AdaptiveSwitchEvidenceV4Error("source exceeds cap")
        after = os.fstat(fd)
    finally:
        os.close(fd)
    identity = lambda item: (
        item.st_dev, item.st_ino, item.st_mode, item.st_uid, item.st_gid,
        item.st_nlink, item.st_size, item.st_mtime_ns, item.st_ctime_ns,
    )
    if identity(before) != identity(after) or len(b"".join(chunks)) != before.st_size:
        raise AdaptiveSwitchEvidenceV4Error("source changed while reading")
    return b"".join(chunks)


_V4_SOURCE_PATH = Path(__file__).resolve(strict=True)
_V4_SOURCE_PAYLOAD = _read_source_bytes(_V4_SOURCE_PATH)
_V4_SOURCE_RECORD = {
    "role": "adaptive_switch_evidence_v4_source",
    "relative_path": _V4_SOURCE_PATH.relative_to(PROJECT).as_posix(),
    "sha256": hashlib.sha256(_V4_SOURCE_PAYLOAD).hexdigest(),
    "bytes": len(_V4_SOURCE_PAYLOAD),
    "execution": "module-load-captured-exact-source-bytes-v4",
}


class _FixedReplayReadonly:
    """Expose only the two pinned historical v3 readonly loaders."""

    __slots__ = ("_load_legacy", "_load_overlay")

    def __init__(self, module: Any) -> None:
        self._load_legacy = module._load_legacy_exact
        self._load_overlay = module._load_overlay_exact

    def load_legacy_exact(
        self, discovery: Mapping[str, Any],
    ) -> tuple[Any, Any, list[dict[str, Any]]]:
        return self._load_legacy(discovery)

    def load_overlay_exact(
        self,
    ) -> tuple[Any, dict[str, Any], list[dict[str, Any]]]:
        return self._load_overlay()


_FIXED_REPLAY_SOURCE_PATHS = (
    FIXED_REPLAY_V3_SOURCE, FIXED_REPLAY_V2_SOURCE,
    FIXED_REPLAY_OVERLAY_SOURCE,
)
_FIXED_REPLAY_SOURCE_EXPECTED = (
    (FAILED_V3_SOURCE_SHA256, FAILED_V3_SOURCE_BYTES),
    (EXPECTED_V2_SOURCE_SHA256, EXPECTED_V2_SOURCE_BYTES),
    (
        FIXED_REPLAY_OVERLAY_SOURCE_SHA256,
        FIXED_REPLAY_OVERLAY_SOURCE_BYTES,
    ),
)
_FIXED_REPLAY_SOURCE_ROLES = (
    "historical_adaptive_switch_evidence_v3_fixed_replay_source",
    "historical_adaptive_switch_evidence_v2_primitives_source",
    "historical_adaptive_leaf_overlay_v2_fixed_replay_source",
)
_FIXED_REPLAY_SOURCE_EXECUTIONS = (
    (
        "on-demand-fixed-replay-"
        "compile-exact-source-bytes-v4-fixed-bootstrap"
    ),
    "on-demand-fixed-replay-compile-exact-source-bytes-v3",
    (
        "on-demand-fixed-replay-historical-v3-readonly-loader-"
        "compile-exact-source-bytes-v3"
    ),
)


def _capture_fixed_replay_sources() -> tuple[
    tuple[dict[str, Any], ...], tuple[bytes, bytes, bytes],
]:
    """Read and pin historical sources without executing historical code."""

    payloads = tuple(
        _read_source_bytes(path) for path in _FIXED_REPLAY_SOURCE_PATHS
    )
    if any(
        hashlib.sha256(payload).hexdigest() != digest
        or len(payload) != size
        for payload, (digest, size) in zip(
            payloads, _FIXED_REPLAY_SOURCE_EXPECTED, strict=True
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "historical fixed-replay source misses frozen pin"
        )
    records = tuple({
        "role": role,
        "absolute_path": str(path),
        "sha256": digest,
        "bytes": size,
        "execution": execution,
    } for role, path, (digest, size), execution in zip(
        _FIXED_REPLAY_SOURCE_ROLES, _FIXED_REPLAY_SOURCE_PATHS,
        _FIXED_REPLAY_SOURCE_EXPECTED, _FIXED_REPLAY_SOURCE_EXECUTIONS,
        strict=True,
    ))
    return records, payloads


(
    _FIXED_REPLAY_SOURCE_RECORDS,
    _FIXED_REPLAY_SOURCE_PAYLOADS,
) = _capture_fixed_replay_sources()


def _load_fixed_replay_readonly() -> _FixedReplayReadonly:
    """Lazily exact-load v3 and retain only its two readonly loaders."""

    module = types.ModuleType(
        "_paper400_adaptive_switch_v3_fixed_replay_exact_bytes"
    )
    module.__file__ = str(FIXED_REPLAY_V3_SOURCE)
    module.__package__ = "scripts"
    module.__loader__ = None
    exec(
        compile(
            _FIXED_REPLAY_SOURCE_PAYLOADS[0],
            str(FIXED_REPLAY_V3_SOURCE), "exec",
            dont_inherit=True,
        ),
        module.__dict__,
    )
    v3_record = getattr(module, "_V3_SOURCE_RECORD", None)
    v2_record = getattr(module, "_BASE_SOURCE_RECORD", None)
    static_binding = module._v3_source_binding()
    if (
        Path(getattr(module, "PROJECT", "")) != FIXED_REPLAY_PROJECT
        or Path(getattr(module, "__file__", "")) != FIXED_REPLAY_V3_SOURCE
        or type(v3_record) is not dict
        or v3_record.get("sha256") != FAILED_V3_SOURCE_SHA256
        or v3_record.get("bytes") != FAILED_V3_SOURCE_BYTES
        or type(v2_record) is not dict
        or v2_record.get("sha256") != EXPECTED_V2_SOURCE_SHA256
        or v2_record.get("bytes") != EXPECTED_V2_SOURCE_BYTES
        or Path(getattr(getattr(module, "base", None), "__file__", ""))
            != FIXED_REPLAY_V2_SOURCE
        or not callable(getattr(module, "_load_legacy_exact", None))
        or not callable(getattr(module, "_load_overlay_exact", None))
        or type(static_binding) is not dict
        or not module.selfhash_valid(
            static_binding, "source_binding_sha256"
        )
        or static_binding.get("source_binding_sha256")
            != FIXED_REPLAY_STATIC_SOURCE_BINDING_SHA256
        or not json_type_equal(
            static_binding, _expected_failed_v3_source_binding()
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "historical v3 fixed-replay bootstrap mismatch"
        )
    return _FixedReplayReadonly(module)


def _load_base_from_exact_source() -> tuple[Any, dict[str, Any]]:
    path = (PROJECT / BASE_RELATIVE).resolve(strict=True)
    payload = _read_source_bytes(path)
    digest = hashlib.sha256(payload).hexdigest()
    if digest != EXPECTED_V2_SOURCE_SHA256 or len(payload) != EXPECTED_V2_SOURCE_BYTES:
        raise AdaptiveSwitchEvidenceV4Error(
            "v2 execution base misses frozen pre-exec pin"
        )
    module = types.ModuleType("_paper400_adaptive_switch_v2_exact_bytes")
    module.__file__ = str(path)
    module.__package__ = "scripts"
    module.__loader__ = None
    exec(compile(payload, str(path), "exec", dont_inherit=True), module.__dict__)
    return module, {
        "role": "adaptive_switch_evidence_v2_primitives_source",
        "relative_path": BASE_RELATIVE.as_posix(),
        "sha256": digest,
        "bytes": len(payload),
        "execution": "compile-exact-source-bytes-v4",
    }


base, _BASE_SOURCE_RECORD = _load_base_from_exact_source()

canonical_bytes = base.canonical_bytes
canonical_sha256 = base.canonical_sha256
seal = base.seal
selfhash_valid = base.selfhash_valid
json_type_equal = base.json_type_equal
validate_switch_record_structure = base.validate_switch_record_structure


_LOAD_GUARD = threading.RLock()
_PROJECT_PREFIXES = (
    "scripts", "scripts.", "investigations", "investigations.",
    "evaluation", "evaluation.",
)


class _ExactSourceLoader(importlib.abc.Loader):
    def __init__(
        self, fullname: str, path: Path, payload: bytes,
        observed: dict[str, dict[str, Any]], *, externally_bound: bool,
    ) -> None:
        self.fullname = fullname
        self.path = path
        self.payload = payload
        self.observed = observed
        self.externally_bound = externally_bound

    def create_module(self, spec: Any) -> types.ModuleType | None:
        return None

    def exec_module(self, module: types.ModuleType) -> None:
        module.__file__ = str(self.path)
        module.__package__ = (
            self.fullname if self.path.name == "__init__.py"
            else self.fullname.rpartition(".")[0]
        )
        if self.path.name == "__init__.py":
            module.__path__ = [str(self.path.parent)]
        digest = hashlib.sha256(self.payload).hexdigest()
        self.observed[self.fullname] = {
            "module": self.fullname, "path": str(self.path),
            "sha256": digest, "bytes": len(self.payload),
            "externally_bound": self.externally_bound,
            "execution": "compile-exact-source-bytes-v4",
        }
        exec(
            compile(self.payload, str(self.path), "exec", dont_inherit=True),
            module.__dict__,
        )


class _ExactSourceFinder(importlib.abc.MetaPathFinder):
    def __init__(
        self, project: Path, bound: Mapping[str, tuple[Path, bytes, str]],
    ) -> None:
        self.project = project.resolve(strict=True)
        self.bound = dict(bound)
        self.observed: dict[str, dict[str, Any]] = {}

    def _spec(
        self, fullname: str, path: Path, payload: bytes, *,
        externally_bound: bool, is_package: bool,
    ) -> Any:
        loader = _ExactSourceLoader(
            fullname, path, payload, self.observed,
            externally_bound=externally_bound,
        )
        return importlib.util.spec_from_loader(
            fullname, loader, origin=str(path), is_package=is_package,
        )

    def find_spec(
        self, fullname: str, path: Sequence[str] | None = None,
        target: types.ModuleType | None = None,
    ) -> Any:
        del path, target
        if fullname in {"sitecustomize", "usercustomize"}:
            raise AdaptiveSwitchEvidenceV4Error(
                "Python startup customization is forbidden"
            )
        bound = self.bound.get(fullname)
        if bound is not None:
            source, payload, expected = bound
            if hashlib.sha256(payload).hexdigest() != expected:
                raise AdaptiveSwitchEvidenceV4Error("bound source payload drift")
            return self._spec(
                fullname, source, payload, externally_bound=True,
                is_package=source.name == "__init__.py",
            )
        if not fullname.startswith(_PROJECT_PREFIXES):
            return None
        parts = fullname.split(".")
        package = self.project.joinpath(*parts) / "__init__.py"
        source = self.project.joinpath(*parts).with_suffix(".py")
        selected: Path | None = None
        is_package = False
        if package.is_file() and not package.is_symlink():
            selected, is_package = package, True
        elif source.is_file() and not source.is_symlink():
            selected = source
        if selected is None:
            return None
        try:
            selected.resolve(strict=True).relative_to(self.project)
        except (FileNotFoundError, OSError, RuntimeError, ValueError) as exc:
            raise AdaptiveSwitchEvidenceV4Error("source escapes exact project") from exc
        payload = _read_source_bytes(selected)
        return self._spec(
            fullname, selected, payload, externally_bound=False,
            is_package=is_package,
        )


def _purge_project_modules() -> dict[str, types.ModuleType]:
    removed: dict[str, types.ModuleType] = {}
    for name, module in list(sys.modules.items()):
        if name == __name__:
            continue
        if name in {"scripts", "investigations", "evaluation"} or name.startswith(
            ("scripts.", "investigations.", "evaluation.")
        ):
            removed[name] = module
            sys.modules.pop(name, None)
    return removed


def _restore_project_modules(
    before_names: set[str], removed: Mapping[str, types.ModuleType],
) -> None:
    for name in list(sys.modules):
        if name not in before_names and (
            name in {"scripts", "investigations", "evaluation"}
            or name.startswith(("scripts.", "investigations.", "evaluation."))
        ):
            sys.modules.pop(name, None)
    for name, module in removed.items():
        sys.modules[name] = module


def _python_loader_state() -> tuple[list[str], Any, Any]:
    if type(sys.path) is not list or any(
        type(item) is not str for item in sys.path
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "exact loader changed sys.path type or entries"
        )
    return (
        list(sys.path), sys.dont_write_bytecode, sys.pycache_prefix,
    )


def _load_legacy_exact(
    discovery: Mapping[str, Any],
) -> tuple[Any, Any, list[dict[str, Any]]]:
    project = discovery["legacy_project"]
    finder = _ExactSourceFinder(project, discovery["source_payloads"])
    coordinator_name = discovery["coordinator_module"]
    child_name = discovery["child_module"]
    with _LOAD_GUARD:
        before_names = set(sys.modules)
        before_meta = list(sys.meta_path)
        before_path = list(sys.path)
        removed = _purge_project_modules()
        try:
            sys.meta_path.insert(0, finder)
            coordinator = importlib.import_module(coordinator_name)
            child = sys.modules.get(child_name)
            if child is None or getattr(coordinator, "child_runner", None) is not child:
                raise AdaptiveSwitchEvidenceV4Error("coordinator exact-child mismatch")
            required = set(discovery["source_payloads"])
            missing = required - set(finder.observed)
            if missing:
                raise AdaptiveSwitchEvidenceV4Error(
                    f"manifest-bound sources not executed from bytes: {sorted(missing)}"
                )
            for name in required:
                if (
                    finder.observed[name]["sha256"]
                    != discovery["source_payloads"][name][2]
                    or finder.observed[name]["externally_bound"] is not True
                ):
                    raise AdaptiveSwitchEvidenceV4Error("bound source execution mismatch")
            return coordinator, child, [
                finder.observed[name] for name in sorted(finder.observed)
            ]
        finally:
            sys.path[:] = before_path
            sys.meta_path[:] = before_meta
            _restore_project_modules(before_names, removed)


def _load_overlay_exact() -> tuple[Any, dict[str, Any], list[dict[str, Any]]]:
    path = (PROJECT / OVERLAY_RELATIVE).resolve(strict=True)
    payload = _read_source_bytes(path)
    digest = hashlib.sha256(payload).hexdigest()
    name = ".".join(OVERLAY_RELATIVE.with_suffix("").parts)
    finder = _ExactSourceFinder(PROJECT, {name: (path, payload, digest)})
    with _LOAD_GUARD:
        before_names = set(sys.modules)
        before_meta = list(sys.meta_path)
        before_path = list(sys.path)
        removed = _purge_project_modules()
        try:
            sys.meta_path.insert(0, finder)
            overlay = importlib.import_module(name)
            if (
                name not in finder.observed
                or finder.observed[name]["sha256"] != digest
                or finder.observed[name]["externally_bound"] is not True
            ):
                raise AdaptiveSwitchEvidenceV4Error("overlay exact-byte load failed")
            return overlay, {
                "role": "adaptive_leaf_overlay_v2_source",
                "relative_path": OVERLAY_RELATIVE.as_posix(),
                "sha256": digest,
                "bytes": len(payload),
                "execution": "compile-exact-source-bytes-v4",
            }, [finder.observed[item] for item in sorted(finder.observed)]
        finally:
            sys.path[:] = before_path
            sys.meta_path[:] = before_meta
            _restore_project_modules(before_names, removed)

class _FixedReplayBundle:
    __slots__ = (
        "coordinator", "child", "overlay", "legacy_executed",
        "overlay_record", "overlay_executed", "snapshot", "record",
    )

    def __init__(
        self, *, coordinator: Any, child: Any, overlay: Any,
        legacy_executed: Sequence[Mapping[str, Any]],
        overlay_record: Mapping[str, Any],
        overlay_executed: Sequence[Mapping[str, Any]],
        snapshot: Mapping[str, Any], record: Mapping[str, Any],
    ) -> None:
        self.coordinator = coordinator
        self.child = child
        self.overlay = overlay
        self.legacy_executed = list(legacy_executed)
        self.overlay_record = dict(overlay_record)
        self.overlay_executed = list(overlay_executed)
        self.snapshot = snapshot
        self.record = dict(record)


class _CurrentScienceBundle:
    __slots__ = (
        "coordinator", "child", "overlay", "legacy_executed",
        "overlay_record", "overlay_executed", "snapshot",
    )

    def __init__(
        self, *, coordinator: Any, child: Any, overlay: Any,
        legacy_executed: Sequence[Mapping[str, Any]],
        overlay_record: Mapping[str, Any],
        overlay_executed: Sequence[Mapping[str, Any]],
        snapshot: Mapping[str, Any],
    ) -> None:
        self.coordinator = coordinator
        self.child = child
        self.overlay = overlay
        self.legacy_executed = list(legacy_executed)
        self.overlay_record = dict(overlay_record)
        self.overlay_executed = list(overlay_executed)
        self.snapshot = snapshot


def _fixed_replay_sources_unchanged() -> None:
    paths = (
        FIXED_REPLAY_V3_SOURCE, FIXED_REPLAY_V2_SOURCE,
        FIXED_REPLAY_OVERLAY_SOURCE,
    )
    if any(
        _read_source_bytes(path) != payload
        for path, payload in zip(
            paths, _FIXED_REPLAY_SOURCE_PAYLOADS, strict=True
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "historical fixed-replay dependency changed since capture"
        )


def _validate_fixed_dynamic_source_binding(
    discovery: Mapping[str, Any],
    legacy_executed: Sequence[Mapping[str, Any]],
    overlay_record: Mapping[str, Any],
    overlay_executed: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    binding = base._source_binding(
        discovery, legacy_executed, overlay_record, overlay_executed
    )
    fields = {
        "schema_version", "method", "legacy_project", "legacy_sources",
        "legacy_executed_source_closure", "current_sources",
        "overlay_executed_source_closure",
        "sitecustomize_imported_by_loader", "pyc_executed_by_loader",
        "source_binding_sha256",
    }
    legacy = binding.get("legacy_executed_source_closure")
    overlay = binding.get("overlay_executed_source_closure")
    current = binding.get("current_sources")
    overlay_module = ".".join(OVERLAY_RELATIVE.with_suffix("").parts)
    fixed_overlay_executions = (
        [] if type(overlay) is not list else [
            item for item in overlay
            if type(item) is dict and item.get("module") == overlay_module
        ]
    )
    if (
        type(binding) is not dict or set(binding) != fields
        or not selfhash_valid(binding, "source_binding_sha256")
        or binding.get("source_binding_sha256")
            != FIXED_REPLAY_DYNAMIC_SOURCE_BINDING_SHA256
        or binding.get("schema_version") != 2
        or binding.get("method")
            != "manifest-pinned-source-bytes-compile-exec-no-pyc-v2"
        or binding.get("legacy_project")
            != str(discovery["legacy_project"])
        or type(legacy) is not list or len(legacy) != 25
        or type(overlay) is not list or len(overlay) != 19
        or type(current) is not list or len(current) != 2
        or current[0] != {
            "role": "adaptive_switch_evidence_v2_source",
            "relative_path": BASE_RELATIVE.as_posix(),
            "sha256": EXPECTED_V2_SOURCE_SHA256,
        }
        or not json_type_equal(current[1], overlay_record)
        or overlay_record.get("sha256")
            != FIXED_REPLAY_OVERLAY_SOURCE_SHA256
        or overlay_record.get("bytes")
            != FIXED_REPLAY_OVERLAY_SOURCE_BYTES
        or overlay_record.get("execution")
            != "compile-exact-source-bytes-v3"
        or any(
            type(item) is not dict
            or item.get("execution") != "compile-exact-source-bytes-v3"
            or type(item.get("path")) is not str
            or not Path(item["path"]).is_relative_to(
                Path(discovery["legacy_project"])
            )
            for item in legacy
        )
        or any(
            type(item) is not dict
            or item.get("execution") != "compile-exact-source-bytes-v3"
            or type(item.get("path")) is not str
            or not Path(item["path"]).is_relative_to(FIXED_REPLAY_PROJECT)
            for item in overlay
        )
        or len(fixed_overlay_executions) != 1
        or fixed_overlay_executions[0].get("path")
            != str(FIXED_REPLAY_OVERLAY_SOURCE)
        or fixed_overlay_executions[0].get("sha256")
            != FIXED_REPLAY_OVERLAY_SOURCE_SHA256
        or fixed_overlay_executions[0].get("bytes")
            != FIXED_REPLAY_OVERLAY_SOURCE_BYTES
        or fixed_overlay_executions[0].get("externally_bound") is not True
        or binding.get("sitecustomize_imported_by_loader") is not False
        or binding.get("pyc_executed_by_loader") is not False
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "historical fixed-replay dynamic source binding mismatch"
        )
    return dict(binding)


def _load_fixed_replay_bundle(
    root: Path, discovery: Mapping[str, Any], *,
    timeout_seconds: float, elapsed_seconds_by_lane: Sequence[float],
) -> _FixedReplayBundle:
    _fixed_replay_sources_unchanged()
    with _LOAD_GUARD:
        before_path = list(sys.path)
        try:
            fixed_replay_readonly = _load_fixed_replay_readonly()
            coordinator, child, legacy_executed = (
                fixed_replay_readonly.load_legacy_exact(discovery)
            )
            overlay, overlay_record, overlay_executed = (
                fixed_replay_readonly.load_overlay_exact()
            )
        finally:
            sys.path[:] = before_path
    fixed_source_binding = _validate_fixed_dynamic_source_binding(
        discovery, legacy_executed, overlay_record, overlay_executed
    )

    if (
        overlay_record.get("role") != "adaptive_leaf_overlay_v2_source"
        or overlay_record.get("relative_path")
            != OVERLAY_RELATIVE.as_posix()
        or overlay_record.get("sha256")
            != FIXED_REPLAY_OVERLAY_SOURCE_SHA256
        or overlay_record.get("bytes")
            != FIXED_REPLAY_OVERLAY_SOURCE_BYTES
        or overlay_record.get("execution")
            != "compile-exact-source-bytes-v3"
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "historical v3 readonly overlay loader misses frozen pin"
        )
    snapshot = base._snapshot_locked(
        root, coordinator, child
    )
    record = base._build_record(
        root, snapshot, discovery, overlay, legacy_executed,
        overlay_record, overlay_executed,
        timeout_seconds=timeout_seconds,
        elapsed_seconds_by_lane=list(elapsed_seconds_by_lane),
    )
    validate_switch_record_structure(record)
    if (
        not json_type_equal(
            record.get("source_binding"), fixed_source_binding
        )
        or record.get("record_sha256") != EXPECTED_SWITCH_EVIDENCE_SHA256
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "historical fixed-replay record misses frozen provenance"
        )
    return _FixedReplayBundle(
        coordinator=coordinator, child=child, overlay=overlay,
        legacy_executed=legacy_executed,
        overlay_record=overlay_record,
        overlay_executed=overlay_executed,
        snapshot=snapshot, record=record,
    )


def _load_current_science_bundle(
    discovery: Mapping[str, Any], *,
    fixed_snapshot: Mapping[str, Any],
) -> _CurrentScienceBundle:
    coordinator, child, legacy_executed = _load_legacy_exact(discovery)
    overlay, overlay_record, overlay_executed = _load_overlay_exact()
    return _CurrentScienceBundle(
        coordinator=coordinator, child=child, overlay=overlay,
        legacy_executed=legacy_executed,
        overlay_record=overlay_record,
        overlay_executed=overlay_executed,
        snapshot=json.loads(canonical_bytes(fixed_snapshot)),
    )



def _v4_source_binding() -> dict[str, Any]:
    _fixed_replay_sources_unchanged()
    if (
        _read_source_bytes(_V4_SOURCE_PATH) != _V4_SOURCE_PAYLOAD
        or hashlib.sha256(
            _read_source_bytes(PROJECT / BASE_RELATIVE)
        ).hexdigest() != EXPECTED_V2_SOURCE_SHA256
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "v4/current-v2 source closure changed since exact module load"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "method": "exact-source-bytes-no-pyc-no-sitecustomize-v4",
        "sources": [
            dict(_V4_SOURCE_RECORD),
            dict(_BASE_SOURCE_RECORD),
        ],
        "historical_fixed_replay_dependency": {
            "purpose": "fixed-incident-switch-record-replay-only",
            "readonly_api": [
                "load_legacy_exact", "load_overlay_exact",
            ],
            "sources": [
                dict(item) for item in _FIXED_REPLAY_SOURCE_RECORDS
            ],
            "static_source_binding":
                _expected_failed_v3_source_binding(),
            "dynamic_source_binding_sha256":
                FIXED_REPLAY_DYNAMIC_SOURCE_BINDING_SHA256,
            "historical_v3_calls_are_readonly_loaders_only": True,
            "fixed_record_primitives": "current-v4-frozen-v2-exact-source",
            "current_science_uses_v4_loaders_and_overlay": True,
        },
        "sitecustomize_executed_by_loader": False,
        "pyc_executed_by_loader": False,
    }, "source_binding_sha256")


def _attempt_binding(
    incident_precondition_sha256: str,
) -> dict[str, Any]:
    incident_pin = base._require_sha256(
        incident_precondition_sha256,
        label="incident precondition pin",
    )
    return {
        "attempt_id": ATTEMPT_ID,
        "incident_precondition_sha256": incident_pin,
        "failed_v3_intent_sha256": FAILED_V3_INTENT_RECORD_SHA256,
        "failed_v3_prepared_sha256": FAILED_V3_PREPARED_RECORD_SHA256,
    }


def _attempt_binding_valid(
    record: Mapping[str, Any], incident_precondition_sha256: str,
) -> bool:
    expected = _attempt_binding(incident_precondition_sha256)
    return all(
        type(record.get(field)) is type(value)
        and record.get(field) == value
        for field, value in expected.items()
    )


def _publish(path: Path, record: Mapping[str, Any]) -> None:
    base._publish_new_json(path, record)


def _make_journal_directory(root: Path, relative: Path) -> Path:
    target = root / relative
    try:
        os.mkdir(target, 0o700)
    except FileExistsError as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            f"stale handoff journal exists: {relative}"
        ) from exc
    lexical = target.lstat()
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISDIR(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o700
    ):
        raise AdaptiveSwitchEvidenceV4Error("unsafe handoff journal directory")
    _fsync_directory(target.parent)
    return target


def _make_attempt_root(root: Path) -> Path:
    target = root / ATTEMPT_ROOT
    try:
        os.mkdir(target, 0o700)
    except FileExistsError as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "fixed v4 attempt namespace already exists"
        ) from exc
    observed = target.lstat()
    if (
        stat.S_ISLNK(observed.st_mode)
        or not stat.S_ISDIR(observed.st_mode)
        or observed.st_uid != os.geteuid()
        or observed.st_gid != os.getegid()
        or observed.st_nlink != 2
        or stat.S_IMODE(observed.st_mode) != 0o700
    ):
        raise AdaptiveSwitchEvidenceV4Error("unsafe fixed attempt root")
    _fsync_directory(root)
    return target


def _fsync_directory(path: Path) -> None:
    fd = os.open(
        path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW
    )
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _stable_raw_json(
    path: Path, *, expected_record_sha256: str,
    expected_physical_sha256: str,
) -> tuple[dict[str, Any], dict[str, int], int]:
    payload, identity = base._stable_bytes(
        path, cap=base.MAX_JSON_BYTES
    )
    if (
        hashlib.sha256(payload).hexdigest() != expected_physical_sha256
        or identity["mode"] != 0o600
        or identity["uid"] != os.geteuid()
        or identity["gid"] != os.getegid()
        or identity["links"] != 1
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 physical JSON misses fixed pin/metadata"
        )
    try:
        value = json.loads(payload)
        base._strict_json(value)
    except (json.JSONDecodeError, UnicodeDecodeError, TypeError, ValueError) as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 JSON is invalid"
        ) from exc
    if (
        type(value) is not dict
        or payload not in {canonical_bytes(value), canonical_bytes(value) + b"\n"}
        or not selfhash_valid(value)
        or value.get("record_sha256") != expected_record_sha256
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 JSON record/self-hash mismatch"
        )
    return value, identity, len(payload)


def _expected_failed_v3_source_binding() -> dict[str, Any]:
    value = {
        "schema_version": 3,
        "method": "exact-source-bytes-no-pyc-no-sitecustomize-v3",
        "sources": [
            {
                "role": "adaptive_switch_evidence_v3_source",
                "relative_path": V3_RELATIVE.as_posix(),
                "sha256": FAILED_V3_SOURCE_SHA256,
                "bytes": FAILED_V3_SOURCE_BYTES,
                "execution":
                    "module-load-captured-exact-source-bytes-v3",
            },
            {
                "role":
                    "adaptive_switch_evidence_v2_primitives_source",
                "relative_path": BASE_RELATIVE.as_posix(),
                "sha256": EXPECTED_V2_SOURCE_SHA256,
                "bytes": EXPECTED_V2_SOURCE_BYTES,
                "execution": "compile-exact-source-bytes-v3",
            },
        ],
        "sitecustomize_executed_by_loader": False,
        "pyc_executed_by_loader": False,
    }
    value["source_binding_sha256"] = canonical_sha256(value)
    if (
        value["source_binding_sha256"]
        != "199bd785ab31bdcc1881d9b3733ff5a41164be68745b3e91d12ec207f3bb747e"
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "internal failed-v3 source-binding pin mismatch"
        )
    return value


def _stable_empty_incident_directory(
    root: Path, relative: Path,
) -> dict[str, Any]:
    path = root / relative
    before = path.lstat()
    if (
        stat.S_ISLNK(before.st_mode)
        or not stat.S_ISDIR(before.st_mode)
        or before.st_uid != os.geteuid()
        or before.st_gid != os.getegid()
        or before.st_nlink != 2
        or stat.S_IMODE(before.st_mode) != 0o700
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 journal directory is unsafe"
        )
    try:
        names = sorted(item.name for item in path.iterdir())
    except OSError as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "cannot inspect failed-v3 journal directory"
        ) from exc
    after = path.lstat()
    if (
        names != []
        or not json_type_equal(
            base._stat_identity(before), base._stat_identity(after)
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 journal directory is nonempty/unstable"
        )
    return {
        "relative_path": relative.as_posix(),
        "identity": base._stat_identity(after),
        "entries": [],
    }


def _validate_failed_v3_incident_locked(
    root: Path, locks: Sequence[Any],
) -> dict[str, Any]:
    if root != EXPECTED_BATCH_ROOT:
        raise AdaptiveSwitchEvidenceV4Error(
            "batch root is not the fixed incident root"
        )
    if (root / ATTEMPT_ROOT).exists() or (root / ATTEMPT_ROOT).is_symlink():
        raise AdaptiveSwitchEvidenceV4Error(
            "fixed v4 attempt namespace is not pristine"
        )
    intent, intent_identity, intent_bytes = _stable_raw_json(
        root / FAILED_V3_INTENT,
        expected_record_sha256=FAILED_V3_INTENT_RECORD_SHA256,
        expected_physical_sha256=FAILED_V3_INTENT_PHYSICAL_SHA256,
    )
    prepared, prepared_identity, prepared_bytes = _stable_raw_json(
        root / FAILED_V3_PREPARED,
        expected_record_sha256=FAILED_V3_PREPARED_RECORD_SHA256,
        expected_physical_sha256=FAILED_V3_PREPARED_PHYSICAL_SHA256,
    )
    intent_fields = {
        "authenticated", "batch_manifest_sha256", "batch_root", "gate",
        "kind", "launch_authorized", "lock_plan", "production_eligible",
        "quiescence_journal_directory", "record_sha256",
        "retirement_complete", "schema_version", "source_binding",
        "started_journal_directory", "switch_evidence_sha256",
        "target_journal_directory", "test_only",
    }
    prepared_fields = {
        "authenticated", "batch_manifest_sha256", "batch_root",
        "batch_root_identity", "gate", "kind", "launch_authorized",
        "old_runner_entrypoints_reachable", "production_eligible",
        "record_sha256", "retired_locks", "retirement_complete",
        "retirement_intent_sha256", "schema_version",
        "scientific_claim", "source_binding",
        "switch_evidence_sha256", "test_only",
    }
    expected_source = _expected_failed_v3_source_binding()
    if (
        set(intent) != intent_fields
        or set(prepared) != prepared_fields
        or intent.get("schema_version") != 3
        or type(intent.get("schema_version")) is not int
        or prepared.get("schema_version") != 3
        or type(prepared.get("schema_version")) is not int
        or intent.get("kind")
            != "paper400-dic5-adaptive-retirement-intent-v3"
        or prepared.get("kind")
            != "paper400-dic5-adaptive-retirement-prepared-v3"
        or intent.get("gate")
            != "paper400-dic5-adaptive-switch-evidence-v3"
        or prepared.get("gate")
            != "paper400-dic5-adaptive-switch-evidence-v3"
        or intent.get("batch_root") != str(root)
        or prepared.get("batch_root") != str(root)
        or intent.get("batch_manifest_sha256")
            != EXPECTED_BATCH_MANIFEST_SHA256
        or prepared.get("batch_manifest_sha256")
            != EXPECTED_BATCH_MANIFEST_SHA256
        or intent.get("switch_evidence_sha256")
            != EXPECTED_SWITCH_EVIDENCE_SHA256
        or prepared.get("switch_evidence_sha256")
            != EXPECTED_SWITCH_EVIDENCE_SHA256
        or intent.get("retirement_complete") is not False
        or prepared.get("retirement_complete") is not True
        or prepared.get("old_runner_entrypoints_reachable") is not False
        or prepared.get("retirement_intent_sha256")
            != FAILED_V3_INTENT_RECORD_SHA256
        or any(
            value is not expected
            for value, expected in (
                (intent.get("authenticated"), False),
                (intent.get("launch_authorized"), False),
                (intent.get("production_eligible"), False),
                (intent.get("test_only"), True),
                (prepared.get("authenticated"), False),
                (prepared.get("launch_authorized"), False),
                (prepared.get("production_eligible"), False),
                (prepared.get("scientific_claim"), False),
                (prepared.get("test_only"), True),
            )
        )
        or not json_type_equal(intent.get("source_binding"), expected_source)
        or not json_type_equal(prepared.get("source_binding"), expected_source)
        or not json_type_equal(
            prepared.get("batch_root_identity"), base._root_identity(root)
        )
        or intent.get("target_journal_directory")
            != str(root / FAILED_V3_TARGET_DIRECTORY)
        or intent.get("started_journal_directory")
            != str(root / FAILED_V3_STARTED_DIRECTORY)
        or intent.get("quiescence_journal_directory")
            != str(root / FAILED_V3_QUIESCENCE_DIRECTORY)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 intent/prepared cross-binding mismatch"
        )
    plans = intent.get("lock_plan")
    retired = prepared.get("retired_locks")
    if (
        type(plans) is not list or type(retired) is not list
        or len(plans) != 9 or len(retired) != 9
        or len(locks) != 9
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 lock cardinality mismatch"
        )
    held_by_role = {item.role: item for item in locks}
    expected_roles = [
        *(f"controller-{index}" for index in range(LANE_COUNT)),
        *(f"lane-{index}" for index in range(LANE_COUNT)), "batch",
    ]
    restored: list[dict[str, Any]] = []
    for sequence, role in enumerate(expected_roles):
        plan = plans[sequence]
        item = retired[sequence]
        held = held_by_role.get(role)
        if (
            type(plan) is not dict or type(item) is not dict or held is None
            or set(plan) != {
                "sequence", "role", "original_path", "retired_path",
                "pre_rename_identity",
            }
            or set(item) != {
                "sequence", "role", "original_path", "retired_path",
                "pre_rename_identity", "identity",
            }
            or plan.get("sequence") != sequence
            or item.get("sequence") != sequence
            or plan.get("role") != role or item.get("role") != role
            or any(
                type(plan.get(field)) is not str
                or type(item.get(field)) is not str
                or plan.get(field) != item.get(field)
                for field in (
                    "original_path", "retired_path",
                )
            )
            or not json_type_equal(
                plan.get("pre_rename_identity"),
                item.get("pre_rename_identity"),
            )
            or Path(plan.get("original_path", "")) != held.original_path
            or Path(held.current_path) != held.original_path
            or Path(plan.get("retired_path", "")).parent
                != held.original_path.parent
            or Path(plan.get("retired_path", "")).name
                != held.original_path.name
                    + ".retired-v3-"
                    + EXPECTED_SWITCH_EVIDENCE_SHA256[:16]
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "failed-v3 lock plan was substituted"
            )
        original = held.original_path
        old_retired = Path(plan["retired_path"])
        if old_retired.exists() or old_retired.is_symlink():
            raise AdaptiveSwitchEvidenceV4Error(
                "failed-v3 retired lock name still exists"
            )
        path_identity = base._stat_identity(original.lstat())
        fd_identity = base._stat_identity(os.fstat(held.fd))
        if (
            not json_type_equal(path_identity, fd_identity)
            or not json_type_equal(fd_identity, held.identity)
            or not json_type_equal(
                _identity_without_ctime(fd_identity),
                _identity_without_ctime(plan["pre_rename_identity"]),
            )
            or not json_type_equal(
                _identity_without_ctime(item["identity"]),
                _identity_without_ctime(plan["pre_rename_identity"]),
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "failed-v3 original lock was not exactly restored"
            )
        restored.append({
            "sequence": sequence,
            "role": role,
            "original_path": str(original),
            "failed_retired_path": str(old_retired),
            "current_identity": fd_identity,
            "historical_pre_rename_identity":
                dict(plan["pre_rename_identity"]),
        })
    directories = [
        _stable_empty_incident_directory(root, relative)
        for relative in (
            FAILED_V3_TARGET_DIRECTORY,
            FAILED_V3_STARTED_DIRECTORY,
            FAILED_V3_QUIESCENCE_DIRECTORY,
        )
    ]
    for absent in (FAILED_V3_HANDOFF, FAILED_V3_ROLLBACK):
        path = root / absent
        if path.exists() or path.is_symlink():
            raise AdaptiveSwitchEvidenceV4Error(
                "failed-v3 terminal record unexpectedly exists"
            )
    # Re-read raw incident evidence after the directory/lock survey.
    repeat_intent, repeat_intent_identity, _ = _stable_raw_json(
        root / FAILED_V3_INTENT,
        expected_record_sha256=FAILED_V3_INTENT_RECORD_SHA256,
        expected_physical_sha256=FAILED_V3_INTENT_PHYSICAL_SHA256,
    )
    repeat_prepared, repeat_prepared_identity, _ = _stable_raw_json(
        root / FAILED_V3_PREPARED,
        expected_record_sha256=FAILED_V3_PREPARED_RECORD_SHA256,
        expected_physical_sha256=FAILED_V3_PREPARED_PHYSICAL_SHA256,
    )
    if (
        not json_type_equal(repeat_intent, intent)
        or not json_type_equal(repeat_prepared, prepared)
        or not json_type_equal(repeat_intent_identity, intent_identity)
        or not json_type_equal(repeat_prepared_identity, prepared_identity)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "failed-v3 incident changed during admission"
        )
    return {
        "failed_v3_intent": {
            "relative_path": FAILED_V3_INTENT.as_posix(),
            "record_sha256": FAILED_V3_INTENT_RECORD_SHA256,
            "physical_sha256": FAILED_V3_INTENT_PHYSICAL_SHA256,
            "bytes": intent_bytes, "identity": intent_identity,
        },
        "failed_v3_prepared": {
            "relative_path": FAILED_V3_PREPARED.as_posix(),
            "record_sha256": FAILED_V3_PREPARED_RECORD_SHA256,
            "physical_sha256": FAILED_V3_PREPARED_PHYSICAL_SHA256,
            "bytes": prepared_bytes, "identity": prepared_identity,
        },
        "failed_v3_source_binding": expected_source,
        "failed_v3_empty_directories": directories,
        "failed_v3_handoff_absent": True,
        "failed_v3_rollback_absent": True,
        "restored_old_locks": restored,
        "historical_prepared_reuse_forbidden": True,
    }


def _stable_directory_inventory(
    path: Path, *, expected_names: set[str],
) -> dict[str, Any]:
    before = path.lstat()
    if (
        stat.S_ISLNK(before.st_mode)
        or not stat.S_ISDIR(before.st_mode)
        or before.st_uid != os.geteuid()
        or before.st_gid != os.getegid()
        or stat.S_IMODE(before.st_mode) != 0o700
    ):
        raise AdaptiveSwitchEvidenceV4Error("target directory is unsafe")
    entries = sorted(item.name for item in path.iterdir())
    after = path.lstat()
    if (
        set(entries) != expected_names
        or len(entries) != len(expected_names)
        or not json_type_equal(
            base._stat_identity(before), base._stat_identity(after)
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "target directory inventory mismatch"
        )
    return {
        "relative_path": path.name,
        "identity": base._stat_identity(after),
        "entries": entries,
    }


def _stable_target_file(
    root: Path, relative: Path, *, cap: int,
) -> dict[str, Any]:
    path = root / relative
    payload, identity = base._stable_bytes(path, cap=cap)
    if (
        identity["mode"] != 0o600
        or identity["uid"] != os.geteuid()
        or identity["gid"] != os.getegid()
        or identity["links"] != 1
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "target static file mode/owner mismatch"
        )
    return {
        "relative_path": relative.as_posix(),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
        "identity": identity,
    }


def _validate_target_outer_fd(
    root: Path, source_fd: int,
) -> dict[str, Any]:
    if type(source_fd) is not int or source_fd < 0:
        raise AdaptiveSwitchEvidenceV4Error("target outer fd is malformed")
    lock_path = root / ".adaptive-child.lock"
    lexical = lock_path.lstat()
    flags = fcntl.fcntl(source_fd, fcntl.F_GETFL)
    descriptor_flags = fcntl.fcntl(source_fd, fcntl.F_GETFD)
    observed = os.fstat(source_fd)
    path_identity = base._stat_identity(lexical)
    fd_identity = base._stat_identity(observed)
    if (
        stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISREG(lexical.st_mode)
        or not json_type_equal(path_identity, fd_identity)
        or path_identity["mode"] != 0o600
        or path_identity["uid"] != os.geteuid()
        or path_identity["links"] != 1
        or path_identity["bytes"] != 0
        or (flags & os.O_ACCMODE) != os.O_RDWR
        or not descriptor_flags & fcntl.FD_CLOEXEC
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "target outer fd/path identity mismatch"
        )
    duplicate = fcntl.fcntl(source_fd, fcntl.F_DUPFD_CLOEXEC, 3)
    try:
        # This is the same open-file-description as source_fd.  It both
        # verifies and (if necessary) establishes the caller-owned EX flock.
        fcntl.flock(duplicate, fcntl.LOCK_EX | fcntl.LOCK_NB)
        probe = os.open(
            lock_path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW
        )
        try:
            try:
                fcntl.flock(probe, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                pass
            else:
                fcntl.flock(probe, fcntl.LOCK_UN)
                raise AdaptiveSwitchEvidenceV4Error(
                    "target outer lock is not exclusively held"
                )
        finally:
            os.close(probe)
    finally:
        os.close(duplicate)
    final = base._stat_identity(lock_path.lstat())
    if not json_type_equal(final, path_identity):
        raise AdaptiveSwitchEvidenceV4Error(
            "target outer lock changed during validation"
        )
    return path_identity


_V5_DECLARED_LOCK_IDENTITY_FIELDS = {
    "relative_path", "device", "inode", "uid", "mode", "links", "bytes",
}


def _compact_v5_switch_policy(observation_policy: Any) -> dict[str, Any]:
    """Validate the full switch policy, then project the v5 static fields."""

    if type(observation_policy) is not dict:
        raise AdaptiveSwitchEvidenceV4Error(
            "switch observation policy malformed"
        )
    try:
        rebuilt = base._observation_policy(
            observation_policy["timeout_seconds"],
            observation_policy["elapsed_seconds_by_lane"],
        )
    except Exception as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "switch observation policy malformed"
        ) from exc
    if not json_type_equal(observation_policy, rebuilt):
        raise AdaptiveSwitchEvidenceV4Error(
            "switch observation policy is noncanonical"
        )
    return {
        "timeout_seconds": rebuilt["timeout_seconds"],
        "elapsed_seconds_by_lane": list(
            rebuilt["elapsed_seconds_by_lane"]
        ),
    }


def _validate_v5_declared_outer_identity(
    value: Any, full_identity: Mapping[str, Any],
) -> dict[str, Any]:
    expected = {
        "relative_path": ".adaptive-child.lock",
        "device": full_identity["device"],
        "inode": full_identity["inode"],
        "uid": full_identity["uid"],
        "mode": full_identity["mode"],
        "links": full_identity["links"],
        "bytes": full_identity["bytes"],
    }
    if (
        type(value) is not dict
        or set(value) != _V5_DECLARED_LOCK_IDENTITY_FIELDS
        or type(value.get("relative_path")) is not str
        or any(
            type(value.get(field)) is not int
            for field in _V5_DECLARED_LOCK_IDENTITY_FIELDS
            - {"relative_path"}
        )
        or not json_type_equal(value, expected)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "v5 declared outer-lock identity mismatch"
        )
    return dict(value)


def _validate_unstarted_target_roots(
    root: Path, target_roots: list[Path],
    target_outer_lock_fds: list[int], switch_record: Mapping[str, Any],
) -> list[dict[str, Any]]:
    if (
        type(target_roots) is not list
        or type(target_outer_lock_fds) is not list
        or len(target_roots) != TARGET_COUNT
        or len(target_outer_lock_fds) != TARGET_COUNT
        or any(not isinstance(item, Path) for item in target_roots)
        or any(
            type(item) is not int or item < 0
            for item in target_outer_lock_fds
        )
        or len(set(target_roots)) != TARGET_COUNT
        or len(set(target_outer_lock_fds)) != TARGET_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "target root/fd cardinality mismatch"
        )
    lanes = switch_record.get("lanes")
    if type(lanes) is not list or len(lanes) != LANE_COUNT:
        raise AdaptiveSwitchEvidenceV4Error(
            "fresh switch lane table malformed"
        )
    compact_switch_policy = _compact_v5_switch_policy(
        switch_record.get("observation_policy")
    )
    expected_static_files = {
        "parent-manifest.json", "width6-campaign.json",
        "width10-campaign.json", "adaptive-overlay.json",
        "hard-evidence.json", "switch-evidence.json", "descendant.cnf",
    }
    observations: list[dict[str, Any]] = []
    for key, target, source_fd in zip(
        TARGET_KEYS, target_roots, target_outer_lock_fds, strict=True
    ):
        lane_index, descendant_index = key
        target = Path(target)
        root_identity = base._root_identity(target)
        lock_identity = _validate_target_outer_fd(target, source_fd)
        if set(item.name for item in target.iterdir()) != {
            ".adaptive-child.lock", "static", "state", "artifacts", "runtime",
        }:
            raise AdaptiveSwitchEvidenceV4Error(
                "unstarted target root inventory mismatch"
            )
        static_inventory = _stable_directory_inventory(
            target / "static", expected_names=expected_static_files
        )
        state_inventory = _stable_directory_inventory(
            target / "state", expected_names={"00-static.json", "actions"}
        )
        actions_inventory = _stable_directory_inventory(
            target / "state" / "actions", expected_names=set()
        )
        artifacts_inventory = _stable_directory_inventory(
            target / "artifacts", expected_names=set()
        )
        runtime_inventory = _stable_directory_inventory(
            target / "runtime", expected_names=set()
        )
        static_path = target / "state/00-static.json"
        static_record = base._read_json(static_path)
        pins = static_record.get("external_pins")
        selection = static_record.get("selection")
        lane = lanes[lane_index]
        static_fields = {
            "schema_version", "kind", "gate", "state", "authority",
            "test_only", "production_eligible", "root", "root_identity",
            "root_lock_identity", "batch_root_identity", "strict_base",
            "python_startup", "external_pins", "selection",
            "switch_policy", "material_files", "campaign_manifest_sha256",
            "overlay_manifest_sha256", "hard_evidence_sha256",
            "switch_evidence_sha256", "overlay_verification",
            "campaign_verification", "switch_structure_validation",
            "descendant", "descendant_cnf", "source_binding",
            "execution_module_binding", "toolchain_binding",
            "resource_policy", "launch_attestation", "resume_policy",
            "claim_scope", "publication_certificate",
            "upload_authorized", "record_sha256",
        }
        if (
            set(static_record) != static_fields
            or not selfhash_valid(static_record)
            or static_record.get("schema_version") != 5
            or type(static_record.get("schema_version")) is not int
            or static_record.get("kind")
                != "paper400-dic5-adaptive-child-resume-static-v5"
            or static_record.get("gate")
                != "paper400-dic5-adaptive-child-resume-v5"
            or static_record.get("state") != "RESUMABLE_STATIC_SEALED"
            or static_record.get("authority")
                != "TEST_ONLY_CANDIDATE_ONLY_V5"
            or static_record.get("test_only") is not True
            or static_record.get("production_eligible") is not False
            or static_record.get("strict_base") is not True
            or static_record.get("root") != str(target)
            or not json_type_equal(
                static_record.get("root_identity"), root_identity
            )
            or not json_type_equal(
                _validate_v5_declared_outer_identity(
                    static_record.get("root_lock_identity"),
                    lock_identity,
                ),
                static_record.get("root_lock_identity"),
            )
            or not json_type_equal(
                static_record.get("batch_root_identity"),
                base._root_identity(root),
            )
            or type(pins) is not dict
            or set(pins) != {
                "expected_overlay_sha256",
                "expected_hard_evidence_sha256",
                "expected_switch_evidence_sha256",
                "expected_batch_manifest_sha256",
            }
            or pins.get("expected_batch_manifest_sha256")
                != EXPECTED_BATCH_MANIFEST_SHA256
            or pins.get("expected_switch_evidence_sha256")
                != EXPECTED_SWITCH_EVIDENCE_SHA256
            or static_record.get("switch_evidence_sha256")
                != EXPECTED_SWITCH_EVIDENCE_SHA256
            or type(selection) is not dict
            or set(selection) != {
                "global_leaf_index", "descendant_index",
                "descendant_sha256", "adaptive_node_id",
                "relative_assignment_literals", "candidate_variables",
            }
            or selection.get("global_leaf_index")
                != lane.get("global_leaf_index")
            or selection.get("descendant_index") != descendant_index
            or not json_type_equal(
                static_record.get("switch_policy"),
                compact_switch_policy,
            )
            or static_record.get("hard_evidence_sha256")
                != lane.get("hard_evidence_sha256")
            or pins.get("expected_hard_evidence_sha256")
                != lane.get("hard_evidence_sha256")
            or static_record.get("publication_certificate") is not False
            or static_record.get("upload_authorized") is not False
            or static_record.get("launch_attestation") != {
                "serialized_overlay_launch_authorized": False,
                "serialized_switch_launch_authorized": False,
                "serialized_composite_launch_authorized": False,
                "candidate_exact_bytes_replayed": True,
                "atomic_switch_v4_lease_required": True,
                "strict_first_start_requires_complete_eight_root_cover": True,
                "adaptive_handoff_reentry_supported": False,
                "maximum_live_workers_during_handoff": MAX_LIVE_WORKERS,
            }
            or static_record.get("launch_attestation", {}).get(
                "atomic_switch_v4_lease_required"
            ) is not True
            or static_record.get("launch_attestation", {}).get(
                "strict_first_start_requires_complete_eight_root_cover"
            ) is not True
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "unstarted target static binding mismatch"
            )
        descendant = static_record.get("descendant")
        if (
            type(descendant) is not dict
            or descendant.get("descendant_index") != descendant_index
            or descendant.get("descendant_sha256")
                != selection.get("descendant_sha256")
            or descendant.get("pending") is not True
            or descendant.get("observed_status") != "PENDING"
            or descendant.get("solver_terminal_authenticated") is not False
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "unstarted target descendant binding mismatch"
            )
        material_files = [
            _stable_target_file(
                target, Path("state/00-static.json"),
                cap=base.MAX_JSON_BYTES,
            ),
            *[
                _stable_target_file(
                    target, Path("static") / name,
                    cap=(
                        MAX_PROOF_BYTES if name == "descendant.cnf"
                        else base.MAX_JSON_BYTES
                    ),
                )
                for name in sorted(expected_static_files)
            ],
        ]
        physical_by_relative = {
            item["relative_path"]: item for item in material_files
        }
        material_spec = {
            "parent_manifest":
                ("static/parent-manifest.json", "parent-manifest"),
            "width6_campaign":
                ("static/width6-campaign.json", "width6-campaign"),
            "width10_campaign":
                ("static/width10-campaign.json", "width10-campaign"),
            "adaptive_overlay":
                ("static/adaptive-overlay.json", "adaptive-overlay"),
            "hard_evidence":
                ("static/hard-evidence.json", "hard-evidence"),
            "switch_evidence":
                ("static/switch-evidence.json", "switch-evidence"),
            "descendant_cnf":
                ("static/descendant.cnf", "exact-descendant-cnf"),
        }
        declared_materials = static_record.get("material_files")
        if (
            type(declared_materials) is not dict
            or set(declared_materials) != set(material_spec)
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "target material declaration is malformed"
            )
        for role_key, (relative, role) in material_spec.items():
            physical = physical_by_relative[relative]
            identity = physical["identity"]
            expected_material = {
                "role": role, "relative_path": relative,
                "sha256": physical["sha256"], "bytes": physical["bytes"],
                "device": identity["device"], "inode": identity["inode"],
                "uid": identity["uid"], "mode": identity["mode"],
                "links": identity["links"],
            }
            if not json_type_equal(
                declared_materials[role_key], expected_material
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "target material bytes/identity miss static record"
                )
        # Recheck the root/lock/static record after the full inventory.
        if (
            not json_type_equal(base._root_identity(target), root_identity)
            or not json_type_equal(
                _validate_target_outer_fd(target, source_fd), lock_identity
            )
            or not json_type_equal(
                base._read_json(static_path), static_record
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "unstarted target changed during admission"
            )
        observations.append({
            "lane_index": lane_index,
            "descendant_index": descendant_index,
            "global_leaf_index": lane["global_leaf_index"],
            "root_identity": root_identity,
            "outer_lock_identity": lock_identity,
            "static_record_sha256": static_record["record_sha256"],
            "descendant_sha256": selection["descendant_sha256"],
            "hard_evidence_sha256": lane["hard_evidence_sha256"],
            "overlay_manifest_sha256":
                static_record["overlay_manifest_sha256"],
            "candidate_variables":
                list(selection["candidate_variables"]),
            "relative_assignment_literals":
                list(selection["relative_assignment_literals"]),
            "material_files": material_files,
            "directory_inventory": [
                static_inventory, state_inventory, actions_inventory,
                artifacts_inventory, runtime_inventory,
            ],
            "session_absent": True,
            "handoff_link_absent": True,
            "terminal_bundle_absent": True,
            "solver_never_started": True,
        })
    paths = [Path(item["root_identity"]["path"]) for item in observations]
    root_inodes = {
        (item["root_identity"]["device"], item["root_identity"]["inode"])
        for item in observations
    }
    lock_inodes = {
        (
            item["outer_lock_identity"]["device"],
            item["outer_lock_identity"]["inode"],
        )
        for item in observations
    }
    if (
        len(root_inodes) != TARGET_COUNT
        or len(lock_inodes) != TARGET_COUNT
        or any(
            path.is_relative_to(root) or root.is_relative_to(path)
            for path in paths
        )
        or any(
            left != right
            and (
                left.is_relative_to(right)
                or right.is_relative_to(left)
            )
            for left in paths for right in paths
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "target paths/inodes overlap or alias"
        )
    for lane_index in range(LANE_COUNT):
        pair = [
            observations[TARGET_KEYS.index((lane_index, descendant))]
            for descendant in range(DESCENDANT_COUNT)
        ]
        if any(
            pair[0][field] != pair[1][field]
            for field in (
                "global_leaf_index", "hard_evidence_sha256",
                "overlay_manifest_sha256", "candidate_variables",
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "sibling target policy mismatch"
            )
    return observations


def _fresh_old_lane_observations(
    root: Path, snapshot: Mapping[str, Any],
    switch_record: Mapping[str, Any], child: Any,
) -> list[dict[str, Any]]:
    """Bind lstat metadata to the proof hash from the one fresh v2 replay."""

    result: list[dict[str, Any]] = []
    runtime_lanes = snapshot.get("lanes")
    switch_lanes = switch_record.get("lanes")
    if (
        type(runtime_lanes) is not list or len(runtime_lanes) != LANE_COUNT
        or type(switch_lanes) is not list or len(switch_lanes) != LANE_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "fresh old lane cardinality mismatch"
        )
    for lane_index, (runtime, lane) in enumerate(
        zip(runtime_lanes, switch_lanes, strict=True)
    ):
        (
            expected_global, expected_transport, expected_proof,
            expected_proof_bytes, expected_hard,
        ) = EXPECTED_OLD_LANE_TUPLES[lane_index]
        chain = runtime.get("chain")
        generations = chain.get("generations") if type(chain) is dict else None
        if type(generations) is not list or not generations:
            raise AdaptiveSwitchEvidenceV4Error(
                "old transport has no generation"
            )
        active = generations[-1]
        pid = active.get("pid")
        ticks = active.get("proc_start_ticks")
        if (
            type(pid) is not int or pid <= 0
            or type(ticks) is not int or ticks <= 0
            or child.controller._pid_identity(pid, ticks)
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "old solver identity is live/malformed"
            )
        lane_root = root / "lanes" / f"lane-{lane_index}"
        proof = lane_root / child.RUNTIME_ROOT / "proof.drat"
        proof_stat = os.stat(proof, follow_symlinks=False)
        proof_identity = base._stat_identity(proof_stat)
        holders = _writable_holders(
            proof, expected_identity=proof_identity
        )
        prefix = lane.get("checkpoint_proof_prefix")
        physical = lane.get("checkpoint_proof_physical")
        physical_fields = {
            "role", "relative_path", "file_sha256", "bytes", "device",
            "inode", "uid", "mode", "links",
        }
        physical_identity_fields = {
            "device", "inode", "uid", "mode", "links", "bytes",
        }
        if (
            lane.get("lane_index") != lane_index
            or type(lane.get("global_leaf_index")) is not int
            or lane.get("global_leaf_index") != expected_global
            or lane.get("transport_chain_sha256") != expected_transport
            or lane.get("hard_evidence_sha256") != expected_hard
            or lane.get("solver_stopped") is not True
            or lane.get("terminal_claimed") is not False
            or lane.get("terminal_committed") is not False
            or type(prefix) is not dict
            or type(physical) is not dict
            or set(physical) != physical_fields
            or tuple(
                physical.get(field) for field in (
                    "device", "inode", "uid", "mode", "links", "bytes",
                )
            ) != EXPECTED_OLD_PROOF_PHYSICAL_TUPLES[lane_index]
            or not json_type_equal(
                chain.get("latest_proof_prefix"), prefix
            )
            or not json_type_equal(
                chain.get("latest_proof_physical"), physical
            )
            or lane.get("transport_chain_sha256")
                != chain.get("record_sha256")
            or prefix.get("sha256") != physical.get("file_sha256")
            or prefix.get("bytes") != physical.get("bytes")
            or prefix.get("sha256") != expected_proof
            or type(prefix.get("bytes")) is not int
            or prefix.get("bytes") != expected_proof_bytes
            or prefix.get("path") != "proof.drat"
            or prefix.get("path_kind") != "root_relative"
            or physical.get("role") != "raw-binary-drat"
            or physical.get("relative_path")
                != (child.RUNTIME_ROOT / "proof.drat").as_posix()
            or any(
                proof_identity[field] != physical[field]
                for field in physical_identity_fields
            )
            or not stat.S_ISREG(proof_stat.st_mode)
            or proof_identity["uid"] != os.geteuid()
            or proof_identity["gid"] != os.getegid()
            or proof_identity["mode"] != 0o600
            or proof_identity["links"] != 1
            or holders != []
            or (lane_root / child.TERMINAL_CLAIM).exists()
            or (lane_root / child.TERMINAL_CLAIM).is_symlink()
            or (lane_root / child.FINAL_COMMIT).exists()
            or (lane_root / child.FINAL_COMMIT).is_symlink()
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "old stopped proof observation mismatch"
            )
        result.append({
            "lane_index": lane_index,
            "global_leaf_index": lane["global_leaf_index"],
            "transport_chain_sha256": lane["transport_chain_sha256"],
            "hard_evidence_sha256": lane["hard_evidence_sha256"],
            "old_pid": pid,
            "old_proc_start_ticks": ticks,
            "pid_identity_alive": False,
            "proof_sha256": prefix["sha256"],
            "proof_bytes": prefix["bytes"],
            "proof_identity": proof_identity,
            "writable_holders": [],
            "terminal_claimed": False,
            "terminal_committed": False,
        })
    return result


def _lightweight_old_checkpoint_fence(
    root: Path, snapshot: Mapping[str, Any],
    incident: Mapping[str, Any], child: Any,
) -> None:
    """Recheck stopped old lanes without reading any proof contents."""

    runtime_lanes = snapshot.get("lanes")
    old_lanes = incident.get("fresh_old_lanes")
    if (
        type(runtime_lanes) is not list
        or len(runtime_lanes) != LANE_COUNT
        or type(old_lanes) is not list
        or len(old_lanes) != LANE_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "lightweight old-lane cardinality mismatch"
        )
    for lane_index, (runtime_lane, expected) in enumerate(
        zip(runtime_lanes, old_lanes, strict=True)
    ):
        chain = runtime_lane.get("chain")
        generations = (
            chain.get("generations") if type(chain) is dict else None
        )
        inspection = runtime_lane.get("inspection")
        inspect_generations = (
            inspection.get("generations")
            if type(inspection) is dict else None
        )
        if (
            type(generations) is not list or not generations
            or type(inspect_generations) is not list
            or not inspect_generations
            or type(expected) is not dict
            or expected.get("lane_index") != lane_index
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "lightweight old-lane snapshot is malformed"
            )
        generation_numbers = [
            item.get("generation") for item in generations
        ]
        active_summary = generations[-1]
        inspect_latest = inspect_generations[-1]
        generation = active_summary.get("generation")
        pid = active_summary.get("pid")
        ticks = active_summary.get("proc_start_ticks")
        runtime_root = (
            root / "lanes" / f"lane-{lane_index}"
            / child.RUNTIME_ROOT
        )
        try:
            with child._fixed_environment():
                current_numbers = child.controller._generation_numbers(
                    runtime_root
                )
                generation_dir = (
                    runtime_root / "generations" / f"{generation:06d}"
                )
                poison = child.controller._claim_without_commit(
                    generation_dir
                )
                active_manifest = child.controller._active_commit(
                    generation_dir, generation
                )
                checkpoint_manifest = child.controller._checkpoint_commit(
                    generation_dir, generation
                )
        except Exception as exc:
            raise AdaptiveSwitchEvidenceV4Error(
                "old controller metadata fence failed"
            ) from exc
        prefix = chain.get("latest_proof_prefix")
        physical = chain.get("latest_proof_physical")
        proof = runtime_root / "proof.drat"
        proof_identity = base._stat_identity(
            os.stat(proof, follow_symlinks=False)
        )
        terminal_claim = (
            root / "lanes" / f"lane-{lane_index}"
            / child.TERMINAL_CLAIM
        )
        final_commit = (
            root / "lanes" / f"lane-{lane_index}"
            / child.FINAL_COMMIT
        )
        if (
            generation_numbers != list(range(len(generations)))
            or current_numbers != generation_numbers
            or type(generation) is not int
            or generation < 0
            or type(pid) is not int or pid <= 0
            or type(ticks) is not int or ticks <= 0
            or expected.get("old_pid") != pid
            or expected.get("old_proc_start_ticks") != ticks
            or child.controller._pid_identity(pid, ticks)
            or chain.get("state") != "CHECKPOINTED"
            or chain.get("record_sha256")
                != expected.get("transport_chain_sha256")
            or type(prefix) is not dict
            or type(physical) is not dict
            or prefix.get("sha256") != expected.get("proof_sha256")
            or prefix.get("bytes") != expected.get("proof_bytes")
            or physical.get("file_sha256")
                != expected.get("proof_sha256")
            or physical.get("bytes") != expected.get("proof_bytes")
            or inspection.get("state") != "CHECKPOINTED"
            or inspection.get("hash_verification_requested") is not True
            or inspect_latest.get("generation") != generation
            or inspect_latest.get("pid_identity_alive") is not False
            or inspect_latest.get("checkpoint_hashes_valid") is not True
            or inspect_latest.get("active_manifest_sha256")
                != active_summary.get("active_manifest_sha256")
            or inspect_latest.get("checkpoint_manifest_sha256")
                != active_summary.get("checkpoint_manifest_sha256")
            or poison is not None
            or active_manifest.get("kind")
                != active_summary.get("active_kind")
            or active_manifest.get("self_sha256")
                != active_summary.get("active_manifest_sha256")
            or active_manifest.get("pid") != pid
            or active_manifest.get("proc_start_ticks") != ticks
            or checkpoint_manifest.get("kind") != "checkpoint.commit"
            or checkpoint_manifest.get("self_sha256")
                != chain.get("latest_checkpoint_sha256")
            or checkpoint_manifest.get("self_sha256")
                != active_summary.get("checkpoint_manifest_sha256")
            or checkpoint_manifest.get("single_writer_stopped") is not True
            or not json_type_equal(
                checkpoint_manifest.get("proof_prefix"), prefix
            )
            or not json_type_equal(
                proof_identity, expected.get("proof_identity")
            )
            or _writable_holders(
                proof, expected_identity=expected["proof_identity"]
            ) != []
            or terminal_claim.exists() or terminal_claim.is_symlink()
            or final_commit.exists() or final_commit.is_symlink()
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "old stopped checkpoint changed after fresh replay"
            )


def _build_incident_precondition_locked(
    root: Path, locks: Sequence[Any], *,
    target_roots: list[Path], target_outer_lock_fds: list[int],
    snapshot: Mapping[str, Any], switch_record: Mapping[str, Any],
    child: Any,
) -> dict[str, Any]:
    historical = _validate_failed_v3_incident_locked(root, locks)
    targets = _validate_unstarted_target_roots(
        root, target_roots, target_outer_lock_fds, switch_record
    )
    old_lanes = _fresh_old_lane_observations(
        root, snapshot, switch_record, child
    )
    if [
        lane["hard_evidence_sha256"]
        for lane in switch_record["lanes"]
    ] != list(EXPECTED_HARD_EVIDENCE_SHA256S):
        raise AdaptiveSwitchEvidenceV4Error(
            "fresh switch replay misses fixed hard-evidence pins"
        )
    if (root / ATTEMPT_ROOT).exists() or (root / ATTEMPT_ROOT).is_symlink():
        raise AdaptiveSwitchEvidenceV4Error(
            "v4 namespace appeared during readonly admission"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-dic5-adaptive-incident-precondition-v4",
        "gate": GATE,
        "attempt_id": ATTEMPT_ID,
        "fixed_attempt_namespace": ATTEMPT_ROOT.as_posix(),
        "test_only": True,
        "production_eligible": False,
        "authenticated": False,
        "launch_authorized": False,
        "scientific_claim": False,
        "batch_root": str(root),
        "batch_root_identity": base._root_identity(root),
        "batch_manifest_sha256": EXPECTED_BATCH_MANIFEST_SHA256,
        "switch_evidence_sha256": EXPECTED_SWITCH_EVIDENCE_SHA256,
        "switch_observation_policy":
            dict(switch_record["observation_policy"]),
        "hard_evidence_sha256s": [
            lane["hard_evidence_sha256"]
            for lane in switch_record["lanes"]
        ],
        "failed_attempt": historical,
        "fresh_old_lanes": old_lanes,
        "target_roots": targets,
        "target_key_order": [
            {"lane_index": lane, "descendant_index": descendant}
            for lane, descendant in TARGET_KEYS
        ],
        "readonly_precondition": {
            "failed_v3_artifacts_preserved_in_place": True,
            "failed_v3_prepared_is_not_reused": True,
            "nine_old_entrypoints_restored": True,
            "eight_targets_static_and_never_started": True,
            "old_batch_fresh_exact_replay": True,
            "old_solver_identities_dead": True,
            "old_proofs_have_no_same_euid_writer": True,
            "attempt_namespace_absent": True,
            "filesystem_mutations_performed": False,
        },
        "source_binding": _v4_source_binding(),
        "claim_scope": {
            "incident_record_can_authorize_launch": False,
            "serialized_record_can_authorize_launch": False,
            "only_same_process_lease_after_fresh_rebuild_can_launch": True,
            "checkpoint_proves_unsat": False,
            "scientific_claim": False,
        },
    })


_STAT_IDENTITY_FIELDS = {
    "device", "inode", "mode", "uid", "gid", "links",
    "bytes", "mtime_ns", "ctime_ns",
}
_ROOT_IDENTITY_FIELDS = {"path", "device", "inode", "uid", "mode"}


def _stat_identity_shape(value: Any) -> bool:
    return (
        type(value) is dict
        and set(value) == _STAT_IDENTITY_FIELDS
        and all(type(value[field]) is int for field in _STAT_IDENTITY_FIELDS)
    )


def _root_identity_shape(value: Any) -> bool:
    return (
        type(value) is dict
        and set(value) == _ROOT_IDENTITY_FIELDS
        and type(value.get("path")) is str
        and all(
            type(value[field]) is int
            for field in _ROOT_IDENTITY_FIELDS - {"path"}
        )
    )


def _identity_without_ctime(identity: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(identity)
    result.pop("ctime_ns", None)
    return result


def _retire_lock_v3(held: Any, retired_path: Path) -> dict[str, Any]:
    original = Path(held.original_path)
    retired = Path(retired_path)
    if (
        Path(held.current_path) != original
        or retired.parent != original.parent
        or retired.name == original.name
        or retired.exists() or retired.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV4Error("unsafe v3 retirement target")
    lexical = original.lstat()
    pre = base._stat_identity(os.fstat(held.fd))
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or not json_type_equal(base._stat_identity(lexical), pre)
        or not json_type_equal(pre, held.identity)
        or pre["uid"] != os.geteuid() or pre["mode"] != 0o600
        or pre["links"] != 1 or pre["bytes"] != 0
    ):
        raise AdaptiveSwitchEvidenceV4Error("held legacy lock changed")
    os.rename(original, retired)
    # Record the new pathname immediately so any later fsync/validation fault
    # can be compensated before a launch-capable lease is returned.
    held.current_path = retired
    held.identity = base._stat_identity(os.fstat(held.fd))
    _fsync_directory(retired.parent)
    post_path = base._stat_identity(retired.lstat())
    post_fd = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(post_path, post_fd)
        or not json_type_equal(
            _identity_without_ctime(pre), _identity_without_ctime(post_fd)
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error("retired legacy lock identity changed")
    held.current_path = retired
    held.identity = post_fd
    return {
        "role": held.role, "original_path": str(original),
        "retired_path": str(retired), "pre_rename_identity": pre,
        "identity": post_fd,
    }


def _restore_lock_v3(held: Any, record: Mapping[str, Any]) -> dict[str, Any]:
    original = Path(record["original_path"])
    retired = Path(record["retired_path"])
    if (
        Path(held.original_path) != original or Path(held.current_path) != retired
        or original.exists() or original.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV4Error("unsafe v3 restore target")
    path_identity = base._stat_identity(retired.lstat())
    fd_identity = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(path_identity, record["identity"])
        or not json_type_equal(fd_identity, record["identity"])
    ):
        raise AdaptiveSwitchEvidenceV4Error("retired lock changed before restore")
    os.rename(retired, original)
    _fsync_directory(original.parent)
    restored_path = base._stat_identity(original.lstat())
    restored_fd = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(restored_path, restored_fd)
        or not json_type_equal(
            _identity_without_ctime(fd_identity),
            _identity_without_ctime(restored_fd),
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error("restored lock identity changed")
    held.current_path = original
    held.identity = restored_fd
    return {
        "role": held.role, "original_path": str(original),
        "retired_path": str(retired), "identity": restored_fd,
    }


def _restore_current_lock_v3(
    held: Any, *, original_path: Path, retired_path: Path,
) -> dict[str, Any] | None:
    original = Path(original_path)
    retired = Path(retired_path)
    if Path(held.current_path) == original:
        return None
    if Path(held.current_path) != retired:
        raise AdaptiveSwitchEvidenceV4Error(
            "held lock has an unknown compensation path"
        )
    path_identity = base._stat_identity(retired.lstat())
    fd_identity = base._stat_identity(os.fstat(held.fd))
    if not json_type_equal(path_identity, fd_identity):
        raise AdaptiveSwitchEvidenceV4Error(
            "retired inode changed before compensation"
        )
    held.identity = fd_identity
    return _restore_lock_v3(held, {
        "original_path": str(original),
        "retired_path": str(retired),
        "identity": fd_identity,
    })


def _stream_hash_size_identity(
    path: Path, *, cap: int = MAX_PROOF_BYTES,
) -> tuple[str, int, dict[str, int]]:
    candidate = Path(path)
    lexical = candidate.lstat()
    if (
        stat.S_ISLNK(lexical.st_mode) or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid() or lexical.st_nlink != 1
        or lexical.st_size < 0 or lexical.st_size > cap
    ):
        raise AdaptiveSwitchEvidenceV4Error("unsafe proof prefix")
    fd = os.open(candidate, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    digest = hashlib.sha256()
    total = 0
    try:
        before = os.fstat(fd)
        if not json_type_equal(
            base._stat_identity(before), base._stat_identity(lexical)
        ):
            raise AdaptiveSwitchEvidenceV4Error("proof changed before streaming")
        while True:
            chunk = os.read(fd, 1 << 20)
            if not chunk:
                break
            total += len(chunk)
            if total > cap:
                raise AdaptiveSwitchEvidenceV4Error("proof exceeds streaming cap")
            digest.update(chunk)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    if (
        not json_type_equal(
            base._stat_identity(before), base._stat_identity(after)
        )
        or total != before.st_size
    ):
        raise AdaptiveSwitchEvidenceV4Error("proof changed while streaming")
    return digest.hexdigest(), total, base._stat_identity(after)


def _stream_hash_size(
    path: Path, *, cap: int = MAX_PROOF_BYTES,
) -> tuple[str, int]:
    digest, total, _ = _stream_hash_size_identity(path, cap=cap)
    return digest, total


def _validate_quiescence_record(record: Any) -> dict[str, Any]:
    expected_fields = {
        "schema_version", "kind", "lane_index", "descendant_index",
        "new_root_identity", "new_pid", "new_proc_start_ticks",
        "state", "pid_identity_alive", "checkpoint_commit_sha256",
        "proof_sha256", "proof_bytes", "writable_holders", "record_sha256",
    }
    if (
        type(record) is not dict or set(record) != expected_fields
        or not selfhash_valid(record)
        or type(record.get("schema_version")) is not int
        or record.get("schema_version") != 5
        or record.get("kind") != QUIESCENCE_INPUT_KIND
        or type(record.get("lane_index")) is not int
        or record["lane_index"] not in range(LANE_COUNT)
        or type(record.get("descendant_index")) is not int
        or record["descendant_index"] not in range(DESCENDANT_COUNT)
        or type(record.get("new_pid")) is not int or record["new_pid"] <= 0
        or type(record.get("new_proc_start_ticks")) is not int
        or record["new_proc_start_ticks"] <= 0
        or type(record.get("new_root_identity")) is not dict
        or type(record["new_root_identity"].get("path")) is not str
        or record.get("state") not in {
            "CHECKPOINTED", "INACTIVE_UNCHECKPOINTED",
        }
        or record.get("pid_identity_alive") is not False
        or (
            record.get("state") == "CHECKPOINTED"
            and not base._is_sha256(
                record.get("checkpoint_commit_sha256")
            )
        )
        or (
            record.get("state") == "INACTIVE_UNCHECKPOINTED"
            and record.get("checkpoint_commit_sha256") is not None
        )
        or record.get("writable_holders") != []
        or not base._is_sha256(record.get("proof_sha256"))
        or type(record.get("proof_bytes")) is not int
        or record["proof_bytes"] < 0 or record["proof_bytes"] > MAX_PROOF_BYTES
    ):
        raise AdaptiveSwitchEvidenceV4Error("quiescence record invalid")
    return dict(record)


def _seal_v4_quiescence_journal(
    record: Mapping[str, Any], incident_precondition_sha256: str,
) -> dict[str, Any]:
    checked = _validate_quiescence_record(record)
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": QUIESCENCE_KIND,
        "lane_index": checked["lane_index"],
        "descendant_index": checked["descendant_index"],
        "new_root_identity": dict(checked["new_root_identity"]),
        "new_pid": checked["new_pid"],
        "new_proc_start_ticks": checked["new_proc_start_ticks"],
        "state": checked["state"],
        "pid_identity_alive": checked["pid_identity_alive"],
        "checkpoint_commit_sha256":
            checked["checkpoint_commit_sha256"],
        "proof_sha256": checked["proof_sha256"],
        "proof_bytes": checked["proof_bytes"],
        "writable_holders": list(checked["writable_holders"]),
        "input_observation_sha256": checked["record_sha256"],
        "authenticated": False,
        "launch_authorized": False,
        **_attempt_binding(incident_precondition_sha256),
    })


def _validate_v4_quiescence_journal(
    record: Any, incident_precondition_sha256: str,
) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "lane_index", "descendant_index",
        "new_root_identity", "new_pid", "new_proc_start_ticks",
        "state", "pid_identity_alive", "checkpoint_commit_sha256",
        "proof_sha256", "proof_bytes", "writable_holders",
        "input_observation_sha256", "authenticated",
        "launch_authorized", "attempt_id",
        "incident_precondition_sha256", "failed_v3_intent_sha256",
        "failed_v3_prepared_sha256", "record_sha256",
    }
    if (
        type(record) is not dict or set(record) != fields
        or not selfhash_valid(record)
        or record.get("schema_version") != SCHEMA_VERSION
        or type(record.get("schema_version")) is not int
        or record.get("kind") != QUIESCENCE_KIND
        or record.get("authenticated") is not False
        or record.get("launch_authorized") is not False
        or not _root_identity_shape(record.get("new_root_identity"))
        or type(record.get("writable_holders")) is not list
        or record.get("writable_holders") != []
        or not base._is_sha256(record.get("input_observation_sha256"))
        or not _attempt_binding_valid(
            record, incident_precondition_sha256
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "v4 quiescence journal schema/binding mismatch"
        )
    neutral = {
        "schema_version": 5,
        "kind": QUIESCENCE_INPUT_KIND,
        "lane_index": record["lane_index"],
        "descendant_index": record["descendant_index"],
        "new_root_identity": dict(record["new_root_identity"]),
        "new_pid": record["new_pid"],
        "new_proc_start_ticks": record["new_proc_start_ticks"],
        "state": record["state"],
        "pid_identity_alive": record["pid_identity_alive"],
        "checkpoint_commit_sha256":
            record["checkpoint_commit_sha256"],
        "proof_sha256": record["proof_sha256"],
        "proof_bytes": record["proof_bytes"],
        "writable_holders": list(record["writable_holders"]),
        "record_sha256": record["input_observation_sha256"],
    }
    _validate_quiescence_record(neutral)
    return dict(record)


def _stable_owned_json(path: Path) -> dict[str, Any]:
    candidate = Path(path)
    try:
        resolved = candidate.resolve(strict=True)
    except (OSError, RuntimeError) as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "committed JSON path cannot be resolved"
        ) from exc
    if not candidate.is_absolute() or candidate != resolved:
        raise AdaptiveSwitchEvidenceV4Error(
            "committed JSON path is noncanonical"
        )
    payload, identity = base._stable_bytes(
        candidate, cap=base.MAX_JSON_BYTES,
    )
    after = base._stat_identity(candidate.lstat())
    if (
        identity["mode"] != 0o600
        or identity["uid"] != os.geteuid()
        or identity["gid"] != os.getegid()
        or identity["links"] != 1
        or not json_type_equal(after, identity)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "committed JSON metadata is unsafe or changed"
        )
    try:
        value = json.loads(payload.decode("ascii"))
        base._strict_json(value, label="committed JSON")
    except Exception as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "committed JSON payload is malformed"
        ) from exc
    if (
        type(value) is not dict
        or payload != canonical_bytes(value) + b"\n"
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "committed JSON payload is not canonical"
        )
    return value


def _verify_attempt_inventory(
    root: Path, *, handoff_published: bool,
) -> None:
    if type(handoff_published) is not bool:
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff publication state is malformed"
        )
    attempt_names = {
        INCIDENT_PRECONDITION.name, RETIREMENT_INTENT.name,
        PREPARED_COMMIT.name, TARGET_DIRECTORY.name,
        STARTED_DIRECTORY.name, QUIESCENCE_DIRECTORY.name,
    }
    if handoff_published:
        attempt_names.add(HANDOFF_COMMIT.name)
    target_names = {
        f"lane-{lane}-descendant-{descendant}.json"
        for lane, descendant in TARGET_KEYS
    }
    quiescence_names = {
        f"lane-{lane}-descendant-0.json"
        for lane in range(LANE_COUNT)
    }
    _stable_directory_inventory(
        root / ATTEMPT_ROOT, expected_names=attempt_names,
    )
    _stable_directory_inventory(
        root / TARGET_DIRECTORY, expected_names=target_names,
    )
    _stable_directory_inventory(
        root / STARTED_DIRECTORY, expected_names=target_names,
    )
    _stable_directory_inventory(
        root / QUIESCENCE_DIRECTORY,
        expected_names=quiescence_names,
    )
def _read_handoff_journal(
    path: Path, *, expected_fields: set[str], expected_kind: str,
) -> dict[str, Any]:
    value = _stable_owned_json(path)
    lexical = path.lstat()
    if (
        set(value) != expected_fields
        or not selfhash_valid(value)
        or value.get("schema_version") != SCHEMA_VERSION
        or type(value.get("schema_version")) is not int
        or value.get("kind") != expected_kind
        or value.get("authenticated") is not False
        or value.get("launch_authorized") is not False
        or stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or stat.S_IMODE(lexical.st_mode) != 0o600
        or lexical.st_nlink != 1
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff journal schema/ownership mismatch"
        )
    return value


def _verify_committed_journals(
    root: Path, record: Mapping[str, Any], *,
    handoff_published: bool = True,
) -> list[dict[str, Any]]:
    _verify_attempt_inventory(
        root, handoff_published=handoff_published,
    )
    target_fields = {
        "schema_version", "kind", "authenticated", "launch_authorized",
        "lane_index", "global_leaf_index", "descendant_index",
        "descendant_sha256", "overlay_manifest_sha256",
        "hard_evidence_sha256", "permit_binding_sha256",
        "new_root_identity", "switch_evidence_sha256",
        "prepared_retirement_sha256", "target_static_sha256",
        "target_outer_lock_identity", "attempt_id",
        "incident_precondition_sha256", "failed_v3_intent_sha256",
        "failed_v3_prepared_sha256", "record_sha256",
    }
    started_fields = {
        "schema_version", "kind", "authenticated", "launch_authorized",
        "lane_index", "descendant_index", "prepared_target_sha256",
        "permit_binding_sha256", "new_root_identity", "new_pid",
        "new_proc_start_ticks", "switch_evidence_sha256",
        "prepared_retirement_sha256", "attempt_id",
        "incident_precondition_sha256", "failed_v3_intent_sha256",
        "failed_v3_prepared_sha256", "record_sha256",
    }
    bindings = record.get("root_bindings")
    if type(bindings) is not list or len(bindings) != TARGET_COUNT:
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff journal binding cardinality mismatch"
        )
    incident = _validate_incident_file(
        root, record["incident_precondition_sha256"]
    )
    if (
        record.get("batch_root") != incident.get("batch_root")
        or not json_type_equal(
            record.get("batch_root_identity"),
            incident.get("batch_root_identity"),
        )
        or record.get("batch_manifest_sha256")
            != incident.get("batch_manifest_sha256")
        or record.get("switch_evidence_sha256")
            != incident.get("switch_evidence_sha256")
        or not json_type_equal(
            record.get("switch_observation_policy"),
            incident.get("switch_observation_policy"),
        )
        or not json_type_equal(
            record.get("source_binding"), incident.get("source_binding")
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff commit misses incident precondition"
        )
    verified: list[dict[str, Any]] = []
    for key, binding in zip(TARGET_KEYS, bindings, strict=True):
        if (
            type(binding) is not dict
            or (
                binding.get("lane_index"),
                binding.get("descendant_index"),
            ) != key
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "handoff journal target order mismatch"
            )
        target_path = (
            root / TARGET_DIRECTORY
            / f"lane-{key[0]}-descendant-{key[1]}.json"
        )
        started_path = (
            root / STARTED_DIRECTORY
            / f"lane-{key[0]}-descendant-{key[1]}.json"
        )
        target = _read_handoff_journal(
            target_path, expected_fields=target_fields,
            expected_kind="paper400-adaptive-prepared-target-v4",
        )
        started = _read_handoff_journal(
            started_path, expected_fields=started_fields,
            expected_kind="paper400-adaptive-started-worker-v4",
        )
        root_identity = binding.get("new_root_identity")
        incident_target = incident["target_roots"][
            TARGET_KEYS.index(key)
        ]
        if (
            type(target.get("lane_index")) is not int
            or type(target.get("global_leaf_index")) is not int
            or type(target.get("descendant_index")) is not int
            or (target["lane_index"], target["descendant_index"]) != key
            or target["global_leaf_index"]
                != binding.get("global_leaf_index")
            or target.get("descendant_sha256")
                != binding.get("descendant_sha256")
            or target.get("global_leaf_index") != incident_target.get("global_leaf_index")
            or target.get("descendant_sha256")
                != incident_target.get("descendant_sha256")
            or target.get("overlay_manifest_sha256")
                != incident_target.get("overlay_manifest_sha256")
            or target.get("hard_evidence_sha256")
                != incident_target.get("hard_evidence_sha256")
            or not json_type_equal(
                target.get("new_root_identity"),
                incident_target.get("root_identity"),
            )
            or target.get("permit_binding_sha256")
                != binding.get("permit_binding_sha256")
            or target.get("target_static_sha256")
                != incident_target.get("static_record_sha256")
            or not json_type_equal(
                target.get("target_outer_lock_identity"),
                incident_target.get("outer_lock_identity"),
            )
            or target.get("record_sha256")
                != binding.get("prepared_target_sha256")
            or target.get("switch_evidence_sha256")
                != record.get("switch_evidence_sha256")
            or target.get("prepared_retirement_sha256")
                != record.get("prepared_retirement_sha256")
            or not _attempt_binding_valid(
                target, record["incident_precondition_sha256"]
            )
            or target.get("incident_precondition_sha256")
                != record.get("incident_precondition_sha256")
            or any(
                not base._is_sha256(target.get(field))
                for field in (
                    "descendant_sha256", "overlay_manifest_sha256",
                    "hard_evidence_sha256", "permit_binding_sha256",
                    "record_sha256",
                )
            )
            or type(root_identity) is not dict
            or not json_type_equal(
                target.get("new_root_identity"), root_identity
            )
            or not json_type_equal(
                base._root_identity(Path(root_identity.get("path", ""))),
                root_identity,
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "prepared-target journal misses commit"
            )
        if (
            type(started.get("lane_index")) is not int
            or type(started.get("descendant_index")) is not int
            or (started["lane_index"], started["descendant_index"]) != key
            or started.get("prepared_target_sha256")
                != target["record_sha256"]
            or started.get("permit_binding_sha256")
                != binding.get("permit_binding_sha256")
            or started.get("record_sha256")
                != binding.get("started_worker_journal_sha256")
            or started.get("switch_evidence_sha256")
                != record.get("switch_evidence_sha256")
            or started.get("prepared_retirement_sha256")
                != record.get("prepared_retirement_sha256")
            or not _attempt_binding_valid(
                started, record["incident_precondition_sha256"]
            )
            or started.get("incident_precondition_sha256")
                != record.get("incident_precondition_sha256")
            or not json_type_equal(
                started.get("new_root_identity"), root_identity
            )
            or started.get("new_pid") != binding.get("new_pid")
            or started.get("new_proc_start_ticks")
                != binding.get("new_proc_start_ticks")
            or type(started.get("new_pid")) is not int
            or type(started.get("new_proc_start_ticks")) is not int
            or started["new_pid"] <= 0
            or started["new_proc_start_ticks"] <= 0
            or any(
                not base._is_sha256(started.get(field))
                for field in (
                    "prepared_target_sha256", "permit_binding_sha256",
                    "record_sha256",
                )
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "started-worker journal misses commit"
            )
        quiescence_path = (
            root / QUIESCENCE_DIRECTORY
            / f"lane-{key[0]}-descendant-{key[1]}.json"
        )
        if key[1] == 0:
            quiescence = _validate_v4_quiescence_journal(
                base._read_json(quiescence_path),
                record["incident_precondition_sha256"],
            )
            lexical = quiescence_path.lstat()
            if (
                stat.S_ISLNK(lexical.st_mode)
                or not stat.S_ISREG(lexical.st_mode)
                or lexical.st_uid != os.geteuid()
                or stat.S_IMODE(lexical.st_mode) != 0o600
                or lexical.st_nlink != 1
                or quiescence["state"] != "CHECKPOINTED"
                or (
                    quiescence["lane_index"],
                    quiescence["descendant_index"],
                ) != key
                or quiescence["record_sha256"]
                    != binding.get("cohort_quiescence_sha256")
                or quiescence["new_pid"] != binding.get("new_pid")
                or quiescence["new_proc_start_ticks"]
                    != binding.get("new_proc_start_ticks")
                or not json_type_equal(
                    quiescence["new_root_identity"], root_identity
                )
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "cohort quiescence journal misses commit"
                )
        elif (
            binding.get("cohort_quiescence_sha256") is not None
            or quiescence_path.exists() or quiescence_path.is_symlink()
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "running cohort has a quiescence journal"
            )
        verified.append({
            "lane_index": key[0], "descendant_index": key[1],
            "prepared_target_sha256": target["record_sha256"],
            "started_worker_journal_sha256":
                started["record_sha256"],
            "cohort_quiescence_sha256":
                binding.get("cohort_quiescence_sha256"),
        })
    return verified


def _acquire_new_root_fences(
    root_identities: Sequence[Mapping[str, Any]], *,
    controller_root_identities:
        Sequence[Mapping[str, Any]] | None = None,
    already_held: Sequence[Any] = (),
) -> list[Any]:
    identities = [dict(item) for item in root_identities]
    by_root = {
        Path(item.get("path", "")): item for item in identities
    }
    if (
        len(by_root) != len(identities)
        or any(
            not json_type_equal(base._root_identity(path), identity)
            for path, identity in by_root.items()
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error("new root fence identities malformed")
    if controller_root_identities is None:
        controller_by_root = dict(by_root)
    else:
        controller_identities = [
            dict(item) for item in controller_root_identities
        ]
        controller_by_root = {
            Path(item.get("path", "")): item
            for item in controller_identities
        }
        if (
            len(controller_by_root) != len(controller_identities)
            or not set(controller_by_root) <= set(by_root)
            or any(
                not json_type_equal(base._root_identity(path), identity)
                for path, identity in controller_by_root.items()
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "controller root fence identities malformed"
            )
    plan: list[tuple[Path, str, int]] = []
    for path in by_root:
        plan.append((
            path / ".adaptive-child.lock",
            f"new-root:{path}", fcntl.LOCK_EX,
        ))
    for path in controller_by_root:
        plan.append((
            path / "runtime/dmtcp/.controller.lock",
            f"new-controller:{path}", fcntl.LOCK_SH,
        ))
    plan.sort(key=lambda item: str(item[0]))
    retained = {Path(item.current_path): item for item in already_held}
    if (
        len(retained) != len(already_held)
        or not set(retained) <= {item[0] for item in plan}
    ):
        raise AdaptiveSwitchEvidenceV4Error("retained new-root locks malformed")
    for path, _, _ in plan:
        if path not in retained:
            continue
        item = retained[path]
        observed = base._stat_identity(path.lstat())
        if (
            Path(item.current_path) != path
            or not json_type_equal(observed, base._stat_identity(os.fstat(item.fd)))
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "retained new-root lock identity changed"
            )
    acquired: list[Any] = []
    try:
        for path, role, operation in plan:
            if path not in retained:
                acquired.append(base._HeldLock(path, role, operation))
        return acquired
    except BaseException:
        _close_locks(acquired)
        raise


def _close_locks(locks: Sequence[Any]) -> None:
    for held in reversed(locks):
        held.close()


def _adopt_exclusive_outer_locks(
    root_identities: Sequence[Mapping[str, Any]],
    outer_lock_fds: Sequence[int],
) -> list[Any]:
    """Duplicate eight already-held EX flock OFDs without a release window."""

    if (
        type(root_identities) is not list
        or any(type(item) is not dict for item in root_identities)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "outer lock transfer root identities malformed"
        )
    identities = [dict(item) for item in root_identities]
    if (
        type(outer_lock_fds) is not list
        or len(identities) != TARGET_COUNT
        or len(outer_lock_fds) != TARGET_COUNT
        or any(type(item) is not int or item < 0 for item in outer_lock_fds)
        or len(set(outer_lock_fds)) != TARGET_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "outer lock transfer cardinality malformed"
        )
    expected: dict[tuple[int, int], tuple[Path, dict[str, Any]]] = {}
    for identity in identities:
        root = Path(identity.get("path", ""))
        if not json_type_equal(base._root_identity(root), identity):
            raise AdaptiveSwitchEvidenceV4Error(
                "outer lock transfer root changed"
            )
        path = root / ".adaptive-child.lock"
        lexical = path.lstat()
        key = (int(lexical.st_dev), int(lexical.st_ino))
        if key in expected:
            raise AdaptiveSwitchEvidenceV4Error(
                "outer lock transfer root duplicated"
            )
        expected[key] = (path, base._stat_identity(lexical))
    adopted: list[Any] = []
    seen: set[tuple[int, int]] = set()
    try:
        for source_fd in outer_lock_fds:
            flags = fcntl.fcntl(source_fd, fcntl.F_GETFL)
            observed = os.fstat(source_fd)
            key = (int(observed.st_dev), int(observed.st_ino))
            if (
                key not in expected or key in seen
                or stat.S_IFMT(observed.st_mode) != stat.S_IFREG
                or stat.S_IMODE(observed.st_mode) != 0o600
                or observed.st_uid != os.geteuid()
                or observed.st_nlink != 1 or observed.st_size != 0
                or (flags & os.O_ACCMODE) != os.O_RDWR
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "outer lock transfer fd is unsafe"
                )
            path, identity = expected[key]
            if not json_type_equal(
                base._stat_identity(observed), identity
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "outer lock transfer inode changed"
                )
            duplicate = fcntl.fcntl(
                source_fd, fcntl.F_DUPFD_CLOEXEC, 3
            )
            held = object.__new__(base._HeldLock)
            held.fd = duplicate
            held.role = f"new-root:{path.parent}"
            held.original_path = path
            held.current_path = path
            held.identity = dict(identity)
            held.operation = fcntl.LOCK_EX
            try:
                fcntl.flock(duplicate, fcntl.LOCK_EX | fcntl.LOCK_NB)
                probe = os.open(
                    path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW
                )
                try:
                    try:
                        fcntl.flock(
                            probe, fcntl.LOCK_EX | fcntl.LOCK_NB
                        )
                    except BlockingIOError:
                        pass
                    else:
                        fcntl.flock(probe, fcntl.LOCK_UN)
                        raise AdaptiveSwitchEvidenceV4Error(
                            "transferred fd did not hold exclusive flock"
                        )
                finally:
                    os.close(probe)
            except BaseException:
                held.close()
                raise
            adopted.append(held)
            seen.add(key)
        if seen != set(expected):
            raise AdaptiveSwitchEvidenceV4Error(
                "outer lock transfer misses prepared roots"
            )
        adopted.sort(key=lambda item: str(item.current_path))
        return adopted
    except BaseException:
        _close_locks(adopted)
        raise


def _acquire_retired_old_locks(
    retirements: Sequence[Mapping[str, Any]],
) -> tuple[list[Any], dict[str, Any]]:
    by_role = {
        item.get("role"): dict(item) for item in retirements
        if type(item) is dict
    }
    roles = [
        "batch", *(f"lane-{index}" for index in range(LANE_COUNT)),
        *(f"controller-{index}" for index in range(LANE_COUNT)),
    ]
    if set(by_role) != set(roles):
        raise AdaptiveSwitchEvidenceV4Error("old retirement roles malformed")
    held: list[Any] = []
    try:
        for role in roles:
            operation = (
                fcntl.LOCK_SH if role.startswith("controller-")
                else fcntl.LOCK_EX
            )
            record = by_role[role]
            item = base._HeldLock(
                Path(record["retired_path"]), f"old-retired:{role}", operation
            )
            if not json_type_equal(item.identity, record["identity"]):
                item.close()
                raise AdaptiveSwitchEvidenceV4Error(
                    "old retired inode misses commit"
                )
            held.append(item)
        return held, by_role
    except BaseException:
        _close_locks(held)
        raise


def _restore_external_old_lock(
    held: Any, retirement: Mapping[str, Any],
) -> dict[str, Any]:
    retired = Path(retirement["retired_path"])
    original = Path(retirement["original_path"])
    if (
        Path(held.original_path) != retired
        or Path(held.current_path) != retired
        or original.exists() or original.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "external old restore target unsafe"
        )
    path_identity = base._stat_identity(retired.lstat())
    fd_identity = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(path_identity, retirement["identity"])
        or not json_type_equal(fd_identity, retirement["identity"])
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "external old retired inode changed"
        )
    os.rename(retired, original)
    _fsync_directory(original.parent)
    restored = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(
            restored, base._stat_identity(original.lstat())
        )
        or not json_type_equal(
            _identity_without_ctime(fd_identity),
            _identity_without_ctime(restored),
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "external old restore identity changed"
        )
    held.current_path = original
    return {
        "role": retirement["role"], "original_path": str(original),
        "retired_path": str(retired), "identity": restored,
    }


def _reretire_external_old_lock(
    held: Any, retirement: Mapping[str, Any],
) -> dict[str, Any]:
    original = Path(retirement["original_path"])
    retired = Path(retirement["retired_path"])
    if (
        Path(held.current_path) != original
        or retired.exists() or retired.is_symlink()
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "external old compensation target unsafe"
        )
    before = base._stat_identity(os.fstat(held.fd))
    if not json_type_equal(before, base._stat_identity(original.lstat())):
        raise AdaptiveSwitchEvidenceV4Error(
            "external old restore changed before compensation"
        )
    os.rename(original, retired)
    _fsync_directory(retired.parent)
    after = base._stat_identity(os.fstat(held.fd))
    if (
        not json_type_equal(after, base._stat_identity(retired.lstat()))
        or not json_type_equal(
            _identity_without_ctime(before), _identity_without_ctime(after)
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "external old compensation identity changed"
        )
    held.current_path = retired
    return {
        "role": retirement["role"], "original_path": str(original),
        "retired_path": str(retired), "identity": after,
    }


def _lock_plan(locks: Sequence[Any], suffix: str) -> list[dict[str, Any]]:
    ordered = [*locks[5:], *locks[1:5], locks[0]]
    result: list[dict[str, Any]] = []
    for sequence, held in enumerate(ordered):
        retired = held.original_path.with_name(
            held.original_path.name + f".retired-v4-{suffix}"
        )
        result.append({
            "sequence": sequence, "role": held.role,
            "original_path": str(held.original_path),
            "retired_path": str(retired),
            "pre_rename_identity": dict(held.identity),
        })
    return result


def _direct_controller_inspect(child: Any, lane_root: Path) -> dict[str, Any]:
    controller = child.controller
    runtime = lane_root / child.RUNTIME_ROOT
    with child._fixed_environment():
        config, binaries = controller._load_and_verify_config(runtime)
        numbers = controller._generation_numbers(runtime)
        generations = [
            controller._generation_summary(runtime, number, verify_hashes=True)
            for number in numbers
        ]
        command_hash = controller.stable_file_record(
            binaries["dmtcp_command"]
        )["sha256"]
    if not numbers:
        state = "INITIALIZED"
    elif any(
        item.get("poison_claim") or item.get("active_error")
        or item.get("checkpoint_error") for item in generations
    ):
        state = "POISONED"
    elif generations[-1].get("checkpointed"):
        state = "CHECKPOINTED"
    elif generations[-1].get("pid_identity_alive"):
        state = "RUNNING"
    else:
        state = "INACTIVE_UNCHECKPOINTED"
    return {
        "authority": controller.AUTHORITY,
        "config_manifest_sha256": config["self_sha256"],
        "dmtcp_command_sha256": command_hash,
        "generations": generations,
        "hash_verification_requested": True,
        "root": str(runtime.resolve(strict=True)), "state": state,
    }


def _fresh_restored_old_checkpoint(
    root: Path, *, expected_batch_manifest_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_switch_record: Mapping[str, Any],
    switch_observation_policy: Mapping[str, Any],
    incident_precondition_sha256: str,
) -> dict[str, Any]:
    if (
        type(expected_switch_record) is not dict
        or not selfhash_valid(expected_switch_record)
        or expected_switch_record.get("record_sha256")
            != expected_switch_evidence_sha256
        or expected_switch_record.get("batch_manifest_sha256")
            != expected_batch_manifest_sha256
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "expected switch record misses external pins"
        )
    validate_switch_record_structure(expected_switch_record)
    discovery = base._discover_sources(
        root,
        expected_batch_manifest_sha256=expected_batch_manifest_sha256,
    )
    policy = dict(switch_observation_policy)
    fixed = _load_fixed_replay_bundle(
        root, discovery,
        timeout_seconds=policy["timeout_seconds"],
        elapsed_seconds_by_lane=policy["elapsed_seconds_by_lane"],
    )
    snapshot = fixed.snapshot
    replay = fixed.record
    executed = fixed.legacy_executed
    overlay_executed = fixed.overlay_executed
    if (
        snapshot["manifest"].get("record_sha256")
        != expected_batch_manifest_sha256
        or replay.get("batch_manifest_sha256")
        != expected_batch_manifest_sha256
        or replay.get("record_sha256")
        != expected_switch_evidence_sha256
        or not json_type_equal(replay, expected_switch_record)
        or len(snapshot.get("lanes", [])) != LANE_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "restored old checkpoint misses exact switch pin"
        )
    return seal({
        "schema_version": SCHEMA_VERSION,
        "kind": "paper400-restored-old-checkpoint-replay-v4",
        **_attempt_binding(incident_precondition_sha256),
        "batch_manifest_sha256": expected_batch_manifest_sha256,
        "switch_evidence_sha256": expected_switch_evidence_sha256,
        "exact_switch_record_rebuilt": True,
        "checkpoint_result_sha256":
            snapshot["checkpoint_result"]["record_sha256"],
        "lane_transport_chain_sha256s": [
            lane["chain"]["record_sha256"] for lane in snapshot["lanes"]
        ],
        "lane_proof_prefixes": [
            dict(lane["chain"]["latest_proof_prefix"])
            for lane in snapshot["lanes"]
        ],
        "executed_source_closure": executed,
        "overlay_executed_source_closure": overlay_executed,
        "authenticated": False, "launch_authorized": False,
    })


def _writable_holders(
    path: Path, *, expected_identity: Mapping[str, Any] | None = None,
    _proc_root: Path = Path("/proc"),
) -> list[int]:
    wanted = os.stat(path, follow_symlinks=False)
    if (
        not stat.S_ISREG(wanted.st_mode)
        or (
            expected_identity is not None
            and not json_type_equal(
                base._stat_identity(wanted), expected_identity
            )
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "proof is not the expected regular inode"
        )
    holders: set[int] = set()
    try:
        processes = list(_proc_root.iterdir())
    except OSError as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "cannot inspect process table"
        ) from exc
    for process in processes:
        if not process.name.isdigit():
            continue
        try:
            status_lines = (process / "status").read_text(
                encoding="ascii"
            ).splitlines()
            uid_lines = [
                line for line in status_lines if line.startswith("Uid:")
            ]
            if len(uid_lines) != 1:
                raise ValueError("process status has no unique Uid field")
            uid_fields = uid_lines[0].split()
            if len(uid_fields) != 5 or uid_fields[0] != "Uid:":
                raise ValueError("process Uid field is malformed")
            uids = [int(value, 10) for value in uid_fields[1:]]
            if any(value < 0 for value in uids):
                raise ValueError("process Uid field is negative")
            if uids[1] != wanted.st_uid:
                continue
            descriptors = list((process / "fd").iterdir())
        except (FileNotFoundError, ProcessLookupError):
            continue
        except (OSError, UnicodeError, ValueError) as exc:
            raise AdaptiveSwitchEvidenceV4Error(
                "cannot inspect process descriptor table"
            ) from exc
        for descriptor in descriptors:
            try:
                observed = os.stat(descriptor)
                if (observed.st_dev, observed.st_ino) != (wanted.st_dev, wanted.st_ino):
                    continue
                lines = (process / "fdinfo" / descriptor.name).read_text(
                    encoding="ascii"
                ).splitlines()
                flags = [item for item in lines if item.startswith("flags:")]
                if len(flags) != 1:
                    raise AdaptiveSwitchEvidenceV4Error("ambiguous descriptor flags")
                value = int(flags[0].split(":", 1)[1].strip(), 8)
                if value & os.O_ACCMODE != os.O_RDONLY:
                    holders.add(int(process.name))
            except (FileNotFoundError, ProcessLookupError):
                continue
            except (OSError, UnicodeError, ValueError) as exc:
                raise AdaptiveSwitchEvidenceV4Error(
                    "cannot inspect descriptor flags"
                ) from exc
    final_identity = base._stat_identity(
        os.stat(path, follow_symlinks=False)
    )
    wanted_identity = base._stat_identity(wanted)
    if (
        not json_type_equal(wanted_identity, final_identity)
        or (
            expected_identity is not None
            and not json_type_equal(final_identity, expected_identity)
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "proof changed during writer scan"
        )
    return sorted(holders)


class StartedWorker:
    __slots__ = (
        "_lease", "_lease_nonce", "_token", "permit_binding_sha256",
        "lane_index", "descendant_index", "new_root_identity",
        "new_pid", "new_proc_start_ticks",
        "prepared_target_sha256", "started_worker_journal_sha256",
        "_fenced",
    )

    def __init__(
        self, lease: "AtomicSwitchLease", permit: Any, *,
        new_root_identity: Mapping[str, Any], new_pid: int,
        new_proc_start_ticks: int, prepared_target_sha256: str,
        started_worker_journal_sha256: str,
    ) -> None:
        self._lease = lease
        self._lease_nonce = lease._nonce
        self._token = uuid.uuid4().hex
        self.permit_binding_sha256 = permit.permit_binding_sha256
        self.lane_index = permit.lane_index
        self.descendant_index = permit.descendant_index
        self.new_root_identity = dict(new_root_identity)
        self.new_pid = new_pid
        self.new_proc_start_ticks = new_proc_start_ticks
        self.prepared_target_sha256 = prepared_target_sha256
        self.started_worker_journal_sha256 = (
            started_worker_journal_sha256
        )
        self._fenced = False

    def __reduce__(self) -> Any:
        raise TypeError("StartedWorker cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("StartedWorker cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("StartedWorker cannot be copied")



class PostStartFence(base.PostStartFence):
    __slots__ = (
        "prepared_target_sha256", "started_worker_journal_sha256",
    )

    def __init__(
        self, lease: "AtomicSwitchLease", permit: Any, *,
        started_worker: StartedWorker, new_session_sha256: str,
        new_start_commit_sha256: str,
    ) -> None:
        self.prepared_target_sha256 = (
            started_worker.prepared_target_sha256
        )
        self.started_worker_journal_sha256 = (
            started_worker.started_worker_journal_sha256
        )
        super().__init__(
            lease, permit,
            new_root_identity=started_worker.new_root_identity,
            new_session_sha256=new_session_sha256,
            new_start_commit_sha256=new_start_commit_sha256,
            new_pid=started_worker.new_pid,
            new_proc_start_ticks=started_worker.new_proc_start_ticks,
        )

    def audit_binding(self) -> dict[str, Any]:
        result = super().audit_binding()
        result["prepared_target_sha256"] = self.prepared_target_sha256
        result["started_worker_journal_sha256"] = (
            self.started_worker_journal_sha256
        )
        return result


class CohortTransitionPermit:
    __slots__ = (
        "_lease", "_lease_nonce", "_token", "_used",
        "quiescence_sha256s",
    )

    def __init__(
        self, lease: "AtomicSwitchLease",
        quiescence_sha256s: Sequence[str],
    ) -> None:
        self._lease = lease
        self._lease_nonce = lease._nonce
        self._token = uuid.uuid4().hex
        self._used = False
        self.quiescence_sha256s = tuple(quiescence_sha256s)

    def __reduce__(self) -> Any:
        raise TypeError("CohortTransitionPermit cannot be serialized")

    def __copy__(self) -> Any:
        raise TypeError("CohortTransitionPermit cannot be copied")

    def __deepcopy__(self, memo: Any) -> Any:
        del memo
        raise TypeError("CohortTransitionPermit cannot be copied")

class AtomicSwitchLease(base.AtomicSwitchLease):
    __slots__ = (
        "_prepared", "_retired_records", "_target_records",
        "_started_workers", "_outer_locks", "_cohort0_quiescence",
        "_cohort_transition_nonce", "_cohort_locks",
        "_rolled_back", "_v4_sources", "_incident_precondition",
        "_incident_target_roots", "_incident_outer_lock_fds",
        "_incident_external_pin",
        "_fixed_replay_bundle", "_current_science_bundle",
    )

    def __init__(
        self, *args: Any, v4_sources: Mapping[str, Any],
        fixed_replay_bundle: _FixedReplayBundle,
        current_science_bundle: _CurrentScienceBundle,
        incident_precondition: Mapping[str, Any] | None,
        incident_target_roots: list[Path] | None,
        incident_outer_lock_fds: list[int] | None,
        incident_external_pin: str | None,
        **kwargs: Any,
    ) -> None:
        super().__init__(*args, **kwargs)
        if (
            type(fixed_replay_bundle) is not _FixedReplayBundle
            or type(current_science_bundle) is not _CurrentScienceBundle
            or self._coordinator is not current_science_bundle.coordinator
            or self._child is not current_science_bundle.child
            or self._overlay is not current_science_bundle.overlay
            or self._snapshot is not current_science_bundle.snapshot
            or not json_type_equal(
                self._legacy_executed,
                current_science_bundle.legacy_executed,
            )
            or not json_type_equal(
                self._overlay_record,
                current_science_bundle.overlay_record,
            )
            or not json_type_equal(
                self._overlay_executed,
                current_science_bundle.overlay_executed,
            )
            or not json_type_equal(
                self._record, fixed_replay_bundle.record
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "fixed/current replay bundle construction mismatch"
            )
        self._fixed_replay_bundle = fixed_replay_bundle
        self._current_science_bundle = current_science_bundle
        self._prepared: dict[str, Any] | None = None
        self._retired_records: list[dict[str, Any]] = []
        self._target_records: dict[
            tuple[int, int], dict[str, Any]
        ] = {}
        self._started_workers: dict[
            tuple[int, int], StartedWorker
        ] = {}
        self._outer_locks: list[Any] = []
        self._cohort0_quiescence: dict[
            tuple[int, int], dict[str, Any]
        ] = {}
        self._cohort_transition_nonce: str | None = None
        self._cohort_locks: list[Any] = []
        self._rolled_back = False
        self._v4_sources = dict(v4_sources)
        self._incident_precondition = (
            None if incident_precondition is None
            else dict(incident_precondition)
        )
        self._incident_target_roots = (
            [] if incident_target_roots is None
            else list(incident_target_roots)
        )
        self._incident_outer_lock_fds = (
            [] if incident_outer_lock_fds is None
            else list(incident_outer_lock_fds)
        )
        self._incident_external_pin = incident_external_pin

    @property
    def incident_precondition(self) -> dict[str, Any]:
        self._assert_active()
        if self._incident_precondition is None:
            raise AdaptiveSwitchEvidenceV4Error(
                "lease has no incident precondition"
            )
        return json.loads(canonical_bytes(self._incident_precondition))

    def _lightweight_incident_prewrite_fence(self) -> None:
        incident = self._incident_precondition
        if (
            type(incident) is not dict
            or not selfhash_valid(incident)
            or incident.get("record_sha256")
                != self._incident_external_pin
            or incident.get("attempt_id") != ATTEMPT_ID
            or (self._root / ATTEMPT_ROOT).exists()
            or (self._root / ATTEMPT_ROOT).is_symlink()
            or len(self._locks) != 9
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident pin/namespace changed before first write"
            )
        absent_paths = [
            self._root / FAILED_V3_HANDOFF,
            self._root / FAILED_V3_ROLLBACK,
            *[
                Path(item["failed_retired_path"])
                for item in incident["failed_attempt"][
                    "restored_old_locks"
                ]
            ],
        ]
        if any(path.exists() or path.is_symlink() for path in absent_paths):
            raise AdaptiveSwitchEvidenceV4Error(
                "failed-v3 terminal/retired name appeared before first write"
            )
        for held in self._locks:
            if (
                Path(held.current_path) != Path(held.original_path)
                or not json_type_equal(
                    base._stat_identity(os.fstat(held.fd)), held.identity
                )
                or not json_type_equal(
                    base._stat_identity(Path(held.original_path).lstat()),
                    held.identity,
                )
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "old lock changed before first write"
                )
        historical = incident["failed_attempt"]
        for key in ("failed_v3_intent", "failed_v3_prepared"):
            item = historical[key]
            current = base._stat_identity(
                (self._root / item["relative_path"]).lstat()
            )
            if not json_type_equal(current, item["identity"]):
                raise AdaptiveSwitchEvidenceV4Error(
                    "failed-v3 evidence metadata changed before first write"
                )
        for relative, item in zip(
            (
                FAILED_V3_TARGET_DIRECTORY,
                FAILED_V3_STARTED_DIRECTORY,
                FAILED_V3_QUIESCENCE_DIRECTORY,
            ),
            historical["failed_v3_empty_directories"],
            strict=True,
        ):
            if item.get("relative_path") != relative.as_posix():
                raise AdaptiveSwitchEvidenceV4Error(
                    "failed-v3 journal path binding changed"
                )
            observed = _stable_empty_incident_directory(
                self._root, relative
            )
            if not json_type_equal(observed, item):
                raise AdaptiveSwitchEvidenceV4Error(
                    "failed-v3 empty journal changed before first write"
                )
        for target, source_fd, expected in zip(
            self._incident_target_roots,
            self._incident_outer_lock_fds,
            incident["target_roots"],
            strict=True,
        ):
            if (
                not json_type_equal(
                    base._root_identity(target),
                    expected["root_identity"],
                )
                or not json_type_equal(
                    _validate_target_outer_fd(target, source_fd),
                    expected["outer_lock_identity"],
                )
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "target root/lock changed before first write"
                )
            fixed_files = [
                Path("state/00-static.json"),
                *[
                    Path("static") / name
                    for name in sorted({
                        "parent-manifest.json", "width6-campaign.json",
                        "width10-campaign.json", "adaptive-overlay.json",
                        "hard-evidence.json", "switch-evidence.json",
                        "descendant.cnf",
                    })
                ],
            ]
            if len(fixed_files) != len(expected["material_files"]):
                raise AdaptiveSwitchEvidenceV4Error(
                    "target material count changed before first write"
                )
            for relative, material in zip(
                fixed_files, expected["material_files"], strict=True
            ):
                if (
                    material.get("relative_path") != relative.as_posix()
                    or not json_type_equal(
                        base._stat_identity((target / relative).lstat()),
                        material["identity"],
                    )
                ):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "target material identity changed before first write"
                    )
            fixed_directories = [
                target / "static", target / "state",
                target / "state" / "actions",
                target / "artifacts", target / "runtime",
            ]
            for directory, expected_directory in zip(
                fixed_directories,
                expected["directory_inventory"],
                strict=True,
            ):
                observed = _stable_directory_inventory(
                    directory,
                    expected_names=set(expected_directory["entries"]),
                )
                if not json_type_equal(observed, expected_directory):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "target directory changed before first write"
                    )
        _lightweight_old_checkpoint_fence(
            self._root, self._fixed_replay_bundle.snapshot, incident,
            self._fixed_replay_bundle.child,
        )
        if not json_type_equal(
            incident.get("source_binding"), _v4_source_binding()
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "v4 execution source changed before first write"
            )

    def _assert_retirement_intact(self) -> None:
        self._assert_active()
        if self._prepared is None or len(self._retired_records) != 9:
            raise AdaptiveSwitchEvidenceV4Error("retirement was not prepared")
        for held, record in zip(
            [*self._locks[5:], *self._locks[1:5], self._locks[0]],
            self._retired_records, strict=True,
        ):
            original = Path(record["original_path"])
            retired = Path(record["retired_path"])
            if original.exists() or original.is_symlink():
                raise AdaptiveSwitchEvidenceV4Error("legacy lock entry point reappeared")
            observed = retired.lstat()
            if (
                stat.S_ISLNK(observed.st_mode) or not stat.S_ISREG(observed.st_mode)
                or not json_type_equal(base._stat_identity(observed), record["identity"])
                or not json_type_equal(base._stat_identity(os.fstat(held.fd)), record["identity"])
            ):
                raise AdaptiveSwitchEvidenceV4Error("retired lock identity changed")

    def _old_post_retirement_fence(self) -> None:
        self._assert_retirement_intact()
        _lightweight_old_checkpoint_fence(
            self._root, self._fixed_replay_bundle.snapshot,
            self._incident_precondition,
            self._fixed_replay_bundle.child,
        )

    def prepare_retirement(self) -> dict[str, Any]:
        self._assert_active()
        if (
            self._candidate_only or self._prepared is not None
            or self._incident_precondition is None
            or len(self._incident_target_roots) != TARGET_COUNT
            or len(self._incident_outer_lock_fds) != TARGET_COUNT
        ):
            raise AdaptiveSwitchEvidenceV4Error("retirement cannot be prepared")
        # _enter performed the only full incident replay and external-pin
        # comparison immediately before constructing this lease.  There is no
        # user yield and all old-nine plus caller-eight locks remain held.
        # This lightweight fence avoids hashing the large proofs a second time.
        self._lightweight_incident_prewrite_fence()
        _make_attempt_root(self._root)
        _publish(
            self._root / INCIDENT_PRECONDITION,
            self._incident_precondition,
        )
        suffix = ATTEMPT_ID[:16]
        target_directory = _make_journal_directory(
            self._root, TARGET_DIRECTORY
        )
        started_directory = _make_journal_directory(
            self._root, STARTED_DIRECTORY
        )
        quiescence_directory = _make_journal_directory(
            self._root, QUIESCENCE_DIRECTORY
        )
        plan = _lock_plan(self._locks, suffix)
        intent = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-dic5-adaptive-retirement-intent-v4",
            "gate": GATE, "test_only": True, "production_eligible": False,
            "authenticated": False, "launch_authorized": False,
            "attempt_id": ATTEMPT_ID,
            "incident_precondition_sha256":
                self._incident_precondition["record_sha256"],
            "failed_v3_intent_sha256": FAILED_V3_INTENT_RECORD_SHA256,
            "failed_v3_prepared_sha256": FAILED_V3_PREPARED_RECORD_SHA256,
            "batch_root": str(self._root),
            "batch_manifest_sha256": self._record["batch_manifest_sha256"],
            "switch_evidence_sha256": self._record["record_sha256"],
            "target_journal_directory": str(target_directory),
            "started_journal_directory": str(started_directory),
            "quiescence_journal_directory": str(quiescence_directory),
            "lock_plan": plan, "retirement_complete": False,
            "source_binding": self._v4_sources,
        })
        _publish(self._root / RETIREMENT_INTENT, intent)
        ordered = [*self._locks[5:], *self._locks[1:5], self._locks[0]]
        retired: list[dict[str, Any]] = []
        try:
            for sequence, held in enumerate(ordered):
                record = _retire_lock_v3(
                    held, Path(plan[sequence]["retired_path"])
                )
                retired.append({"sequence": sequence, **record})
                if (
                    record["role"] != plan[sequence]["role"]
                    or record["original_path"]
                    != plan[sequence]["original_path"]
                    or record["retired_path"]
                    != plan[sequence]["retired_path"]
                    or not json_type_equal(
                        record["pre_rename_identity"],
                        plan[sequence]["pre_rename_identity"],
                    )
                ):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "retirement plan drift"
                    )
            prepared = seal({
                "schema_version": SCHEMA_VERSION, "kind": PREPARED_KIND,
                "gate": GATE, "test_only": True,
                "production_eligible": False,
                "authenticated": False, "launch_authorized": False,
                "scientific_claim": False,
                "attempt_id": ATTEMPT_ID,
                "incident_precondition_sha256":
                    self._incident_precondition["record_sha256"],
                "failed_v3_intent_sha256":
                    FAILED_V3_INTENT_RECORD_SHA256,
                "failed_v3_prepared_sha256":
                    FAILED_V3_PREPARED_RECORD_SHA256,
                "batch_root": str(self._root),
                "batch_root_identity": base._root_identity(self._root),
                "batch_manifest_sha256":
                    self._record["batch_manifest_sha256"],
                "switch_evidence_sha256": self._record["record_sha256"],
                "retirement_intent_sha256": intent["record_sha256"],
                "retired_locks": retired, "retirement_complete": True,
                "old_runner_entrypoints_reachable": False,
                "source_binding": self._v4_sources,
            })
            _publish(self._root / PREPARED_COMMIT, prepared)
            self._retired_records = retired
            self._prepared = prepared
            self._old_post_retirement_fence()
            return json.loads(canonical_bytes(prepared))
        except BaseException as retirement_error:
            restore_failures: list[BaseException] = []
            for sequence in reversed(range(len(ordered))):
                held = ordered[sequence]
                try:
                    _restore_current_lock_v3(
                        held,
                        original_path=Path(
                            plan[sequence]["original_path"]
                        ),
                        retired_path=Path(
                            plan[sequence]["retired_path"]
                        ),
                    )
                except BaseException as exc:
                    restore_failures.append(exc)
            if restore_failures:
                raise AdaptiveSwitchEvidenceV4Error(
                    "pre-yield retirement failed and old restore failed"
                ) from restore_failures[0]
            self._retired_records = []
            self._prepared = None
            try:
                for held, expected in zip(
                    ordered, plan, strict=True
                ):
                    if (
                        Path(held.current_path)
                            != Path(expected["original_path"])
                        or not json_type_equal(
                            base._stat_identity(os.fstat(held.fd)),
                            expected["pre_rename_identity"],
                        )
                        or not json_type_equal(
                            base._stat_identity(
                                Path(expected["original_path"]).lstat()
                            ),
                            expected["pre_rename_identity"],
                        )
                    ):
                        raise AdaptiveSwitchEvidenceV4Error(
                            "restored old lock identity changed"
                        )
                _lightweight_old_checkpoint_fence(
                    self._root, self._fixed_replay_bundle.snapshot,
                    self._incident_precondition,
                    self._fixed_replay_bundle.child,
                )
            except BaseException as replay_error:
                reretire_failures: list[BaseException] = []
                for sequence, held in enumerate(ordered):
                    try:
                        if Path(held.current_path) == Path(
                            plan[sequence]["original_path"]
                        ):
                            _retire_lock_v3(
                                held,
                                Path(plan[sequence]["retired_path"]),
                            )
                    except BaseException as exc:
                        reretire_failures.append(exc)
                message = (
                    "pre-yield compensation replay failed; old entrypoints "
                    "were re-retired"
                )
                if reretire_failures:
                    message += " with additional retirement failures"
                raise AdaptiveSwitchEvidenceV4Error(message) from replay_error
            raise retirement_error

    def _fresh_record(self) -> dict[str, Any]:
        # Once the lock names are retired the legacy loader correctly refuses
        # to replay its session.  Equivalent post-retirement checking is done
        # directly under the still-held original inodes.
        if self._prepared is not None:
            self._old_post_retirement_fence()
            return dict(self._record)
        fixed = self._fixed_replay_bundle
        _fixed_replay_sources_unchanged()
        fixed_source_binding = _validate_fixed_dynamic_source_binding(
            self._discovery, fixed.legacy_executed,
            fixed.overlay_record, fixed.overlay_executed,
        )
        snapshot = base._snapshot_locked(
            self._root, fixed.coordinator, fixed.child
        )
        record = base._build_record(
            self._root, snapshot, self._discovery, fixed.overlay,
            fixed.legacy_executed, fixed.overlay_record,
            fixed.overlay_executed, timeout_seconds=self._timeout,
            elapsed_seconds_by_lane=self._elapsed,
        )
        validate_switch_record_structure(record)
        if (
            not json_type_equal(
                record.get("source_binding"), fixed_source_binding
            )
            or not json_type_equal(record, self._record)
        ):
            self._poisoned = True
            raise AdaptiveSwitchEvidenceV4Error(
                "fixed old stopped state changed under lease"
            )
        return record

    def verify_target(
        self, overlay_manifest: Mapping[str, Any], *,
        expected_overlay_sha256: str, global_leaf_index: int,
        expected_hard_evidence_sha256: str,
        candidate_variables: list[int], descendant_index: int,
        expected_descendant_sha256: str,
    ) -> Any:
        matches = [
            lane for lane in self._record["lanes"]
            if lane["global_leaf_index"] == global_leaf_index
        ]
        if len(matches) != 1:
            raise AdaptiveSwitchEvidenceV4Error(
                "target is not one old batch lane"
            )
        lane_index = matches[0]["lane_index"]
        key = (lane_index, descendant_index)
        if key not in TARGET_KEYS or key in self._permits:
            raise AdaptiveSwitchEvidenceV4Error(
                "target permit is duplicated/malformed"
            )
        incident_target = self._incident_precondition["target_roots"][
            TARGET_KEYS.index(key)
        ]
        if (
            incident_target.get("global_leaf_index")
                != global_leaf_index
            or incident_target.get("descendant_index")
                != descendant_index
            or incident_target.get("overlay_manifest_sha256")
                != expected_overlay_sha256
            or incident_target.get("hard_evidence_sha256")
                != expected_hard_evidence_sha256
            or incident_target.get("descendant_sha256")
                != expected_descendant_sha256
            or incident_target.get("candidate_variables")
                != candidate_variables
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "target permit kwargs miss incident admission"
            )
        permit = super().verify_target(
            overlay_manifest,
            expected_overlay_sha256=expected_overlay_sha256,
            global_leaf_index=global_leaf_index,
            expected_hard_evidence_sha256=
                expected_hard_evidence_sha256,
            candidate_variables=candidate_variables,
            descendant_index=descendant_index,
            expected_descendant_sha256=expected_descendant_sha256,
        )
        transient = self._permits.pop(lane_index, None)
        if transient is not permit:
            raise AdaptiveSwitchEvidenceV4Error(
                "base target permit registry drift"
            )
        self._permits[key] = permit
        return permit

    def prepare_target(
        self, *, permit: Any, new_root_identity: Mapping[str, Any],
    ) -> dict[str, Any]:
        """Durably bind a verified permit to its root before spawning."""

        self._assert_retirement_intact()
        key = (
            getattr(permit, "lane_index", None),
            getattr(permit, "descendant_index", None),
        )
        if (
            type(permit) is not base.LaunchPermit or permit._lease is not self
            or permit._lease_nonce != self._nonce or permit._used
            or key not in TARGET_KEYS
            or self._permits.get(key) is not permit
            or key in self._target_records
            or key in self._started_workers
        ):
            raise AdaptiveSwitchEvidenceV4Error("prepared target permit is invalid")
        if (
            type(new_root_identity) is not dict
            or type(new_root_identity.get("path")) is not str
        ):
            raise AdaptiveSwitchEvidenceV4Error("prepared root identity malformed")
        root = base._root_identity(Path(new_root_identity["path"]))
        if not json_type_equal(root, new_root_identity):
            raise AdaptiveSwitchEvidenceV4Error("prepared root identity changed")
        if any(
            item["new_root_identity"]["path"] == root["path"]
            for item in self._target_records.values()
        ):
            raise AdaptiveSwitchEvidenceV4Error("prepared root is duplicated")
        incident_target = self._incident_precondition["target_roots"][
            TARGET_KEYS.index(key)
        ]
        if (
            (incident_target.get("lane_index"),
             incident_target.get("descendant_index")) != key
            or not json_type_equal(
                incident_target.get("root_identity"), root
            )
            or incident_target.get("global_leaf_index")
                != permit.global_leaf_index
            or incident_target.get("descendant_sha256")
                != permit.descendant_sha256
            or incident_target.get("hard_evidence_sha256")
                != permit.hard_evidence_sha256
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "prepared root misses incident-bound target"
            )
        record = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-adaptive-prepared-target-v4",
            "authenticated": False, "launch_authorized": False,
            "lane_index": permit.lane_index,
            "global_leaf_index": permit.global_leaf_index,
            "descendant_index": permit.descendant_index,
            "descendant_sha256": permit.descendant_sha256,
            "overlay_manifest_sha256": permit.overlay_manifest_sha256,
            "hard_evidence_sha256": permit.hard_evidence_sha256,
            "permit_binding_sha256": permit.permit_binding_sha256,
            "new_root_identity": root,
            "switch_evidence_sha256": self._record["record_sha256"],
            "prepared_retirement_sha256": self._prepared["record_sha256"],
            "target_static_sha256":
                incident_target["static_record_sha256"],
            "target_outer_lock_identity":
                dict(incident_target["outer_lock_identity"]),
            **_attempt_binding(
                self._incident_precondition["record_sha256"]
            ),
        })
        _publish(
            self._root / TARGET_DIRECTORY
            / (
                f"lane-{permit.lane_index}-"
                f"descendant-{permit.descendant_index}.json"
            ),
            record,
        )
        self._target_records[key] = record
        return json.loads(canonical_bytes(record))

    def adopt_prepared_outer_locks(
        self, *, outer_lock_fds: list[int],
    ) -> None:
        """Take continuous ownership of all eight runner-held outer locks."""

        self._assert_retirement_intact()
        if (
            self._candidate_only or self._committed or self._rolled_back
            or self._outer_locks or self._started_workers
            or set(self._target_records) != set(TARGET_KEYS)
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "prepared outer locks cannot be adopted"
            )
        identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        locks = _adopt_exclusive_outer_locks(
            identities, outer_lock_fds
        )
        try:
            self._old_post_retirement_fence()
        except BaseException:
            _close_locks(locks)
            raise
        self._outer_locks = locks

    def note_started_worker(
        self, *, permit: Any, new_root_identity: Mapping[str, Any],
        new_pid: int, new_proc_start_ticks: int,
        cohort_transition_permit: CohortTransitionPermit | None = None,
    ) -> StartedWorker:
        self._assert_retirement_intact()
        key = (
            getattr(permit, "lane_index", None),
            getattr(permit, "descendant_index", None),
        )
        target_record = self._target_records.get(key)
        transition_valid = (
            type(cohort_transition_permit) is CohortTransitionPermit
            and cohort_transition_permit._lease is self
            and cohort_transition_permit._lease_nonce == self._nonce
            and self._cohort_transition_nonce
                == cohort_transition_permit._token
            and not cohort_transition_permit._used
        )
        if (
            type(permit) is not base.LaunchPermit or permit._lease is not self
            or permit._lease_nonce != self._nonce or permit._used
            or key not in TARGET_KEYS
            or self._permits.get(key) is not permit
            or type(target_record) is not dict
            or len(self._target_records) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
            or len(self._outer_locks) != TARGET_COUNT
            or key in self._started_workers
            or (
                permit.descendant_index == 0
                and cohort_transition_permit is not None
            )
            or (
                permit.descendant_index == 1
                and not transition_valid
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error("started worker permit is invalid")
        if type(new_pid) is not int or type(new_proc_start_ticks) is not int:
            raise AdaptiveSwitchEvidenceV4Error("new PID identity must be strict ints")
        if base._proc_start_ticks(new_pid) != new_proc_start_ticks:
            raise AdaptiveSwitchEvidenceV4Error("new PID identity is not alive")
        live_existing = 0
        for worker in self._started_workers.values():
            try:
                if (
                    base._proc_start_ticks(worker.new_pid)
                    == worker.new_proc_start_ticks
                ):
                    live_existing += 1
            except Exception:
                pass
        if live_existing >= MAX_LIVE_WORKERS:
            raise AdaptiveSwitchEvidenceV4Error(
                "max-live cohort invariant would be exceeded"
            )
        if (
            type(new_root_identity) is not dict
            or type(new_root_identity.get("path")) is not str
        ):
            raise AdaptiveSwitchEvidenceV4Error("new root identity malformed")
        root = base._root_identity(Path(new_root_identity["path"]))
        if (
            not json_type_equal(root, new_root_identity)
            or not json_type_equal(root, target_record["new_root_identity"])
        ):
            raise AdaptiveSwitchEvidenceV4Error("new root identity changed")
        journal = seal({
            "schema_version": SCHEMA_VERSION,
            "kind": "paper400-adaptive-started-worker-v4",
            "authenticated": False, "launch_authorized": False,
            "lane_index": permit.lane_index,
            "descendant_index": permit.descendant_index,
            "prepared_target_sha256": target_record["record_sha256"],
            "permit_binding_sha256": permit.permit_binding_sha256,
            "new_root_identity": root, "new_pid": new_pid,
            "new_proc_start_ticks": new_proc_start_ticks,
            "switch_evidence_sha256": self._record["record_sha256"],
            "prepared_retirement_sha256": self._prepared["record_sha256"],
            **_attempt_binding(
                self._incident_precondition["record_sha256"]
            ),
        })
        started = StartedWorker(
            self, permit, new_root_identity=root, new_pid=new_pid,
            new_proc_start_ticks=new_proc_start_ticks,
            prepared_target_sha256=target_record["record_sha256"],
            started_worker_journal_sha256=journal["record_sha256"],
        )
        # The process exists already.  Register it before the durable publish,
        # so an I/O fault cannot misclassify this lane as never-started.
        self._started_workers[key] = started
        if (
            permit.descendant_index == 1
            and all(
                (lane, 1) in self._started_workers
                for lane in range(LANE_COUNT)
            )
        ):
            cohort_transition_permit._used = True
        _publish(
            self._root / STARTED_DIRECTORY
            / (
                f"lane-{permit.lane_index}-"
                f"descendant-{permit.descendant_index}.json"
            ),
            journal,
        )
        return started

    def started_target_keys(self) -> tuple[tuple[int, int], ...]:
        """Return process-local truth for cleanup after a note fault."""

        self._assert_active()
        return tuple(
            key for key in TARGET_KEYS if key in self._started_workers
        )

    def _verify_quiescent_worker(
        self, key: tuple[int, int], record: Mapping[str, Any], *,
        require_checkpointed: bool = False,
    ) -> dict[str, Any]:
        checked = _validate_quiescence_record(record)
        worker = self._started_workers.get(key)
        target = self._target_records.get(key)
        if (
            worker is None or target is None
            or (
                require_checkpointed
                and checked["state"] != "CHECKPOINTED"
            )
            or (checked["lane_index"], checked["descendant_index"]) != key
            or checked["new_pid"] != worker.new_pid
            or checked["new_proc_start_ticks"] != worker.new_proc_start_ticks
            or not json_type_equal(
                checked["new_root_identity"], worker.new_root_identity
            )
            or not json_type_equal(
                checked["new_root_identity"], target["new_root_identity"]
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "quiescence/start/target binding mismatch"
            )
        try:
            alive = (
                base._proc_start_ticks(worker.new_pid)
                == worker.new_proc_start_ticks
            )
        except Exception:
            alive = False
        if alive:
            raise AdaptiveSwitchEvidenceV4Error(
                "quiescent worker remains alive"
            )
        root = Path(worker.new_root_identity["path"])
        if not json_type_equal(
            base._root_identity(root), worker.new_root_identity
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "quiescent root identity changed"
            )
        inspection = _direct_controller_inspect(self._child, root)
        generations = inspection.get("generations")
        latest = (
            generations[-1]
            if type(generations) is list and generations else {}
        )
        if (
            inspection.get("hash_verification_requested") is not True
            or inspection.get("state") != checked["state"]
            or latest.get("pid_identity_alive") is not False
            or latest.get("poison_claim") not in {None, False}
            or latest.get("active_error") not in {None, False}
            or latest.get("checkpoint_error") not in {None, False}
            or type(latest.get("generation")) is not int
            or latest["generation"] < 0
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "fresh controller quiescence inspection failed"
            )
        runtime = root / self._child.RUNTIME_ROOT
        generation = latest["generation"]
        generation_dir = (
            runtime / "generations" / f"{generation:06d}"
        )
        with self._child._fixed_environment():
            active = self._child.controller._active_commit(
                generation_dir, generation
            )
        fence = self._fences.get(key)
        if (
            active.get("pid") != worker.new_pid
            or active.get("proc_start_ticks")
                != worker.new_proc_start_ticks
            or active.get("self_sha256")
                != latest.get("active_manifest_sha256")
            or (
                fence is not None
                and active.get("self_sha256")
                    != fence.new_start_commit_sha256
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "active generation misses started worker"
            )
        if checked["state"] == "CHECKPOINTED":
            if (
                latest.get("checkpointed") is not True
                or latest.get("checkpoint_hashes_valid") is not True
                or latest.get("checkpoint_manifest_sha256")
                    != checked["checkpoint_commit_sha256"]
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "fresh checkpoint inspection failed"
                )
            with self._child._fixed_environment():
                checkpoint = self._child.controller._checkpoint_commit(
                    generation_dir, generation
                )
            prefix = checkpoint.get("proof_prefix")
            if (
                checkpoint.get("kind") != "checkpoint.commit"
                or checkpoint.get("self_sha256")
                    != checked["checkpoint_commit_sha256"]
                or checkpoint.get("single_writer_stopped") is not True
                or type(prefix) is not dict
                or prefix.get("sha256") != checked["proof_sha256"]
                or prefix.get("bytes") != checked["proof_bytes"]
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "checkpoint commit misses quiescent proof"
                )
        elif latest.get("checkpointed") is not False:
            raise AdaptiveSwitchEvidenceV4Error(
                "inactive generation unexpectedly has a checkpoint"
            )
        proof = runtime / "proof.drat"
        digest, size, proof_identity = _stream_hash_size_identity(proof)
        if (
            digest != checked["proof_sha256"]
            or size != checked["proof_bytes"]
            or _writable_holders(
                proof, expected_identity=proof_identity
            ) != []
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "new proof is not quiescent"
            )
        return checked

    def note_cohort_checkpointed(
        self, *, quiescence_records: list[dict[str, Any]],
    ) -> CohortTransitionPermit:
        """Fence the stopped descendant-0 cohort before descendant-1 starts."""

        self._assert_retirement_intact()
        cohort0 = {(lane, 0) for lane in range(LANE_COUNT)}
        if (
            self._committed or self._rolled_back
            or self._cohort_transition_nonce is not None
            or self._cohort_locks
            or type(quiescence_records) is not list
            or len(quiescence_records) != LANE_COUNT
            or set(self._started_workers) != cohort0
            or set(self._fences) != cohort0
            or len(self._outer_locks) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "cohort transition preconditions failed"
            )
        observations: dict[tuple[int, int], dict[str, Any]] = {}
        for value in quiescence_records:
            record = _validate_quiescence_record(value)
            key = (record["lane_index"], record["descendant_index"])
            if key in observations:
                raise AdaptiveSwitchEvidenceV4Error(
                    "duplicate cohort quiescence target"
                )
            observations[key] = record
        if set(observations) != cohort0:
            raise AdaptiveSwitchEvidenceV4Error(
                "cohort quiescence is not exact descendant-0 coverage"
            )
        identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        cohort0_identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS if key in cohort0
        ]
        locks = _acquire_new_root_fences(
            identities,
            controller_root_identities=cohort0_identities,
            already_held=self._outer_locks,
        )
        try:
            for key in TARGET_KEYS:
                if key in cohort0:
                    self._verify_quiescent_worker(
                        key, observations[key],
                        require_checkpointed=True,
                    )
            persisted = {
                key: _seal_v4_quiescence_journal(
                    observations[key],
                    self._incident_precondition["record_sha256"],
                )
                for key in TARGET_KEYS if key in cohort0
            }
            for key in TARGET_KEYS:
                if key in cohort0:
                    _publish(
                        self._root / QUIESCENCE_DIRECTORY
                        / (
                            f"lane-{key[0]}-"
                            f"descendant-{key[1]}.json"
                        ),
                        persisted[key],
                    )
            self._old_post_retirement_fence()
        except BaseException:
            _close_locks(locks)
            raise
        self._cohort_locks = locks
        self._cohort0_quiescence = persisted
        permit = CohortTransitionPermit(
            self, [persisted[key]["record_sha256"] for key in TARGET_KEYS
                   if key in cohort0],
        )
        self._cohort_transition_nonce = permit._token
        return permit

    def post_start_fence(
        self, *, permit: Any, started_worker: StartedWorker,
        new_session_sha256: str, new_start_commit_sha256: str,
    ) -> PostStartFence:
        self._assert_retirement_intact()
        key = (
            getattr(permit, "lane_index", None),
            getattr(permit, "descendant_index", None),
        )
        if (
            type(permit) is not base.LaunchPermit
            or type(started_worker) is not StartedWorker
            or started_worker._lease is not self
            or started_worker._lease_nonce != self._nonce
            or started_worker.permit_binding_sha256
                != permit.permit_binding_sha256
            or self._started_workers.get(key) is not started_worker
            or key in self._fences
            or started_worker._fenced or permit._used
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "started worker is stale/foreign"
            )
        if (
            base._proc_start_ticks(started_worker.new_pid)
            != started_worker.new_proc_start_ticks
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "new worker died before post fence"
            )
        session = base._require_sha256(
            new_session_sha256, label="new session"
        )
        start = base._require_sha256(
            new_start_commit_sha256, label="new start commit"
        )
        self._old_post_retirement_fence()
        fence = PostStartFence(
            self, permit, started_worker=started_worker,
            new_session_sha256=session,
            new_start_commit_sha256=start,
        )
        permit._used = True
        started_worker._fenced = True
        self._fences[key] = fence
        return fence

    def commit_handoff(
        self, *, fences: list[Any], batch_commit_path: Path,
    ) -> dict[str, Any]:
        self._assert_retirement_intact()
        cohort0 = {(lane, 0) for lane in range(LANE_COUNT)}
        cohort1 = {(lane, 1) for lane in range(LANE_COUNT)}
        if (
            self._candidate_only or self._committed or self._rolled_back
            or type(fences) is not list or len(fences) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
            or set(self._started_workers) != set(TARGET_KEYS)
            or set(self._fences) != set(TARGET_KEYS)
            or set(self._cohort0_quiescence) != cohort0
            or self._cohort_transition_nonce is None
            or len(self._outer_locks) != TARGET_COUNT
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "eight-target commit preconditions failed"
            )
        by_key: dict[tuple[int, int], PostStartFence] = {}
        for fence in fences:
            key = (
                getattr(fence, "lane_index", None),
                getattr(fence, "descendant_index", None),
            )
            if (
                type(fence) is not PostStartFence
                or fence._lease is not self
                or fence._lease_nonce != self._nonce
                or self._fences.get(key) is not fence
                or key in by_key
            ):
                raise AdaptiveSwitchEvidenceV4Error("fence set invalid")
            by_key[key] = fence
        if set(by_key) != set(TARGET_KEYS):
            raise AdaptiveSwitchEvidenceV4Error(
                "fences do not cover eight targets"
            )
        roots = [by_key[key].new_root_identity["path"] for key in TARGET_KEYS]
        pids = [by_key[key].new_pid for key in TARGET_KEYS]
        if (
            len(set(roots)) != TARGET_COUNT
            or len(set(pids)) != TARGET_COUNT
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "new roots/PIDs duplicate"
            )
        identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        extra_controller_locks = _acquire_new_root_fences(
            identities,
            already_held=[*self._outer_locks, *self._cohort_locks],
        )
        self._cohort_locks.extend(extra_controller_locks)
        for key in TARGET_KEYS:
            fence = by_key[key]
            root = Path(fence.new_root_identity["path"])
            if not json_type_equal(
                base._root_identity(root), fence.new_root_identity
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "new root changed before commit"
                )
            if key in cohort0:
                self._verify_quiescent_worker(
                    key, self._cohort0_quiescence[key],
                    require_checkpointed=True,
                )
            else:
                if (
                    base._proc_start_ticks(fence.new_pid)
                    != fence.new_proc_start_ticks
                ):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "running cohort worker died before commit"
                    )
                inspection = _direct_controller_inspect(
                    self._child, root
                )
                generations = inspection.get("generations")
                latest = (
                    generations[-1]
                    if type(generations) is list and generations else {}
                )
                if (
                    inspection.get("hash_verification_requested") is not True
                    or inspection.get("state") != "RUNNING"
                    or latest.get("pid_identity_alive") is not True
                    or latest.get("checkpointed") is not False
                    or latest.get("poison_claim") not in {None, False}
                    or latest.get("active_error") not in {None, False}
                    or latest.get("checkpoint_error") not in {None, False}
                    or type(latest.get("generation")) is not int
                    or latest["generation"] < 0
                ):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "running cohort controller inspection failed"
                    )
                generation = latest["generation"]
                with self._child._fixed_environment():
                    active = self._child.controller._active_commit(
                        root / self._child.RUNTIME_ROOT
                        / "generations" / f"{generation:06d}",
                        generation,
                    )
                if (
                    active.get("pid") != fence.new_pid
                    or active.get("proc_start_ticks")
                        != fence.new_proc_start_ticks
                    or active.get("self_sha256")
                        != latest.get("active_manifest_sha256")
                    or active.get("self_sha256")
                        != fence.new_start_commit_sha256
                ):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "running cohort misses exact start manifest"
                    )
        self._old_post_retirement_fence()
        target = Path(batch_commit_path)
        if target != self._root / HANDOFF_COMMIT:
            raise AdaptiveSwitchEvidenceV4Error(
                "wrong batch commit path"
            )
        bindings: list[dict[str, Any]] = []
        for key in TARGET_KEYS:
            fence = by_key[key]
            quiescence = self._cohort0_quiescence.get(key)
            bindings.append({
                **fence.audit_binding(),
                "fence_sha256": fence.fence_sha256,
                "cohort_index": key[1],
                "handoff_state": (
                    "CHECKPOINTED" if key in cohort0 else "RUNNING"
                ),
                "cohort_quiescence_sha256": (
                    quiescence["record_sha256"]
                    if quiescence is not None else None
                ),
            })
        record = seal({
            "schema_version": SCHEMA_VERSION, "kind": HANDOFF_KIND,
            "gate": GATE, "test_only": True,
            "production_eligible": False,
            "authenticated": False, "launch_authorized": False,
            "scientific_claim": False,
            "historical_atomic_handoff_observed": True,
            **_attempt_binding(
                self._incident_precondition["record_sha256"]
            ),
            "batch_root": str(self._root),
            "batch_root_identity": base._root_identity(self._root),
            "batch_manifest_sha256":
                self._record["batch_manifest_sha256"],
            "switch_evidence_sha256": self._record["record_sha256"],
            "switch_observation_policy":
                dict(self._record["observation_policy"]),
            "prepared_retirement_sha256":
                self._prepared["record_sha256"],
            "retired_locks": list(self._retired_records),
            "root_bindings": bindings,
            "fence_sha256s": [
                item["fence_sha256"] for item in bindings
            ],
            "cohort_policy": {
                "target_keys": [
                    [lane, descendant]
                    for lane, descendant in TARGET_KEYS
                ],
                "target_count": TARGET_COUNT,
                "cohort_count": DESCENDANT_COUNT,
                "cohort_size": LANE_COUNT,
                "max_live_workers": MAX_LIVE_WORKERS,
                "checkpointed_at_commit": LANE_COUNT,
                "running_at_commit": LANE_COUNT,
            },
            "source_binding": self._v4_sources,
            "root_link_policy": {
                "relative_path": "state/15-batch-handoff.json",
                "publish": "o-excl-canonical-json-fsync-v1",
                "repair_only_from_externally_pinned_batch_commit": True,
            },
            "claim_scope": {
                "old_transport_durably_retired_before_first_new_start":
                    True,
                "eight_new_processes_observed_started": True,
                "four_new_processes_checkpointed_at_commit": True,
                "four_new_processes_observed_alive_at_commit": True,
                "max_live_workers": MAX_LIVE_WORKERS,
                "serialized_record_can_authorize_launch": False,
                "serialized_record_can_authenticate_unsat": False,
            },
        })
        _verify_committed_journals(
            self._root, record, handoff_published=False,
        )
        _publish(target, record)
        self._committed = True
        return json.loads(canonical_bytes(record))

    def rollback_after_new_quiescent(
        self, *, quiescence_records: list[dict[str, Any]],
        not_started_target_keys: list[tuple[int, int]],
    ) -> dict[str, Any]:
        """Retire all prepared new entrypoints, then restore the old batch."""

        self._assert_retirement_intact()
        if (
            self._committed or self._rolled_back
            or len(self._outer_locks) != TARGET_COUNT
            or set(self._target_records) != set(TARGET_KEYS)
            or type(quiescence_records) is not list
            or type(not_started_target_keys) is not list
            or any(
                type(item) is not tuple or len(item) != 2
                or type(item[0]) is not int or type(item[1]) is not int
                or item not in TARGET_KEYS
                for item in not_started_target_keys
            )
            or len(not_started_target_keys)
                != len(set(not_started_target_keys))
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "rollback partition malformed"
            )
        records: dict[tuple[int, int], dict[str, Any]] = {}
        for value in quiescence_records:
            record = _validate_quiescence_record(value)
            key = (record["lane_index"], record["descendant_index"])
            if key in records:
                raise AdaptiveSwitchEvidenceV4Error(
                    "duplicate quiescence target"
                )
            records[key] = record
        started = set(self._started_workers)
        not_started = set(not_started_target_keys)
        if (
            set(records) != started
            or not_started != set(TARGET_KEYS) - started
            or set(records) & not_started
            or set(records) | not_started != set(TARGET_KEYS)
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "rollback is not an exact target partition"
            )
        for key in TARGET_KEYS:
            if key not in not_started:
                continue
            root = Path(
                self._target_records[key]["new_root_identity"]["path"]
            )
            runtime = root / "runtime/dmtcp"
            if runtime.exists() or runtime.is_symlink():
                raise AdaptiveSwitchEvidenceV4Error(
                    "not-started target has a controller runtime"
                )
        root_identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS
        ]
        controller_identities = [
            self._target_records[key]["new_root_identity"]
            for key in TARGET_KEYS if key in started
        ]
        additional = _acquire_new_root_fences(
            root_identities,
            controller_root_identities=controller_identities,
            already_held=[*self._outer_locks, *self._cohort_locks],
        )
        self._cohort_locks.extend(additional)
        for key in TARGET_KEYS:
            if key in started:
                self._verify_quiescent_worker(key, records[key])
        all_new_locks = sorted(
            [*self._outer_locks, *self._cohort_locks],
            key=lambda item: str(item.current_path),
        )
        if len(all_new_locks) != TARGET_COUNT + len(started):
            raise AdaptiveSwitchEvidenceV4Error(
                "new rollback lock coverage is not exact"
            )
        new_retired: list[tuple[Any, dict[str, Any]]] = []
        try:
            suffix = self._record["record_sha256"][:16] + "-precommit"
            for sequence, held in enumerate(all_new_locks):
                target = held.original_path.with_name(
                    held.original_path.name
                    + f".rolled-back-v4-{suffix}"
                )
                retirement = _retire_lock_v3(held, target)
                new_retired.append((
                    held, {"sequence": sequence, **retirement}
                ))
        except BaseException:
            failures: list[BaseException] = []
            for held, retirement in reversed(new_retired):
                try:
                    _restore_lock_v3(held, retirement)
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV4Error(
                    "partial prepared-new retirement could not be restored"
                ) from failures[0]
            raise
        ordered = [
            *self._locks[5:], *self._locks[1:5], self._locks[0]
        ]
        pairs = list(zip(
            ordered, self._retired_records, strict=True
        ))
        restored_pairs: list[tuple[Any, dict[str, Any]]] = []
        try:
            restored: list[str] = []
            for held, retirement in reversed(pairs):
                _restore_lock_v3(held, retirement)
                restored_pairs.append((held, retirement))
                restored.append(held.role)
            fixed = self._fixed_replay_bundle
            _fixed_replay_sources_unchanged()
            fixed_source_binding = _validate_fixed_dynamic_source_binding(
                self._discovery, fixed.legacy_executed,
                fixed.overlay_record, fixed.overlay_executed,
            )
            snapshot = base._snapshot_locked(
                self._root, fixed.coordinator, fixed.child
            )
            replay = base._build_record(
                self._root, snapshot, self._discovery, fixed.overlay,
                fixed.legacy_executed, fixed.overlay_record,
                fixed.overlay_executed,
                timeout_seconds=self._timeout,
                elapsed_seconds_by_lane=self._elapsed,
            )
            validate_switch_record_structure(replay)
            if (
                not json_type_equal(
                    replay.get("source_binding"), fixed_source_binding
                )
                or not json_type_equal(replay, self._record)
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "old checkpoint failed rollback replay"
                )
            rollback = seal({
                "schema_version": SCHEMA_VERSION,
                "kind": ROLLBACK_KIND, "gate": GATE,
                "test_only": True, "production_eligible": False,
                "authenticated": False, "launch_authorized": False,
                "scientific_claim": False,
                **_attempt_binding(
                    self._incident_precondition["record_sha256"]
                ),
                "batch_root": str(self._root),
                "batch_manifest_sha256":
                    self._record["batch_manifest_sha256"],
                "switch_evidence_sha256":
                    self._record["record_sha256"],
                "prepared_retirement_sha256":
                    self._prepared["record_sha256"],
                "quiescence_record_sha256s": [
                    records[key]["record_sha256"]
                    for key in TARGET_KEYS if key in records
                ],
                "not_started_target_keys": [
                    [lane, descendant]
                    for lane, descendant in TARGET_KEYS
                    if (lane, descendant) in not_started
                ],
                "retired_new_locks": [
                    item for _, item in new_retired
                ],
                "restored_roles": restored,
                "old_checkpoint_replayed": True,
                "new_workers_quiescent": True,
                "claim_scope": {
                    "all_prepared_outer_entrypoints_retired": True,
                    "all_started_controller_entrypoints_retired": True,
                    "new_locks_held_until_old_replay_and_publish": True,
                    "serialized_record_can_authorize_launch": False,
                },
                "source_binding": self._v4_sources,
            })
            _publish(self._root / ROLLBACK_COMMIT, rollback)
        except BaseException:
            failures: list[BaseException] = []
            for held, retirement in reversed(restored_pairs):
                try:
                    _retire_lock_v3(
                        held, Path(retirement["retired_path"])
                    )
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV4Error(
                    "rollback failed and old entrypoint compensation failed"
                ) from failures[0]
            raise
        self._rolled_back = True
        self._outer_locks = []
        self._cohort_locks = []
        _close_locks(all_new_locks)
        return json.loads(canonical_bytes(rollback))

    def _close(self) -> None:
        if not self._active:
            return
        _close_locks(self._cohort_locks)
        _close_locks(self._outer_locks)
        self._cohort_locks = []
        self._outer_locks = []
        super()._close()


def _enter(
    batch_root: Path, *, expected_batch_manifest_sha256: str | None,
    expected_switch_evidence_sha256: str | None,
    expected_hard_evidence_sha256s: list[str] | None,
    timeout_seconds: float, elapsed_seconds_by_lane: list[float],
    strict_base: bool, candidate_only: bool,
    target_roots: list[Path] | None = None,
    target_outer_lock_fds: list[int] | None = None,
    expected_incident_precondition_sha256: str | None = None,
) -> AtomicSwitchLease:
    if type(strict_base) is not bool or strict_base is not True:
        raise AdaptiveSwitchEvidenceV4Error("only strict real replay is allowed")
    entry_python_state = _python_loader_state()
    root = Path(batch_root)
    if (
        root != EXPECTED_BATCH_ROOT
        or expected_batch_manifest_sha256 not in {
            None, EXPECTED_BATCH_MANIFEST_SHA256,
        }
        or expected_switch_evidence_sha256 not in {
            None, EXPECTED_SWITCH_EVIDENCE_SHA256,
        }
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "request misses fixed incident batch/switch pins"
        )
    if not candidate_only and (
        target_roots is None
        or target_outer_lock_fds is None
        or not base._is_sha256(expected_incident_precondition_sha256)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "launch lease requires eight targets and an incident pin"
        )
    locks, discovery = base._acquire_all_locks(root)
    try:
        discovery = base._discover_sources(
            root,
            expected_batch_manifest_sha256=EXPECTED_BATCH_MANIFEST_SHA256,
        )
        fixed_replay_bundle = _load_fixed_replay_bundle(
            root, discovery, timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane,
        )
        record = fixed_replay_bundle.record
        current_science_bundle = _load_current_science_bundle(
            discovery, fixed_snapshot=fixed_replay_bundle.snapshot
        )
        if (
            record.get("record_sha256")
                != EXPECTED_SWITCH_EVIDENCE_SHA256
            or record.get("batch_manifest_sha256")
                != EXPECTED_BATCH_MANIFEST_SHA256
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "fresh replay misses fixed incident pins"
            )
        hard_pins = [
            item["hard_evidence_sha256"] for item in record["lanes"]
        ]
        if hard_pins != list(EXPECTED_HARD_EVIDENCE_SHA256S):
            raise AdaptiveSwitchEvidenceV4Error(
                "fresh replay misses fixed hard-evidence pins"
            )
        if expected_hard_evidence_sha256s is not None and (
            type(expected_hard_evidence_sha256s) is not list
            or len(expected_hard_evidence_sha256s) != LANE_COUNT
            or hard_pins != [
                base._require_sha256(item, label="hard evidence pin")
                for item in expected_hard_evidence_sha256s
            ]
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "hard evidence pins mismatch"
            )
        incident: dict[str, Any] | None = None
        incident_roots: list[Path] | None = None
        incident_fds: list[int] | None = None
        if target_roots is not None or target_outer_lock_fds is not None:
            if (
                type(target_roots) is not list
                or type(target_outer_lock_fds) is not list
                or any(
                    not isinstance(item, Path)
                    for item in target_roots
                )
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "incident target inputs are malformed"
                )
            incident_roots = [Path(item) for item in target_roots]
            incident_fds = list(target_outer_lock_fds)
            incident = _build_incident_precondition_locked(
                root, locks, target_roots=incident_roots,
                target_outer_lock_fds=incident_fds,
                snapshot=fixed_replay_bundle.snapshot,
                switch_record=record,
                child=fixed_replay_bundle.child,
            )
            if (
                expected_incident_precondition_sha256 is not None
                and incident["record_sha256"]
                    != base._require_sha256(
                        expected_incident_precondition_sha256,
                        label="incident precondition pin",
                    )
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "fresh incident rebuild misses external pin"
                )
        science = current_science_bundle
        lease = AtomicSwitchLease(
            root, locks, discovery,
            science.coordinator, science.child, science.overlay,
            science.legacy_executed, science.overlay_record,
            science.overlay_executed, science.snapshot, record,
            timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane,
            candidate_only=candidate_only, v4_sources=_v4_source_binding(),
            fixed_replay_bundle=fixed_replay_bundle,
            current_science_bundle=current_science_bundle,
            incident_precondition=incident,
            incident_target_roots=incident_roots,
            incident_outer_lock_fds=incident_fds,
            incident_external_pin=(
                None if incident is None
                else incident["record_sha256"]
            ),
        )
        if _python_loader_state() != entry_python_state:
            raise AdaptiveSwitchEvidenceV4Error(
                "exact loader changed Python global state"
            )
        if not candidate_only:
            lease.prepare_retirement()
        return lease
    except BaseException:
        for held in reversed(locks):
            held.close()
        raise


@contextlib.contextmanager
def acquire_atomic_switch_lease(
    batch_root: Path, *, target_roots: list[Path],
    target_outer_lock_fds: list[int],
    expected_incident_precondition_sha256: str,
    expected_batch_manifest_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_hard_evidence_sha256s: list[str], timeout_seconds: float,
    elapsed_seconds_by_lane: list[float], strict_base: bool = True,
) -> Iterator[AtomicSwitchLease]:
    lease = _enter(
        batch_root,
        expected_batch_manifest_sha256=expected_batch_manifest_sha256,
        expected_switch_evidence_sha256=expected_switch_evidence_sha256,
        expected_hard_evidence_sha256s=expected_hard_evidence_sha256s,
        timeout_seconds=timeout_seconds,
        elapsed_seconds_by_lane=elapsed_seconds_by_lane,
        strict_base=strict_base, candidate_only=False,
        target_roots=target_roots,
        target_outer_lock_fds=target_outer_lock_fds,
        expected_incident_precondition_sha256=
            expected_incident_precondition_sha256,
    )
    try:
        yield lease
        if not lease._committed and not lease._rolled_back:
            raise AdaptiveSwitchEvidenceV4Error(
                "lease exited without commit or explicit quiescent rollback"
            )
    finally:
        lease._close()


def _acquire_incident_target_locks(
    target_roots: list[Path],
) -> list[Any]:
    if (
        type(target_roots) is not list
        or len(target_roots) != TARGET_COUNT
        or len(set(target_roots)) != TARGET_COUNT
        or any(not isinstance(item, Path) for item in target_roots)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident target roots are malformed"
        )
    acquired: list[Any] = []
    by_root: dict[Path, Any] = {}
    try:
        key_by_root = {
            Path(root): key
            for key, root in zip(TARGET_KEYS, target_roots, strict=True)
        }
        for root in sorted(key_by_root, key=lambda item: str(item)):
            key = key_by_root[root]
            held = base._HeldLock(
                root / ".adaptive-child.lock",
                f"incident-target-{key[0]}-{key[1]}",
                fcntl.LOCK_EX,
            )
            acquired.append(held)
            by_root[root] = held
        return [by_root[Path(root)] for root in target_roots]
    except BaseException:
        _close_locks(acquired)
        raise


def build_incident_precondition(
    batch_root: Path, *, target_roots: list[Path],
    timeout_seconds: float, elapsed_seconds_by_lane: list[float],
    strict_base: bool = True,
) -> dict[str, Any]:
    """Build the fixed incident record without publishing or renaming."""

    if (
        type(target_roots) is not list
        or any(not isinstance(item, Path) for item in target_roots)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident builder requires a list of Path objects"
        )
    roots = [Path(item) for item in target_roots]
    target_locks = _acquire_incident_target_locks(roots)
    try:
        lease = _enter(
            batch_root,
            expected_batch_manifest_sha256=
                EXPECTED_BATCH_MANIFEST_SHA256,
            expected_switch_evidence_sha256=
                EXPECTED_SWITCH_EVIDENCE_SHA256,
            expected_hard_evidence_sha256s=None,
            timeout_seconds=timeout_seconds,
            elapsed_seconds_by_lane=elapsed_seconds_by_lane,
            strict_base=strict_base, candidate_only=True,
            target_roots=roots,
            target_outer_lock_fds=[item.fd for item in target_locks],
        )
        try:
            return lease.incident_precondition
        finally:
            lease._close()
    finally:
        _close_locks(target_locks)


def build_switch_evidence_record(
    batch_root: Path, *, timeout_seconds: float,
    elapsed_seconds_by_lane: list[float], strict_base: bool = True,
) -> dict[str, Any]:
    """Readonly fixed old-batch replay; it never authorizes a retry."""

    lease = _enter(
        batch_root,
        expected_batch_manifest_sha256=EXPECTED_BATCH_MANIFEST_SHA256,
        expected_switch_evidence_sha256=EXPECTED_SWITCH_EVIDENCE_SHA256,
        expected_hard_evidence_sha256s=None,
        timeout_seconds=timeout_seconds,
        elapsed_seconds_by_lane=elapsed_seconds_by_lane,
        strict_base=strict_base, candidate_only=True,
    )
    try:
        return lease.switch_record
    finally:
        lease._close()


_V5_STATIC_FIELDS = {
    "schema_version", "kind", "gate", "state", "authority",
    "test_only", "production_eligible", "root", "root_identity",
    "root_lock_identity", "batch_root_identity", "strict_base",
    "python_startup", "external_pins", "selection", "switch_policy",
    "material_files", "campaign_manifest_sha256",
    "overlay_manifest_sha256", "hard_evidence_sha256",
    "switch_evidence_sha256", "overlay_verification",
    "campaign_verification", "switch_structure_validation",
    "descendant", "descendant_cnf", "source_binding",
    "execution_module_binding", "toolchain_binding", "resource_policy",
    "launch_attestation", "resume_policy", "claim_scope",
    "publication_certificate", "upload_authorized", "record_sha256",
}
_V5_SELECTION_FIELDS = {
    "global_leaf_index", "descendant_index", "descendant_sha256",
    "adaptive_node_id", "relative_assignment_literals",
    "candidate_variables",
}


def _validate_incident_target_semantics(
    root: Path, targets: Any, old_lanes: Any, hard_pins: Any,
    switch_observation_policy: Any,
) -> None:
    if (
        type(targets) is not list or len(targets) != TARGET_COUNT
        or type(old_lanes) is not list or len(old_lanes) != LANE_COUNT
        or type(hard_pins) is not list or len(hard_pins) != LANE_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident target semantic cardinality mismatch"
        )
    compact_switch_policy = _compact_v5_switch_policy(
        switch_observation_policy
    )
    batch_identity = base._root_identity(root)
    paths: list[Path] = []
    root_inodes: set[tuple[int, int]] = set()
    lock_inodes: set[tuple[int, int]] = set()
    for key, target in zip(TARGET_KEYS, targets, strict=True):
        lane_index, descendant_index = key
        if type(target) is not dict:
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target semantic record malformed"
            )
        candidates = target.get("candidate_variables")
        literals = target.get("relative_assignment_literals")
        old_lane = old_lanes[lane_index]
        if (
            type(candidates) is not list or not candidates
            or any(
                type(candidate) is not int
                or candidate < 1 or candidate > 400
                for candidate in candidates
            )
            or candidates != sorted(set(candidates))
            or type(literals) is not list or len(literals) != 1
            or type(literals[0]) is not int or literals[0] == 0
            or abs(literals[0]) not in candidates
            or target.get("global_leaf_index")
                != old_lane.get("global_leaf_index")
            or target.get("hard_evidence_sha256") != hard_pins[lane_index]
            or target.get("hard_evidence_sha256")
                != old_lane.get("hard_evidence_sha256")
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target selection semantics mismatch"
            )
        root_identity = target.get("root_identity")
        lock_identity = target.get("outer_lock_identity")
        if not _root_identity_shape(root_identity):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target root identity malformed"
            )
        target_root = Path(root_identity["path"])
        try:
            resolved = target_root.resolve(strict=True)
        except (OSError, RuntimeError, ValueError) as exc:
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target root cannot be resolved"
            ) from exc
        if (
            not target_root.is_absolute() or resolved != target_root
            or target_root.is_relative_to(root)
            or root.is_relative_to(target_root)
            or not json_type_equal(
                base._root_identity(target_root), root_identity
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target root path/identity mismatch"
            )
        lock_path = target_root / ".adaptive-child.lock"
        lock_stat = lock_path.lstat()
        if (
            stat.S_ISLNK(lock_stat.st_mode)
            or not stat.S_ISREG(lock_stat.st_mode)
            or not json_type_equal(
                base._stat_identity(lock_stat), lock_identity
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target outer lock changed"
            )
        material = target.get("material_files")
        if type(material) is not list or not material:
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target static material missing"
            )
        expected_static = material[0]
        before = _stable_target_file(
            target_root, Path("state/00-static.json"),
            cap=base.MAX_JSON_BYTES,
        )
        static_record = base._read_json(
            target_root / "state/00-static.json"
        )
        after = _stable_target_file(
            target_root, Path("state/00-static.json"),
            cap=base.MAX_JSON_BYTES,
        )
        selection = static_record.get("selection")
        pins = static_record.get("external_pins")
        expected_pins = {
            "expected_overlay_sha256":
                target.get("overlay_manifest_sha256"),
            "expected_hard_evidence_sha256":
                target.get("hard_evidence_sha256"),
            "expected_switch_evidence_sha256":
                EXPECTED_SWITCH_EVIDENCE_SHA256,
            "expected_batch_manifest_sha256":
                EXPECTED_BATCH_MANIFEST_SHA256,
        }
        expected_launch_attestation = {
            "serialized_overlay_launch_authorized": False,
            "serialized_switch_launch_authorized": False,
            "serialized_composite_launch_authorized": False,
            "candidate_exact_bytes_replayed": True,
            "atomic_switch_v4_lease_required": True,
            "strict_first_start_requires_complete_eight_root_cover": True,
            "adaptive_handoff_reentry_supported": False,
            "maximum_live_workers_during_handoff": MAX_LIVE_WORKERS,
        }
        expected_resume_policy = {
            "single_process": True, "single_cpu": True,
            "cpu_rlimit_unlimited": True,
            "proof_fsize_cap_required": True,
            "dmtcp_checkpoint_resource_hard_limit": None,
            "dmtcp_checkpoint_oom_risk_accepted": True,
            "controller": "cadical-dmtcp-exact-resume-v1",
            "checkpoint_has_scientific_authority": False,
            "resume_has_scientific_authority": False,
        }
        expected_claim_scope = {
            "pending_is_solver_evidence": False,
            "overlay_proves_leaf_unsat": False,
            "switch_record_proves_leaf_unsat": False,
            "checkpoint_proves_leaf_unsat": False,
            "only_final_fresh_drat_lrat_certificate_authenticates_leaf_unsat": True,
            "parent_leaf_unsat_claim": False,
            "distance_lower_bound_claim": False,
        }
        material_spec = {
            "parent_manifest":
                ("static/parent-manifest.json", "parent-manifest"),
            "width6_campaign":
                ("static/width6-campaign.json", "width6-campaign"),
            "width10_campaign":
                ("static/width10-campaign.json", "width10-campaign"),
            "adaptive_overlay":
                ("static/adaptive-overlay.json", "adaptive-overlay"),
            "hard_evidence":
                ("static/hard-evidence.json", "hard-evidence"),
            "switch_evidence":
                ("static/switch-evidence.json", "switch-evidence"),
            "descendant_cnf":
                ("static/descendant.cnf", "exact-descendant-cnf"),
        }
        declared_materials = static_record.get("material_files")
        physical_by_relative = {
            item["relative_path"]: item for item in material
        }
        if (
            type(declared_materials) is not dict
            or set(declared_materials) != set(material_spec)
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "target static material declaration malformed"
            )
        for role_key, (relative, role) in material_spec.items():
            physical = physical_by_relative.get(relative)
            if type(physical) is not dict:
                raise AdaptiveSwitchEvidenceV4Error(
                    "target static material is absent"
                )
            observed_physical = _stable_target_file(
                target_root, Path(relative),
                cap=(
                    MAX_PROOF_BYTES
                    if relative == "static/descendant.cnf"
                    else base.MAX_JSON_BYTES
                ),
            )
            identity = physical["identity"]
            expected_declared = {
                "role": role, "relative_path": relative,
                "sha256": physical["sha256"], "bytes": physical["bytes"],
                "device": identity["device"], "inode": identity["inode"],
                "uid": identity["uid"], "mode": identity["mode"],
                "links": identity["links"],
            }
            if (
                not json_type_equal(observed_physical, physical)
                or not json_type_equal(
                    declared_materials[role_key], expected_declared
                )
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "target static material bytes/identity drifted"
                )
        if (
            not json_type_equal(before, expected_static)
            or not json_type_equal(after, expected_static)
            or set(static_record) != _V5_STATIC_FIELDS
            or not selfhash_valid(static_record)
            or type(static_record.get("schema_version")) is not int
            or static_record.get("schema_version") != 5
            or static_record.get("kind")
                != "paper400-dic5-adaptive-child-resume-static-v5"
            or static_record.get("gate")
                != "paper400-dic5-adaptive-child-resume-v5"
            or static_record.get("state") != "RESUMABLE_STATIC_SEALED"
            or static_record.get("authority")
                != "TEST_ONLY_CANDIDATE_ONLY_V5"
            or static_record.get("test_only") is not True
            or static_record.get("production_eligible") is not False
            or static_record.get("strict_base") is not True
            or static_record.get("publication_certificate") is not False
            or static_record.get("upload_authorized") is not False
            or not json_type_equal(
                static_record.get("switch_policy"), compact_switch_policy
            )
            or not json_type_equal(
                static_record.get("launch_attestation"),
                expected_launch_attestation,
            )
            or static_record.get("record_sha256")
                != target.get("static_record_sha256")
            or static_record.get("root") != str(target_root)
            or not json_type_equal(
                static_record.get("root_identity"), root_identity
            )
            or not json_type_equal(
                static_record.get("batch_root_identity"), batch_identity
            )
            or not json_type_equal(pins, expected_pins)
            or static_record.get("overlay_manifest_sha256")
                != target.get("overlay_manifest_sha256")
            or static_record.get("hard_evidence_sha256")
                != target.get("hard_evidence_sha256")
            or static_record.get("switch_evidence_sha256")
                != EXPECTED_SWITCH_EVIDENCE_SHA256
            or not json_type_equal(
                _validate_v5_declared_outer_identity(
                    static_record.get("root_lock_identity"), lock_identity
                ),
                static_record.get("root_lock_identity"),
            )
            or type(selection) is not dict
            or set(selection) != _V5_SELECTION_FIELDS
            or type(selection.get("global_leaf_index")) is not int
            or selection.get("global_leaf_index")
                != target.get("global_leaf_index")
            or type(selection.get("descendant_index")) is not int
            or selection.get("descendant_index") != descendant_index
            or selection.get("descendant_sha256")
                != target.get("descendant_sha256")
            or not json_type_equal(
                selection.get("candidate_variables"), candidates
            )
            or not json_type_equal(
                selection.get("relative_assignment_literals"), literals
            )
            or type(static_record.get("descendant")) is not dict
            or static_record["descendant"].get("descendant_index")
                != descendant_index
            or static_record["descendant"].get("descendant_sha256")
                != target.get("descendant_sha256")
            or static_record["descendant"].get("pending") is not True
            or static_record["descendant"].get("observed_status")
                != "PENDING"
            or static_record["descendant"].get(
                "solver_terminal_authenticated"
            ) is not False
            or not json_type_equal(
                static_record.get("resume_policy"),
                expected_resume_policy,
            )
            or not json_type_equal(
                static_record.get("claim_scope"),
                expected_claim_scope,
            )
            or not json_type_equal(
                _stable_target_file(
                    target_root, Path("state/00-static.json"),
                    cap=base.MAX_JSON_BYTES,
                ),
                expected_static,
            )
            or not json_type_equal(
                base._read_json(
                    target_root / "state/00-static.json"
                ),
                static_record,
            )
            or not json_type_equal(
                _stable_directory_inventory(
                    target_root / "static",
                    expected_names={
                        "parent-manifest.json", "width6-campaign.json",
                        "width10-campaign.json", "adaptive-overlay.json",
                        "hard-evidence.json", "switch-evidence.json",
                        "descendant.cnf",
                    },
                ),
                target["directory_inventory"][0],
            )
            or not json_type_equal(
                base._root_identity(target_root), root_identity
            )
            or not json_type_equal(
                base._stat_identity(lock_path.lstat()), lock_identity
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target static preimage mismatch"
            )
        paths.append(target_root)
        root_inodes.add((root_identity["device"], root_identity["inode"]))
        lock_inodes.add((lock_identity["device"], lock_identity["inode"]))
    if (
        len(set(paths)) != TARGET_COUNT
        or len(root_inodes) != TARGET_COUNT
        or len(lock_inodes) != TARGET_COUNT
        or any(
            left != right and (
                left.is_relative_to(right)
                or right.is_relative_to(left)
            )
            for left in paths for right in paths
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident target roots/locks alias or nest"
        )
    for lane_index in range(LANE_COUNT):
        first = targets[TARGET_KEYS.index((lane_index, 0))]
        second = targets[TARGET_KEYS.index((lane_index, 1))]
        if (
            any(
                not json_type_equal(first.get(field), second.get(field))
                for field in (
                    "global_leaf_index", "hard_evidence_sha256",
                    "overlay_manifest_sha256", "candidate_variables",
                )
            )
            or first["relative_assignment_literals"][0]
                != -second["relative_assignment_literals"][0]
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident sibling cover is not exact"
            )


def _validate_incident_nested(
    root: Path, value: Mapping[str, Any],
) -> None:
    failed = value.get("failed_attempt")
    failed_fields = {
        "failed_v3_intent", "failed_v3_prepared",
        "failed_v3_source_binding", "failed_v3_empty_directories",
        "failed_v3_handoff_absent", "failed_v3_rollback_absent",
        "restored_old_locks", "historical_prepared_reuse_forbidden",
    }
    if type(failed) is not dict or set(failed) != failed_fields:
        raise AdaptiveSwitchEvidenceV4Error(
            "incident failed-attempt schema mismatch"
        )
    observed_incident: list[dict[str, Any]] = []
    predecessor_records: list[dict[str, Any]] = []
    for relative, record_pin, physical_pin in (
        (
            FAILED_V3_INTENT, FAILED_V3_INTENT_RECORD_SHA256,
            FAILED_V3_INTENT_PHYSICAL_SHA256,
        ),
        (
            FAILED_V3_PREPARED, FAILED_V3_PREPARED_RECORD_SHA256,
            FAILED_V3_PREPARED_PHYSICAL_SHA256,
        ),
    ):
        predecessor, identity, size = _stable_raw_json(
            root / relative, expected_record_sha256=record_pin,
            expected_physical_sha256=physical_pin,
        )
        predecessor_records.append(predecessor)
        observed_incident.append({
            "relative_path": relative.as_posix(),
            "record_sha256": record_pin,
            "physical_sha256": physical_pin,
            "bytes": size, "identity": identity,
        })
    if (
        not json_type_equal(
            failed.get("failed_v3_intent"), observed_incident[0]
        )
        or not json_type_equal(
            failed.get("failed_v3_prepared"), observed_incident[1]
        )
        or not json_type_equal(
            failed.get("failed_v3_source_binding"),
            _expected_failed_v3_source_binding(),
        )
        or failed.get("failed_v3_handoff_absent") is not True
        or failed.get("failed_v3_rollback_absent") is not True
        or failed.get("historical_prepared_reuse_forbidden") is not True
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident predecessor pins mismatch"
        )
    if any(
        (root / relative).exists() or (root / relative).is_symlink()
        for relative in (FAILED_V3_HANDOFF, FAILED_V3_ROLLBACK)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "historical v3 terminal artifact appeared"
        )
    directories = failed.get("failed_v3_empty_directories")
    if type(directories) is not list or len(directories) != 3:
        raise AdaptiveSwitchEvidenceV4Error(
            "historical empty-directory schema mismatch"
        )
    for relative, expected in zip(
        (
            FAILED_V3_TARGET_DIRECTORY, FAILED_V3_STARTED_DIRECTORY,
            FAILED_V3_QUIESCENCE_DIRECTORY,
        ),
        directories, strict=True,
    ):
        if (
            type(expected) is not dict
            or set(expected) != {"relative_path", "identity", "entries"}
            or expected.get("relative_path") != relative.as_posix()
            or not json_type_equal(
                _stable_empty_incident_directory(root, relative),
                expected,
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "historical empty-directory binding mismatch"
            )
    restored = failed.get("restored_old_locks")
    roles = [
        *(f"controller-{index}" for index in range(LANE_COUNT)),
        *(f"lane-{index}" for index in range(LANE_COUNT)), "batch",
    ]
    if type(restored) is not list or len(restored) != 9:
        raise AdaptiveSwitchEvidenceV4Error(
            "historical restored-lock schema mismatch"
        )
    for sequence, (role, item) in enumerate(
        zip(roles, restored, strict=True)
    ):
        if role.startswith("controller-"):
            lane = int(role.rsplit("-", 1)[1])
            expected_original = (
                EXPECTED_BATCH_ROOT / "lanes" / f"lane-{lane}"
                / "runtime/dmtcp/.controller.lock"
            )
        elif role.startswith("lane-"):
            lane = int(role.rsplit("-", 1)[1])
            expected_original = (
                EXPECTED_BATCH_ROOT / "lanes" / f"lane-{lane}"
                / ".hierarchical-resume.lock"
            )
        else:
            expected_original = EXPECTED_BATCH_ROOT / ".batch.lock"
        expected_failed_retired = expected_original.with_name(
            expected_original.name
            + ".retired-v3-"
            + EXPECTED_SWITCH_EVIDENCE_SHA256[:16]
        )
        if (
            type(item) is not dict
            or set(item) != {
                "sequence", "role", "original_path",
                "failed_retired_path", "current_identity",
                "historical_pre_rename_identity",
            }
            or item.get("sequence") != sequence
            or item.get("role") != role
            or item.get("original_path") != str(expected_original)
            or item.get("failed_retired_path")
                != str(expected_failed_retired)
            or not _stat_identity_shape(item.get("current_identity"))
            or not _stat_identity_shape(
                item.get("historical_pre_rename_identity")
            )
            or not json_type_equal(
                _identity_without_ctime(item["current_identity"]),
                _identity_without_ctime(
                    item["historical_pre_rename_identity"]
                ),
            )
            or item.get("original_path")
                != predecessor_records[0]["lock_plan"][sequence][
                    "original_path"
                ]
            or item.get("failed_retired_path")
                != predecessor_records[0]["lock_plan"][sequence][
                    "retired_path"
                ]
            or not json_type_equal(
                item.get("historical_pre_rename_identity"),
                predecessor_records[0]["lock_plan"][sequence][
                    "pre_rename_identity"
                ],
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "historical restored-lock binding malformed"
            )
    old_lanes = value.get("fresh_old_lanes")
    old_fields = {
        "lane_index", "global_leaf_index", "transport_chain_sha256",
        "hard_evidence_sha256", "old_pid", "old_proc_start_ticks",
        "pid_identity_alive", "proof_sha256", "proof_bytes",
        "proof_identity", "writable_holders", "terminal_claimed",
        "terminal_committed",
    }
    hard_pins = value.get("hard_evidence_sha256s")
    if (
        type(old_lanes) is not list or len(old_lanes) != LANE_COUNT
        or type(hard_pins) is not list or len(hard_pins) != LANE_COUNT
        or hard_pins != list(EXPECTED_HARD_EVIDENCE_SHA256S)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident old-lane schema mismatch"
        )
    for lane_index, lane in enumerate(old_lanes):
        (
            expected_global, expected_transport, expected_proof,
            expected_proof_bytes, expected_hard,
        ) = EXPECTED_OLD_LANE_TUPLES[lane_index]
        if (
            type(lane) is not dict or set(lane) != old_fields
            or lane.get("lane_index") != lane_index
            or type(lane.get("global_leaf_index")) is not int
            or lane.get("global_leaf_index") != expected_global
            or lane.get("transport_chain_sha256") != expected_transport
            or lane.get("hard_evidence_sha256") != expected_hard
            or lane.get("hard_evidence_sha256") != hard_pins[lane_index]
            or type(lane.get("old_pid")) is not int
            or type(lane.get("old_proc_start_ticks")) is not int
            or lane["old_pid"] <= 0 or lane["old_proc_start_ticks"] <= 0
            or lane.get("pid_identity_alive") is not False
            or lane.get("proof_sha256") != expected_proof
            or type(lane.get("proof_bytes")) is not int
            or lane["proof_bytes"] != expected_proof_bytes
            or lane.get("writable_holders") != []
            or lane.get("terminal_claimed") is not False
            or lane.get("terminal_committed") is not False
            or not _stat_identity_shape(lane.get("proof_identity"))
            or tuple(
                lane["proof_identity"].get(field) for field in (
                    "device", "inode", "uid", "mode", "links", "bytes",
                )
            ) != EXPECTED_OLD_PROOF_PHYSICAL_TUPLES[lane_index]
            or lane["proof_identity"]["bytes"] != lane["proof_bytes"]
            or lane["proof_identity"]["uid"] != os.geteuid()
            or lane["proof_identity"]["gid"] != os.getegid()
            or lane["proof_identity"]["mode"] != 0o600
            or lane["proof_identity"]["links"] != 1
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident old-lane binding malformed"
            )
    targets = value.get("target_roots")
    target_fields = {
        "lane_index", "descendant_index", "global_leaf_index",
        "root_identity", "outer_lock_identity", "static_record_sha256",
        "descendant_sha256", "hard_evidence_sha256",
        "overlay_manifest_sha256", "candidate_variables",
        "relative_assignment_literals", "material_files",
        "directory_inventory", "session_absent", "handoff_link_absent",
        "terminal_bundle_absent", "solver_never_started",
    }
    if type(targets) is not list or len(targets) != TARGET_COUNT:
        raise AdaptiveSwitchEvidenceV4Error(
            "incident target schema mismatch"
        )
    root_paths: set[str] = set()
    root_inodes: set[tuple[int, int]] = set()
    lock_inodes: set[tuple[int, int]] = set()
    for key, target in zip(TARGET_KEYS, targets, strict=True):
        if (
            type(target) is not dict or set(target) != target_fields
            or (
                target.get("lane_index"),
                target.get("descendant_index"),
            ) != key
            or type(target.get("global_leaf_index")) is not int
            or not _root_identity_shape(target.get("root_identity"))
            or not _stat_identity_shape(
                target.get("outer_lock_identity")
            )
            or not base._is_sha256(target.get("static_record_sha256"))
            or not base._is_sha256(target.get("descendant_sha256"))
            or not base._is_sha256(target.get("hard_evidence_sha256"))
            or not base._is_sha256(target.get("overlay_manifest_sha256"))
            or type(target.get("candidate_variables")) is not list
            or not target["candidate_variables"]
            or any(type(item) is not int for item in target["candidate_variables"])
            or type(target.get("relative_assignment_literals")) is not list
            or any(
                type(item) is not int
                for item in target["relative_assignment_literals"]
            )
            or type(target.get("material_files")) is not list
            or len(target["material_files"]) != 8
            or type(target.get("directory_inventory")) is not list
            or len(target["directory_inventory"]) != 5
            or any(
                target.get(field) is not True
                for field in (
                    "session_absent", "handoff_link_absent",
                    "terminal_bundle_absent", "solver_never_started",
                )
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target binding malformed"
            )
        root_id = target["root_identity"]
        lock_id = target["outer_lock_identity"]
        root_identity_fields = {
            "path", "device", "inode", "uid", "mode",
        }
        file_identity_fields = {
            "device", "inode", "mode", "uid", "gid", "links",
            "bytes", "mtime_ns", "ctime_ns",
        }
        material_fields = {
            "relative_path", "sha256", "bytes", "identity",
        }
        directory_fields = {
            "relative_path", "identity", "entries",
        }
        fixed_material_paths = [
            "state/00-static.json",
            *[
                "static/" + name
                for name in sorted({
                    "parent-manifest.json", "width6-campaign.json",
                    "width10-campaign.json", "adaptive-overlay.json",
                    "hard-evidence.json", "switch-evidence.json",
                    "descendant.cnf",
                })
            ],
        ]
        fixed_directory_names = [
            "static", "state", "actions", "artifacts", "runtime",
        ]
        fixed_directory_entries = {
            "static": sorted({
                "parent-manifest.json", "width6-campaign.json",
                "width10-campaign.json", "adaptive-overlay.json",
                "hard-evidence.json", "switch-evidence.json",
                "descendant.cnf",
            }),
            "state": ["00-static.json", "actions"],
            "actions": [],
            "artifacts": [],
            "runtime": [],
        }
        if (
            set(root_id) != root_identity_fields
            or set(lock_id) != file_identity_fields
            or [
                item.get("relative_path")
                if type(item) is dict else None
                for item in target["material_files"]
            ] != fixed_material_paths
            or [
                item.get("relative_path")
                if type(item) is dict else None
                for item in target["directory_inventory"]
            ] != fixed_directory_names
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "incident target identity/inventory schema mismatch"
            )
        for material in target["material_files"]:
            if (
                type(material) is not dict
                or set(material) != material_fields
                or not base._is_sha256(material.get("sha256"))
                or type(material.get("bytes")) is not int
                or material["bytes"] < 0
                or not _stat_identity_shape(material.get("identity"))
                or material["bytes"] != material["identity"]["bytes"]
                or material["identity"]["mode"] != 0o600
                or material["identity"]["uid"] != os.geteuid()
                or material["identity"]["gid"] != os.getegid()
                or material["identity"]["links"] != 1
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "incident target material schema mismatch"
                )
        for expected_name, directory in zip(
            fixed_directory_names, target["directory_inventory"],
            strict=True,
        ):
            if (
                type(directory) is not dict
                or set(directory) != directory_fields
                or type(directory.get("entries")) is not list
                or directory.get("relative_path") != expected_name
                or directory["entries"] != fixed_directory_entries[expected_name]
                or not _stat_identity_shape(directory.get("identity"))
                or directory["identity"]["mode"] != 0o700
                or directory["identity"]["uid"] != os.geteuid()
                or directory["identity"]["gid"] != os.getegid()
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "incident target directory schema mismatch"
                )
        root_paths.add(root_id["path"])
        root_inodes.add((root_id["device"], root_id["inode"]))
        lock_inodes.add((lock_id["device"], lock_id["inode"]))
    _validate_incident_target_semantics(
        root, targets, old_lanes, hard_pins,
        value.get("switch_observation_policy"),
    )
    if (
        len(root_paths) != TARGET_COUNT
        or len(root_inodes) != TARGET_COUNT
        or len(lock_inodes) != TARGET_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident target roots/locks are not unique"
        )
    readonly = {
        "failed_v3_artifacts_preserved_in_place": True,
        "failed_v3_prepared_is_not_reused": True,
        "nine_old_entrypoints_restored": True,
        "eight_targets_static_and_never_started": True,
        "old_batch_fresh_exact_replay": True,
        "old_solver_identities_dead": True,
        "old_proofs_have_no_same_euid_writer": True,
        "attempt_namespace_absent": True,
        "filesystem_mutations_performed": False,
    }
    scope = {
        "incident_record_can_authorize_launch": False,
        "serialized_record_can_authorize_launch": False,
        "only_same_process_lease_after_fresh_rebuild_can_launch": True,
        "checkpoint_proves_unsat": False,
        "scientific_claim": False,
    }
    if (
        not json_type_equal(value.get("readonly_precondition"), readonly)
        or not json_type_equal(value.get("claim_scope"), scope)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident authority/scope mismatch"
        )


def _validate_incident_file(
    root: Path, expected_incident_precondition_sha256: str,
) -> dict[str, Any]:
    pin = base._require_sha256(
        expected_incident_precondition_sha256,
        label="incident precondition pin",
    )
    if root != EXPECTED_BATCH_ROOT:
        raise AdaptiveSwitchEvidenceV4Error(
            "incident file is outside the fixed failed batch"
        )
    path = root / INCIDENT_PRECONDITION
    lexical = path.lstat()
    if (
        stat.S_ISLNK(lexical.st_mode)
        or not stat.S_ISREG(lexical.st_mode)
        or lexical.st_uid != os.geteuid()
        or lexical.st_gid != os.getegid()
        or stat.S_IMODE(lexical.st_mode) != 0o600
        or lexical.st_nlink != 1
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident precondition file metadata is unsafe"
        )
    before_identity = base._stat_identity(lexical)
    value = _stable_owned_json(path)
    after_identity = base._stat_identity(path.lstat())
    if not json_type_equal(before_identity, after_identity):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident precondition file changed while reading"
        )
    fields = {
        "schema_version", "kind", "gate", "attempt_id",
        "fixed_attempt_namespace", "test_only", "production_eligible",
        "authenticated", "launch_authorized", "scientific_claim",
        "batch_root", "batch_root_identity", "batch_manifest_sha256",
        "switch_evidence_sha256", "switch_observation_policy",
        "hard_evidence_sha256s", "failed_attempt", "fresh_old_lanes",
        "target_roots", "target_key_order", "readonly_precondition",
        "source_binding", "claim_scope", "record_sha256",
    }
    if (
        type(value) is not dict or set(value) != fields
        or not selfhash_valid(value)
        or value.get("record_sha256") != pin
        or value.get("schema_version") != SCHEMA_VERSION
        or type(value.get("schema_version")) is not int
        or value.get("kind")
            != "paper400-dic5-adaptive-incident-precondition-v4"
        or value.get("gate") != GATE
        or value.get("attempt_id") != ATTEMPT_ID
        or value.get("fixed_attempt_namespace") != ATTEMPT_ROOT.as_posix()
        or value.get("batch_root") != str(root)
        or value.get("batch_manifest_sha256")
            != EXPECTED_BATCH_MANIFEST_SHA256
        or value.get("switch_evidence_sha256")
            != EXPECTED_SWITCH_EVIDENCE_SHA256
        or value.get("test_only") is not True
        or value.get("production_eligible") is not False
        or value.get("authenticated") is not False
        or value.get("launch_authorized") is not False
        or value.get("scientific_claim") is not False
        or not json_type_equal(
            value.get("batch_root_identity"), base._root_identity(root)
        )
        or not json_type_equal(
            value.get("source_binding"), _v4_source_binding()
        )
        or type(value.get("target_roots")) is not list
        or len(value["target_roots"]) != TARGET_COUNT
        or value.get("target_key_order") != [
            {"lane_index": lane, "descendant_index": descendant}
            for lane, descendant in TARGET_KEYS
        ]
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident precondition file misses external pin/schema"
        )
    policy = value.get("switch_observation_policy")
    try:
        rebuilt_policy = base._observation_policy(
            policy["timeout_seconds"],
            policy["elapsed_seconds_by_lane"],
        )
    except Exception as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "incident observation policy malformed"
        ) from exc
    if not json_type_equal(policy, rebuilt_policy):
        raise AdaptiveSwitchEvidenceV4Error(
            "incident observation policy is noncanonical"
        )
    _validate_incident_nested(root, value)
    return value


def _validate_committed(record: Mapping[str, Any]) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "gate", "test_only",
        "production_eligible", "authenticated", "launch_authorized",
        "scientific_claim", "historical_atomic_handoff_observed",
        "batch_root", "batch_root_identity", "batch_manifest_sha256",
        "switch_evidence_sha256", "switch_observation_policy",
        "prepared_retirement_sha256", "retired_locks",
        "root_bindings", "fence_sha256s", "cohort_policy",
        "source_binding", "root_link_policy", "claim_scope",
        "attempt_id", "incident_precondition_sha256",
        "failed_v3_intent_sha256", "failed_v3_prepared_sha256",
        "record_sha256",
    }
    if (
        type(record) is not dict or set(record) != fields
        or not selfhash_valid(record)
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff schema/self-hash mismatch"
        )
    if (
        type(record.get("schema_version")) is not int
        or record.get("schema_version") != SCHEMA_VERSION
        or record.get("kind") != HANDOFF_KIND
        or record.get("gate") != GATE
        or record.get("test_only") is not True
        or record.get("production_eligible") is not False
        or record.get("authenticated") is not False
        or record.get("launch_authorized") is not False
        or record.get("scientific_claim") is not False
        or record.get("historical_atomic_handoff_observed") is not True
        or record.get("batch_root") != str(EXPECTED_BATCH_ROOT)
        or not json_type_equal(
            record.get("batch_root_identity"),
            base._root_identity(EXPECTED_BATCH_ROOT),
        )
        or record.get("batch_manifest_sha256")
            != EXPECTED_BATCH_MANIFEST_SHA256
        or record.get("switch_evidence_sha256")
            != EXPECTED_SWITCH_EVIDENCE_SHA256
        or not json_type_equal(
            record.get("source_binding"), _v4_source_binding()
        )
        or not json_type_equal(record.get("root_link_policy"), {
            "relative_path": "state/15-batch-handoff.json",
            "publish": "o-excl-canonical-json-fsync-v1",
            "repair_only_from_externally_pinned_batch_commit": True,
        })
        or not json_type_equal(record.get("claim_scope"), {
            "old_transport_durably_retired_before_first_new_start":
                True,
            "eight_new_processes_observed_started": True,
            "four_new_processes_checkpointed_at_commit": True,
            "four_new_processes_observed_alive_at_commit": True,
            "max_live_workers": MAX_LIVE_WORKERS,
            "serialized_record_can_authorize_launch": False,
            "serialized_record_can_authenticate_unsat": False,
        })
        or not base._is_sha256(
            record.get("incident_precondition_sha256")
        )
        or not _attempt_binding_valid(
            record, record["incident_precondition_sha256"]
        )
        or type(record.get("batch_root")) is not str
        or any(
            not base._is_sha256(record.get(field))
            for field in (
                "batch_manifest_sha256", "switch_evidence_sha256",
                "prepared_retirement_sha256", "record_sha256",
            )
        )
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff authority/hash mismatch"
        )
    policy = record.get("switch_observation_policy")
    try:
        rebuilt_policy = base._observation_policy(
            policy["timeout_seconds"],
            policy["elapsed_seconds_by_lane"],
        )
    except Exception as exc:
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff observation policy malformed"
        ) from exc
    if not json_type_equal(policy, rebuilt_policy):
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff observation policy mismatch"
        )
    expected_cohort_policy = {
        "target_keys": [
            [lane, descendant] for lane, descendant in TARGET_KEYS
        ],
        "target_count": TARGET_COUNT,
        "cohort_count": DESCENDANT_COUNT,
        "cohort_size": LANE_COUNT,
        "max_live_workers": MAX_LIVE_WORKERS,
        "checkpointed_at_commit": LANE_COUNT,
        "running_at_commit": LANE_COUNT,
    }
    if not json_type_equal(
        record.get("cohort_policy"), expected_cohort_policy
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff cohort policy mismatch"
        )
    bindings = record.get("root_bindings")
    fences = record.get("fence_sha256s")
    retired = record.get("retired_locks")
    if (
        type(bindings) is not list or len(bindings) != TARGET_COUNT
        or type(fences) is not list or len(fences) != TARGET_COUNT
        or type(retired) is not list or len(retired) != 9
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff cardinality mismatch"
        )
    binding_fields = {
        "lane_index", "global_leaf_index", "descendant_index",
        "descendant_sha256", "new_root_identity",
        "new_session_sha256", "new_start_commit_sha256",
        "new_pid", "new_proc_start_ticks", "permit_binding_sha256",
        "prepared_target_sha256", "started_worker_journal_sha256",
        "fence_sha256", "cohort_index", "handoff_state",
        "cohort_quiescence_sha256",
    }
    roots: set[str] = set()
    pids: set[int] = set()
    for position, (key, item) in enumerate(
        zip(TARGET_KEYS, bindings, strict=True)
    ):
        unsigned = dict(item) if type(item) is dict else {}
        fence = unsigned.pop("fence_sha256", None)
        cohort_index = unsigned.pop("cohort_index", None)
        state = unsigned.pop("handoff_state", None)
        quiescence = unsigned.pop(
            "cohort_quiescence_sha256", None
        )
        expected_state = (
            "CHECKPOINTED" if key[1] == 0 else "RUNNING"
        )
        if (
            type(item) is not dict or set(item) != binding_fields
            or (item.get("lane_index"),
                item.get("descendant_index")) != key
            or cohort_index != key[1] or state != expected_state
            or (
                key[1] == 0 and not base._is_sha256(quiescence)
            )
            or (key[1] == 1 and quiescence is not None)
            or canonical_sha256(unsigned) != fence
            or fences[position] != fence
            or any(
                not base._is_sha256(item.get(field))
                for field in (
                    "descendant_sha256", "new_session_sha256",
                    "new_start_commit_sha256",
                    "permit_binding_sha256",
                    "prepared_target_sha256",
                    "started_worker_journal_sha256", "fence_sha256",
                )
            )
            or type(item.get("global_leaf_index")) is not int
            or type(item.get("new_pid")) is not int
            or type(item.get("new_proc_start_ticks")) is not int
            or item["new_pid"] <= 0
            or item["new_proc_start_ticks"] <= 0
            or type(item.get("new_root_identity")) is not dict
            or type(item["new_root_identity"].get("path")) is not str
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "fence/cohort binding mismatch"
            )
        roots.add(item["new_root_identity"]["path"])
        pids.add(item["new_pid"])
    if len(roots) != TARGET_COUNT or len(pids) != TARGET_COUNT:
        raise AdaptiveSwitchEvidenceV4Error(
            "handoff roots/PIDs duplicate"
        )
    return dict(record)


def _validate_retirement_chain(
    root: Path, commit: Mapping[str, Any],
    incident_precondition_sha256: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    common = {
        "attempt_id", "incident_precondition_sha256",
        "failed_v3_intent_sha256", "failed_v3_prepared_sha256",
    }
    intent_fields = {
        "schema_version", "kind", "gate", "test_only",
        "production_eligible", "authenticated", "launch_authorized",
        *common, "batch_root", "batch_manifest_sha256",
        "switch_evidence_sha256", "target_journal_directory",
        "started_journal_directory", "quiescence_journal_directory",
        "lock_plan", "retirement_complete", "source_binding",
        "record_sha256",
    }
    prepared_fields = {
        "schema_version", "kind", "gate", "test_only",
        "production_eligible", "authenticated", "launch_authorized",
        "scientific_claim", *common, "batch_root",
        "batch_root_identity", "batch_manifest_sha256",
        "switch_evidence_sha256", "retirement_intent_sha256",
        "retired_locks", "retirement_complete",
        "old_runner_entrypoints_reachable", "source_binding",
        "record_sha256",
    }
    intent = _read_handoff_journal(
        root / RETIREMENT_INTENT,
        expected_fields=intent_fields,
        expected_kind=
            "paper400-dic5-adaptive-retirement-intent-v4",
    )
    prepared = _read_handoff_journal(
        root / PREPARED_COMMIT,
        expected_fields=prepared_fields,
        expected_kind=PREPARED_KIND,
    )
    plans = intent.get("lock_plan")
    retired = prepared.get("retired_locks")
    if (
        not _attempt_binding_valid(
            intent, incident_precondition_sha256
        )
        or not _attempt_binding_valid(
            prepared, incident_precondition_sha256
        )
        or intent.get("test_only") is not True
        or intent.get("production_eligible") is not False
        or prepared.get("test_only") is not True
        or prepared.get("production_eligible") is not False
        or intent.get("batch_root") != str(root)
        or prepared.get("batch_root") != str(root)
        or intent.get("batch_manifest_sha256")
            != commit.get("batch_manifest_sha256")
        or prepared.get("batch_manifest_sha256")
            != commit.get("batch_manifest_sha256")
        or intent.get("switch_evidence_sha256")
            != commit.get("switch_evidence_sha256")
        or prepared.get("switch_evidence_sha256")
            != commit.get("switch_evidence_sha256")
        or intent.get("target_journal_directory")
            != str(root / TARGET_DIRECTORY)
        or intent.get("started_journal_directory")
            != str(root / STARTED_DIRECTORY)
        or intent.get("quiescence_journal_directory")
            != str(root / QUIESCENCE_DIRECTORY)
        or intent.get("retirement_complete") is not False
        or prepared.get("retirement_complete") is not True
        or prepared.get("old_runner_entrypoints_reachable") is not False
        or prepared.get("scientific_claim") is not False
        or prepared.get("retirement_intent_sha256")
            != intent.get("record_sha256")
        or prepared.get("record_sha256")
            != commit.get("prepared_retirement_sha256")
        or not json_type_equal(
            prepared.get("batch_root_identity"),
            base._root_identity(root),
        )
        or not json_type_equal(
            intent.get("source_binding"), _v4_source_binding()
        )
        or not json_type_equal(
            prepared.get("source_binding"), _v4_source_binding()
        )
        or not json_type_equal(
            retired, commit.get("retired_locks")
        )
        or type(plans) is not list or len(plans) != 9
        or type(retired) is not list or len(retired) != 9
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "v4 retirement journal chain mismatch"
        )
    expected_roles = [
        *(f"controller-{index}" for index in range(LANE_COUNT)),
        *(f"lane-{index}" for index in range(LANE_COUNT)), "batch",
    ]
    for sequence, (role, plan, item) in enumerate(
        zip(expected_roles, plans, retired, strict=True)
    ):
        if role.startswith("controller-"):
            lane = int(role.rsplit("-", 1)[1])
            expected_original = (
                root / "lanes" / f"lane-{lane}"
                / "runtime/dmtcp/.controller.lock"
            )
        elif role.startswith("lane-"):
            lane = int(role.rsplit("-", 1)[1])
            expected_original = (
                root / "lanes" / f"lane-{lane}"
                / ".hierarchical-resume.lock"
            )
        else:
            expected_original = root / ".batch.lock"
        expected_retired = expected_original.with_name(
            expected_original.name
            + ".retired-v4-" + ATTEMPT_ID[:16]
        )
        if (
            type(plan) is not dict
            or set(plan) != {
                "sequence", "role", "original_path", "retired_path",
                "pre_rename_identity",
            }
            or type(item) is not dict
            or set(item) != {
                "sequence", "role", "original_path", "retired_path",
                "pre_rename_identity", "identity",
            }
            or plan.get("sequence") != sequence
            or item.get("sequence") != sequence
            or plan.get("role") != role
            or item.get("role") != role
            or plan.get("original_path") != str(expected_original)
            or item.get("original_path") != str(expected_original)
            or plan.get("retired_path") != str(expected_retired)
            or item.get("retired_path") != str(expected_retired)
            or not _stat_identity_shape(
                plan.get("pre_rename_identity")
            )
            or not _stat_identity_shape(item.get("identity"))
            or not json_type_equal(
                plan.get("pre_rename_identity"),
                item.get("pre_rename_identity"),
            )
            or not json_type_equal(
                _identity_without_ctime(
                    plan["pre_rename_identity"]
                ),
                _identity_without_ctime(item["identity"]),
            )
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "v4 retirement plan/prepared mismatch"
            )
    return intent, prepared


def verify_committed_handoff(
    batch_commit_path: Path, *, expected_batch_commit_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_batch_manifest_sha256: str,
    expected_attempt_id: str,
    expected_incident_precondition_sha256: str,
) -> dict[str, Any]:
    commit_pin = base._require_sha256(
        expected_batch_commit_sha256, label="batch handoff pin"
    )
    switch_pin = base._require_sha256(
        expected_switch_evidence_sha256, label="switch evidence pin"
    )
    batch_pin = base._require_sha256(
        expected_batch_manifest_sha256, label="batch manifest pin"
    )
    incident_pin = base._require_sha256(
        expected_incident_precondition_sha256,
        label="incident precondition pin",
    )
    if (
        type(expected_attempt_id) is not str
        or expected_attempt_id != ATTEMPT_ID
    ):
        raise AdaptiveSwitchEvidenceV4Error("wrong fixed v4 attempt id")
    if (
        switch_pin != EXPECTED_SWITCH_EVIDENCE_SHA256
        or batch_pin != EXPECTED_BATCH_MANIFEST_SHA256
        or Path(batch_commit_path)
            != EXPECTED_BATCH_ROOT / HANDOFF_COMMIT
    ):
        raise AdaptiveSwitchEvidenceV4Error("wrong production path/pin")
    path = Path(batch_commit_path)
    record = _validate_committed(_stable_owned_json(path))
    root = Path(record["batch_root"])
    rollback_path = root / ROLLBACK_COMMIT
    if rollback_path.exists() or rollback_path.is_symlink():
        raise AdaptiveSwitchEvidenceV4Error(
            "committed handoff was rolled back"
        )
    if (
        path != root / HANDOFF_COMMIT or record["record_sha256"] != commit_pin
        or record["switch_evidence_sha256"] != switch_pin
        or record["batch_manifest_sha256"] != batch_pin
        or record["attempt_id"] != expected_attempt_id
        or record["incident_precondition_sha256"] != incident_pin
        or not json_type_equal(record["batch_root_identity"], base._root_identity(root))
    ):
        raise AdaptiveSwitchEvidenceV4Error("handoff path/pin mismatch")
    incident = _validate_incident_file(root, incident_pin)
    _, prepared = _validate_retirement_chain(
        root, record, incident_pin
    )
    if prepared["record_sha256"] != record["prepared_retirement_sha256"]:
        raise AdaptiveSwitchEvidenceV4Error(
            "prepared retirement misses handoff commit"
        )
    journal_bindings = _verify_committed_journals(root, record)
    verified: list[dict[str, Any]] = []
    for item in record["retired_locks"]:
        original = Path(item["original_path"])
        retired = Path(item["retired_path"])
        if original.exists() or original.is_symlink():
            raise AdaptiveSwitchEvidenceV4Error("old runner entry point was restored")
        observed = retired.lstat()
        if (
            stat.S_ISLNK(observed.st_mode) or not stat.S_ISREG(observed.st_mode)
            or not json_type_equal(base._stat_identity(observed), item["identity"])
        ):
            raise AdaptiveSwitchEvidenceV4Error("retired lock identity mismatch")
        verified.append(dict(item))
    return seal({
        "schema_version": SCHEMA_VERSION, "kind": HANDOFF_VERIFY_KIND,
        "valid": True, "authenticated": False, "launch_authorized": False,
        "production_eligible": False, "scientific_claim": False,
        "historical_handoff_only": True,
        "batch_commit_sha256": record["record_sha256"],
        **_attempt_binding(incident_pin),
        "incident_record_sha256": incident["record_sha256"],
        "switch_evidence_sha256": record["switch_evidence_sha256"],
        "batch_manifest_sha256": record["batch_manifest_sha256"],
        "prepared_retirement_sha256": record["prepared_retirement_sha256"],
        "old_runner_entrypoints_absent": True,
        "retired_locks": verified,
        "root_bindings": list(record["root_bindings"]),
        "fence_sha256s": list(record["fence_sha256s"]),
        "cohort_policy": dict(record["cohort_policy"]),
        "journal_bindings": journal_bindings,
        "root_link_policy": dict(record["root_link_policy"]),
    })


def rollback_committed_handoff(
    batch_commit_path: Path, *, expected_batch_commit_sha256: str,
    expected_switch_evidence_sha256: str,
    expected_batch_manifest_sha256: str,
    expected_attempt_id: str,
    expected_incident_precondition_sha256: str,
    expected_switch_record: Mapping[str, Any],
    quiescence_records: list[dict[str, Any]],
) -> dict[str, Any]:
    """Retire eight new roots/16 entrypoints and restore the exact old batch."""

    commit_pin = base._require_sha256(
        expected_batch_commit_sha256, label="batch handoff pin"
    )
    switch_pin = base._require_sha256(
        expected_switch_evidence_sha256, label="switch evidence pin"
    )
    batch_pin = base._require_sha256(
        expected_batch_manifest_sha256, label="batch manifest pin"
    )
    incident_pin = base._require_sha256(
        expected_incident_precondition_sha256,
        label="incident precondition pin",
    )
    if (
        switch_pin != EXPECTED_SWITCH_EVIDENCE_SHA256
        or batch_pin != EXPECTED_BATCH_MANIFEST_SHA256
        or type(expected_attempt_id) is not str
        or expected_attempt_id != ATTEMPT_ID
        or Path(batch_commit_path)
            != EXPECTED_BATCH_ROOT / HANDOFF_COMMIT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "wrong rollback production path/attempt/pin"
        )
    if (
        type(expected_switch_record) is not dict
        or not selfhash_valid(expected_switch_record)
        or expected_switch_record.get("record_sha256") != switch_pin
        or expected_switch_record.get("batch_manifest_sha256")
            != batch_pin
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "committed rollback switch record misses external pins"
        )
    validate_switch_record_structure(expected_switch_record)
    verify_committed_handoff(
        batch_commit_path,
        expected_batch_commit_sha256=commit_pin,
        expected_switch_evidence_sha256=switch_pin,
        expected_batch_manifest_sha256=batch_pin,
        expected_attempt_id=expected_attempt_id,
        expected_incident_precondition_sha256=
            expected_incident_precondition_sha256,
    )
    if (
        type(quiescence_records) is not list
        or len(quiescence_records) != TARGET_COUNT
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "committed rollback quiescence cardinality malformed"
        )
    by_key: dict[tuple[int, int], dict[str, Any]] = {}
    for value in quiescence_records:
        item = _validate_quiescence_record(value)
        key = (item["lane_index"], item["descendant_index"])
        if key in by_key:
            raise AdaptiveSwitchEvidenceV4Error(
                "duplicate committed rollback target"
            )
        by_key[key] = item
    if set(by_key) != set(TARGET_KEYS):
        raise AdaptiveSwitchEvidenceV4Error(
            "committed rollback must cover eight targets"
        )
    path = Path(batch_commit_path)
    commit = _validate_committed(_stable_owned_json(path))
    root = Path(commit["batch_root"])
    if (
        path != root / HANDOFF_COMMIT
        or commit["record_sha256"] != commit_pin
        or commit["switch_evidence_sha256"] != switch_pin
        or commit["batch_manifest_sha256"] != batch_pin
        or commit["attempt_id"] != expected_attempt_id
        or commit["incident_precondition_sha256"]
            != expected_incident_precondition_sha256
    ):
        raise AdaptiveSwitchEvidenceV4Error(
            "committed rollback pin/path mismatch"
        )
    bindings = {
        (item["lane_index"], item["descendant_index"]): item
        for item in commit["root_bindings"]
    }
    if set(bindings) != set(TARGET_KEYS):
        raise AdaptiveSwitchEvidenceV4Error(
            "committed root bindings are not exact"
        )
    root_identities = [
        bindings[key]["new_root_identity"] for key in TARGET_KEYS
    ]
    for key in TARGET_KEYS:
        item = by_key[key]
        if not json_type_equal(
            item["new_root_identity"],
            bindings[key]["new_root_identity"],
        ):
            raise AdaptiveSwitchEvidenceV4Error(
                "committed quiescence misses target root"
            )
    discovery = base._discover_sources(
        root, expected_batch_manifest_sha256=batch_pin
    )
    _, child, _ = _load_legacy_exact(discovery)
    new_locks = _acquire_new_root_fences(root_identities)
    new_retired: list[tuple[Any, dict[str, Any]]] = []
    old_locks: list[Any] = []
    old_restored: list[tuple[Any, dict[str, Any]]] = []
    try:
        rollback_path = root / ROLLBACK_COMMIT
        if rollback_path.exists() or rollback_path.is_symlink():
            raise AdaptiveSwitchEvidenceV4Error(
                "committed handoff already rolled back"
            )
        fresh_commit = _validate_committed(_stable_owned_json(path))
        if not json_type_equal(fresh_commit, commit):
            raise AdaptiveSwitchEvidenceV4Error(
                "handoff commit changed under rollback locks"
            )
        _verify_committed_journals(root, fresh_commit)
        for key in TARGET_KEYS:
            item = by_key[key]
            binding = bindings[key]
            identity = binding["new_root_identity"]
            target_root = Path(identity["path"])
            if not json_type_equal(
                base._root_identity(target_root), identity
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "new root changed before rollback"
                )
            try:
                alive = (
                    base._proc_start_ticks(item["new_pid"])
                    == item["new_proc_start_ticks"]
                )
            except Exception:
                alive = False
            if alive:
                raise AdaptiveSwitchEvidenceV4Error(
                    "new worker remains alive"
                )
            inspection = _direct_controller_inspect(child, target_root)
            generations = inspection.get("generations")
            latest = (
                generations[-1]
                if type(generations) is list and generations else {}
            )
            if (
                inspection.get("hash_verification_requested") is not True
                or inspection.get("state") != item["state"]
                or latest.get("pid_identity_alive") is not False
                or latest.get("poison_claim") not in {None, False}
                or latest.get("active_error") not in {None, False}
                or latest.get("checkpoint_error") not in {None, False}
                or type(latest.get("generation")) is not int
                or latest["generation"] < 0
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "committed rollback controller is not quiescent"
                )
            generation = latest["generation"]
            generation_dir = (
                target_root / child.RUNTIME_ROOT
                / "generations" / f"{generation:06d}"
            )
            with child._fixed_environment():
                active = child.controller._active_commit(
                    generation_dir, generation
                )
            if (
                active.get("pid") != item["new_pid"]
                or active.get("proc_start_ticks")
                    != item["new_proc_start_ticks"]
                or active.get("self_sha256")
                    != latest.get("active_manifest_sha256")
                or (
                    item["new_pid"] == binding["new_pid"]
                    and item["new_proc_start_ticks"]
                        == binding["new_proc_start_ticks"]
                    and active.get("self_sha256")
                        != binding["new_start_commit_sha256"]
                )
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "committed rollback active generation mismatch"
                )
            if item["state"] == "CHECKPOINTED":
                if (
                    latest.get("checkpointed") is not True
                    or latest.get("checkpoint_hashes_valid") is not True
                    or latest.get("checkpoint_manifest_sha256")
                        != item["checkpoint_commit_sha256"]
                ):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "committed rollback checkpoint mismatch"
                    )
                with child._fixed_environment():
                    checkpoint = child.controller._checkpoint_commit(
                        generation_dir, generation
                    )
                prefix = checkpoint.get("proof_prefix")
                if (
                    checkpoint.get("self_sha256")
                        != item["checkpoint_commit_sha256"]
                    or checkpoint.get("single_writer_stopped") is not True
                    or type(prefix) is not dict
                    or prefix.get("sha256") != item["proof_sha256"]
                    or prefix.get("bytes") != item["proof_bytes"]
                ):
                    raise AdaptiveSwitchEvidenceV4Error(
                        "committed checkpoint proof mismatch"
                    )
            elif latest.get("checkpointed") is not False:
                raise AdaptiveSwitchEvidenceV4Error(
                    "inactive rollback target has a checkpoint"
                )
            proof = (
                target_root / child.RUNTIME_ROOT / "proof.drat"
            )
            digest, size, proof_identity = _stream_hash_size_identity(
                proof
            )
            if (
                digest != item["proof_sha256"]
                or size != item["proof_bytes"]
                or _writable_holders(
                    proof, expected_identity=proof_identity
                ) != []
            ):
                raise AdaptiveSwitchEvidenceV4Error(
                    "new proof changed or has a writer"
                )
        suffix = ATTEMPT_ID[:16]
        try:
            for sequence, held in enumerate(new_locks):
                retired_path = held.original_path.with_name(
                    held.original_path.name
                    + f".rolled-back-v4-{suffix}"
                )
                retirement = _retire_lock_v3(held, retired_path)
                new_retired.append((
                    held, {"sequence": sequence, **retirement}
                ))
        except BaseException:
            failures: list[BaseException] = []
            for held, retirement in reversed(new_retired):
                try:
                    _restore_lock_v3(held, retirement)
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV4Error(
                    "partial new retirement could not be compensated"
                ) from failures[0]
            raise
        try:
            old_locks, old_by_role = _acquire_retired_old_locks(
                commit["retired_locks"]
            )
        except BaseException:
            failures = []
            for held, retirement in reversed(new_retired):
                try:
                    _restore_lock_v3(held, retirement)
                except BaseException as exc:
                    failures.append(exc)
            if failures:
                raise AdaptiveSwitchEvidenceV4Error(
                    "old lock acquisition failed and new restore failed"
                ) from failures[0]
            raise
        try:
            roles = [
                "batch", *(
                    f"lane-{index}" for index in range(LANE_COUNT)
                ), *(
                    f"controller-{index}"
                    for index in range(LANE_COUNT)
                ),
            ]
            held_by_role = {
                held.role.removeprefix("old-retired:"): held
                for held in old_locks
            }
            restored_old: list[dict[str, Any]] = []
            for role in reversed(roles):
                held = held_by_role[role]
                retirement = old_by_role[role]
                restored_old.append(
                    _restore_external_old_lock(held, retirement)
                )
                old_restored.append((held, retirement))
            replay = _fresh_restored_old_checkpoint(
                root,
                expected_batch_manifest_sha256=batch_pin,
                expected_switch_evidence_sha256=switch_pin,
                expected_switch_record=expected_switch_record,
                switch_observation_policy=
                    commit["switch_observation_policy"],
                incident_precondition_sha256=
                    expected_incident_precondition_sha256,
            )
            rollback = seal({
                "schema_version": SCHEMA_VERSION,
                "kind": ROLLBACK_KIND, "gate": GATE,
                "test_only": True, "production_eligible": False,
                "authenticated": False, "launch_authorized": False,
                "scientific_claim": False,
                **_attempt_binding(
                    expected_incident_precondition_sha256
                ),
                "batch_root": str(root),
                "batch_root_identity": base._root_identity(root),
                "committed_handoff_sha256": commit_pin,
                "switch_evidence_sha256": switch_pin,
                "batch_manifest_sha256": batch_pin,
                "prepared_retirement_sha256":
                    commit["prepared_retirement_sha256"],
                "quiescence_record_sha256s": [
                    by_key[key]["record_sha256"]
                    for key in TARGET_KEYS
                ],
                "retired_new_locks": [
                    item for _, item in new_retired
                ],
                "restored_old_locks": restored_old,
                "old_checkpoint_replay": replay,
                "old_checkpoint_replayed": True,
                "exact_switch_record_equal": True,
                "new_workers_quiescent": True,
                "claim_scope": {
                    "sixteen_new_entrypoints_retired_before_old_restore":
                        True,
                    "eight_new_roots_locked_during_transition": True,
                    "serialized_record_can_authorize_launch": False,
                    "serialized_record_can_authenticate_unsat": False,
                },
                "source_binding": _v4_source_binding(),
            })
            _publish(rollback_path, rollback)
        except BaseException:
            compensation_failures: list[BaseException] = []
            for held, retirement in reversed(old_restored):
                try:
                    _reretire_external_old_lock(held, retirement)
                except BaseException as exc:
                    compensation_failures.append(exc)
            if compensation_failures:
                raise AdaptiveSwitchEvidenceV4Error(
                    "committed rollback failed and old re-retirement failed"
                ) from compensation_failures[0]
            raise
        return json.loads(canonical_bytes(rollback))
    finally:
        _close_locks(old_locks)
        _close_locks(new_locks)


LaunchPermit = base.LaunchPermit

__all__ = [
    "AdaptiveSwitchEvidenceV4Error", "AtomicSwitchLease", "LaunchPermit",
    "StartedWorker", "PostStartFence", "CohortTransitionPermit",
    "ATTEMPT_ID", "ATTEMPT_ROOT", "INCIDENT_PRECONDITION",
    "HANDOFF_COMMIT", "PREPARED_COMMIT", "ROLLBACK_COMMIT",
    "TARGET_KEYS", "TARGET_COUNT", "MAX_LIVE_WORKERS",
    "QUIESCENCE_INPUT_KIND", "QUIESCENCE_KIND",
    "EXPECTED_HARD_EVIDENCE_SHA256S",
    "acquire_atomic_switch_lease", "build_incident_precondition",
    "build_switch_evidence_record", "validate_switch_record_structure",
    "verify_committed_handoff", "rollback_committed_handoff",
    "canonical_bytes", "canonical_sha256",
    "seal", "selfhash_valid", "json_type_equal",
]
