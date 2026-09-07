from __future__ import annotations

import fcntl
import hashlib
import os
from pathlib import Path
from typing import Any

import pytest

from scripts import paper400_drat_segv_quarantine_guard_v1 as guard
from scripts import render_paper400_drat_segv_quarantine_v1 as renderer


def _write(path: Path, payload: bytes, mode: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(payload)
    path.chmod(mode)


def _full(path: Path) -> dict[str, int]:
    return guard.identity_record(path.stat(follow_symlinks=False), full=True)


def _root(path: Path) -> dict[str, int]:
    return guard.identity_record(path.stat(follow_symlinks=False), full=False)


def _entry(root: Path, checker: Path, entry_id: str) -> dict[str, Any]:
    lock = root / ".hierarchical-resume.lock"
    proof = root / "runtime/dmtcp/proof.drat"
    cube = root / "static/cube.cnf"
    return {
        "id": entry_id,
        "quarantine_enabled": True,
        "root": str(root),
        "root_identity": _root(root),
        "lock": {
            "relative_path": ".hierarchical-resume.lock",
            "identity": _full(lock),
            "sha256": hashlib.sha256(b"").hexdigest(),
        },
        "proof": {
            "relative_path": "runtime/dmtcp/proof.drat",
            "identity": _full(proof),
            "sha256": hashlib.sha256(proof.read_bytes()).hexdigest(),
            "content_hash_replay": "journal-bound-stat-only",
        },
        "cube": {
            "relative_path": "static/cube.cnf",
            "identity": _full(cube),
            "sha256": hashlib.sha256(cube.read_bytes()).hexdigest(),
        },
        "checker": {
            "path": str(checker),
            "identity": _full(checker),
            "sha256": guard.BAD_CHECKER_SHA256,
        },
        "incident": {
            "deterministic_attempts": 56,
            "signal": 11,
            "all_same_proof_cube_checker": True,
        },
        "alternative_certification": "none",
        "required_absent_relative_paths": sorted(guard.REQUIRED_ABSENT),
    }


def _fixture(
    tmp_path: Path, *, entries: int = 1,
) -> tuple[Path, str, list[dict[str, Any]]]:
    checker = tmp_path / "toolchain/drat-trim"
    # Tests exercise binding, not the executable.  Override the production
    # digest constant to a deterministic fixture digest.
    _write(checker, b"fixed checker fixture\n", 0o755)
    fixture_sha = hashlib.sha256(checker.read_bytes()).hexdigest()
    roots: list[Path] = []
    for index in range(entries):
        root = tmp_path / f"leaf-{index}"
        root.mkdir(mode=0o700)
        root.chmod(0o700)
        _write(root / ".hierarchical-resume.lock", b"", 0o600)
        _write(root / "runtime/dmtcp/proof.drat", b"proof\x00" + bytes([index]), 0o600)
        _write(root / "static/cube.cnf", b"p cnf 1 2\n1 0\n-1 0\n", 0o600)
        (root / "state").mkdir(mode=0o700)
        roots.append(root)
    old = guard.BAD_CHECKER_SHA256
    guard.BAD_CHECKER_SHA256 = fixture_sha
    try:
        values = [_entry(root, checker, f"r4-c{index:04d}") for index, root in enumerate(roots)]
    finally:
        guard.BAD_CHECKER_SHA256 = old
    manifest = guard.seal_manifest({
        "schema_version": 1,
        "kind": guard.SCHEMA,
        "bad_checker_sha256": fixture_sha,
        "entries": values,
    })
    path = tmp_path / "incident.json"
    path.write_bytes(guard.manifest_payload(manifest))
    path.chmod(0o600)
    return path, hashlib.sha256(path.read_bytes()).hexdigest(), values


@pytest.fixture(autouse=True)
def _fixture_checker_digest(monkeypatch: pytest.MonkeyPatch, tmp_path: Path):
    # _fixture creates the checker after this fixture starts.  Individual tests
    # update the digest immediately after construction via this holder.
    yield


def _set_digest(monkeypatch: pytest.MonkeyPatch, manifest: Path) -> None:
    value = __import__("json").loads(manifest.read_bytes())
    digest = value["bad_checker_sha256"]
    monkeypatch.setattr(guard, "BAD_CHECKER_SHA256", digest)


def _rewrite_manifest(manifest: Path, mutate) -> str:
    import json

    value = json.loads(manifest.read_bytes())
    value.pop("record_sha256")
    mutate(value)
    manifest.write_bytes(guard.manifest_payload(guard.seal_manifest(value)))
    return hashlib.sha256(manifest.read_bytes()).hexdigest()


def _exclusive_available(path: Path) -> bool:
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return False
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        return True
    finally:
        os.close(descriptor)


def test_acquire_retains_shared_lock_without_modifying_inputs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    lock = Path(entries[0]["root"]) / ".hierarchical-resume.lock"
    before = {path: path.stat(follow_symlinks=False) for path in (manifest, lock)}
    held = guard.acquire(manifest, digest, entries[0]["id"])
    try:
        assert not _exclusive_available(lock)
        guard.replay(held)
    finally:
        guard.close(held)
    assert _exclusive_available(lock)
    for path, info in before.items():
        after = path.stat(follow_symlinks=False)
        assert (after.st_size, after.st_mtime_ns, after.st_ctime_ns) == (
            info.st_size, info.st_mtime_ns, info.st_ctime_ns,
        )


def test_busy_exclusive_checker_is_retried_only_after_natural_release(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    lock = Path(entries[0]["root"]) / ".hierarchical-resume.lock"
    competitor = os.open(lock, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        fcntl.flock(competitor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(guard.QuarantineBusyError, match="exclusively busy"):
            guard.acquire(manifest, digest, entries[0]["id"])
    finally:
        fcntl.flock(competitor, fcntl.LOCK_UN)
        os.close(competitor)
    held = guard.acquire(manifest, digest, entries[0]["id"])
    guard.close(held)


def test_two_shared_guards_allow_gapless_handoff(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    lock = Path(entries[0]["root"]) / ".hierarchical-resume.lock"
    old = guard.acquire(manifest, digest, entries[0]["id"])
    new = guard.acquire(manifest, digest, entries[0]["id"])
    try:
        assert not _exclusive_available(lock)
        guard.close(old)
        old = None
        assert not _exclusive_available(lock)
        guard.replay(new)
    finally:
        guard.close(old)
        guard.close(new)
    assert _exclusive_available(lock)


def test_ready_occurs_only_after_complete_replay(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    lock = Path(entries[0]["root"]) / ".hierarchical-resume.lock"

    class ReadyObserved(RuntimeError):
        pass

    def inspect(held: guard.HeldQuarantine) -> None:
        guard.replay(held)
        assert not _exclusive_available(lock)
        raise ReadyObserved

    monkeypatch.setattr(guard, "_notify_ready", inspect)
    with pytest.raises(ReadyObserved):
        guard.hold(manifest, digest, entries[0]["id"], replay_seconds=0.1)
    assert _exclusive_available(lock)


def test_periodic_replay_rejects_proof_path_replacement(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    proof = Path(entries[0]["root"]) / "runtime/dmtcp/proof.drat"
    held = guard.acquire(manifest, digest, entries[0]["id"])
    try:
        proof.rename(proof.with_suffix(".old"))
        _write(proof, b"replacement", 0o600)
        with pytest.raises(guard.QuarantineGuardError, match="bound pathname changed"):
            guard.replay(held)
    finally:
        guard.close(held)


def test_terminal_progress_between_manifest_and_lock_rejects_quarantine(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    root = Path(entries[0]["root"])
    _write(root / "state/21-drat.json", b"{}\n", 0o600)
    with pytest.raises(guard.QuarantineGuardError, match="artifact exists"):
        guard.acquire(manifest, digest, entries[0]["id"])
    assert _exclusive_available(root / ".hierarchical-resume.lock")


def test_terminal_absence_cannot_be_hidden_behind_state_symlink(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    root = Path(entries[0]["root"])
    state = root / "state"
    state.rename(root / "real-state")
    decoy = tmp_path / "decoy-state"
    decoy.mkdir(mode=0o700)
    state.symlink_to(decoy, target_is_directory=True)
    with pytest.raises(
        guard.QuarantineGuardError,
        match="terminal-absence ancestor is unavailable or unsafe",
    ):
        guard.acquire(manifest, digest, entries[0]["id"])
    assert _exclusive_available(root / ".hierarchical-resume.lock")


def test_manifest_tamper_and_alternate_path_fail_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    payload = bytearray(manifest.read_bytes())
    payload[payload.index(b"56")] = ord("4")
    manifest.write_bytes(payload)
    with pytest.raises(guard.QuarantineGuardError, match="manifest file SHA"):
        guard.acquire(manifest, digest, entries[0]["id"])


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda value: value["entries"][0].__setitem__("quarantine_enabled", False),
            "admitted deterministic crash quarantine",
        ),
        (
            lambda value: value["entries"][0]["lock"].__setitem__("sha256", "0" * 64),
            "hierarchy lock sentinel",
        ),
        (
            lambda value: value["entries"][0]["proof"].__setitem__(
                "relative_path", "runtime/dmtcp/not-the-proof.drat",
            ),
            "hash replay policy",
        ),
        (
            lambda value: value["entries"][0]["cube"].__setitem__(
                "relative_path", "static/not-the-cube.cnf",
            ),
            "static cube pathname",
        ),
    ],
)
def test_manifest_cannot_redirect_or_disable_quarantine_contract(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mutate, message: str,
) -> None:
    manifest, _digest, entries = _fixture(tmp_path)
    _set_digest(monkeypatch, manifest)
    digest = _rewrite_manifest(manifest, mutate)
    with pytest.raises(guard.QuarantineGuardError, match=message):
        guard.acquire(manifest, digest, entries[0]["id"])


def test_entries_acquire_independently_when_one_root_is_busy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, digest, entries = _fixture(tmp_path, entries=2)
    _set_digest(monkeypatch, manifest)
    busy_lock = Path(entries[0]["root"]) / ".hierarchical-resume.lock"
    descriptor = os.open(busy_lock, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(guard.QuarantineBusyError):
            guard.acquire(manifest, digest, entries[0]["id"])
        other = guard.acquire(manifest, digest, entries[1]["id"])
        guard.close(other)
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def test_renderer_emits_one_notify_restart_unit_per_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    manifest, _digest, entries = _fixture(tmp_path, entries=2)
    # Renderer only needs the manifest source binding; runtime checker binding
    # remains enforced by the guard.
    payloads = renderer.candidates(manifest)
    names = [renderer.unit_name(entry["id"]) for entry in entries]
    anchors = [renderer.anchor_name(entry["id"]) for entry in entries]
    assert set(payloads) == {*names, *anchors, renderer.TARGET_NAME}
    for name in names:
        payload = payloads[name].decode("utf-8")
        assert "Type=notify\n" in payload
        assert "Restart=always\n" in payload
        assert "RestartSec=5s\n" in payload
        assert "RefuseManualStart=yes\n" in payload
        assert "RefuseManualStop=yes\n" in payload
        assert payload.count("--entry-id") == 1
    target = payloads[renderer.TARGET_NAME].decode("utf-8")
    assert all(name in target for name in anchors)
    assert "WantedBy=default.target\n" in target
    assert "RefuseManualStop=yes\n" in target
    for entry, name in zip(entries, anchors, strict=True):
        payload = payloads[name].decode("utf-8")
        assert f"Upholds={renderer.unit_name(entry['id'])}\n" in payload
        assert "RefuseManualStop=yes\n" in payload


def test_renderer_rejects_entry_with_recursive_alternative(
    tmp_path: Path,
) -> None:
    manifest, _digest, _entries = _fixture(tmp_path)
    import json

    value = json.loads(manifest.read_bytes())
    value.pop("record_sha256")
    value["entries"][0]["alternative_certification"] = "recursive-active"
    manifest.write_bytes(guard.manifest_payload(guard.seal_manifest(value)))
    with pytest.raises(renderer.QuarantineRenderError, match="alternate certification"):
        renderer.candidates(manifest)
