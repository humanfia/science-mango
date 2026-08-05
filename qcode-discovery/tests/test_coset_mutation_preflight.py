from __future__ import annotations

import hashlib
import os
import sys
import time
from pathlib import Path

import pytest

from evolve import coset_mutation_preflight as preflight
from evolve.coset_policy_dsl import (
    canonical_policy_json,
    default_policy,
    normalize_policy,
    policy_digest,
    policy_document,
    render_candidates,
)
from evolve.coset_search_contract import MAX_GENERATED_CANDIDATES


def _write_default_policy(path: Path):
    policy = default_policy()
    payload = canonical_policy_json(policy).encode("utf-8")
    path.write_bytes(payload)
    return policy, payload


def _process_state(pid: int) -> str | None:
    try:
        raw = Path(f"/proc/{pid}/stat").read_text()
    except (FileNotFoundError, ProcessLookupError):
        return None
    closing = raw.rfind(")")
    return None if closing < 1 else raw[closing + 2 :].split()[0]


def test_default_policy_preflight_returns_revalidated_candidates(tmp_path):
    path = tmp_path / "mutation.py"
    policy, payload = _write_default_policy(path)

    result = preflight.preflight_coset_policy(path)

    assert result.program_sha256 == hashlib.sha256(payload).hexdigest()
    assert result.program_bytes == len(payload)
    assert result.policy_sha256 == policy_digest(policy)
    assert len(result.candidates) == MAX_GENERATED_CANDIDATES
    assert len({row["action_id"] for row in result.candidates}) == 2
    assert result.elapsed_s > 0


@pytest.mark.parametrize(
    "payload",
    [
        b"def generate_candidates():\n    return missing_name\n",
        b'{"schema_version":1,"kind":"wrong"}',
        b"{not-json}",
        b"\xff\xfe",
    ],
)
def test_python_and_malformed_text_are_invalid_mutations(tmp_path, payload):
    path = tmp_path / "mutation.py"
    path.write_bytes(payload)

    with pytest.raises(preflight.InvalidCosetMutation) as raised:
        preflight.preflight_coset_policy(path)

    assert raised.value.reason_code == "dsl_invalid"
    assert raised.value.error_type == "CosetPolicyError"
    assert raised.value.program_sha256 == hashlib.sha256(payload).hexdigest()
    assert raised.value.program_bytes == len(payload)


def test_python_side_effect_text_is_inert(tmp_path):
    marker = tmp_path / "must-not-exist"
    source = (
        "__import__('pathlib').Path("
        + repr(str(marker))
        + ").write_text('executed')"
    ).encode("utf-8")
    path = tmp_path / "mutation.py"
    path.write_bytes(source)

    with pytest.raises(preflight.InvalidCosetMutation):
        preflight.preflight_coset_policy(path)

    assert not marker.exists()


def test_oversize_policy_is_rejected_before_launch(tmp_path, monkeypatch):
    path = tmp_path / "mutation.py"
    path.write_bytes(b" " * (preflight.MAX_POLICY_SOURCE_BYTES + 1))
    launched = False

    def forbidden_command(*_args, **_kwargs):
        nonlocal launched
        launched = True
        raise AssertionError("oversize mutation must not launch a child")

    monkeypatch.setattr(preflight, "_child_command", forbidden_command)
    with pytest.raises(preflight.InvalidCosetMutation) as raised:
        preflight.preflight_coset_policy(path)

    assert raised.value.reason_code == "source_too_large"
    assert raised.value.program_bytes == preflight.MAX_POLICY_SOURCE_BYTES + 1
    assert raised.value.program_sha256 is None
    assert launched is False


def test_noncanonical_child_protocol_fails_closed(tmp_path, monkeypatch):
    path = tmp_path / "mutation.py"
    _write_default_policy(path)
    command = [
        sys.executable,
        "-I",
        "-c",
        "import sys; sys.stdin.buffer.read(); sys.stdout.buffer.write(b'{ }\\n')",
    ]
    monkeypatch.setattr(
        preflight,
        "_child_command",
        lambda *_args, **_kwargs: command,
    )

    with pytest.raises(
        preflight.CosetMutationRuntimeError,
        match="protocol_not_canonical",
    ):
        preflight.preflight_coset_policy(path)


def _valid_child_response(payload: bytes):
    response = preflight._child_response(payload)
    assert response["status"] == "valid"
    snapshot = preflight._SourceSnapshot(
        payload=payload,
        sha256=hashlib.sha256(payload).hexdigest(),
        size=len(payload),
    )
    return response, snapshot


def test_parent_rejects_nonproduction_candidate_count():
    payload = canonical_policy_json(default_policy()).encode("utf-8")
    response, snapshot = _valid_child_response(payload)
    response["candidates"].pop()
    response["candidate_count"] -= 1

    with pytest.raises(
        preflight.CosetMutationRuntimeError,
        match="candidate_count_invalid",
    ):
        preflight._validated_response(response, snapshot)


def test_parent_rejects_wrong_per_action_quota():
    source_policy = default_policy()
    payload = canonical_policy_json(source_policy).encode("utf-8")
    response, snapshot = _valid_child_response(payload)

    document = policy_document(source_policy)
    assert [action["quota"] for action in document["actions"]] == [288, 96]
    document["actions"][0]["quota"] -= 1
    document["actions"][1]["quota"] += 1
    wrong_policy = normalize_policy(document)
    wrong_candidates = render_candidates(wrong_policy)
    response["policy"] = policy_document(wrong_policy)
    response["policy_sha256"] = policy_digest(wrong_policy)
    response["candidate_count"] = len(wrong_candidates)
    response["candidates"] = wrong_candidates

    with pytest.raises(
        preflight.CosetMutationRuntimeError,
        match="candidate_quota_invalid",
    ):
        preflight._validated_response(response, snapshot)


def test_oversize_child_stdout_is_killed_and_fails_closed(tmp_path, monkeypatch):
    path = tmp_path / "mutation.py"
    _write_default_policy(path)
    command = [
        sys.executable,
        "-I",
        "-c",
        (
            "import sys; sys.stdin.buffer.read(); "
            f"sys.stdout.buffer.write(b'x'*{preflight.MAX_PROTOCOL_BYTES + 1}); "
            "sys.stdout.buffer.flush()"
        ),
    ]
    monkeypatch.setattr(
        preflight,
        "_child_command",
        lambda *_args, **_kwargs: command,
    )

    with pytest.raises(
        preflight.CosetMutationRuntimeError,
        match="stdout_limit_exceeded",
    ):
        preflight.preflight_coset_policy(path, hard_timeout_s=5.0)


def test_timeout_kills_and_reaps_private_process_group(tmp_path, monkeypatch):
    path = tmp_path / "mutation.py"
    _write_default_policy(path)
    pid_file = tmp_path / "pids"
    helper = (
        "import os,time; "
        "child=os.fork(); "
        f"open({str(pid_file)!r},'w').write(str(os.getpid())+' '+str(child)) "
        "if child else None; "
        "time.sleep(60)"
    )
    command = [sys.executable, "-I", "-c", helper]
    monkeypatch.setattr(
        preflight,
        "_child_command",
        lambda *_args, **_kwargs: command,
    )

    with pytest.raises(
        preflight.CosetMutationRuntimeError,
        match="hard_timeout",
    ):
        preflight.preflight_coset_policy(path, hard_timeout_s=0.5)

    assert pid_file.is_file()
    pids = [int(value) for value in pid_file.read_text().split()]
    deadline = time.monotonic() + 3.0
    while time.monotonic() < deadline and any(
        _process_state(pid) not in (None, "Z") for pid in pids
    ):
        time.sleep(0.02)
    assert all(_process_state(pid) in (None, "Z") for pid in pids)


def test_atomic_path_rotation_uses_the_opened_inode_snapshot(tmp_path, monkeypatch):
    path = tmp_path / "mutation.py"
    policy, original = _write_default_policy(path)
    replacement = tmp_path / "replacement"
    replacement.write_bytes(b"this is not JSON")
    real_open = os.open
    rotated = False

    def rotating_open(raw_path, flags, *args, **kwargs):
        nonlocal rotated
        descriptor = real_open(raw_path, flags, *args, **kwargs)
        if not rotated and os.path.abspath(os.fspath(raw_path)) == str(path):
            os.replace(replacement, path)
            rotated = True
        return descriptor

    monkeypatch.setattr(preflight.os, "open", rotating_open)
    result = preflight.preflight_coset_policy(path)

    assert rotated is True
    assert path.read_bytes() == b"this is not JSON"
    assert result.program_sha256 == hashlib.sha256(original).hexdigest()
    assert result.policy_sha256 == policy_digest(policy)


def test_symlink_source_fails_closed(tmp_path):
    target = tmp_path / "target"
    _write_default_policy(target)
    link = tmp_path / "mutation.py"
    link.symlink_to(target)

    with pytest.raises(
        preflight.CosetMutationRuntimeError,
        match="source_open_failed",
    ):
        preflight.preflight_coset_policy(link)
