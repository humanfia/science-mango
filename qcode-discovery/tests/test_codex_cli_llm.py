import asyncio
from types import SimpleNamespace

import pytest

from evolve.ansatz_v3_codex_view import materialize_sanitized_codex_view
from evolve.codex_cli_llm import CodexCliLLM, render_prompt
from evolve.codex_cli_llm import PROJECT_ROOT


def test_render_prompt_preserves_roles_and_sets_no_edit_boundary():
    prompt = render_prompt("system", [
        {"role": "user", "content": "first"},
        {"role": "assistant", "content": "second"},
    ])
    assert "Do not edit files" in prompt
    assert "## System message\nsystem" in prompt
    assert "## USER\nfirst" in prompt
    assert "## ASSISTANT\nsecond" in prompt


def test_codex_cli_adapter_reads_output_last_message(tmp_path, monkeypatch):
    fake = tmp_path / "codex"
    fake.write_text("""#!/bin/sh
out=''
while [ "$#" -gt 0 ]; do
  if [ "$1" = '--output-last-message' ]; then
    shift
    out="$1"
  fi
  shift
done
cat >/dev/null
printf 'FAKE_CODEX_OK\\n' > "$out"
""")
    fake.chmod(0o755)
    monkeypatch.setenv("QCODE_CODEX_BIN", str(fake))
    monkeypatch.setenv("QCODE_CODEX_CWD", str(tmp_path))
    config = SimpleNamespace(
        name="gpt-5.5",
        system_message="system",
        reasoning_effort="xhigh",
        timeout=30,
        retries=0,
        retry_delay=0,
    )
    result = asyncio.run(CodexCliLLM(config).generate("hello"))
    assert result == "FAKE_CODEX_OK"


def test_ansatz_v3_codex_cli_runs_inside_physical_chroot(tmp_path, monkeypatch):
    fake = tmp_path / "codex"
    fake.write_text("""#!/bin/sh
out=''
cwd=''
while [ "$#" -gt 0 ]; do
  if [ "$1" = '--output-last-message' ]; then
    shift
    out="$1"
  elif [ "$1" = '--cd' ]; then
    shift
    cwd="$1"
  fi
  shift
done
[ "$cwd" = '/workspace' ] || exit 31
[ -f /workspace/evolve/seed_solution_twisted_torus_ansatz_v3.py ] || exit 32
[ ! -e /workspace/evaluation/twisted_torus_published_anchors.v1.json ] || exit 33
[ ! -e /workspace/scripts/verify_blind_ansatz_v3_calibration.py ] || exit 34
[ ! -e /root/qcode-ansatz-v3-preregister ] || exit 35
cat >/dev/null
printf 'ISOLATED_CODEX_OK\n' > "$out"
""", encoding="utf-8")
    fake.chmod(0o755)
    auth_home = tmp_path / "codex-home"
    auth_home.mkdir()
    (auth_home / "auth.json").write_text("{}\n", encoding="utf-8")
    view_path = tmp_path / "view"
    view = materialize_sanitized_codex_view(PROJECT_ROOT, view_path)
    monkeypatch.setenv("QCODE_CODEX_BIN", str(fake))
    monkeypatch.setenv("QCODE_CODEX_CWD", str(view_path))
    monkeypatch.setenv("CODEX_HOME", str(auth_home))
    monkeypatch.setenv(
        "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST", view["manifest_path"]
    )
    monkeypatch.setenv(
        "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST_SHA256",
        view["manifest_file_sha256"],
    )
    monkeypatch.setenv(
        "QCODE_ANSATZ_V3_CODEX_VIEW_SOURCE_FINGERPRINT_SHA256",
        view["source_fingerprint_sha256"],
    )
    monkeypatch.setenv(
        "QCODE_ANSATZ_V3_CODEX_FILESYSTEM_BOUNDARY",
        view["filesystem_boundary"],
    )
    config = SimpleNamespace(
        name="gpt-5.5",
        system_message="system",
        reasoning_effort="xhigh",
        timeout=30,
        retries=0,
        retry_delay=0,
    )
    assert asyncio.run(CodexCliLLM(config).generate("hello")) == (
        "ISOLATED_CODEX_OK"
    )

    monkeypatch.setenv(
        "QCODE_ANSATZ_V3_CODEX_VIEW_MANIFEST_SHA256", "0" * 64
    )
    with pytest.raises(RuntimeError, match="binding changed"):
        CodexCliLLM(config)
