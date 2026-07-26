import asyncio
from types import SimpleNamespace

from evolve.codex_cli_llm import CodexCliLLM, render_prompt


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
