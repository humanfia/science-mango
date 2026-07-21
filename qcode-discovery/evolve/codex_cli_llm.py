"""OpenEvolve LLM adapter backed by an authenticated Codex CLI.

This is intentionally a text-generation boundary. Every invocation is a fresh,
ephemeral, read-only Codex session; OpenEvolve owns all evolutionary memory.
"""

from __future__ import annotations

import asyncio
import os
import tempfile
from pathlib import Path
from typing import Any


PROJECT_ROOT = Path(__file__).resolve().parent.parent


def render_prompt(system_message: str, messages: list[dict[str, str]]) -> str:
    chunks = [
        "You are the text-generation backend for OpenEvolve. Do not edit files. "
        "Return only the response requested by the evolutionary prompt.",
        "",
        "## System message",
        system_message,
    ]
    for message in messages:
        role = str(message.get("role", "user")).upper()
        chunks.extend(["", f"## {role}", str(message.get("content", ""))])
    return "\n".join(chunks).strip() + "\n"


class CodexCliLLM:
    """Duck-typed OpenEvolve LLMInterface implemented with ``codex exec``."""

    def __init__(self, model_cfg: Any):
        self.model = model_cfg.name
        self.system_message = model_cfg.system_message or ""
        self.reasoning_effort = getattr(model_cfg, "reasoning_effort", None) or "xhigh"
        self.timeout = int(getattr(model_cfg, "timeout", None) or 900)
        self.retries = int(getattr(model_cfg, "retries", None) or 0)
        self.retry_delay = int(getattr(model_cfg, "retry_delay", None) or 5)
        self.codex_bin = os.environ.get("QCODE_CODEX_BIN", "codex")
        self.cwd = Path(os.environ.get("QCODE_CODEX_CWD", PROJECT_ROOT)).resolve()

    async def generate(self, prompt: str, **kwargs: Any) -> str:
        return await self.generate_with_context(
            self.system_message,
            [{"role": "user", "content": prompt}],
            **kwargs,
        )

    async def generate_with_context(
        self,
        system_message: str,
        messages: list[dict[str, str]],
        **kwargs: Any,
    ) -> str:
        prompt = render_prompt(system_message, messages)
        timeout = int(kwargs.get("timeout", self.timeout) or self.timeout)
        retries = int(kwargs.get("retries", self.retries) or 0)
        last_error = "unknown Codex CLI failure"
        for attempt in range(retries + 1):
            try:
                return await self._invoke(prompt, timeout)
            except (RuntimeError, asyncio.TimeoutError) as exc:
                last_error = str(exc)
                if attempt < retries:
                    await asyncio.sleep(self.retry_delay)
        raise RuntimeError(last_error)

    async def _invoke(self, prompt: str, timeout: int) -> str:
        output_dir = Path(tempfile.mkdtemp(prefix="qcode-codex-"))
        output_path = output_dir / "response.txt"
        command = [
            self.codex_bin,
            "exec",
            "--model", self.model,
            "--config", f'model_reasoning_effort="{self.reasoning_effort}"',
            "--sandbox", "read-only",
            "--ephemeral",
            "--ignore-user-config",
            "--ignore-rules",
            "--skip-git-repo-check",
            "--color", "never",
            "--cd", str(self.cwd),
            "--output-last-message", str(output_path),
            "-",
        ]
        process = await asyncio.create_subprocess_exec(
            *command,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.PIPE,
        )
        try:
            _, stderr = await asyncio.wait_for(
                process.communicate(prompt.encode()), timeout=timeout
            )
        except asyncio.TimeoutError:
            process.kill()
            await process.wait()
            raise asyncio.TimeoutError(
                f"Codex CLI timed out after {timeout}s for model {self.model}"
            )
        try:
            if process.returncode != 0:
                detail = stderr.decode(errors="replace")[-4000:]
                raise RuntimeError(
                    f"Codex CLI exited {process.returncode} for {self.model}: {detail}"
                )
            if not output_path.is_file():
                raise RuntimeError("Codex CLI produced no output-last-message file")
            response = output_path.read_text().strip()
            if not response:
                raise RuntimeError("Codex CLI produced an empty response")
            return response
        finally:
            try:
                output_path.unlink(missing_ok=True)
                output_dir.rmdir()
            except OSError:
                pass


def make_codex_cli_client(model_cfg: Any) -> CodexCliLLM:
    """Factory matching OpenEvolve's ``LLMModelConfig.init_client`` contract."""
    return CodexCliLLM(model_cfg)
