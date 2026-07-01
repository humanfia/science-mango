#!/usr/bin/env python3
"""Archon -> Rethlas blueprint wrapper.

Reads the JSON payload emitted by `archon physics-formalize --rethlas-command`
from stdin, writes a Rethlas problem markdown file, runs Rethlas' generation
runner, and prints the verified or draft proof blueprint to stdout.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Rethlas for an Archon physics problem.")
    parser.add_argument(
        "--rethlas-root",
        default=os.environ.get("RETHLAS_ROOT", "/Users/hq/Python_project/Rethlas"),
        help="Path to the Rethlas repository root. Defaults to $RETHLAS_ROOT.",
    )
    parser.add_argument(
        "--model",
        default=os.environ.get("RETHLAS_MODEL", "gpt-5.5"),
        help="Codex model passed to Rethlas' generation runner.",
    )
    parser.add_argument(
        "--reasoning-effort",
        default=os.environ.get("RETHLAS_REASONING_EFFORT", "xhigh"),
        help="Codex reasoning effort passed to Rethlas' generation runner.",
    )
    parser.add_argument(
        "--max-iterations",
        type=int,
        default=int(os.environ.get("RETHLAS_MAX_ITERATIONS", "3")),
        help="Maximum Rethlas generation iterations.",
    )
    parser.add_argument(
        "--problem-prefix",
        default=os.environ.get("RETHLAS_PROBLEM_PREFIX", "archon_physics"),
        help="Subdirectory under agents/generation/data for Archon-written problems.",
    )
    parser.add_argument(
        "--strict-verified",
        action="store_true",
        help="Exit non-zero unless Rethlas produces blueprint_verified.md.",
    )
    parser.add_argument(
        "--direct-chat",
        action="store_true",
        default=os.environ.get("RETHLAS_DIRECT_CHAT", "").lower() in {"1", "true", "yes"},
        help=(
            "Bypass Codex CLI and call an OpenAI-compatible chat/completions "
            "gateway directly. Useful when the gateway does not support the "
            "Responses API required by newer Codex CLI versions."
        ),
    )
    parser.add_argument(
        "--base-url",
        default=(
            os.environ.get("RETHLAS_BASE_URL")
            or os.environ.get("ANTHROPIC_BASE_URL")
            or os.environ.get("OPENAI_BASE_URL")
            or "http://115.120.87.159:8082/v1"
        ),
        help="OpenAI-compatible base URL used by --direct-chat.",
    )
    parser.add_argument(
        "--api-key-env",
        default=os.environ.get("RETHLAS_API_KEY_ENV", "ANTHROPIC_AUTH_TOKEN"),
        help="Environment variable containing the API key for --direct-chat.",
    )
    parser.add_argument(
        "--chat-timeout",
        type=int,
        default=int(os.environ.get("RETHLAS_CHAT_TIMEOUT", "120")),
        help="HTTP timeout in seconds for --direct-chat.",
    )
    return parser.parse_args()


def safe_slug(value: str) -> str:
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("._-")
    return value or "problem"


def load_payload() -> dict[str, Any]:
    try:
        payload = json.load(sys.stdin)
    except json.JSONDecodeError as exc:
        raise SystemExit(f"stdin must be Archon JSON payload: {exc}") from exc
    if not isinstance(payload, dict):
        raise SystemExit("stdin JSON payload must be an object")
    return payload


def problem_markdown(payload: dict[str, Any]) -> str:
    question = str(payload.get("question") or "").strip()
    answer = str(payload.get("answer") or "").strip()
    declarations = payload.get("declarations") or []
    decl_lines = []
    if isinstance(declarations, list):
        for decl in declarations:
            if isinstance(decl, dict):
                kind = decl.get("kind", "declaration")
                name = decl.get("full_name") or decl.get("name") or "unknown"
                decl_lines.append(f"- `{kind} {name}`")

    sections = [
        "# Archon physics proof-blueprint task",
        "",
        "## statement",
        question or "No problem statement was provided.",
    ]
    if answer:
        sections.extend(["", "## recorded answer", answer])
    if decl_lines:
        sections.extend([
            "",
            "## Lean declarations to support",
            *decl_lines,
        ])
    sections.extend([
        "",
        "## requested proof blueprint",
        "Write a natural-language physics solution route suitable for conversion "
        "into an Archon leanblueprint chapter. Prefer explicit intermediate "
        "claims: physical-law hypotheses, geometry/orientation claims, local "
        "algebra or vector reductions, cancellation claims, and the final result. "
        "Do not write Lean code. If the problem relies on a physical law not "
        "stated in the Lean declarations, state that law as a proof assumption "
        "or redraft requirement rather than pretending it has been proved.",
    ])
    return "\n".join(sections).rstrip() + "\n"


def run_rethlas(
    *,
    generation_root: Path,
    problem_file: str,
    model: str,
    reasoning_effort: str,
    max_iterations: int,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    extra_path = []
    node_home = env.get("NODE_HOME")
    if node_home:
        extra_path.append(str(Path(node_home).expanduser() / "bin"))
    extra_path.extend([
        "/home/ma-user/.local/node-v22.15.1/bin",
        str(Path.home() / ".local" / "node-v22.15.1" / "bin"),
    ])
    env["PATH"] = os.pathsep.join([p for p in extra_path if p]) + os.pathsep + env.get("PATH", "")
    env.update(
        {
            "PROBLEM_FILE": problem_file,
            "MODEL": model,
            "REASONING_EFFORT": reasoning_effort,
            "MAX_ITERATIONS": str(max_iterations),
        }
    )
    return subprocess.run(
        ["./tests/run_example.sh"],
        cwd=generation_root,
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )


def chat_completions_url(base_url: str) -> str:
    base_url = base_url.rstrip("/")
    if base_url.endswith("/chat/completions"):
        return base_url
    return f"{base_url}/chat/completions"


def extract_chat_content(response: dict[str, Any]) -> str:
    choices = response.get("choices")
    if not isinstance(choices, list) or not choices:
        raise ValueError("chat response did not contain choices")
    first = choices[0]
    if not isinstance(first, dict):
        raise ValueError("chat response choice was not an object")
    message = first.get("message")
    if isinstance(message, dict):
        content = message.get("content")
        if isinstance(content, str) and content.strip():
            return content.strip()
        if isinstance(content, list):
            parts = [
                part.get("text", "")
                for part in content
                if isinstance(part, dict) and isinstance(part.get("text"), str)
            ]
            text = "\n".join(part for part in parts if part).strip()
            if text:
                return text
    text = first.get("text")
    if isinstance(text, str) and text.strip():
        return text.strip()
    raise ValueError("chat response did not contain message content")


def run_direct_chat(
    *,
    payload: dict[str, Any],
    problem_text: str,
    model: str,
    base_url: str,
    api_key_env: str,
    timeout: int,
) -> str:
    api_key = os.environ.get(api_key_env)
    if not api_key:
        raise RuntimeError(f"{api_key_env} is not set")

    request_payload = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You are a mathematical physics proof-planning assistant. "
                    "Produce a natural-language proof blueprint for the given "
                    "problem. Do not write Lean code."
                ),
            },
            {
                "role": "user",
                "content": problem_text,
            },
        ],
        "temperature": 0,
        "max_tokens": int(os.environ.get("RETHLAS_CHAT_MAX_TOKENS", "2000")),
    }
    request = urllib.request.Request(
        chat_completions_url(base_url),
        data=json.dumps(request_payload).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    del payload
    with urllib.request.urlopen(request, timeout=timeout) as response:
        response_payload = json.loads(response.read().decode("utf-8"))
    return extract_chat_content(response_payload)


def print_http_error(exc: urllib.error.HTTPError) -> None:
    body = exc.read().decode("utf-8", errors="replace")
    if body:
        print(body, file=sys.stderr)
    else:
        print(f"HTTP {exc.code}: {exc.reason}", file=sys.stderr)


def main() -> int:
    args = parse_args()
    payload = load_payload()

    rethlas_root = Path(args.rethlas_root).expanduser().resolve()
    generation_root = rethlas_root / "agents" / "generation"
    runner = generation_root / "tests" / "run_example.sh"
    if not args.direct_chat and not runner.is_file():
        print(f"Rethlas runner not found: {runner}", file=sys.stderr)
        return 2

    problem_id = safe_slug(str(payload.get("index") or "problem"))
    problem_rel = f"{safe_slug(args.problem_prefix)}/{problem_id}"
    problem_file = f"data/{problem_rel}.md"
    problem_path = generation_root / problem_file
    problem_path.parent.mkdir(parents=True, exist_ok=True)
    markdown = problem_markdown(payload)
    problem_path.write_text(markdown, encoding="utf-8")

    result_dir = generation_root / "results" / problem_rel
    if args.direct_chat:
        try:
            blueprint = run_direct_chat(
                payload=payload,
                problem_text=markdown,
                model=args.model,
                base_url=args.base_url,
                api_key_env=args.api_key_env,
                timeout=args.chat_timeout,
            )
        except urllib.error.HTTPError as exc:
            print_http_error(exc)
            return 1
        except Exception as exc:
            print(f"Direct chat Rethlas blueprint failed: {exc}", file=sys.stderr)
            return 1
        result_dir.mkdir(parents=True, exist_ok=True)
        (result_dir / "blueprint.md").write_text(blueprint.rstrip() + "\n", encoding="utf-8")
        print(blueprint)
        return 0

    completed = run_rethlas(
        generation_root=generation_root,
        problem_file=problem_file,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        max_iterations=args.max_iterations,
    )
    if completed.stdout:
        print(completed.stdout, file=sys.stderr, end="" if completed.stdout.endswith("\n") else "\n")
    if completed.stderr:
        print(completed.stderr, file=sys.stderr, end="" if completed.stderr.endswith("\n") else "\n")

    verified = result_dir / "blueprint_verified.md"
    draft = result_dir / "blueprint.md"
    if verified.is_file():
        print(verified.read_text(encoding="utf-8").strip())
        return 0
    if draft.is_file() and not args.strict_verified:
        print(
            "Rethlas did not produce blueprint_verified.md; using draft blueprint.md.",
            file=sys.stderr,
        )
        print(draft.read_text(encoding="utf-8").strip())
        return 0

    if completed.returncode != 0:
        print(f"Rethlas exited with code {completed.returncode}.", file=sys.stderr)
    print(f"No usable Rethlas blueprint found under {result_dir}.", file=sys.stderr)
    return completed.returncode or 1


if __name__ == "__main__":
    raise SystemExit(main())
