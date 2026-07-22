"""`archon physics-formalize` — physics multimodal Lean stub generation.

This command hosts Archon's bundled physics Formalizer pipeline, including
concept decomposition, multimodal grounding, Lean/PhysLean stub generation, and
semantic alignment.
"""

from __future__ import annotations

import importlib.util
import importlib
import json
import os
import queue
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import urllib.error
import urllib.request
from datetime import datetime
from pathlib import Path
from types import SimpleNamespace
from typing import Optional

import typer
import yaml

from archon import log
from archon.commands.init.utils import data_path
from archon.commands.tooling.blueprint import BlueprintChapter, BlueprintStructure


FORMALIZER_ROOT_ENV = "ARCHON_PHYSICS_FORMALIZER_ROOT"
BUILTIN_FORMALIZER_ROOT = Path(__file__).resolve().parents[1] / "formalizer"
DEFAULT_ANTHROPIC_BASE_URL = "https://api.anthropic.com/v1"
DEFAULT_ANTHROPIC_VERSION = "2023-06-01"
DEFAULT_ANTHROPIC_MAX_TOKENS = 8192
DEFAULT_LLM_TIMEOUT = 120
SUPPORTED_LLM_PROVIDERS = {"openai-compatible", "anthropic"}
PHYSICS_PROVER_MODE = "physics"
PHYSLEAN_GIT_URL = "https://github.com/HEPLean/PhysLean"
PHYSLEAN_REQUIRE_LEAN = f'\nrequire PhysLean from git "{PHYSLEAN_GIT_URL}" @ "master"\n'
PHYSLEAN_REQUIRE_TOML = (
    "\n[[require]]\n"
    'name = "PhysLean"\n'
    f'git = "{PHYSLEAN_GIT_URL}"\n'
    'rev = "master"\n'
)
PHYSICS_PREFLIGHT_IMPORTS = [
    "import Mathlib",
    "import Physlib.Units.Basic",
    "import Physlib.Units.Dimension",
    "import Physlib.Units.WithDim.Basic",
    "import Physlib.Units.WithDim.Mass",
    "import Physlib.Units.WithDim.Velocity",
    "import Physlib.Units.WithDim.Energy",
    "import Physlib.SpaceAndTime.Space.Basic",
    "import Physlib.SpaceAndTime.Time.Basic",
    "import Physlib.SpaceAndTime.Space.Derivatives.Basic",
    "import Physlib.Mathematics.InnerProductSpace.Basic",
    "import Physlib.ClassicalMechanics.Basic",
    "import Physlib.ClassicalMechanics.EulerLagrange",
    "import Physlib.ClassicalMechanics.HarmonicOscillator.Basic",
    "import Physlib.ClassicalMechanics.RigidBody.Basic",
    "import Physlib.Electromagnetism.Basic",
    "import Physlib.Electromagnetism.Dynamics.Basic",
    "import Physlib.Thermodynamics.Basic",
    "import Physlib.Thermodynamics.Temperature.Basic",
    "import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic",
    "import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic",
    "import Physlib.Relativity.LorentzGroup.Basic",
    "import Physlib.Relativity.Special.ProperTime",
]


class _AnthropicOpenAICompatClient:
    """Tiny adapter for Formalizer's OpenAI-style chat completion calls."""

    def __init__(
        self,
        *,
        api_key: str,
        base_url: str,
        max_tokens: int,
        anthropic_version: str = DEFAULT_ANTHROPIC_VERSION,
        timeout: int = 120,
    ) -> None:
        self.api_key = api_key
        self.base_url = base_url.rstrip("/")
        self.max_tokens = max_tokens
        self.anthropic_version = anthropic_version
        self.timeout = timeout
        self.chat = SimpleNamespace(
            completions=SimpleNamespace(create=self._create_completion)
        )

    def _messages_url(self) -> str:
        if self.base_url.endswith("/messages"):
            return self.base_url
        if self.base_url.endswith("/v1"):
            return f"{self.base_url}/messages"
        return f"{self.base_url}/v1/messages"

    def _create_completion(self, **kwargs):
        payload = self._to_anthropic_payload(kwargs)
        request = urllib.request.Request(
            self._messages_url(),
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "content-type": "application/json",
                "x-api-key": self.api_key,
                "authorization": f"Bearer {self.api_key}",
                "anthropic-version": self.anthropic_version,
            },
            method="POST",
        )
        try:
            raw = self._read_urlopen_response(request)
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            raise RuntimeError(
                f"Anthropic API error {exc.code}: {detail[:1000]}"
            ) from exc
        except TimeoutError as exc:
            raise RuntimeError(
                f"Anthropic API request timed out after {self.timeout} seconds."
            ) from exc
        except urllib.error.URLError as exc:
            raise RuntimeError(f"Anthropic API connection failed: {exc}") from exc

        data = json.loads(raw)
        text = self._extract_text(data)
        return SimpleNamespace(
            choices=[SimpleNamespace(message=SimpleNamespace(content=text))]
        )

    def _read_urlopen_response(self, request: urllib.request.Request) -> str:
        if (
            threading.current_thread() is not threading.main_thread()
            or not hasattr(signal, "setitimer")
        ):
            return self._read_urlopen_response_in_worker_thread(request)

        previous_handler = signal.getsignal(signal.SIGALRM)

        def _timeout_handler(_signum, _frame):
            raise TimeoutError()

        signal.signal(signal.SIGALRM, _timeout_handler)
        signal.setitimer(signal.ITIMER_REAL, float(self.timeout))
        try:
            with urllib.request.urlopen(request, timeout=self.timeout) as response:
                return response.read().decode("utf-8")
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0.0)
            signal.signal(signal.SIGALRM, previous_handler)

    def _read_urlopen_response_in_worker_thread(
        self, request: urllib.request.Request
    ) -> str:
        results: queue.Queue[tuple[str, str | BaseException]] = queue.Queue(maxsize=1)

        def _request_worker() -> None:
            try:
                with urllib.request.urlopen(request, timeout=self.timeout) as response:
                    results.put(("ok", response.read().decode("utf-8")))
            except BaseException as exc:
                results.put(("error", exc))

        worker = threading.Thread(target=_request_worker, daemon=True)
        worker.start()
        worker.join(float(self.timeout))
        if worker.is_alive():
            raise TimeoutError()

        status, value = results.get_nowait()
        if status == "error":
            raise value
        return str(value)

    def _to_anthropic_payload(self, kwargs: dict) -> dict:
        system_parts: list[str] = []
        anthropic_messages: list[dict] = []
        for message in kwargs.get("messages", []):
            role = message.get("role", "user")
            content = message.get("content", "")
            if role == "system":
                system_parts.append(self._content_to_text(content))
                continue
            anthropic_role = "assistant" if role == "assistant" else "user"
            anthropic_messages.append(
                {
                    "role": anthropic_role,
                    "content": self._convert_content_blocks(content),
                }
            )

        payload = {
            "model": kwargs["model"],
            "max_tokens": self.max_tokens,
            "messages": anthropic_messages,
        }
        if system_parts:
            payload["system"] = "\n\n".join(part for part in system_parts if part)
        if "temperature" in kwargs:
            payload["temperature"] = kwargs["temperature"]
        return payload

    def _convert_content_blocks(self, content) -> list[dict]:
        if isinstance(content, str):
            return [{"type": "text", "text": content}]
        if not isinstance(content, list):
            return [{"type": "text", "text": str(content)}]

        blocks: list[dict] = []
        for item in content:
            if not isinstance(item, dict):
                blocks.append({"type": "text", "text": str(item)})
                continue
            item_type = item.get("type")
            if item_type == "text":
                blocks.append({"type": "text", "text": str(item.get("text", ""))})
            elif item_type == "image_url":
                blocks.append(self._image_url_to_anthropic_block(item))
            else:
                blocks.append({"type": "text", "text": json.dumps(item)})
        return blocks

    @staticmethod
    def _image_url_to_anthropic_block(item: dict) -> dict:
        url = item.get("image_url", {}).get("url", "")
        match = re.match(r"data:([^;]+);base64,(.*)", url, flags=re.DOTALL)
        if not match:
            raise RuntimeError("Anthropic adapter only supports base64 data image URLs.")
        media_type, data = match.groups()
        return {
            "type": "image",
            "source": {
                "type": "base64",
                "media_type": media_type,
                "data": data,
            },
        }

    def _content_to_text(self, content) -> str:
        if isinstance(content, str):
            return content
        blocks = self._convert_content_blocks(content)
        return "\n".join(
            block.get("text", "") for block in blocks if block["type"] == "text"
        )

    @staticmethod
    def _extract_text(data: dict) -> str:
        chunks = []
        for block in data.get("content", []):
            if isinstance(block, dict) and block.get("type") == "text":
                chunks.append(block.get("text", ""))
        return "\n".join(chunk for chunk in chunks if chunk).strip()


class PhysicsFormalizeCommand:
    """Run the local physics auto-formalizer and write a Lean `sorry` stub."""

    def __init__(
        self,
        project_path: str,
        *,
        question: str | None = None,
        question_file: Path | None = None,
        input_jsonl: Path | None = None,
        image_root: Path | None = None,
        image: Path | None = None,
        answer: str = "",
        out: Path | None = None,
        report_out: Path | None = None,
        out_dir: Path | None = None,
        report_dir: Path | None = None,
        work_dir: Path | None = None,
        index: str = "001",
        category: str = "physics",
        limit: int = -1,
        formalizer_root: Path | None = None,
        workers: int = 1,
        decompose: bool = True,
        ensure_physlean: bool = False,
        build_physlean: bool = False,
        preflight: bool = False,
        fail_on_semantic: bool = False,
        dry_run: bool = False,
        update_progress: bool = False,
        with_rethlas_blueprint: bool = False,
        rethlas_command: str | None = None,
        rethlas_timeout: int = 180,
        llm_api_key: str | None = None,
        llm_api_key_env: str | None = None,
        llm_provider: str = "openai-compatible",
        llm_base_url: str | None = None,
        llm_model: str | None = None,
        llm_max_tokens: int | None = None,
        llm_timeout: int = DEFAULT_LLM_TIMEOUT,
        llm_no_temperature: bool = False,
        leanexplore_api_key: str | None = None,
        leanexplore_api_key_env: str | None = None,
    ) -> None:
        self.project_path = Path(project_path).resolve()
        self.question = question
        self.question_file = question_file
        self.input_jsonl = input_jsonl
        self.image_root = image_root
        self.image = image
        self.answer = answer
        self.out = out
        self.report_out = report_out
        self.out_dir = out_dir
        self.report_dir = report_dir
        self.work_dir = work_dir
        self.index = index
        self.category = category
        self.limit = limit
        self.formalizer_root = formalizer_root
        self.workers = workers
        self.decompose = decompose
        self.ensure_physlean = ensure_physlean
        self.build_physlean = build_physlean
        self.preflight = preflight
        self.fail_on_semantic = fail_on_semantic
        self.dry_run = dry_run
        self.update_progress = update_progress
        self.with_rethlas_blueprint = with_rethlas_blueprint
        self.rethlas_command = rethlas_command
        self.rethlas_timeout = rethlas_timeout
        self.llm_api_key = llm_api_key
        self.llm_api_key_env = llm_api_key_env
        self.llm_provider = llm_provider
        self.llm_base_url = llm_base_url
        self.llm_model = llm_model
        self.llm_max_tokens = llm_max_tokens
        self.llm_timeout = llm_timeout
        self.llm_no_temperature = llm_no_temperature
        self.leanexplore_api_key = leanexplore_api_key
        self.leanexplore_api_key_env = leanexplore_api_key_env

    def run(self) -> None:
        log.header("archon physics-formalize")
        self._validate_project()
        if self.input_jsonl:
            self._validate_batch_mode()
        else:
            self._validate_single_mode()

        formalizer_root = self._resolve_formalizer_root()
        work_dir = self._resolve_work_dir()
        runtime_config = self._resolve_runtime_config()

        if self.input_jsonl:
            self._run_batch(
                formalizer_root=formalizer_root,
                work_dir=work_dir,
                runtime_config=runtime_config,
            )
            return

        question = self._read_question()
        image_path = self._resolve_image()
        out_path = self._resolve_out_path()
        report_path = self._resolve_report_path(out_path)

        log.key_value({
            "Project": str(self.project_path),
            "Formalizer": str(formalizer_root),
            "Image": str(image_path) if image_path else "none",
            "Output": str(out_path),
            "Report": str(report_path),
            "Work dir": str(work_dir),
            "Concept decomposition": "enabled" if self.decompose else "disabled",
            "Ensure PhysLean": "enabled" if self.ensure_physlean else "disabled",
            "Build PhysLean": "enabled" if self.build_physlean else "disabled",
            "Lean preflight": "enabled" if self.preflight else "disabled",
            "Mode": "dry run" if self.dry_run else "run",
            "Update PROGRESS.md": "yes" if self.update_progress else "no",
            "Rethlas blueprint": "enabled" if self.with_rethlas_blueprint else "disabled",
            "LLM provider": runtime_config["llm_provider"],
            "LLM model": runtime_config["llm_model"] or "(Formalizer config)",
            "LLM base URL": runtime_config["llm_base_url"] or "(Formalizer config)",
            "LLM max tokens": (
                str(runtime_config["llm_max_tokens"])
                if runtime_config["llm_max_tokens"]
                else "(provider default)"
            ),
        })

        entry = self._build_entry(question, image_path)
        image_root = str(image_path.parent) if image_path else None
        ensure_result = (
            self._ensure_physlean_dependency() if self.ensure_physlean else None
        )
        build_result = (
            self._run_physlean_build() if self.build_physlean else None
        )
        preflight_result = (
            self._run_lean_preflight(work_dir) if self.preflight else None
        )

        if self.dry_run:
            manifest_path = self._write_manifest(
                work_dir=work_dir,
                formalizer_root=formalizer_root,
                out_path=out_path,
                report_path=report_path,
                entry=entry,
                image_root=image_root,
                runtime_config=runtime_config,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
            )
            self._write_archon_metadata(
                work_dir=work_dir,
                formalizer_root=formalizer_root,
                out_path=out_path,
                report_path=report_path,
                entry=entry,
                image_root=image_root,
                runtime_config=runtime_config,
                result=None,
                dry_run=True,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
            )
            if self.update_progress:
                log.warn("--update-progress is ignored during --dry-run.")
            log.success(f"Dry run complete. Manifest written to {manifest_path}")
            return

        process_single_problem, config = self._load_formalizer(formalizer_root)
        self._configure_formalizer(config, runtime_config)

        log.phase(1, "Physics multimodal formalization")
        result = process_single_problem(entry, str(work_dir), image_root_dir=image_root)

        try:
            self._copy_formalizer_outputs(
                index=self.index,
                result=result,
                work_dir=work_dir,
                out_path=out_path,
                report_path=report_path,
            )
        except RuntimeError as exc:
            log.error(str(exc))
            raise typer.Exit(1)

        self._write_archon_metadata(
            work_dir=work_dir,
            formalizer_root=formalizer_root,
            out_path=out_path,
            report_path=report_path,
            entry=entry,
            image_root=image_root,
            runtime_config=runtime_config,
            result=result,
            dry_run=False,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
        )

        self._summarize(result, out_path, report_path)
        if self.update_progress:
            self._update_progress(out_path, report_path)

    def _copy_formalizer_outputs(
        self,
        *,
        index: str,
        result: dict,
        work_dir: Path,
        out_path: Path,
        report_path: Path,
    ) -> None:
        generated = work_dir / f"problem_{index}.lean"
        generated_report = work_dir / f"problem_{index}_report.json"
        if generated.exists():
            code = self._stub_lean_proofs(generated.read_text(encoding="utf-8"))
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(code, encoding="utf-8")
            result["generated_code"] = code
        elif result.get("generated_code"):
            code = self._stub_lean_proofs(result["generated_code"])
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(code, encoding="utf-8")
            result["generated_code"] = code
        else:
            raise RuntimeError("Formalizer did not produce Lean code.")

        report_path.parent.mkdir(parents=True, exist_ok=True)
        if generated_report.exists():
            try:
                report_data = json.loads(generated_report.read_text(encoding="utf-8"))
                report_data["generated_code"] = result.get("generated_code", "")
                report_path.write_text(
                    json.dumps(report_data, indent=2, ensure_ascii=False),
                    encoding="utf-8",
                )
            except Exception:
                shutil.copy2(generated_report, report_path)
        else:
            report_path.write_text(
                json.dumps(result, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )

    @staticmethod
    def _stub_lean_proofs(code: str) -> str:
        """Turn generated theorem/lemma proofs into `by sorry` stubs."""

        def replace_by(match: re.Match) -> str:
            return f"{match.group('head')} sorry{match.group('tail')}"

        top_level_boundary = (
            r"(?=\n\s*(?:"
            r"--\s*-{5,}|"
            r"--\s*Node:|"
            r"/--|"
            r"\b(?:theorem|lemma|def|structure|class|inductive|instance|namespace|section|end)\b"
            r")|\Z)"
        )
        by_pattern = re.compile(
            r"(?P<head>\b(?:theorem|lemma)\b[\s\S]*?:=\s*by)"
            r"(?P<body>[\s\S]*?)"
            r"(?P<tail>" + top_level_boundary + r")",
            flags=re.MULTILINE,
        )
        code = by_pattern.sub(replace_by, code)

        sorry_pattern = re.compile(
            r"(?P<head>\b(?:theorem|lemma)\b[\s\S]*?:=\s*)sorry"
            r"(?P<body>[\s\S]*?)"
            r"(?P<tail>" + top_level_boundary + r")",
            flags=re.MULTILINE,
        )
        return sorry_pattern.sub(lambda m: f"{m.group('head')}by sorry{m.group('tail')}", code)

    def _run_batch(
        self,
        *,
        formalizer_root: Path,
        work_dir: Path,
        runtime_config: dict,
    ) -> None:
        self._validate_batch_mode()
        input_path, entries = self._read_input_jsonl()
        image_root = self._resolve_batch_image_root(input_path, entries)
        out_dir = self._resolve_out_dir()
        report_dir = self._resolve_report_dir(out_dir)
        has_images = any(entry.get("image") for entry in entries)

        log.key_value({
            "Project": str(self.project_path),
            "Formalizer": str(formalizer_root),
            "Input JSONL": str(input_path),
            "Problems": str(len(entries)),
            "Image root": str(image_root) if image_root else "none",
            "Output dir": str(out_dir),
            "Report dir": str(report_dir),
            "Work dir": str(work_dir),
            "Concept decomposition": "enabled" if self.decompose else "disabled",
            "Ensure PhysLean": "enabled" if self.ensure_physlean else "disabled",
            "Build PhysLean": "enabled" if self.build_physlean else "disabled",
            "Lean preflight": "enabled" if self.preflight else "disabled",
            "Mode": "dry run" if self.dry_run else "run",
            "Update PROGRESS.md": "yes" if self.update_progress else "no",
            "Rethlas blueprint": "enabled" if self.with_rethlas_blueprint else "disabled",
            "LLM provider": runtime_config["llm_provider"],
            "LLM model": runtime_config["llm_model"] or "(Formalizer config)",
            "LLM base URL": runtime_config["llm_base_url"] or "(Formalizer config)",
            "LLM max tokens": (
                str(runtime_config["llm_max_tokens"])
                if runtime_config["llm_max_tokens"]
                else "(provider default)"
            ),
        })

        ensure_result = (
            self._ensure_physlean_dependency() if self.ensure_physlean else None
        )
        build_result = (
            self._run_physlean_build() if self.build_physlean else None
        )
        preflight_result = (
            self._run_lean_preflight(work_dir) if self.preflight else None
        )

        if self.dry_run:
            manifest_path = self._write_batch_manifest(
                work_dir=work_dir,
                formalizer_root=formalizer_root,
                input_path=input_path,
                entries=entries,
                image_root=image_root,
                out_dir=out_dir,
                report_dir=report_dir,
                runtime_config=runtime_config,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
                records=[],
                dry_run=True,
            )
            self._write_batch_metadata(
                work_dir=work_dir,
                formalizer_root=formalizer_root,
                input_path=input_path,
                entries=entries,
                image_root=image_root,
                out_dir=out_dir,
                report_dir=report_dir,
                runtime_config=runtime_config,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
                records=[],
                dry_run=True,
            )
            if self.update_progress:
                log.warn("--update-progress is ignored during --dry-run.")
            log.success(f"Dry run complete. Batch manifest written to {manifest_path}")
            return

        process_single_problem, config = self._load_formalizer(formalizer_root)
        self._configure_formalizer(
            config,
            runtime_config,
            use_multimodal=has_images,
        )

        log.phase(1, "Physics multimodal batch formalization")
        records: list[dict] = []
        compiled_count = 0
        semantic_count = 0
        summary_path = work_dir / "summary.jsonl"
        out_dir.mkdir(parents=True, exist_ok=True)
        report_dir.mkdir(parents=True, exist_ok=True)

        for entry in entries:
            idx = str(entry["index"])
            log.info(f"Processing physics problem {idx}")
            try:
                result = process_single_problem(
                    entry,
                    str(work_dir),
                    image_root_dir=str(image_root) if image_root else None,
                )
            except Exception as exc:
                result = {
                    "index": idx,
                    "question": entry.get("question", ""),
                    "status": "error",
                    "compilation_passed": False,
                    "semantic_passed": False,
                    "consistency_level": "N/A",
                    "error": str(exc),
                    "generated_code": "",
                }

            out_path = self._batch_out_path(out_dir, idx)
            report_path = self._batch_report_path(report_dir, idx)
            copy_error = None
            try:
                self._copy_formalizer_outputs(
                    index=idx,
                    result=result,
                    work_dir=work_dir,
                    out_path=out_path,
                    report_path=report_path,
                )
            except RuntimeError as exc:
                copy_error = str(exc)
                result["error"] = result.get("error") or copy_error

            compiled = bool(result.get("compilation_passed", False))
            semantic = bool(result.get("semantic_passed", False))
            if compiled:
                compiled_count += 1
            if semantic:
                semantic_count += 1

            record = {
                "index": idx,
                "output_lean": str(out_path),
                "output_report": str(report_path),
                "copied": copy_error is None,
                "status": result.get("status", "unknown"),
                "compilation_passed": compiled,
                "semantic_passed": semantic,
                "consistency_level": result.get("consistency_level", "N/A"),
                "error": result.get("error"),
            }
            records.append(record)
            with summary_path.open("a", encoding="utf-8") as f:
                f.write(json.dumps(record, ensure_ascii=False) + "\n")

        self._write_batch_manifest(
            work_dir=work_dir,
            formalizer_root=formalizer_root,
            input_path=input_path,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            runtime_config=runtime_config,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
            records=records,
            dry_run=False,
        )
        self._write_batch_metadata(
            work_dir=work_dir,
            formalizer_root=formalizer_root,
            input_path=input_path,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            runtime_config=runtime_config,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
            records=records,
            dry_run=False,
        )

        log.phase(2, "Batch result")
        log.key_value({
            "Problems": str(len(entries)),
            "Lean compiled": f"{compiled_count}/{len(entries)}",
            "Semantic passed": f"{semantic_count}/{len(entries)}",
            "Summary": str(summary_path),
            "Lean dir": str(out_dir),
            "Report dir": str(report_dir),
        })

        if self.update_progress:
            successful = [
                (
                    record["index"],
                    Path(record["output_lean"]),
                    Path(record["output_report"]),
                )
                for record in records
                if record["copied"] and record["compilation_passed"]
            ]
            if successful:
                self._update_progress_batch(successful)

        failed = [record["index"] for record in records if not record["compilation_passed"]]
        semantic_failed = [
            record["index"] for record in records if not record["semantic_passed"]
        ]
        if failed:
            log.error("Some generated Lean files did not compile: " + ", ".join(failed))
            raise typer.Exit(1)
        if self.fail_on_semantic and semantic_failed:
            log.error("Semantic alignment failed for: " + ", ".join(semantic_failed))
            raise typer.Exit(2)
        if semantic_failed:
            log.warn("Lean compiled, but semantic alignment did not pass for: " + ", ".join(semantic_failed))
        else:
            log.success("Physics batch formalization generated successfully.")

    # ── setup ─────────────────────────────────────────────────────────

    def _validate_project(self) -> None:
        if not self.project_path.exists():
            log.error(f"Project path does not exist: {self.project_path}")
            raise typer.Exit(1)
        if not self.project_path.is_dir():
            log.error(f"Project path is not a directory: {self.project_path}")
            raise typer.Exit(1)
        if not (
            (self.project_path / "lakefile.lean").exists()
            or (self.project_path / "lakefile.toml").exists()
        ):
            log.warn(
                "No lakefile.lean/toml found. The formalizer can run, but Lean "
                "compilation will fail unless this is a Lean project."
            )

    def _validate_single_mode(self) -> None:
        if self.out_dir or self.report_dir or self.image_root:
            log.error("--out-dir, --report-dir, and --image-root are only used with --input-jsonl.")
            raise typer.Exit(1)

    def _validate_batch_mode(self) -> None:
        if self.question or self.question_file or self.image or self.out or self.report_out:
            log.error(
                "--input-jsonl cannot be combined with --question, --question-file, "
                "--image, --out, or --report-out."
            )
            raise typer.Exit(1)
        if self.answer:
            log.error("--answer is only used for single-problem input; put answers in the JSONL entries.")
            raise typer.Exit(1)
        if self.limit == 0 or self.limit < -1:
            log.error("--limit must be -1 or a positive integer.")
            raise typer.Exit(1)

    def _read_question(self) -> str:
        if self.question and self.question_file:
            log.error("Use either --question or --question-file, not both.")
            raise typer.Exit(1)
        if self.question_file:
            path = self.question_file.expanduser().resolve()
            if not path.is_file():
                log.error(f"Question file not found: {path}")
                raise typer.Exit(1)
            text = path.read_text(encoding="utf-8").strip()
        else:
            text = (self.question or "").strip()
        if not text:
            log.error("A physics problem is required via --question or --question-file.")
            raise typer.Exit(1)
        return text

    def _read_input_jsonl(self) -> tuple[Path, list[dict]]:
        assert self.input_jsonl is not None
        path = self.input_jsonl.expanduser()
        if not path.is_absolute():
            path = Path.cwd() / path
        path = path.resolve()
        if not path.is_file():
            log.error(f"Input JSONL not found: {path}")
            raise typer.Exit(1)

        entries: list[dict] = []
        with path.open("r", encoding="utf-8") as f:
            for line_no, line in enumerate(f, start=1):
                line = line.strip()
                if not line:
                    continue
                try:
                    entry = json.loads(line)
                except json.JSONDecodeError as exc:
                    log.error(f"Invalid JSON on line {line_no} of {path}: {exc}")
                    raise typer.Exit(1)
                if not isinstance(entry, dict):
                    log.error(f"JSONL line {line_no} must be an object.")
                    raise typer.Exit(1)
                question = str(entry.get("question", "")).strip()
                if not question:
                    log.error(f"JSONL line {line_no} is missing a non-empty `question`.")
                    raise typer.Exit(1)
                normalized = dict(entry)
                normalized["index"] = str(normalized.get("index") or f"{line_no:03d}")
                normalized["question"] = question
                normalized["answer"] = str(normalized.get("answer", ""))
                normalized["category"] = str(normalized.get("category", self.category))
                if normalized.get("image") is None:
                    normalized["image"] = None
                elif normalized.get("image"):
                    normalized["image"] = str(normalized["image"])
                entries.append(normalized)
                if self.limit > 0 and len(entries) >= self.limit:
                    break

        if not entries:
            log.error(f"Input JSONL contains no usable physics problems: {path}")
            raise typer.Exit(1)
        return path, entries

    def _resolve_image(self) -> Path | None:
        if self.image is None:
            return None
        path = self.image.expanduser().resolve()
        if not path.is_file():
            log.error(f"Image file not found: {path}")
            raise typer.Exit(1)
        return path

    def _resolve_batch_image_root(self, input_path: Path, entries: list[dict]) -> Path | None:
        has_images = any(entry.get("image") for entry in entries)
        if self.image_root:
            root = self.image_root.expanduser()
            if not root.is_absolute():
                root = input_path.parent / root
        else:
            root = input_path.parent / "image"

        root = root.resolve()
        if root.exists() and not root.is_dir():
            log.error(f"Image root is not a directory: {root}")
            raise typer.Exit(1)
        if has_images and not root.is_dir():
            log.warn(f"Some JSONL entries reference images, but image root does not exist: {root}")
        if has_images or root.is_dir():
            return root
        return None

    def _resolve_work_dir(self) -> Path:
        if self.work_dir:
            work_dir = self.work_dir.expanduser()
            if not work_dir.is_absolute():
                work_dir = self.project_path / work_dir
        else:
            stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            prefix = "batch" if self.input_jsonl else f"problem_{self.index}"
            work_dir = (
                self.project_path
                / ".archon"
                / "physics-formalize"
                / f"{prefix}_{stamp}"
            )
        work_dir.mkdir(parents=True, exist_ok=True)
        return work_dir.resolve()

    def _resolve_out_path(self) -> Path:
        if self.out:
            out_path = self.out.expanduser()
            if not out_path.is_absolute():
                out_path = self.project_path / out_path
        else:
            out_path = self.project_path / "PhysicsProblems" / f"problem_{self.index}.lean"
        return out_path.resolve()

    def _resolve_report_path(self, out_path: Path) -> Path:
        if self.report_out:
            report_path = self.report_out.expanduser()
            if not report_path.is_absolute():
                report_path = self.project_path / report_path
            return report_path.resolve()
        return out_path.with_suffix(".report.json")

    def _resolve_out_dir(self) -> Path:
        out_dir = self.out_dir.expanduser() if self.out_dir else Path("PhysicsProblems")
        if not out_dir.is_absolute():
            out_dir = self.project_path / out_dir
        return out_dir.resolve()

    def _resolve_report_dir(self, out_dir: Path) -> Path:
        report_dir = self.report_dir.expanduser() if self.report_dir else out_dir
        if not report_dir.is_absolute():
            report_dir = self.project_path / report_dir
        return report_dir.resolve()

    @staticmethod
    def _batch_out_path(out_dir: Path, index: str) -> Path:
        return out_dir / f"problem_{index}.lean"

    @staticmethod
    def _batch_report_path(report_dir: Path, index: str) -> Path:
        return report_dir / f"problem_{index}.report.json"

    @staticmethod
    def _missing_images(entries: list[dict], image_root: Path | None) -> list[dict]:
        missing: list[dict] = []
        if image_root is None:
            return missing
        for entry in entries:
            image = entry.get("image")
            if not image:
                continue
            image_path = Path(image)
            if not image_path.is_absolute():
                image_path = image_root / image
            if not image_path.is_file():
                missing.append({
                    "index": str(entry.get("index")),
                    "image": str(image),
                    "expected_path": str(image_path),
                })
        return missing

    def _ensure_physlean_dependency(self) -> dict:
        lakefile, kind = self._resolve_lakefile()
        text = lakefile.read_text(encoding="utf-8", errors="replace")
        result = {
            "requested": True,
            "modified": False,
            "path": str(lakefile),
            "kind": kind,
            "update_passed": None,
        }

        if self._lakefile_has_physlean(text):
            log.success("PhysLean dependency already declared.")
            return result

        if kind == "lean":
            addition = PHYSLEAN_REQUIRE_LEAN
        elif kind == "toml":
            addition = PHYSLEAN_REQUIRE_TOML
        else:
            log.error(f"Unsupported lakefile type: {lakefile.name}")
            raise typer.Exit(1)

        with lakefile.open("a", encoding="utf-8") as f:
            f.write(addition)
        result["modified"] = True
        log.success(f"Added PhysLean dependency to {lakefile.name}.")
        result["update_passed"] = self._run_lake_update_physlean()
        return result

    def _resolve_lakefile(self) -> tuple[Path, str]:
        lean = self.project_path / "lakefile.lean"
        toml = self.project_path / "lakefile.toml"
        if lean.exists():
            return lean, "lean"
        if toml.exists():
            return toml, "toml"
        log.error("PhysLean dependency setup failed: target project has no lakefile.")
        raise typer.Exit(1)

    @staticmethod
    def _lakefile_has_physlean(text: str) -> bool:
        return bool(
            re.search(r"\brequire\s+PhysLean\b", text)
            or re.search(r'name\s*=\s*"PhysLean"', text)
            or PHYSLEAN_GIT_URL in text
        )

    def _run_lake_update_physlean(self) -> bool:
        lake = shutil.which("lake")
        if not lake:
            log.error("PhysLean dependency setup failed: could not find `lake` on PATH.")
            raise typer.Exit(1)
        command = [lake, "update", "PhysLean"]
        log.phase(0, "Update PhysLean dependency")
        try:
            proc = subprocess.run(
                command,
                cwd=self.project_path,
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
                timeout=600,
                stdin=subprocess.DEVNULL,
            )
        except subprocess.TimeoutExpired:
            log.error("`lake update PhysLean` timed out after 600 seconds.")
            raise typer.Exit(1)
        except OSError as exc:
            log.error(f"`lake update PhysLean` failed to start: {exc}")
            raise typer.Exit(1)
        if proc.returncode == 0:
            log.success("Updated PhysLean dependency manifest.")
            return True
        output = (proc.stderr or proc.stdout or "").strip()
        log.error("`lake update PhysLean` failed.")
        if output:
            log.info(output[:1200])
        raise typer.Exit(1)

    def _run_physlean_build(self) -> dict:
        lake = shutil.which("lake")
        if not lake:
            log.error("PhysLean build failed: could not find `lake` on PATH.")
            raise typer.Exit(1)
        if not (
            (self.project_path / "lakefile.lean").exists()
            or (self.project_path / "lakefile.toml").exists()
        ):
            log.error("PhysLean build failed: target project has no lakefile.")
            raise typer.Exit(1)

        command = [lake, "build", "PhysLean"]
        log.phase(0, "Build PhysLean")
        try:
            proc = subprocess.run(
                command,
                cwd=self.project_path,
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
                timeout=1800,
                stdin=subprocess.DEVNULL,
            )
        except subprocess.TimeoutExpired:
            log.error("PhysLean build timed out after 1800 seconds.")
            raise typer.Exit(1)
        except OSError as exc:
            log.error(f"PhysLean build failed to start: {exc}")
            raise typer.Exit(1)

        result = {
            "requested": True,
            "passed": proc.returncode == 0,
            "command": " ".join(command),
            "target": "PhysLean",
        }
        if proc.returncode == 0:
            log.success("PhysLean build completed.")
            return result

        output = (proc.stderr or proc.stdout or "").strip()
        result["error"] = output[:4000]
        log.error("PhysLean build failed.")
        if output:
            log.info(output[:1200])
        raise typer.Exit(1)

    def _run_lean_preflight(self, work_dir: Path) -> dict:
        lake = shutil.which("lake")
        if not lake:
            log.error("Lean preflight failed: could not find `lake` on PATH.")
            raise typer.Exit(1)

        if not (
            (self.project_path / "lakefile.lean").exists()
            or (self.project_path / "lakefile.toml").exists()
        ):
            log.error("Lean preflight failed: target project has no lakefile.")
            raise typer.Exit(1)

        preflight_path = work_dir / "physics_preflight.lean"
        preflight_code = "\n".join(PHYSICS_PREFLIGHT_IMPORTS) + "\n\n#check True\n"
        preflight_path.write_text(preflight_code, encoding="utf-8")

        command = [lake, "env", "lean", str(preflight_path)]
        log.phase(0, "Lean/PhysLean preflight")
        try:
            proc = subprocess.run(
                command,
                cwd=self.project_path,
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
                timeout=180,
                stdin=subprocess.DEVNULL,
            )
        except subprocess.TimeoutExpired:
            log.error("Lean preflight timed out after 180 seconds.")
            raise typer.Exit(1)
        except OSError as exc:
            log.error(f"Lean preflight failed to start: {exc}")
            raise typer.Exit(1)

        result = {
            "requested": True,
            "passed": proc.returncode == 0,
            "file": str(preflight_path),
            "command": " ".join(command),
            "packages": ["Mathlib", "PhysLean"],
        }
        if proc.returncode == 0:
            log.success("Lean preflight passed: Mathlib/PhysLean imports compile.")
            return result

        output = (proc.stderr or proc.stdout or "").strip()
        result["error"] = output[:4000]
        log.error("Lean preflight failed: Mathlib/PhysLean imports did not compile.")
        if output:
            log.info(output[:1200])
            hint = self._preflight_hint(output)
            if hint:
                log.info(hint)
        raise typer.Exit(1)

    @staticmethod
    def _preflight_hint(output: str) -> str | None:
        if "unknown module prefix 'PhysLean'" in output or "unknown package PhysLean" in output:
            return (
                "Hint: the target project does not currently expose PhysLean to "
                "`lake env lean`. Run `lake update PhysLean`/`lake build` in the "
                "target project, or point `archon physics-formalize` at a Lean "
                "project whose lakefile has a working PhysLean dependency."
            )
        if "unknown module prefix 'Mathlib'" in output or "unknown package Mathlib" in output:
            return (
                "Hint: the target project does not currently expose Mathlib to "
                "`lake env lean`. Run `lake update`/`lake build` in the target "
                "project before calling the model."
            )
        return None

    def _build_entry(self, question: str, image_path: Path | None) -> dict:
        return {
            "index": self.index,
            "question": question,
            "answer": self.answer,
            "category": self.category,
            "image": image_path.name if image_path else None,
        }

    def _write_manifest(
        self,
        *,
        work_dir: Path,
        formalizer_root: Path,
        out_path: Path,
        report_path: Path,
        entry: dict,
        image_root: str | None,
        runtime_config: dict,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
    ) -> Path:
        manifest = {
            "command": "physics-formalize",
            "project_path": str(self.project_path),
            "formalizer_root": str(formalizer_root),
            "work_dir": str(work_dir),
            "output_lean": str(out_path),
            "output_report": str(report_path),
            "image_root": image_root,
            "domain": "physics",
            "use_multimodal": bool(entry.get("image")),
            "lean_search_packages": ["Mathlib", "PhysLean"],
            "workers": max(1, self.workers),
            "decompose": self.decompose,
            "physlean_dependency": self._metadata_physlean_dependency(ensure_result),
            "physlean_build": self._metadata_physlean_build(build_result),
            "preflight": self._metadata_preflight(preflight_result),
            "llm": self._metadata_llm_config(runtime_config),
            "leanexplore": self._metadata_leanexplore_config(runtime_config),
            "entry": entry,
        }
        manifest_path = work_dir / f"problem_{self.index}_manifest.json"
        manifest_path.write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        return manifest_path

    def _write_archon_metadata(
        self,
        *,
        work_dir: Path,
        formalizer_root: Path,
        out_path: Path,
        report_path: Path,
        entry: dict,
        image_root: str | None,
        runtime_config: dict,
        result: dict | None,
        dry_run: bool,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
    ) -> Path:
        state_dir = self.project_path / ".archon" / "physics-formalize"
        state_dir.mkdir(parents=True, exist_ok=True)
        result_summary = {}
        if result:
            result_summary = {
                "status": result.get("status", "unknown"),
                "compilation_passed": bool(result.get("compilation_passed", False)),
                "semantic_passed": bool(result.get("semantic_passed", False)),
                "consistency_level": result.get("consistency_level", "N/A"),
                "error": result.get("error"),
            }
        metadata = {
            "schema_version": 1,
            "command": "physics-formalize",
            "dry_run": dry_run,
            "project_path": str(self.project_path),
            "formalizer_root": str(formalizer_root),
            "work_dir": str(work_dir),
            "output_lean": str(out_path),
            "output_report": str(report_path),
            "image_root": image_root,
            "domain": "physics",
            "use_multimodal": bool(entry.get("image")),
            "lean_search_packages": ["Mathlib", "PhysLean"],
            "workers": max(1, self.workers),
            "decompose": self.decompose,
            "physlean_dependency": self._metadata_physlean_dependency(ensure_result),
            "physlean_build": self._metadata_physlean_build(build_result),
            "preflight": self._metadata_preflight(preflight_result),
            "llm": self._metadata_llm_config(runtime_config),
            "leanexplore": self._metadata_leanexplore_config(runtime_config),
            "entry": entry,
            "result": result_summary,
        }
        run_path = state_dir / f"problem_{self.index}.json"
        latest_path = state_dir / "latest.json"
        payload = json.dumps(metadata, indent=2, ensure_ascii=False)
        run_path.write_text(payload, encoding="utf-8")
        latest_path.write_text(payload, encoding="utf-8")
        return run_path

    def _write_batch_manifest(
        self,
        *,
        work_dir: Path,
        formalizer_root: Path,
        input_path: Path,
        entries: list[dict],
        image_root: Path | None,
        out_dir: Path,
        report_dir: Path,
        runtime_config: dict,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
        records: list[dict],
        dry_run: bool,
    ) -> Path:
        manifest = self._batch_metadata_payload(
            work_dir=work_dir,
            formalizer_root=formalizer_root,
            input_path=input_path,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            runtime_config=runtime_config,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
            records=records,
            dry_run=dry_run,
        )
        manifest_path = work_dir / "batch_manifest.json"
        manifest_path.write_text(
            json.dumps(manifest, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        return manifest_path

    def _write_batch_metadata(
        self,
        *,
        work_dir: Path,
        formalizer_root: Path,
        input_path: Path,
        entries: list[dict],
        image_root: Path | None,
        out_dir: Path,
        report_dir: Path,
        runtime_config: dict,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
        records: list[dict],
        dry_run: bool,
    ) -> Path:
        state_dir = self.project_path / ".archon" / "physics-formalize"
        state_dir.mkdir(parents=True, exist_ok=True)
        metadata = self._batch_metadata_payload(
            work_dir=work_dir,
            formalizer_root=formalizer_root,
            input_path=input_path,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            runtime_config=runtime_config,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
            records=records,
            dry_run=dry_run,
        )
        safe_stem = re.sub(r"[^A-Za-z0-9_.-]+", "_", input_path.stem).strip("_") or "batch"
        run_path = state_dir / f"batch_{safe_stem}.json"
        latest_path = state_dir / "latest.json"
        payload = json.dumps(metadata, indent=2, ensure_ascii=False)
        run_path.write_text(payload, encoding="utf-8")
        latest_path.write_text(payload, encoding="utf-8")
        return run_path

    def _batch_metadata_payload(
        self,
        *,
        work_dir: Path,
        formalizer_root: Path,
        input_path: Path,
        entries: list[dict],
        image_root: Path | None,
        out_dir: Path,
        report_dir: Path,
        runtime_config: dict,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
        records: list[dict],
        dry_run: bool,
    ) -> dict:
        compiled_count = sum(1 for record in records if record.get("compilation_passed"))
        semantic_count = sum(1 for record in records if record.get("semantic_passed"))
        return {
            "schema_version": 1,
            "command": "physics-formalize",
            "mode": "batch",
            "dry_run": dry_run,
            "project_path": str(self.project_path),
            "formalizer_root": str(formalizer_root),
            "work_dir": str(work_dir),
            "input_jsonl": str(input_path),
            "output_dir": str(out_dir),
            "report_dir": str(report_dir),
            "image_root": str(image_root) if image_root else None,
            "domain": "physics",
            "use_multimodal": any(entry.get("image") for entry in entries),
            "lean_search_packages": ["Mathlib", "PhysLean"],
            "workers": max(1, self.workers),
            "decompose": self.decompose,
            "limit": self.limit,
            "entry_count": len(entries),
            "missing_images": self._missing_images(entries, image_root),
            "physlean_dependency": self._metadata_physlean_dependency(ensure_result),
            "physlean_build": self._metadata_physlean_build(build_result),
            "preflight": self._metadata_preflight(preflight_result),
            "llm": self._metadata_llm_config(runtime_config),
            "leanexplore": self._metadata_leanexplore_config(runtime_config),
            "entries": entries,
            "records": records,
            "result": {
                "total": len(entries),
                "compiled": compiled_count,
                "semantic_passed": semantic_count,
                "failed": len([record for record in records if not record.get("compilation_passed")]),
            },
        }

    def _ensure_physics_prover_mode(self) -> Path:
        state_dir = self.project_path / ".archon" / "prover-modes"
        state_dir.mkdir(parents=True, exist_ok=True)
        src = data_path(f"prover-modes/{PHYSICS_PROVER_MODE}.md")
        dst = state_dir / f"{PHYSICS_PROVER_MODE}.md"
        if not src.is_file():
            raise RuntimeError(f"Bundled physics prover mode missing: {src}")
        if not dst.exists() or src.read_bytes() != dst.read_bytes():
            shutil.copy2(src, dst)
        return dst

    def _write_physics_proving_scaffold(
        self,
        items: list[tuple[str, Path, Path]],
    ) -> dict[str, dict]:
        """Create Archon proof-stage scaffolding for generated physics files."""

        self._ensure_physics_prover_mode()
        scaffold: dict[str, dict] = {}
        protect_items: list[tuple[str, str, str]] = []

        for index, out_path, report_path in items:
            rel_lean = self._rel_to_project(out_path)
            declarations = self._parse_lean_declarations(out_path)
            chapter_path, labels = self._write_physics_blueprint_chapter(
                index=index,
                out_path=out_path,
                report_path=report_path,
                declarations=declarations,
            )
            for decl, label in zip(declarations, labels):
                protect_items.append((rel_lean, decl["full_name"], label))
            scaffold[rel_lean] = {
                "chapter_path": chapter_path,
                "declarations": declarations,
                "labels": labels,
            }

        self._merge_protected_surface(protect_items)
        return scaffold

    def _write_physics_blueprint_chapter(
        self,
        *,
        index: str,
        out_path: Path,
        report_path: Path,
        declarations: list[dict],
    ) -> tuple[Path, list[str]]:
        rel_lean = self._rel_to_project(out_path)
        rel_report = self._rel_to_project(report_path)
        structure = BlueprintStructure(self.project_path)
        structure.blueprint_src.mkdir(parents=True, exist_ok=True)
        if not structure.content_tex.exists():
            structure.content_tex.write_text(
                "% Archon physics blueprint.\n", encoding="utf-8"
            )

        chapter = BlueprintChapter(self.project_path, rel_lean)
        report = self._read_report(report_path)
        question = (
            report.get("question")
            or (self._read_question() if not self.input_jsonl else "")
            or f"Physics problem {index}"
        )
        answer = report.get("answer") or self.answer
        rethlas_result = self._run_rethlas_blueprint_agent(
            index=index,
            question=question,
            answer=str(answer or ""),
            report=report,
            declarations=declarations,
        )

        labels = [
            self._physics_blueprint_label(index, decl["full_name"])
            for decl in declarations
        ]
        generated = self._physics_blueprint_block(
            index=index,
            rel_lean=rel_lean,
            rel_report=rel_report,
            question=question,
            answer=answer,
            rethlas_result=rethlas_result,
            declarations=declarations,
            labels=labels,
            include_chapter=not chapter.path.exists(),
        )

        chapter.chapter_dir.mkdir(parents=True, exist_ok=True)
        if chapter.path.exists():
            old = chapter.path.read_text(encoding="utf-8")
            new = self._replace_or_append_generated_block(old, generated)
        else:
            new = generated
        chapter.path.write_text(new, encoding="utf-8")

        structure.convert_to_dispatcher()
        return chapter.path, labels

    @staticmethod
    def _replace_or_append_generated_block(existing: str, generated: str) -> str:
        begin = "% --- Archon physics formalizer begin ---"
        end = "% --- Archon physics formalizer end ---"
        pattern = rf"{re.escape(begin)}.*?{re.escape(end)}"
        new_text, count = re.subn(
            pattern,
            generated.strip(),
            existing,
            count=1,
            flags=re.DOTALL,
        )
        if count:
            return new_text.rstrip() + "\n"
        return existing.rstrip() + "\n\n" + generated

    def _physics_blueprint_block(
        self,
        *,
        index: str,
        rel_lean: str,
        rel_report: str,
        question: str,
        answer: str,
        rethlas_result: dict | None,
        declarations: list[dict],
        labels: list[str],
        include_chapter: bool,
    ) -> str:
        proof_steps = self._physics_proof_steps(
            question=question,
            answer=str(answer or ""),
            rethlas_result=rethlas_result,
        )
        lines = [
            "% --- Archon physics formalizer begin ---",
            f"% archon:covers {rel_lean}",
        ]
        if include_chapter:
            title = self._latex_escape(f"Physics problem {index}")
            slug = BlueprintChapter(self.project_path, rel_lean).slug
            lines.extend([
                "",
                f"\\chapter{{{title}}}",
                f"\\label{{ch:{slug}}}",
            ])
        else:
            title = self._latex_escape(f"Physics formalization {index}")
            lines.extend(["", f"\\section{{{title}}}"])

        lines.extend([
            "",
            "\\paragraph{Problem source.}",
            self._latex_escape(question),
        ])
        if answer:
            lines.extend([
                "",
                "\\paragraph{Recorded answer.}",
                self._latex_escape(str(answer)),
            ])
        lines.extend([
            "",
            "\\paragraph{Formalizer report.}",
            f"The semantic-alignment and grounding report is `{self._latex_escape(rel_report)}`.",
            "",
            "\\paragraph{Proof route.}",
            "The Lean declarations below were generated from the physics formalizer. "
            "Their statements are fixed; the prover should formalize the same physical "
            "argument by using the recorded assumptions, grounded Mathlib or PhysLean "
            "objects, and the relevant algebraic simplification.",
        ])
        if self.with_rethlas_blueprint:
            lines.extend(["", "\\paragraph{Rethlas-assisted proof route.}"])
            if rethlas_result and rethlas_result.get("status") == "success":
                lines.append(
                    "Rethlas supplied the following natural-language proof sketch; "
                    "use it as guidance, not as a Lean authority."
                )
            else:
                lines.append(
                    "Rethlas was requested but unavailable; Archon generated a "
                    "local physics proof route from the formalizer report."
                )
                if rethlas_result and rethlas_result.get("message"):
                    lines.append(self._latex_escape(str(rethlas_result["message"])))
            lines.append("\\begin{enumerate}")
            for step in proof_steps:
                lines.append(f"\\item {self._latex_escape(step)}")
            lines.append("\\end{enumerate}")

        if not declarations:
            lines.extend([
                "",
                "% No theorem/lemma/definition declarations were detected in the Lean file.",
            ])

        for decl, label in zip(declarations, labels):
            env = "theorem" if decl["kind"] in {"theorem", "lemma"} else "definition"
            title = self._latex_escape(decl["full_name"])
            lines.extend([
                "",
                f"\\begin{{{env}}}[{title}]",
                f"\\label{{{label}}}",
                f"\\lean{{{decl['full_name']}}}",
                self._latex_escape(
                    f"This is the Lean {decl['kind']} `{decl['full_name']}` "
                    f"generated for physics problem {index}."
                ),
                f"\\end{{{env}}}",
                "\\begin{proof}",
                self._latex_escape(
                    "Use the problem statement and the generated hypotheses exactly as "
                    "formalized. For computational physics questions, follow the proof "
                    "route above: isolate the physical law hypotheses, prove the local "
                    "vector/algebraic reductions, combine the intermediate forces or "
                    "quantities, and close the stated result. If a required physical "
                    "law is absent from the Lean statement, keep the signature fixed "
                    "and report a redraft need rather than changing the theorem."
                ),
                "\\end{proof}",
            ])

        lines.append("% --- Archon physics formalizer end ---")
        return "\n".join(lines).rstrip() + "\n"

    def _run_rethlas_blueprint_agent(
        self,
        *,
        index: str,
        question: str,
        answer: str,
        report: dict,
        declarations: list[dict],
    ) -> dict | None:
        if not self.with_rethlas_blueprint:
            return None

        command = self.rethlas_command or os.environ.get("RETHLAS_COMMAND")
        if not command:
            found = shutil.which("rethlas")
            command = found if found else None
        if not command:
            return {
                "status": "unavailable",
                "message": (
                    "Rethlas command not configured. Set --rethlas-command, "
                    "RETHLAS_COMMAND, or install a `rethlas` executable."
                ),
                "sketch": "",
            }

        payload = {
            "index": index,
            "question": question,
            "answer": answer,
            "status": report.get("status"),
            "consistency_level": report.get("consistency_level"),
            "declarations": declarations,
        }
        try:
            proc = subprocess.run(
                shlex.split(command),
                input=json.dumps(payload, ensure_ascii=False),
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
                timeout=max(1, int(self.rethlas_timeout)),
            )
        except FileNotFoundError:
            return {
                "status": "unavailable",
                "message": f"Rethlas command not found: {command}",
                "sketch": "",
            }
        except subprocess.TimeoutExpired:
            return {
                "status": "timeout",
                "message": f"Rethlas timed out after {self.rethlas_timeout} seconds.",
                "sketch": "",
            }
        except OSError as exc:
            return {
                "status": "error",
                "message": f"Rethlas failed to start: {exc}",
                "sketch": "",
            }

        stdout = (proc.stdout or "").strip()
        stderr = (proc.stderr or "").strip()
        if proc.returncode != 0:
            return {
                "status": "error",
                "message": (
                    f"Rethlas exited with code {proc.returncode}: "
                    f"{(stderr or stdout)[:500]}"
                ),
                "sketch": stdout,
            }
        return {
            "status": "success",
            "message": "Rethlas proof sketch generated.",
            "sketch": stdout,
        }

    def _physics_proof_steps(
        self,
        *,
        question: str,
        answer: str,
        rethlas_result: dict | None,
    ) -> list[str]:
        if rethlas_result and rethlas_result.get("status") == "success":
            steps = self._split_proof_sketch(str(rethlas_result.get("sketch") or ""))
            if steps:
                return steps

        lower = question.lower()
        steps: list[str] = [
            "Model the physical quantities named in the statement as the Lean variables and hypotheses already present in the generated declaration.",
        ]
        if "magnetic" in lower and ("current" in lower or "loop" in lower):
            steps.extend([
                "Introduce the magnetic-force law for each relevant current-carrying segment as a local hypothesis or use the corresponding generated hypothesis.",
                "Decompose the loop into oriented path segments and compute the force contribution on each segment using the stated field expression and orientation convention.",
                "Show that opposite side contributions cancel whenever the geometry and field values make them equal and opposite.",
                "Sum the remaining segment contributions as vectors and simplify the scalar factors.",
            ])
        elif "force" in lower or "acceleration" in lower:
            steps.extend([
                "Isolate the governing force law or kinematic law supplied by the generated hypotheses.",
                "Rewrite the target quantity using that law and simplify the resulting real-number expression.",
            ])
        elif "energy" in lower or "work" in lower:
            steps.extend([
                "Isolate the conservation or work-energy relation supplied by the generated hypotheses.",
                "Reduce the target statement to algebra over the declared scalar quantities.",
            ])
        else:
            steps.extend([
                "Identify the physical law hypothesis that connects the known quantities to the target quantity.",
                "Reduce the statement to the algebraic or vector identity expressed by that law.",
            ])
        if answer:
            steps.append(f"Conclude that the formal target equals the recorded answer {answer}.")
        else:
            steps.append("Conclude by matching the simplified expression to the target statement.")
        return steps

    @staticmethod
    def _split_proof_sketch(sketch: str) -> list[str]:
        lines = []
        for raw in sketch.splitlines():
            line = raw.strip()
            if not line:
                continue
            line = re.sub(r"^\s*(?:[-*]|\d+[.)])\s*", "", line).strip()
            if line:
                lines.append(line)
        if len(lines) > 1:
            return lines
        sentences = re.split(r"(?<=[.!?])\s+", sketch.strip())
        return [s.strip() for s in sentences if s.strip()]

    @staticmethod
    def _read_report(report_path: Path) -> dict:
        try:
            data = json.loads(report_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return {}
        return data if isinstance(data, dict) else {}

    @classmethod
    def _parse_lean_declarations(cls, lean_path: Path) -> list[dict]:
        try:
            lines = lean_path.read_text(encoding="utf-8").splitlines()
        except OSError:
            return []

        declarations: list[dict] = []
        namespace_stack: list[str] = []
        decl_re = re.compile(
            r"^\s*(?:(?:private|protected|noncomputable|irreducible|unsafe|"
            r"scoped|partial)\s+)*(?P<kind>theorem|lemma|def|abbrev|instance|"
            r"structure|class|inductive)\s+(?P<name>[^\s:(\[{=]+)"
        )
        namespace_re = re.compile(r"^\s*namespace\s+(.+?)\s*$")
        end_re = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.'`]+))?\s*$")

        for line in lines:
            stripped = line.strip()
            if not stripped or stripped.startswith("--"):
                continue
            ns_match = namespace_re.match(line)
            if ns_match:
                namespace_stack.extend(ns_match.group(1).split())
                continue
            end_match = end_re.match(line)
            if end_match and namespace_stack:
                name = end_match.group(1)
                if name and name in namespace_stack:
                    while namespace_stack:
                        popped = namespace_stack.pop()
                        if popped == name:
                            break
                else:
                    namespace_stack.pop()
                continue
            decl_match = decl_re.match(line)
            if not decl_match:
                continue
            name = decl_match.group("name")
            if name in {":", ":="}:
                continue
            full_name = name if "." in name else ".".join([*namespace_stack, name])
            declarations.append({
                "kind": decl_match.group("kind"),
                "name": name,
                "full_name": full_name,
            })

        return declarations

    @staticmethod
    def _physics_blueprint_label(index: str, decl_name: str) -> str:
        safe_index = re.sub(r"[^A-Za-z0-9_.-]+", "_", index).strip("_") or "problem"
        safe_decl = re.sub(
            r"[^A-Za-z0-9_.-]+",
            "_",
            decl_name.replace("/", "."),
        ).strip("_") or "decl"
        return f"thm:physics:{safe_index}:{safe_decl}"

    @staticmethod
    def _latex_escape(text: str) -> str:
        replacements = {
            "\\": r"\textbackslash{}",
            "&": r"\&",
            "%": r"\%",
            "$": r"\$",
            "#": r"\#",
            "_": r"\_",
            "{": r"\{",
            "}": r"\}",
            "~": r"\textasciitilde{}",
            "^": r"\textasciicircum{}",
        }
        return "".join(replacements.get(ch, ch) for ch in str(text))

    def _merge_protected_surface(self, items: list[tuple[str, str, str]]) -> None:
        if not items:
            return
        target = self.project_path / "archon-protected.yaml"
        raw: object = {}
        if target.exists():
            try:
                raw = yaml.safe_load(target.read_text(encoding="utf-8")) or {}
            except yaml.YAMLError:
                raw = {}
        if not isinstance(raw, dict):
            raw = {}

        lean = raw.get("lean")
        if not isinstance(lean, dict):
            lean = {}
            raw["lean"] = lean
        blueprint = raw.get("blueprint")
        if not isinstance(blueprint, list):
            blueprint = []
            raw["blueprint"] = blueprint

        for rel_lean, decl_name, label in items:
            rules = lean.get(rel_lean)
            if not isinstance(rules, list):
                rules = []
                lean[rel_lean] = rules
            if not self._lean_protection_exists(rules, decl_name):
                rules.append(decl_name)
            if not self._blueprint_label_protection_exists(blueprint, label):
                blueprint.append({"label": label, "protect": "statement"})

        yaml_body = yaml.safe_dump(raw, sort_keys=False, default_flow_style=False)
        header = ""
        if target.exists():
            header_lines = []
            for line in target.read_text(encoding="utf-8").splitlines():
                if line.startswith("#") or not line.strip():
                    header_lines.append(line)
                else:
                    break
            if header_lines:
                header = "\n".join(header_lines).rstrip() + "\n\n"
        target.write_text(header + yaml_body, encoding="utf-8")

    @staticmethod
    def _lean_protection_exists(rules: list, decl_name: str) -> bool:
        for rule in rules:
            if rule == decl_name:
                return True
            if isinstance(rule, dict) and rule.get("name") == decl_name:
                return True
        return False

    @staticmethod
    def _blueprint_label_protection_exists(rules: list, label: str) -> bool:
        for rule in rules:
            if isinstance(rule, dict) and rule.get("label") == label:
                return True
        return False

    def _update_progress(self, out_path: Path, report_path: Path) -> None:
        self._update_progress_entries([(self.index, out_path, report_path)])

    def _update_progress_batch(self, items: list[tuple[str, Path, Path]]) -> None:
        self._update_progress_entries(items)

    def _update_progress_entries(self, items: list[tuple[str, Path, Path]]) -> None:
        state_dir = self.project_path / ".archon"
        state_dir.mkdir(parents=True, exist_ok=True)
        progress = state_dir / "PROGRESS.md"
        scaffold = self._write_physics_proving_scaffold(items)
        objective_parts: list[str] = []
        for number, (index, out_path, report_path) in enumerate(items, start=1):
            rel_lean = self._rel_to_project(out_path)
            rel_report = self._rel_to_project(report_path)
            chapter = scaffold.get(rel_lean, {}).get("chapter_path")
            rel_chapter = self._rel_to_project(chapter) if chapter else None
            objective_parts.append(
                f"### {number}. **`{rel_lean}`** [prover-mode: {PHYSICS_PROVER_MODE}]\n"
                f"- Generated by `archon physics-formalize` for physics problem `{index}`.\n"
                f"- Formalization report: `{rel_report}`.\n"
                + (f"- Blueprint chapter: `{rel_chapter}`.\n" if rel_chapter else "")
            )
        objective = "\n".join(objective_parts)
        if progress.exists():
            text = progress.read_text(encoding="utf-8")
        else:
            text = (
                "# Project Progress\n\n"
                "## Current Stage\n\n"
                "prover\n\n"
                "## Stages\n"
                "- [x] init\n"
                "- [x] autoformalize\n"
                "- [ ] prover\n"
                "- [ ] polish\n\n"
                "## Current Objectives\n\n"
            )

        text = self._replace_or_add_section(
            text,
            "## Current Stage",
            "prover\n",
            before="## Stages",
        )
        text = self._mark_stage_checkboxes(text)
        text = self._replace_or_add_section(
            text,
            "## Current Objectives",
            objective,
            before=None,
        )
        progress.write_text(text, encoding="utf-8")
        log.success(f"Updated PROGRESS.md objectives for {len(items)} generated Lean file(s).")

    def _rel_to_project(self, path: Path) -> str:
        resolved = path.resolve()
        try:
            return resolved.relative_to(self.project_path).as_posix()
        except ValueError:
            return str(resolved)

    @staticmethod
    def _replace_or_add_section(
        text: str,
        heading: str,
        body: str,
        *,
        before: str | None,
    ) -> str:
        if before:
            pattern = rf"{re.escape(heading)}\s*.*?(?={re.escape(before)})"
            replacement = f"{heading}\n\n{body.rstrip()}\n\n"
        else:
            pattern = rf"{re.escape(heading)}\s*.*?(?=\n## |\Z)"
            replacement = f"{heading}\n\n{body.rstrip()}\n"
        new_text, count = re.subn(pattern, replacement, text, count=1, flags=re.DOTALL)
        if count:
            return new_text
        suffix = "" if text.endswith("\n") else "\n"
        return f"{text}{suffix}\n{replacement}"

    @staticmethod
    def _mark_stage_checkboxes(text: str) -> str:
        replacements = {
            r"- \[[ xX]\] init": "- [x] init",
            r"- \[[ xX]\] autoformalize": "- [x] autoformalize",
            r"- \[[ xX]\] prover": "- [ ] prover",
            r"- \[[ xX]\] polish": "- [ ] polish",
        }
        for pattern, repl in replacements.items():
            text = re.sub(pattern, repl, text)
        return text

    # ── runtime model/search configuration ────────────────────────────

    def _resolve_runtime_config(self) -> dict:
        provider = self._normalize_llm_provider(self.llm_provider)
        llm_key, llm_key_source = self._resolve_secret(
            direct_value=self.llm_api_key,
            env_name=self.llm_api_key_env,
            label="LLM API key",
            fallback_env="ANTHROPIC_API_KEY" if provider == "anthropic" else None,
        )
        leanexplore_key, leanexplore_key_source = self._resolve_secret(
            direct_value=self.leanexplore_api_key,
            env_name=self.leanexplore_api_key_env,
            label="LeanExplore API key",
        )
        llm_base_url = self.llm_base_url
        llm_max_tokens = self.llm_max_tokens
        if provider == "anthropic":
            llm_base_url = llm_base_url or DEFAULT_ANTHROPIC_BASE_URL
            llm_max_tokens = llm_max_tokens or DEFAULT_ANTHROPIC_MAX_TOKENS
            if not llm_key:
                log.warn(
                    "Anthropic provider selected without an explicit key; "
                    "the Formalizer config value will be used at runtime."
                )
        if llm_max_tokens is not None and llm_max_tokens <= 0:
            log.error("--llm-max-tokens must be a positive integer.")
            raise typer.Exit(1)
        if self.llm_timeout <= 0:
            log.error("--llm-timeout must be a positive integer.")
            raise typer.Exit(1)
        supports_temperature = None
        if self.llm_no_temperature:
            supports_temperature = False
        elif provider == "anthropic":
            supports_temperature = True
        elif self.llm_model:
            supports_temperature = self._model_supports_temperature(self.llm_model)
        return {
            "llm_provider": provider,
            "llm_api_key": llm_key,
            "llm_api_key_source": llm_key_source,
            "llm_base_url": llm_base_url,
            "llm_model": self.llm_model,
            "llm_max_tokens": llm_max_tokens,
            "llm_timeout": self.llm_timeout,
            "llm_supports_temperature": supports_temperature,
            "leanexplore_api_key": leanexplore_key,
            "leanexplore_api_key_source": leanexplore_key_source,
        }

    @staticmethod
    def _normalize_llm_provider(provider: str) -> str:
        value = (provider or "openai-compatible").strip().lower()
        aliases = {
            "openai": "openai-compatible",
            "openai_compatible": "openai-compatible",
            "openai-compatible": "openai-compatible",
            "anthropic": "anthropic",
            "claude": "anthropic",
        }
        normalized = aliases.get(value)
        if normalized not in SUPPORTED_LLM_PROVIDERS:
            log.error(
                "--llm-provider must be one of: "
                + ", ".join(sorted(SUPPORTED_LLM_PROVIDERS))
            )
            raise typer.Exit(1)
        return normalized

    @staticmethod
    def _resolve_secret(
        *,
        direct_value: str | None,
        env_name: str | None,
        label: str,
        fallback_env: str | None = None,
    ) -> tuple[str | None, str]:
        if direct_value and env_name:
            log.error(f"Use either direct {label} or env-var {label}, not both.")
            raise typer.Exit(1)
        if env_name:
            value = os.environ.get(env_name)
            if not value:
                log.error(f"{label} env var is not set: {env_name}")
                raise typer.Exit(1)
            return value, f"env:{env_name}"
        if direct_value:
            return direct_value, "cli"
        if fallback_env:
            value = os.environ.get(fallback_env)
            if value:
                return value, f"env:{fallback_env}"
        return None, "formalizer-config"

    @staticmethod
    def _model_supports_temperature(model: str) -> bool:
        model_name = model.lower().strip()
        return not model_name.startswith(("o1", "o3", "gpt-5"))

    @staticmethod
    def _metadata_llm_config(runtime_config: dict) -> dict:
        return {
            "provider": runtime_config.get("llm_provider"),
            "model": runtime_config.get("llm_model"),
            "base_url": runtime_config.get("llm_base_url"),
            "max_tokens": runtime_config.get("llm_max_tokens"),
            "timeout": runtime_config.get("llm_timeout"),
            "api_key_source": runtime_config.get("llm_api_key_source"),
            "supports_temperature": runtime_config.get("llm_supports_temperature"),
        }

    @staticmethod
    def _metadata_leanexplore_config(runtime_config: dict) -> dict:
        return {
            "api_key_source": runtime_config.get("leanexplore_api_key_source"),
        }

    def _metadata_physlean_dependency(self, ensure_result: dict | None) -> dict:
        if ensure_result:
            return ensure_result
        return {
            "requested": self.ensure_physlean,
            "modified": None,
            "update_passed": None,
        }

    def _metadata_physlean_build(self, build_result: dict | None) -> dict:
        if build_result:
            return build_result
        return {
            "requested": self.build_physlean,
            "passed": None,
            "target": "PhysLean",
        }

    def _metadata_preflight(self, preflight_result: dict | None) -> dict:
        if preflight_result:
            return preflight_result
        return {
            "requested": self.preflight,
            "passed": None,
            "packages": ["Mathlib", "PhysLean"],
        }

    # ── formalizer integration ────────────────────────────────────────

    def _resolve_formalizer_root(self) -> Path:
        candidates: list[Path] = []
        if self.formalizer_root:
            candidates.append(self.formalizer_root.expanduser())
        env_value = os.environ.get(FORMALIZER_ROOT_ENV)
        if env_value:
            candidates.append(Path(env_value).expanduser())
        candidates.append(BUILTIN_FORMALIZER_ROOT)

        seen: set[Path] = set()
        for candidate in candidates:
            root = candidate.resolve()
            if root in seen:
                continue
            seen.add(root)
            if (root / "Formalizer" / "main.py").is_file():
                return root

        log.error(
            "Could not find Archon's bundled physics Formalizer. Reinstall Archon, "
            "or pass --formalizer-root /path/to/formalizer-root, or set "
            f"{FORMALIZER_ROOT_ENV}."
        )
        raise typer.Exit(1)

    def _load_formalizer(self, root: Path):
        formalizer_dir = root / "Formalizer"
        if str(formalizer_dir) not in sys.path:
            sys.path.insert(0, str(formalizer_dir))

        existing_config = sys.modules.get("config")
        existing_config_file = Path(
            getattr(existing_config, "__file__", "") or "/"
        ).resolve()
        if existing_config and not existing_config_file.is_relative_to(formalizer_dir):
            del sys.modules["config"]

        spec = importlib.util.spec_from_file_location(
            "_archon_physics_formalizer_main",
            formalizer_dir / "main.py",
        )
        if spec is None or spec.loader is None:
            log.error(f"Could not load Formalizer/main.py from {formalizer_dir}")
            raise typer.Exit(1)

        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        try:
            config = sys.modules.get("config") or importlib.import_module("config")
            process_single_problem = module.process_single_problem
        except (KeyError, AttributeError):
            log.error("Physics Formalizer does not expose the expected API.")
            raise typer.Exit(1)

        return process_single_problem, config

    def _configure_formalizer(
        self,
        config,
        runtime_config: dict | None = None,
        *,
        use_multimodal: bool | None = None,
    ) -> None:
        runtime_config = runtime_config or {}
        config.CURRENT_DOMAIN = "physics"
        config.USE_MULTIMODAL = (self.image is not None) if use_multimodal is None else use_multimodal
        config.LEAN_SEARCH_PACKAGES = ["Mathlib", "PhysLean"]
        config.LEAN_SANDBOX_PATH = str(self.project_path)
        config.CONCURRENT_WORKERS = max(1, self.workers)
        config.ABLATION_NO_DECOMPOSE = not self.decompose
        if runtime_config.get("llm_api_key"):
            config.LLM_API_KEY = runtime_config["llm_api_key"]
        if runtime_config.get("llm_base_url"):
            config.LLM_BASE_URL = runtime_config["llm_base_url"]
        if runtime_config.get("llm_model"):
            config.LLM_MODEL_NAME = runtime_config["llm_model"]
        if runtime_config.get("llm_max_tokens"):
            config.LLM_MAX_TOKENS = runtime_config["llm_max_tokens"]
        if runtime_config.get("llm_timeout"):
            config.LLM_TIMEOUT = runtime_config["llm_timeout"]
        if runtime_config.get("llm_supports_temperature") is not None:
            config.SUPPORTS_TEMPERATURE = runtime_config["llm_supports_temperature"]
        if runtime_config.get("leanexplore_api_key"):
            config.LEANEXPLORE_API_KEY = runtime_config["leanexplore_api_key"]
        if runtime_config.get("llm_provider") == "anthropic":
            self._patch_anthropic_client(config, runtime_config)
        try:
            from modules.external_tools import LeanCompilerClient

            # The Formalizer binds config.LEAN_SANDBOX_PATH into this default at
            # import time. Patch after setting config so GoTSynthesizer()
            # compiles inside the Archon project passed here.
            LeanCompilerClient.__init__.__defaults__ = (str(self.project_path),)
        except Exception as exc:
            log.warn(f"Could not patch Formalizer Lean sandbox path: {exc}")

    def _patch_anthropic_client(self, config, runtime_config: dict) -> None:
        try:
            llm_modules = importlib.import_module("modules.llm_modules")
        except Exception as exc:
            log.warn(f"Could not patch Anthropic client adapter: {exc}")
            return

        api_key = runtime_config.get("llm_api_key") or getattr(config, "LLM_API_KEY", "")
        base_url = runtime_config.get("llm_base_url") or DEFAULT_ANTHROPIC_BASE_URL
        max_tokens = runtime_config.get("llm_max_tokens") or DEFAULT_ANTHROPIC_MAX_TOKENS
        timeout = runtime_config.get("llm_timeout") or DEFAULT_LLM_TIMEOUT

        def _create_anthropic_client():
            return _AnthropicOpenAICompatClient(
                api_key=api_key,
                base_url=base_url,
                max_tokens=max_tokens,
                timeout=timeout,
            )

        llm_modules._create_openai_client = _create_anthropic_client
        log.success("Patched Formalizer LLM client for Anthropic Claude.")

    # ── output ────────────────────────────────────────────────────────

    def _summarize(self, result: dict, out_path: Path, report_path: Path) -> None:
        status = result.get("status", "unknown")
        compiled = bool(result.get("compilation_passed", False))
        semantic = bool(result.get("semantic_passed", False))
        consistency = result.get("consistency_level", "N/A")

        log.phase(2, "Result")
        log.key_value({
            "Status": status,
            "Lean compiled": "yes" if compiled else "no",
            "Semantic check": "passed" if semantic else "not passed",
            "Consistency": str(consistency),
            "Lean file": str(out_path),
            "Report": str(report_path),
        })

        if not compiled:
            log.error("Generated Lean did not compile.")
            raise typer.Exit(1)
        if self.fail_on_semantic and not semantic:
            log.error("Semantic alignment failed.")
            raise typer.Exit(2)
        if semantic:
            log.success("Physics formalization generated successfully.")
        else:
            log.warn("Lean compiled, but semantic alignment did not pass.")


def physics_formalize(
    project_path: str = typer.Argument(
        ...,
        help="Archon/Lean project where the generated Lean file should be written.",
    ),
    question: Optional[str] = typer.Option(
        None, "--question", "-q", help="Natural-language physics problem.",
    ),
    question_file: Optional[Path] = typer.Option(
        None, "--question-file", help="Read the physics problem from a text file.",
    ),
    input_jsonl: Optional[Path] = typer.Option(
        None,
        "--input-jsonl",
        help=(
            "Read Formalizer-style JSONL entries for batch mode. Each line should "
            "contain question plus optional index, answer, category, and image."
        ),
    ),
    image_root: Optional[Path] = typer.Option(
        None,
        "--image-root",
        help=(
            "Batch mode image directory. Relative paths are resolved against the "
            "JSONL file directory; defaults to <input-jsonl-dir>/image."
        ),
    ),
    image: Optional[Path] = typer.Option(
        None, "--image", "-i", help="Optional diagram/image for multimodal fusion.",
    ),
    answer: str = typer.Option(
        "", "--answer", "-a", help="Optional known final answer used in the result theorem.",
    ),
    out: Optional[Path] = typer.Option(
        None, "--out", "-o", help="Output Lean path, relative to project if not absolute.",
    ),
    report_out: Optional[Path] = typer.Option(
        None, "--report-out", help="Output JSON report path, relative to project if not absolute.",
    ),
    out_dir: Optional[Path] = typer.Option(
        None,
        "--out-dir",
        help="Batch mode Lean output directory, relative to project if not absolute.",
    ),
    report_dir: Optional[Path] = typer.Option(
        None,
        "--report-dir",
        help="Batch mode report output directory, relative to project if not absolute.",
    ),
    work_dir: Optional[Path] = typer.Option(
        None, "--work-dir", help="Directory for logs/intermediate files, relative to project if not absolute.",
    ),
    index: str = typer.Option(
        "001", "--index", help="Problem id used for intermediate filenames.",
    ),
    category: str = typer.Option(
        "physics", "--category", help="Category label stored in the formalization report.",
    ),
    limit: int = typer.Option(
        -1,
        "--limit",
        help="Batch mode limit. Use -1 to process all JSONL entries.",
    ),
    formalizer_root: Optional[Path] = typer.Option(
        None,
        "--formalizer-root",
        help=(
            "Optional override for the bundled physics Formalizer root. Defaults "
            f"to Archon's packaged Formalizer, or ${FORMALIZER_ROOT_ENV} if set."
        ),
    ),
    workers: int = typer.Option(
        1, "--workers", help="Concurrent synthesis workers inside the Formalizer.",
    ),
    decompose: bool = typer.Option(
        True,
        "--decompose/--no-decompose",
        help="Enable the Formalizer conceptual decomposition/grounding stage.",
    ),
    ensure_physlean: bool = typer.Option(
        False,
        "--ensure-physlean/--no-ensure-physlean",
        help=(
            "Append a PhysLean dependency to lakefile.lean/toml when missing, "
            "then run `lake update PhysLean`."
        ),
    ),
    build_physlean: bool = typer.Option(
        False,
        "--build-physlean/--no-build-physlean",
        help="Run `lake build PhysLean` in the target project before preflight/model calls.",
    ),
    preflight: bool = typer.Option(
        False,
        "--preflight/--no-preflight",
        help=(
            "Before calling the model, compile the physics import header in "
            "the target Lean project."
        ),
    ),
    fail_on_semantic: bool = typer.Option(
        False,
        "--fail-on-semantic",
        help="Exit non-zero when semantic alignment fails even if Lean compiles.",
    ),
    dry_run: bool = typer.Option(
        False,
        "--dry-run",
        help="Resolve inputs and write a manifest without calling the LLM/Formalizer.",
    ),
    update_progress: bool = typer.Option(
        False,
        "--update-progress",
        help=(
            "After a successful run, set .archon/PROGRESS.md to prover stage "
            "with physics prover objectives, blueprint chapters, and protected "
            "generated signatures."
        ),
    ),
    with_rethlas_blueprint: bool = typer.Option(
        False,
        "--with-rethlas-blueprint",
        help=(
            "When writing Archon proof scaffolding, ask an optional Rethlas-style "
            "natural-language proof agent for a physics proof sketch."
        ),
    ),
    rethlas_command: Optional[str] = typer.Option(
        None,
        "--rethlas-command",
        help=(
            "Command for the optional Rethlas blueprint agent. It receives JSON "
            "on stdin and should write a natural-language proof sketch to stdout. "
            "Defaults to $RETHLAS_COMMAND or `rethlas` on PATH."
        ),
    ),
    rethlas_timeout: int = typer.Option(
        180,
        "--rethlas-timeout",
        help="Timeout in seconds for the optional Rethlas blueprint command.",
    ),
    llm_api_key: Optional[str] = typer.Option(
        None,
        "--llm-api-key",
        help=(
            "Runtime LLM API key for the Formalizer. Prefer --llm-api-key-env; "
            "the value is never written to metadata."
        ),
    ),
    llm_api_key_env: Optional[str] = typer.Option(
        None,
        "--llm-api-key-env",
        help="Name of an environment variable containing the runtime LLM API key.",
    ),
    llm_provider: str = typer.Option(
        "openai-compatible",
        "--llm-provider",
        help=(
            "LLM transport provider: openai-compatible or anthropic. "
            "Use anthropic for native Claude API."
        ),
    ),
    llm_base_url: Optional[str] = typer.Option(
        None,
        "--llm-base-url",
        help=(
            "Runtime LLM base URL. For openai-compatible this is the chat "
            "completion gateway; for anthropic it defaults to the Anthropic API."
        ),
    ),
    llm_model: Optional[str] = typer.Option(
        None,
        "--llm-model",
        help="Runtime model name passed to the bundled physics Formalizer.",
    ),
    llm_max_tokens: Optional[int] = typer.Option(
        None,
        "--llm-max-tokens",
        help=(
            "Maximum output tokens for providers that require it. Native "
            "Anthropic defaults to 8192."
        ),
    ),
    llm_timeout: int = typer.Option(
        DEFAULT_LLM_TIMEOUT,
        "--llm-timeout",
        help="Timeout in seconds for each Formalizer LLM API request.",
    ),
    llm_no_temperature: bool = typer.Option(
        False,
        "--llm-no-temperature",
        help=(
            "Force the Formalizer to omit temperature. If not set, known "
            "reasoning models such as gpt-5/o1/o3 are detected automatically."
        ),
    ),
    leanexplore_api_key: Optional[str] = typer.Option(
        None,
        "--leanexplore-api-key",
        help=(
            "Runtime LeanExplore API key. Prefer --leanexplore-api-key-env; "
            "the value is never written to metadata."
        ),
    ),
    leanexplore_api_key_env: Optional[str] = typer.Option(
        None,
        "--leanexplore-api-key-env",
        help="Name of an environment variable containing the LeanExplore API key.",
    ),
) -> None:
    """Generate PhysLean/Lean `by sorry` stubs from a physics text/image problem."""
    PhysicsFormalizeCommand(
        project_path,
        question=question,
        question_file=question_file,
        input_jsonl=input_jsonl,
        image_root=image_root,
        image=image,
        answer=answer,
        out=out,
        report_out=report_out,
        out_dir=out_dir,
        report_dir=report_dir,
        work_dir=work_dir,
        index=index,
        category=category,
        limit=limit,
        formalizer_root=formalizer_root,
        workers=workers,
        decompose=decompose,
        ensure_physlean=ensure_physlean,
        build_physlean=build_physlean,
        preflight=preflight,
        fail_on_semantic=fail_on_semantic,
        dry_run=dry_run,
        update_progress=update_progress,
        with_rethlas_blueprint=with_rethlas_blueprint,
        rethlas_command=rethlas_command,
        rethlas_timeout=rethlas_timeout,
        llm_api_key=llm_api_key,
        llm_api_key_env=llm_api_key_env,
        llm_provider=llm_provider,
        llm_base_url=llm_base_url,
        llm_model=llm_model,
        llm_max_tokens=llm_max_tokens,
        llm_timeout=llm_timeout,
        llm_no_temperature=llm_no_temperature,
        leanexplore_api_key=leanexplore_api_key,
        leanexplore_api_key_env=leanexplore_api_key_env,
    ).run()
