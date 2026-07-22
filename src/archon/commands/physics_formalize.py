"""`archon physics-formalize` - prepare physics tasks for Archon's loop.

This command is intentionally not an Auto-Formalizer host. It turns a
text/image physics problem, JSONL batch, or multi-part problem set into
Archon-native physics blueprint chapters and autoformalize-stage objectives.
The actual Lean-by-sorry formalization is performed later by `archon loop`
using the `physics-formalize` prover mode; proof filling then uses the
`physics` prover mode.
"""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Optional

import typer

from archon import log
from archon.commands.init.utils import data_path
from archon.commands.tooling.blueprint import BlueprintChapter, BlueprintStructure


PHYSICS_FORMALIZE_MODE = "physics-formalize"
PHYSICS_PROVER_MODE = "physics"
PHYSICS_REVIEWER = "physics-reviewer"
SUPPORTED_DATASET_FORMATS = {"auto", "native", "phyx"}

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


class PhysicsFormalizeCommand:
    """Prepare physics blueprint/progress entries for the Archon loop."""

    def __init__(
        self,
        project_path: str,
        *,
        question: str | None = None,
        question_file: Path | None = None,
        input_jsonl: Path | None = None,
        problem_id: str | None = None,
        as_problem_set: bool = False,
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
        dataset_format: str = "auto",
        ensure_physlean: bool = False,
        build_physlean: bool = False,
        preflight: bool = False,
        dry_run: bool = False,
        update_progress: bool = False,
        with_rethlas_blueprint: bool = False,
        rethlas_command: str | None = None,
        rethlas_timeout: int = 180,
    ) -> None:
        self.project_path = Path(project_path).resolve()
        self.question = question
        self.question_file = question_file
        self.input_jsonl = input_jsonl
        self.problem_id = problem_id
        self.as_problem_set = as_problem_set
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
        self.dataset_format = dataset_format.lower().strip()
        self.ensure_physlean = ensure_physlean
        self.build_physlean = build_physlean
        self.preflight = preflight
        self.dry_run = dry_run
        self.update_progress = update_progress
        self.with_rethlas_blueprint = with_rethlas_blueprint
        self.rethlas_command = rethlas_command
        self.rethlas_timeout = rethlas_timeout

    def run(self) -> None:
        log.header("archon physics-formalize")
        self._validate_project()
        if self.input_jsonl:
            self._validate_batch_mode()
        else:
            self._validate_single_mode()

        work_dir = self._resolve_work_dir()
        ensure_result = self._ensure_physlean_dependency() if self.ensure_physlean else None
        build_result = self._run_physlean_build() if self.build_physlean else None
        preflight_result = self._run_lean_preflight(work_dir) if self.preflight else None

        if self.input_jsonl:
            if self.as_problem_set:
                self._prepare_problem_set(
                    work_dir=work_dir,
                    ensure_result=ensure_result,
                    build_result=build_result,
                    preflight_result=preflight_result,
                )
            else:
                self._prepare_batch(
                    work_dir=work_dir,
                    ensure_result=ensure_result,
                    build_result=build_result,
                    preflight_result=preflight_result,
                )
            return

        question = self._read_question()
        image_path = self._resolve_image()
        entry = self._build_entry(question, image_path)
        out_path = self._resolve_out_path()
        report_path = self._resolve_report_path(out_path)

        log.key_value({
            "Project": str(self.project_path),
            "Output Lean target": str(out_path),
            "Source report": str(report_path),
            "Work dir": str(work_dir),
            "Image": str(image_path) if image_path else "none",
            "Mode": "dry run" if self.dry_run else "prepare",
            "Next stage": "autoformalize",
            "Update PROGRESS.md": "yes" if self.update_progress else "no",
        })

        if self.dry_run:
            manifest_path = self._write_single_manifest(
                work_dir=work_dir,
                out_path=out_path,
                report_path=report_path,
                entry=entry,
                dry_run=True,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
            )
            self._write_single_metadata(
                work_dir=work_dir,
                out_path=out_path,
                report_path=report_path,
                entry=entry,
                dry_run=True,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
                record=None,
            )
            if self.update_progress:
                log.warn("--update-progress is ignored during --dry-run.")
            log.success(f"Dry run complete. Manifest written to {manifest_path}")
            return

        record = self._prepare_one(
            entry=entry,
            out_path=out_path,
            report_path=report_path,
            work_dir=work_dir,
        )
        self._write_single_manifest(
            work_dir=work_dir,
            out_path=out_path,
            report_path=report_path,
            entry=entry,
            dry_run=False,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
        )
        self._write_single_metadata(
            work_dir=work_dir,
            out_path=out_path,
            report_path=report_path,
            entry=entry,
            dry_run=False,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
            record=record,
        )
        if self.update_progress:
            self._update_progress_records([record])
        log.success("Physics formalization task prepared for archon loop.")

    # setup and input -------------------------------------------------

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
                "No lakefile.lean/toml found. Loop formalization will need a "
                "working Lean project before it can compile generated files."
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
        if self.dataset_format not in SUPPORTED_DATASET_FORMATS:
            supported = ", ".join(sorted(SUPPORTED_DATASET_FORMATS))
            log.error(f"--dataset-format must be one of: {supported}.")
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
                raw = line.strip()
                if not raw:
                    continue
                try:
                    entry = json.loads(raw)
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
                normalized = self._normalize_dataset_entry(entry, line_no=line_no)
                normalized["index"] = str(normalized.get("index") or f"{line_no:03d}")
                normalized["question"] = str(normalized.get("question", "")).strip()
                normalized["answer"] = str(normalized.get("answer", ""))
                normalized["category"] = str(normalized.get("category", self.category))
                normalized["image"] = self._normalize_entry_image(normalized)
                entries.append(normalized)
                if not self.as_problem_set and self.limit > 0 and len(entries) >= self.limit:
                    break

        if not entries:
            log.error(f"Input JSONL contains no usable physics problems: {path}")
            raise typer.Exit(1)
        return path, entries

    def _normalize_dataset_entry(self, entry: dict, *, line_no: int) -> dict:
        dataset_format = self.dataset_format
        if dataset_format == "auto":
            phyx_markers = {
                "description",
                "question_description",
                "question_simply",
                "question_description_simplified",
                "image_caption",
                "reasoning_type",
                "subfield",
            }
            dataset_format = "phyx" if phyx_markers.intersection(entry) else "native"
        if dataset_format == "native":
            return dict(entry)
        return self._normalize_phyx_entry(entry, line_no=line_no)

    @classmethod
    def _normalize_phyx_entry(cls, entry: dict, *, line_no: int) -> dict:
        """Map an official Cloudriver/PhyX row to Archon's physics contract."""
        normalized = dict(entry)
        source_index = str(entry.get("index") or entry.get("id") or line_no)
        description = str(
            entry.get("description")
            or entry.get("question_description")
            or entry.get("question_simply")
            or entry.get("question_description_simplified")
            or ""
        ).strip()
        question = str(entry.get("question") or "").strip()
        caption = str(entry.get("image_caption") or "").strip()
        options = cls._parse_phyx_options(entry.get("options"))
        answer_label = str(entry.get("answer") or "").strip()
        answer_text = options.get(answer_label.upper(), "")

        sections: list[str] = []
        if description and description != question:
            sections.extend(["## Physical scenario", description])
        sections.extend(["## Question", question])
        if options:
            sections.extend(
                ["## Answer choices"]
                + [f"- {label}: {value}" for label, value in options.items()]
            )
        if caption:
            sections.extend([
                "## Figure caption (auxiliary; use the image as primary evidence)",
                caption,
            ])
        subfield = str(entry.get("subfield") or "").strip()
        reasoning = entry.get("reasoning_type")
        if isinstance(reasoning, list):
            reasoning_text = ", ".join(str(item) for item in reasoning)
        else:
            reasoning_text = str(reasoning or "").strip()
        metadata = [part for part in (subfield, reasoning_text) if part]
        if metadata:
            sections.extend(["## Dataset metadata", "; ".join(metadata)])

        normalized.update(
            {
                "index": f"phyx_{source_index}",
                "source_index": source_index,
                "dataset": "Cloudriver/PhyX",
                "dataset_format": "phyx",
                "question": "\n\n".join(part for part in sections if part).strip(),
                "answer": (
                    f"{answer_label.upper()}: {answer_text}"
                    if answer_text
                    else answer_label
                ),
                "answer_label": answer_label.upper(),
                "answer_text": answer_text,
                "options_parsed": options,
            }
        )
        return normalized

    @staticmethod
    def _parse_phyx_options(raw_options: object) -> dict[str, str]:
        if isinstance(raw_options, (list, tuple)):
            return {
                chr(ord("A") + index): str(value).strip()
                for index, value in enumerate(raw_options)
            }
        if isinstance(raw_options, dict):
            return {
                str(label).strip().upper(): str(value).strip()
                for label, value in raw_options.items()
            }
        text = str(raw_options or "").strip()
        matches = list(re.finditer(r"(?:^|,)\s*([A-Za-z])\s*:\s*", text))
        parsed: dict[str, str] = {}
        for index, match in enumerate(matches):
            end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
            value = text[match.end():end].strip().strip(",").strip()
            if len(value) >= 2 and value[0] == value[-1] and value[0] in {chr(34), chr(39)}:
                value = value[1:-1]
            parsed[match.group(1).upper()] = value
        return parsed

    @staticmethod
    def _normalize_entry_image(entry: dict) -> str | None:
        if entry.get("image"):
            return str(entry["image"])
        images = entry.get("images")
        if isinstance(images, list) and images:
            first = images[0]
            if isinstance(first, dict) and first.get("path"):
                return str(first["path"])
            if isinstance(first, str):
                return first
        return None

    def _build_problem_set_entries(
        self, raw_entries: list[dict]
    ) -> tuple[str, list[dict], str]:
        groups: dict[str, list[dict]] = {}
        for entry in raw_entries:
            pid = str(entry.get("problem_id") or "").strip()
            if not pid:
                log.error("Problem-set mode requires every JSONL entry to include `problem_id`.")
                raise typer.Exit(1)
            groups.setdefault(pid, []).append(entry)

        if self.problem_id:
            problem_id = self.problem_id
            selected = groups.get(problem_id, [])
            if not selected:
                log.error(f"No entries found for --problem-id {problem_id}.")
                raise typer.Exit(1)
        elif len(groups) == 1:
            problem_id, selected = next(iter(groups.items()))
        else:
            log.error(
                "Problem-set mode needs --problem-id when the JSONL contains "
                f"multiple problem_id values: {', '.join(sorted(groups))}"
            )
            raise typer.Exit(1)

        if self.limit > 0:
            selected = selected[: self.limit]
        if not selected:
            log.error(f"No usable subquestions selected for problem set {problem_id}.")
            raise typer.Exit(1)

        shared_context = self._derive_shared_context(selected)
        enriched = [
            self._problem_set_entry(entry, shared_context=shared_context)
            for entry in selected
        ]
        return problem_id, enriched, shared_context

    @staticmethod
    def _derive_shared_context(entries: list[dict]) -> str:
        for entry in entries:
            context = str(entry.get("context") or "").strip()
            if context:
                return context
        return str(entries[0].get("question") or "").strip()

    def _problem_set_entry(self, entry: dict, *, shared_context: str) -> dict:
        enriched = dict(entry)
        part_id = str(enriched.get("part_id") or enriched.get("index") or "").strip()
        current_question = str(
            enriched.get("current_question") or enriched.get("question") or ""
        ).strip()
        local_context = str(enriched.get("context") or "").strip()
        previous_parts = enriched.get("previous_parts") or []
        if not isinstance(previous_parts, list):
            previous_parts = []
        enriched["part_id"] = part_id
        enriched["shared_context"] = shared_context
        enriched["local_context"] = local_context
        enriched["current_question"] = current_question
        enriched["previous_parts"] = previous_parts
        enriched["question"] = self._assemble_problem_set_question(
            part_id=part_id,
            shared_context=shared_context,
            local_context=local_context,
            current_question=current_question,
            previous_parts=previous_parts,
        )
        return enriched

    @staticmethod
    def _assemble_problem_set_question(
        *,
        part_id: str,
        shared_context: str,
        local_context: str,
        current_question: str,
        previous_parts: list,
    ) -> str:
        sections = [
            "## Shared problem context",
            shared_context,
            "",
            f"## Current subquestion {part_id}".rstrip(),
            current_question,
        ]
        if local_context:
            sections.extend(["", "## Local context for this subquestion", local_context])
        if previous_parts:
            sections.extend(["", "## Reusable previous-part conclusions"])
            for previous in previous_parts:
                if not isinstance(previous, dict):
                    continue
                label = previous.get("part_id") or previous.get("source_id") or "previous part"
                sections.append(f"- Source {label}:")
                question = str(previous.get("question") or "").strip()
                if question:
                    sections.append(f"  Previous question: {question}")
                conclusions = previous.get("reusable_conclusions") or []
                if isinstance(conclusions, list) and conclusions:
                    for conclusion in conclusions:
                        sections.append(f"  Reusable conclusion: {conclusion}")
                else:
                    answer = str(previous.get("answer") or "").strip()
                    if answer:
                        sections.append(f"  Reusable answer: {answer}")
                policy = str(previous.get("dependency_policy") or "").strip()
                if policy:
                    sections.append(f"  Dependency policy: {policy}")
        return "\n".join(sections).strip() + "\n"

    # path resolution -------------------------------------------------

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
            is_phyx = any(entry.get("dataset_format") == "phyx" for entry in entries)
            root = input_path.parent / ("test_image" if is_phyx else "image")
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
            work_dir = self.project_path / ".archon" / "physics-formalize" / f"{prefix}_{stamp}"
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
        return out_path.with_suffix(".source.json")

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
        return report_dir / f"problem_{index}.source.json"

    def _problem_set_out_path(self, out_dir: Path, entry: dict) -> Path:
        part = str(entry.get("part_id") or entry.get("index") or "part")
        return out_dir / f"{self._safe_path_component(part)}.lean"

    def _problem_set_report_path(self, report_dir: Path, entry: dict) -> Path:
        part = str(entry.get("part_id") or entry.get("index") or "part")
        return report_dir / f"{self._safe_path_component(part)}.source.json"

    @staticmethod
    def _safe_path_component(value: str) -> str:
        safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("_")
        safe = safe.replace(".", "_")
        return safe or "item"

    def _build_entry(self, question: str, image_path: Path | None) -> dict:
        return {
            "index": self.index,
            "question": question,
            "answer": self.answer,
            "category": self.category,
            "image": image_path.name if image_path else None,
            "image_path": str(image_path) if image_path else None,
        }

    def _entry_image_path(self, entry: dict, image_root: Path | None) -> str | None:
        image = entry.get("image")
        if not image:
            return None
        path = Path(str(image))
        if not path.is_absolute() and image_root is not None:
            path = image_root / path
        return str(path.resolve())

    # batch/problem set -----------------------------------------------

    def _prepare_batch(
        self,
        *,
        work_dir: Path,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
    ) -> None:
        input_path, entries = self._read_input_jsonl()
        image_root = self._resolve_batch_image_root(input_path, entries)
        out_dir = self._resolve_out_dir()
        report_dir = self._resolve_report_dir(out_dir)

        log.key_value({
            "Project": str(self.project_path),
            "Input JSONL": str(input_path),
            "Problems": str(len(entries)),
            "Output dir": str(out_dir),
            "Report dir": str(report_dir),
            "Mode": "dry run" if self.dry_run else "prepare",
            "Next stage": "autoformalize",
        })

        if self.dry_run:
            manifest_path = self._write_batch_manifest(
                work_dir=work_dir,
                input_path=input_path,
                entries=entries,
                image_root=image_root,
                out_dir=out_dir,
                report_dir=report_dir,
                records=[],
                dry_run=True,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
            )
            self._write_batch_metadata(
                work_dir=work_dir,
                input_path=input_path,
                entries=entries,
                image_root=image_root,
                out_dir=out_dir,
                report_dir=report_dir,
                records=[],
                dry_run=True,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
            )
            if self.update_progress:
                log.warn("--update-progress is ignored during --dry-run.")
            log.success(f"Dry run complete. Batch manifest written to {manifest_path}")
            return

        records: list[dict] = []
        for entry in entries:
            idx = str(entry["index"])
            entry = dict(entry)
            entry["image_path"] = self._entry_image_path(entry, image_root)
            records.append(
                self._prepare_one(
                    entry=entry,
                    out_path=self._batch_out_path(out_dir, idx),
                    report_path=self._batch_report_path(report_dir, idx),
                    work_dir=work_dir,
                )
            )
        self._write_batch_manifest(
            work_dir=work_dir,
            input_path=input_path,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            records=records,
            dry_run=False,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
        )
        self._write_batch_metadata(
            work_dir=work_dir,
            input_path=input_path,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            records=records,
            dry_run=False,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
        )
        if self.update_progress:
            self._update_progress_records(records)
        log.success(f"Prepared {len(records)} physics formalization target(s) for archon loop.")

    def _prepare_problem_set(
        self,
        *,
        work_dir: Path,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
    ) -> None:
        input_path, raw_entries = self._read_input_jsonl()
        problem_id, entries, shared_context = self._build_problem_set_entries(raw_entries)
        image_root = self._resolve_batch_image_root(input_path, entries)
        out_dir = self._resolve_out_dir() / self._safe_path_component(problem_id)
        report_dir = self._resolve_report_dir(self._resolve_out_dir()) / self._safe_path_component(problem_id)

        log.key_value({
            "Project": str(self.project_path),
            "Input JSONL": str(input_path),
            "Problem set": problem_id,
            "Subquestions": str(len(entries)),
            "Output dir": str(out_dir),
            "Report dir": str(report_dir),
            "Mode": "dry run" if self.dry_run else "prepare",
            "Next stage": "autoformalize",
        })

        if self.dry_run:
            manifest_path = self._write_problem_set_manifest(
                work_dir=work_dir,
                input_path=input_path,
                problem_id=problem_id,
                shared_context=shared_context,
                entries=entries,
                image_root=image_root,
                out_dir=out_dir,
                report_dir=report_dir,
                records=[],
                dry_run=True,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
            )
            self._write_problem_set_metadata(
                work_dir=work_dir,
                input_path=input_path,
                problem_id=problem_id,
                shared_context=shared_context,
                entries=entries,
                image_root=image_root,
                out_dir=out_dir,
                report_dir=report_dir,
                records=[],
                dry_run=True,
                ensure_result=ensure_result,
                build_result=build_result,
                preflight_result=preflight_result,
            )
            if self.update_progress:
                log.warn("--update-progress is ignored during --dry-run.")
            log.success(f"Dry run complete. Problem-set manifest written to {manifest_path}")
            return

        records: list[dict] = []
        for entry in entries:
            entry = dict(entry)
            entry["image_path"] = self._entry_image_path(entry, image_root)
            records.append(
                self._prepare_one(
                    entry=entry,
                    out_path=self._problem_set_out_path(out_dir, entry),
                    report_path=self._problem_set_report_path(report_dir, entry),
                    work_dir=work_dir,
                )
            )

        self._write_problem_set_manifest(
            work_dir=work_dir,
            input_path=input_path,
            problem_id=problem_id,
            shared_context=shared_context,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            records=records,
            dry_run=False,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
        )
        self._write_problem_set_metadata(
            work_dir=work_dir,
            input_path=input_path,
            problem_id=problem_id,
            shared_context=shared_context,
            entries=entries,
            image_root=image_root,
            out_dir=out_dir,
            report_dir=report_dir,
            records=records,
            dry_run=False,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
        )
        if self.update_progress:
            self._update_progress_records(records)
        log.success(f"Prepared {len(records)} physics subquestion target(s) for archon loop.")

    # preparation artifacts ------------------------------------------

    def _prepare_one(
        self,
        *,
        entry: dict,
        out_path: Path,
        report_path: Path,
        work_dir: Path,
    ) -> dict:
        out_path = out_path.resolve()
        report_path = report_path.resolve()
        rel_lean = self._rel_to_project(out_path)
        rel_report = self._rel_to_project(report_path)
        report = self._source_report(entry, out_path, report_path)
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(
            json.dumps(report, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        chapter_path = self._write_physics_blueprint_chapter(
            entry=entry,
            out_path=out_path,
            report_path=report_path,
        )
        record = {
            "index": str(entry.get("index", "")),
            "problem_id": entry.get("problem_id"),
            "part_id": entry.get("part_id"),
            "output_lean": str(out_path),
            "output_report": str(report_path),
            "source_report": str(report_path),
            "blueprint_chapter": str(chapter_path),
            "rel_lean": rel_lean,
            "rel_report": rel_report,
            "rel_chapter": self._rel_to_project(chapter_path),
            "status": "prepared",
            "next_stage": "autoformalize",
        }
        summary_path = work_dir / "summary.jsonl"
        with summary_path.open("a", encoding="utf-8") as f:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
        return record

    def _source_report(self, entry: dict, out_path: Path, report_path: Path) -> dict:
        return {
            "schema_version": 1,
            "command": "physics-formalize",
            "status": "prepared",
            "next_stage": "autoformalize",
            "prover_mode": PHYSICS_FORMALIZE_MODE,
            "proof_mode": PHYSICS_PROVER_MODE,
            "project_path": str(self.project_path),
            "output_lean": str(out_path),
            "source_report": str(report_path),
            "domain": "physics",
            "lean_search_packages": ["Mathlib", "Physlib"],
            "entry": entry,
            "problem_id": entry.get("problem_id"),
            "part_id": entry.get("part_id"),
            "previous_parts": entry.get("previous_parts", []),
        }

    def _write_physics_blueprint_chapter(
        self,
        *,
        entry: dict,
        out_path: Path,
        report_path: Path,
    ) -> Path:
        self._ensure_loop_assets()
        rel_lean = self._rel_to_project(out_path)
        rel_report = self._rel_to_project(report_path)
        structure = BlueprintStructure(self.project_path)
        structure.blueprint_src.mkdir(parents=True, exist_ok=True)
        if not structure.content_tex.exists():
            structure.content_tex.write_text("% Archon physics blueprint.\n", encoding="utf-8")

        chapter = BlueprintChapter(self.project_path, rel_lean)
        generated = self._physics_blueprint_block(
            entry=entry,
            rel_lean=rel_lean,
            rel_report=rel_report,
            slug=chapter.slug,
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
        return chapter.path

    def _physics_blueprint_block(
        self,
        *,
        entry: dict,
        rel_lean: str,
        rel_report: str,
        slug: str,
        include_chapter: bool,
    ) -> str:
        index = str(entry.get("index") or "physics")
        answer = str(entry.get("answer") or "")
        question = str(entry.get("question") or "")
        title = self._latex_escape(f"Physics problem {index}")
        lines = [
            "% --- Archon physics formalization source begin ---",
            "% archon:physics",
            f"% archon:covers {rel_lean}",
            f"% archon:source-report {rel_report}",
        ]
        if entry.get("problem_id"):
            lines.append(f"% archon:problem-id {entry['problem_id']}")
        if entry.get("part_id"):
            lines.append(f"% archon:part-id {entry['part_id']}")
        for previous in entry.get("previous_parts", []) or []:
            if not isinstance(previous, dict):
                continue
            source_id = str(previous.get("source_id") or "").strip()
            if not source_id:
                continue
            lines.append(f"% archon:previous-part {source_id}")
            policy = str(previous.get("dependency_policy") or "natural_language_prerequisite_only").strip()
            lines.append(f"% archon:previous-part-policy {policy.split(';', 1)[0].strip()}")

        if include_chapter:
            lines.extend(["", f"\\chapter{{{title}}}", f"\\label{{ch:{slug}}}"])
        else:
            lines.extend(["", f"\\section{{{title}}}"])

        lines.extend([
            "",
            "\\paragraph{Problem source.}",
            self._latex_escape(question),
        ])
        if entry.get("shared_context"):
            lines.extend([
                "",
                "\\paragraph{Shared problem context.}",
                self._latex_escape(str(entry.get("shared_context") or "")),
            ])
        if entry.get("current_question"):
            lines.extend([
                "",
                "\\paragraph{Current subquestion.}",
                self._latex_escape(str(entry.get("current_question") or "")),
            ])
        if answer:
            lines.extend(["", "\\paragraph{Recorded answer/context.}", self._latex_escape(answer)])
        if entry.get("image_path"):
            lines.extend(["", "\\paragraph{Figure/image path.}", self._latex_escape(str(entry["image_path"]))])
        if entry.get("previous_parts"):
            lines.extend(["", "\\paragraph{Reusable previous-part conclusions.}"])
            lines.extend(self._previous_parts_latex(entry.get("previous_parts") or []))

        lines.extend([
            "",
            "\\paragraph{Formalization target.}",
            "create a compiling Lean file with sorry bodies at "
            f"`{self._latex_escape(rel_lean)}`. The Lean declarations must preserve "
            "the physical quantities, dimensions or dimensional roles, figure labels, "
            "governing-law hypotheses, and final relation expressed by this problem.",
            "Use Mathlib/Physlib names found through LeanExplore where available. "
            "If a physics API is missing, introduce faithful local abstractions rather "
            "than scalar placeholder aliases.",
            "",
            "\\begin{theorem}[Physics formalization target]",
            f"\\label{{thm:physics:{self._safe_label(index)}:target}}",
            "The assigned autoformalize agent should translate this physics problem "
            "into Lean declarations in the covered file, with theorem and lemma proof "
            "bodies written as `by sorry`.",
            "\\end{theorem}",
            "\\begin{proof}",
            "This is an autoformalization task, not a proof task. Produce statements "
            "that can later be proved by the physics prover without weakening the "
            "physical model.",
            "\\end{proof}",
        ])

        rethlas = self._run_rethlas_blueprint_agent(entry)
        if rethlas is not None:
            lines.extend(["", "\\paragraph{Optional natural-language proof route.}"])
            if rethlas.get("status") == "success":
                lines.append(self._latex_escape(str(rethlas.get("sketch") or "")))
            else:
                lines.append(self._latex_escape(str(rethlas.get("message") or "Rethlas unavailable.")))

        lines.append("% --- Archon physics formalization source end ---")
        return "\n".join(lines).rstrip() + "\n"

    def _previous_parts_latex(self, previous_parts: list) -> list[str]:
        lines = ["\\begin{itemize}"]
        for previous in previous_parts:
            if not isinstance(previous, dict):
                continue
            label = previous.get("part_id") or previous.get("source_id") or "previous part"
            chunks = [f"Source {label}."]
            question = str(previous.get("question") or "").strip()
            if question:
                chunks.append(f"Question: {question}")
            conclusions = previous.get("reusable_conclusions") or []
            if isinstance(conclusions, list) and conclusions:
                chunks.append("Reusable conclusions: " + "; ".join(map(str, conclusions)))
            elif previous.get("answer"):
                chunks.append("Reusable answer: " + str(previous["answer"]))
            policy = str(previous.get("dependency_policy") or "").strip()
            if policy:
                chunks.append("Policy: " + policy)
            lines.append(f"\\item {self._latex_escape(' '.join(chunks))}")
        lines.append("\\end{itemize}")
        return lines

    def _run_rethlas_blueprint_agent(self, entry: dict) -> dict | None:
        if not self.with_rethlas_blueprint:
            return None
        command = self.rethlas_command or os.environ.get("RETHLAS_COMMAND")
        if not command:
            found = shutil.which("rethlas")
            command = found if found else None
        if not command:
            return {
                "status": "unavailable",
                "message": "Rethlas command not configured.",
                "sketch": "",
            }
        payload = {
            "index": entry.get("index"),
            "question": entry.get("question"),
            "answer": entry.get("answer"),
            "previous_parts": entry.get("previous_parts", []),
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
            return {"status": "unavailable", "message": f"Rethlas command not found: {command}", "sketch": ""}
        except subprocess.TimeoutExpired:
            return {"status": "timeout", "message": f"Rethlas timed out after {self.rethlas_timeout} seconds.", "sketch": ""}
        except OSError as exc:
            return {"status": "error", "message": f"Rethlas failed to start: {exc}", "sketch": ""}
        stdout = (proc.stdout or "").strip()
        stderr = (proc.stderr or "").strip()
        if proc.returncode != 0:
            return {
                "status": "error",
                "message": f"Rethlas exited with code {proc.returncode}: {(stderr or stdout)[:500]}",
                "sketch": stdout,
            }
        return {"status": "success", "message": "Rethlas proof sketch generated.", "sketch": stdout}

    @staticmethod
    def _replace_or_append_generated_block(existing: str, generated: str) -> str:
        begin = "% --- Archon physics formalization source begin ---"
        end = "% --- Archon physics formalization source end ---"
        pattern = rf"{re.escape(begin)}.*?{re.escape(end)}"
        new_text, count = re.subn(pattern, generated.strip(), existing, count=1, flags=re.DOTALL)
        if count:
            return new_text.rstrip() + "\n"
        return existing.rstrip() + "\n\n" + generated

    def _ensure_loop_assets(self) -> None:
        self._copy_archon_asset("prover-modes", f"{PHYSICS_FORMALIZE_MODE}.md")
        self._copy_archon_asset("prover-modes", f"{PHYSICS_PROVER_MODE}.md")
        self._copy_archon_asset("subagents", f"{PHYSICS_REVIEWER}.md")

    def _copy_archon_asset(self, folder: str, filename: str) -> None:
        src = data_path(f"{folder}/{filename}")
        dst = self.project_path / ".archon" / folder / filename
        if not src.is_file():
            raise RuntimeError(f"Bundled Archon asset missing: {src}")
        dst.parent.mkdir(parents=True, exist_ok=True)
        if not dst.exists() or src.read_bytes() != dst.read_bytes():
            shutil.copy2(src, dst)

    # metadata --------------------------------------------------------

    def _write_single_manifest(
        self,
        *,
        work_dir: Path,
        out_path: Path,
        report_path: Path,
        entry: dict,
        dry_run: bool,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
    ) -> Path:
        manifest = self._single_metadata_payload(
            work_dir=work_dir,
            out_path=out_path,
            report_path=report_path,
            entry=entry,
            dry_run=dry_run,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
            record=None,
        )
        manifest_path = work_dir / f"problem_{self.index}_manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8")
        return manifest_path

    def _write_single_metadata(
        self,
        *,
        work_dir: Path,
        out_path: Path,
        report_path: Path,
        entry: dict,
        dry_run: bool,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
        record: dict | None,
    ) -> Path:
        state_dir = self.project_path / ".archon" / "physics-formalize"
        state_dir.mkdir(parents=True, exist_ok=True)
        metadata = self._single_metadata_payload(
            work_dir=work_dir,
            out_path=out_path,
            report_path=report_path,
            entry=entry,
            dry_run=dry_run,
            ensure_result=ensure_result,
            build_result=build_result,
            preflight_result=preflight_result,
            record=record,
        )
        run_path = state_dir / f"problem_{self.index}.json"
        payload = json.dumps(metadata, indent=2, ensure_ascii=False)
        run_path.write_text(payload, encoding="utf-8")
        (state_dir / "latest.json").write_text(payload, encoding="utf-8")
        return run_path

    def _single_metadata_payload(
        self,
        *,
        work_dir: Path,
        out_path: Path,
        report_path: Path,
        entry: dict,
        dry_run: bool,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
        record: dict | None,
    ) -> dict:
        return {
            "schema_version": 2,
            "command": "physics-formalize",
            "mode": "single",
            "dry_run": dry_run,
            "project_path": str(self.project_path),
            "work_dir": str(work_dir),
            "output_lean": str(out_path),
            "source_report": str(report_path),
            "output_report": str(report_path),
            "domain": "physics",
            "next_stage": "autoformalize",
            "prover_mode": PHYSICS_FORMALIZE_MODE,
            "proof_mode": PHYSICS_PROVER_MODE,
            "lean_search_packages": ["Mathlib", "Physlib"],
            "physlean_dependency": self._metadata_physlean_dependency(ensure_result),
            "physlean_build": self._metadata_physlean_build(build_result),
            "preflight": self._metadata_preflight(preflight_result),
            "entry": entry,
            "record": record,
            "result": {
                "status": "prepared" if not dry_run else "dry-run",
                "next_stage": "autoformalize",
                "prepared": 0 if dry_run else 1,
            },
        }

    def _write_batch_manifest(self, **kwargs) -> Path:
        manifest = self._batch_metadata_payload(**kwargs)
        manifest_path = kwargs["work_dir"] / "batch_manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8")
        return manifest_path

    def _write_batch_metadata(self, **kwargs) -> Path:
        input_path = kwargs["input_path"]
        state_dir = self.project_path / ".archon" / "physics-formalize"
        state_dir.mkdir(parents=True, exist_ok=True)
        metadata = self._batch_metadata_payload(**kwargs)
        safe_stem = re.sub(r"[^A-Za-z0-9_.-]+", "_", input_path.stem).strip("_") or "batch"
        run_path = state_dir / f"batch_{safe_stem}.json"
        payload = json.dumps(metadata, indent=2, ensure_ascii=False)
        run_path.write_text(payload, encoding="utf-8")
        (state_dir / "latest.json").write_text(payload, encoding="utf-8")
        return run_path

    def _write_problem_set_manifest(self, **kwargs) -> Path:
        manifest = self._problem_set_metadata_payload(**kwargs)
        manifest_path = kwargs["work_dir"] / "problem_set_manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8")
        return manifest_path

    def _write_problem_set_metadata(self, **kwargs) -> Path:
        problem_id = kwargs["problem_id"]
        state_dir = self.project_path / ".archon" / "physics-formalize"
        state_dir.mkdir(parents=True, exist_ok=True)
        metadata = self._problem_set_metadata_payload(**kwargs)
        run_path = state_dir / f"problem_set_{self._safe_path_component(problem_id)}.json"
        payload = json.dumps(metadata, indent=2, ensure_ascii=False)
        run_path.write_text(payload, encoding="utf-8")
        (state_dir / "latest.json").write_text(payload, encoding="utf-8")
        return run_path

    def _batch_metadata_payload(
        self,
        *,
        work_dir: Path,
        input_path: Path,
        entries: list[dict],
        image_root: Path | None,
        out_dir: Path,
        report_dir: Path,
        records: list[dict],
        dry_run: bool,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
    ) -> dict:
        return {
            "schema_version": 2,
            "command": "physics-formalize",
            "mode": "batch",
            "dry_run": dry_run,
            "project_path": str(self.project_path),
            "work_dir": str(work_dir),
            "input_jsonl": str(input_path),
            "output_dir": str(out_dir),
            "report_dir": str(report_dir),
            "image_root": str(image_root) if image_root else None,
            "domain": "physics",
            "next_stage": "autoformalize",
            "prover_mode": PHYSICS_FORMALIZE_MODE,
            "proof_mode": PHYSICS_PROVER_MODE,
            "lean_search_packages": ["Mathlib", "Physlib"],
            "limit": self.limit,
            "entry_count": len(entries),
            "missing_images": self._missing_images(entries, image_root),
            "physlean_dependency": self._metadata_physlean_dependency(ensure_result),
            "physlean_build": self._metadata_physlean_build(build_result),
            "preflight": self._metadata_preflight(preflight_result),
            "entries": entries,
            "records": records,
            "result": {
                "status": "prepared" if not dry_run else "dry-run",
                "next_stage": "autoformalize",
                "total": len(entries),
                "prepared": len(records),
            },
        }

    def _problem_set_metadata_payload(
        self,
        *,
        work_dir: Path,
        input_path: Path,
        problem_id: str,
        shared_context: str,
        entries: list[dict],
        image_root: Path | None,
        out_dir: Path,
        report_dir: Path,
        records: list[dict],
        dry_run: bool,
        ensure_result: dict | None,
        build_result: dict | None,
        preflight_result: dict | None,
    ) -> dict:
        dependencies = {
            str(entry.get("index")): [
                str(prev.get("source_id"))
                for prev in entry.get("previous_parts", [])
                if isinstance(prev, dict) and prev.get("source_id")
            ]
            for entry in entries
        }
        return {
            "schema_version": 2,
            "command": "physics-formalize",
            "mode": "problem-set",
            "dry_run": dry_run,
            "project_path": str(self.project_path),
            "work_dir": str(work_dir),
            "input_jsonl": str(input_path),
            "problem_id": problem_id,
            "shared_context": shared_context,
            "part_count": len(entries),
            "output_dir": str(out_dir),
            "report_dir": str(report_dir),
            "image_root": str(image_root) if image_root else None,
            "domain": "physics",
            "next_stage": "autoformalize",
            "prover_mode": PHYSICS_FORMALIZE_MODE,
            "proof_mode": PHYSICS_PROVER_MODE,
            "lean_search_packages": ["Mathlib", "Physlib"],
            "limit": self.limit,
            "dependencies": dependencies,
            "missing_images": self._missing_images(entries, image_root),
            "physlean_dependency": self._metadata_physlean_dependency(ensure_result),
            "physlean_build": self._metadata_physlean_build(build_result),
            "preflight": self._metadata_preflight(preflight_result),
            "entries": entries,
            "records": records,
            "result": {
                "status": "prepared" if not dry_run else "dry-run",
                "next_stage": "autoformalize",
                "total": len(entries),
                "prepared": len(records),
            },
        }

    @staticmethod
    def _missing_images(entries: list[dict], image_root: Path | None) -> list[dict]:
        missing: list[dict] = []
        if image_root is None:
            return missing
        for entry in entries:
            image = entry.get("image")
            if not image:
                continue
            image_path = Path(str(image))
            if not image_path.is_absolute():
                image_path = image_root / image_path
            if not image_path.is_file():
                missing.append({
                    "index": str(entry.get("index")),
                    "image": str(image),
                    "expected_path": str(image_path),
                })
        return missing

    def _metadata_physlean_dependency(self, ensure_result: dict | None) -> dict:
        if ensure_result:
            return ensure_result
        return {"requested": self.ensure_physlean, "modified": None, "update_passed": None}

    def _metadata_physlean_build(self, build_result: dict | None) -> dict:
        if build_result:
            return build_result
        return {"requested": self.build_physlean, "passed": None, "target": "Physlib"}

    def _metadata_preflight(self, preflight_result: dict | None) -> dict:
        if preflight_result:
            return preflight_result
        return {"requested": self.preflight, "passed": None, "packages": ["Mathlib", "Physlib"]}

    # progress --------------------------------------------------------

    def _update_progress_records(self, records: list[dict]) -> None:
        self._ensure_loop_assets()
        state_dir = self.project_path / ".archon"
        state_dir.mkdir(parents=True, exist_ok=True)
        progress = state_dir / "PROGRESS.md"
        objective_parts: list[str] = []
        for number, record in enumerate(records, start=1):
            rel_lean = record["rel_lean"]
            rel_report = record["rel_report"]
            rel_chapter = record["rel_chapter"]
            objective_parts.append(
                f"### {number}. **`{rel_lean}`** [prover-mode: {PHYSICS_FORMALIZE_MODE}]\n"
                f"- Autoformalize this physics blueprint chapter into Lean declarations with `by sorry` bodies.\n"
                f"- Blueprint chapter: `{rel_chapter}`.\n"
                f"- Source report: `{rel_report}`.\n"
                f"- After this file compiles with expected sorry warnings, move it to prover mode `{PHYSICS_PROVER_MODE}`.\n"
            )
        objective = "\n".join(objective_parts)
        if progress.exists():
            text = progress.read_text(encoding="utf-8")
        else:
            text = (
                "# Project Progress\n\n"
                "## Current Stage\n\n"
                "autoformalize\n\n"
                "## Stages\n"
                "- [x] init\n"
                "- [ ] autoformalize\n"
                "- [ ] prover\n"
                "- [ ] polish\n\n"
                "## Current Objectives\n\n"
            )
        text = self._replace_or_add_section(text, "## Current Stage", "autoformalize\n", before="## Stages")
        text = self._mark_stage_checkboxes_for_autoformalize(text)
        text = self._replace_or_add_section(text, "## Current Objectives", objective, before=None)
        progress.write_text(text, encoding="utf-8")
        log.success(f"Updated PROGRESS.md with {len(records)} physics autoformalize target(s).")

    @staticmethod
    def _replace_or_add_section(text: str, heading: str, body: str, *, before: str | None) -> str:
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
    def _mark_stage_checkboxes_for_autoformalize(text: str) -> str:
        replacements = {
            r"- \[[ xX]\] init": "- [x] init",
            r"- \[[ xX]\] autoformalize": "- [ ] autoformalize",
            r"- \[[ xX]\] prover": "- [ ] prover",
            r"- \[[ xX]\] polish": "- [ ] polish",
        }
        for pattern, repl in replacements.items():
            text = re.sub(pattern, repl, text)
        return text

    # PhysLean environment ------------------------------------------

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
        addition = PHYSLEAN_REQUIRE_LEAN if kind == "lean" else PHYSLEAN_REQUIRE_TOML
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
        if not ((self.project_path / "lakefile.lean").exists() or (self.project_path / "lakefile.toml").exists()):
            log.error("PhysLean build failed: target project has no lakefile.")
            raise typer.Exit(1)
        command = [lake, "build", "Physlib"]
        log.phase(0, "Build Physlib")
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
            "target": "Physlib",
        }
        if proc.returncode == 0:
            log.success("Physlib build completed.")
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
        if not ((self.project_path / "lakefile.lean").exists() or (self.project_path / "lakefile.toml").exists()):
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
            "packages": ["Mathlib", "Physlib"],
        }
        if proc.returncode == 0:
            log.success("Lean preflight passed: Mathlib/Physlib imports compile.")
            return result
        output = (proc.stderr or proc.stdout or "").strip()
        result["error"] = output[:4000]
        log.error("Lean preflight failed: Mathlib/Physlib imports did not compile.")
        if output:
            log.info(output[:1200])
            hint = self._preflight_hint(output)
            if hint:
                log.info(hint)
        raise typer.Exit(1)

    @staticmethod
    def _preflight_hint(output: str) -> str | None:
        if "unknown module prefix 'Physlib'" in output or "unknown package Physlib" in output:
            return (
                "Hint: the target project does not currently expose Physlib to "
                "`lake env lean`. Run `lake update PhysLean`/`lake build` in the "
                "target project, or point `archon physics-formalize` at a Lean "
                "project whose lakefile has a working PhysLean/Physlib dependency."
            )
        if "unknown module prefix 'Mathlib'" in output or "unknown package Mathlib" in output:
            return (
                "Hint: the target project does not currently expose Mathlib to "
                "`lake env lean`. Run `lake update`/`lake build` in the target project."
            )
        return None

    # misc ------------------------------------------------------------

    def _rel_to_project(self, path: Path) -> str:
        resolved = path.resolve()
        try:
            return resolved.relative_to(self.project_path).as_posix()
        except ValueError:
            return str(resolved)

    @staticmethod
    def _safe_label(value: str) -> str:
        return re.sub(r"[^A-Za-z0-9_.:-]+", "_", value).strip("_") or "problem"

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


def physics_formalize(
    project_path: str = typer.Argument(
        ...,
        help="Archon/Lean project where physics blueprint targets should be prepared.",
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
            "Read physics JSONL entries for batch mode. Each line should contain "
            "question plus optional index, answer, category, image, and dependency fields."
        ),
    ),
    problem_id: Optional[str] = typer.Option(
        None,
        "--problem-id",
        help="In problem-set mode, select one multi-part problem_id from the JSONL.",
    ),
    as_problem_set: bool = typer.Option(
        False,
        "--as-problem-set",
        help=(
            "Treat --input-jsonl rows with the same problem_id as one multi-part "
            "physics problem, preserving previous_parts dependencies in blueprint."
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
        None, "--image", "-i", help="Optional diagram/image for the physics problem.",
    ),
    answer: str = typer.Option(
        "", "--answer", "-a", help="Optional known final answer/context.",
    ),
    out: Optional[Path] = typer.Option(
        None, "--out", "-o", help="Target Lean path for loop autoformalization.",
    ),
    report_out: Optional[Path] = typer.Option(
        None, "--report-out", help="Source-report JSON path, relative to project if not absolute.",
    ),
    out_dir: Optional[Path] = typer.Option(
        None,
        "--out-dir",
        help="Batch mode target Lean directory, relative to project if not absolute.",
    ),
    report_dir: Optional[Path] = typer.Option(
        None,
        "--report-dir",
        help="Batch mode source-report directory, relative to project if not absolute.",
    ),
    work_dir: Optional[Path] = typer.Option(
        None, "--work-dir", help="Directory for manifests/intermediate files.",
    ),
    index: str = typer.Option(
        "001", "--index", help="Problem id used for filenames in single mode.",
    ),
    category: str = typer.Option(
        "physics", "--category", help="Category label stored in source reports.",
    ),
    limit: int = typer.Option(
        -1,
        "--limit",
        help="Batch/problem-set limit. Use -1 to process all selected entries.",
    ),
    dataset_format: str = typer.Option(
        "auto",
        "--dataset-format",
        help=(
            "Input schema: auto, native, or phyx. PhyX mode combines the visual "
            "scenario/question/options and resolves letter answers to answer text."
        ),
    ),
    ensure_physlean: bool = typer.Option(
        False,
        "--ensure-physlean/--no-ensure-physlean",
        help="Append a PhysLean dependency to lakefile.lean/toml when missing.",
    ),
    build_physlean: bool = typer.Option(
        False,
        "--build-physlean/--no-build-physlean",
        help="Run `lake build Physlib` in the target project before loop preparation.",
    ),
    preflight: bool = typer.Option(
        False,
        "--preflight/--no-preflight",
        help="Compile the physics import header in the target Lean project.",
    ),
    dry_run: bool = typer.Option(
        False,
        "--dry-run",
        help="Resolve inputs and write metadata without blueprint/progress changes.",
    ),
    update_progress: bool = typer.Option(
        False,
        "--update-progress",
        help=(
            "Set .archon/PROGRESS.md to autoformalize with physics-formalize "
            "objectives for the prepared targets."
        ),
    ),
    with_rethlas_blueprint: bool = typer.Option(
        False,
        "--with-rethlas-blueprint",
        help="Optionally add a Rethlas-style natural-language proof sketch to blueprint.",
    ),
    rethlas_command: Optional[str] = typer.Option(
        None,
        "--rethlas-command",
        help="Command for the optional Rethlas blueprint sketch agent.",
    ),
    rethlas_timeout: int = typer.Option(
        180,
        "--rethlas-timeout",
        help="Timeout in seconds for the optional Rethlas blueprint command.",
    ),
) -> None:
    """Prepare physics blueprint/progress entries for `archon loop`."""
    PhysicsFormalizeCommand(
        project_path,
        question=question,
        question_file=question_file,
        input_jsonl=input_jsonl,
        problem_id=problem_id,
        as_problem_set=as_problem_set,
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
        dataset_format=dataset_format,
        ensure_physlean=ensure_physlean,
        build_physlean=build_physlean,
        preflight=preflight,
        dry_run=dry_run,
        update_progress=update_progress,
        with_rethlas_blueprint=with_rethlas_blueprint,
        rethlas_command=rethlas_command,
        rethlas_timeout=rethlas_timeout,
    ).run()
