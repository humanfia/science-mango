from __future__ import annotations

import hashlib
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from typer.testing import CliRunner

import archon.commands.blind_evaluation as blind
from archon.cli import app as archon_app
from archon.commands.loop.review_source_contract import (
    blind_result_payload_sha256,
    build_review_source_contract,
    expected_numeric_result_types,
    lean_result_type_sha256,
    normalized_review_source_certificate,
    source_contract_provenance,
)
from archon.commands.loop.formalization_review_gate import apply_formalization_review


REPORTING_POLICY = {
    "intermediate_rounding": "forbidden",
    "explicit_precision": "use_only_precision_requested_in_problem",
    "default_final_display": "three_significant_figures",
    "final_precision": {
        "kind": "significant_figures",
        "digits": 3,
        "source": "uniform_blind_evaluation_default",
    },
    "tie_rule": "half_away_from_zero",
    "raw_result_required": True,
}
MEASUREMENT_POLICY = {
    "stipulated_constants": "exact_as_printed_unless_problem_calls_them_measured",
    "measured_display_half_width": "one_half_of_last_displayed_quantum",
    "derived_tolerances": "must_be_proved_from_source_measurement_intervals",
}
CANDIDATE_DOMAIN_POLICY = {
    "allowed_sources": [
        "problem_text",
        "problem_image",
        "problem_stated_fallback",
        "trusted_general_law",
        "derived_theorem",
    ],
    "previous_part_results": (
        "derive_inline_from_problem_only_material_or_use_problem_stated_fallback"
    ),
    "unjustified_search_bounds": "forbidden",
    "underdetermined_result": "must_be_reported",
}


def _gpt_response_and_sse(text: str, *, suffix: str) -> tuple[dict[str, object], bytes]:
    response_id = f"resp_{suffix}"
    message_id = f"msg_{suffix}"
    part = {"type": "output_text", "annotations": [], "logprobs": [], "text": text}
    message = {
        "id": message_id, "type": "message", "status": "completed",
        "role": "assistant", "phase": "final_answer", "content": [part],
    }
    completed_response: dict[str, object] = {
        "id": response_id, "status": "completed", "error": None,
        "incomplete_details": None, "output": [message],
        "tools": [], "tool_choice": "none",
    }
    events: list[dict[str, object]] = [
        {"type": "response.created", "sequence_number": 0, "response": {
            "id": response_id, "status": "in_progress", "error": None,
            "output": [], "tools": [], "tool_choice": "none",
        }},
        {"type": "response.in_progress", "sequence_number": 1, "response": {
            "id": response_id, "status": "in_progress", "error": None,
            "output": [], "tools": [], "tool_choice": "none",
        }},
        {"type": "response.output_item.added", "sequence_number": 2,
         "output_index": 0, "item": {
             "id": message_id, "type": "message", "status": "in_progress",
             "role": "assistant", "phase": "final_answer", "content": [],
         }},
        {"type": "response.content_part.added", "sequence_number": 3,
         "output_index": 0, "item_id": message_id, "content_index": 0,
         "part": {**part, "text": ""}},
        {"type": "response.output_text.delta", "sequence_number": 4,
         "output_index": 0, "item_id": message_id, "content_index": 0,
         "delta": text},
        {"type": "response.output_text.done", "sequence_number": 5,
         "output_index": 0, "item_id": message_id, "content_index": 0,
         "text": text},
        {"type": "response.content_part.done", "sequence_number": 6,
         "output_index": 0, "item_id": message_id, "content_index": 0,
         "part": part},
        {"type": "response.output_item.done", "sequence_number": 7,
         "output_index": 0, "item": message},
        {"type": "response.completed", "sequence_number": 8,
         "response": completed_response},
    ]
    raw = b"".join(
        f"event: {event['type']}\ndata: ".encode()
        + json.dumps(event, separators=(",", ":")).encode() + b"\n\n"
        for event in events
    )
    return completed_response, raw


def _gpt_reasoning_sse(text: str, *, suffix: str, summary: str = "summary") -> bytes:
    _response, raw = _gpt_response_and_sse(text, suffix=suffix)
    events = [
        json.loads(line[6:]) for line in raw.decode().splitlines()
        if line.startswith("data: ") and line != "data: [DONE]"
    ]
    for event in events[2:-1]:
        if event.get("output_index") == 0:
            event["output_index"] = 1
    events[-1]["response"]["output"] = []
    reasoning_id = f"rs_{suffix}"
    summary_part = {"type": "summary_text", "text": summary}
    reasoning_events = [
        {"type": "response.output_item.added", "output_index": 0,
         "item": {
             "id": reasoning_id, "type": "reasoning", "summary": [],
             "content": [], "encrypted_content": "opaque-added",
         }},
        {"type": "response.reasoning_summary_part.added", "output_index": 0,
         "item_id": reasoning_id, "summary_index": 0,
         "part": {"type": "summary_text", "text": ""}},
        {"type": "response.reasoning_summary_text.delta", "output_index": 0,
         "item_id": reasoning_id, "summary_index": 0, "delta": summary},
        {"type": "response.reasoning_summary_text.done", "output_index": 0,
         "item_id": reasoning_id, "summary_index": 0, "text": summary},
        {"type": "response.reasoning_summary_part.done", "output_index": 0,
         "item_id": reasoning_id, "summary_index": 0, "part": summary_part},
        {"type": "response.output_item.done", "output_index": 0,
         "item": {
             "id": reasoning_id, "type": "reasoning",
             "summary": [summary_part], "content": [],
             "encrypted_content": "opaque-done",
         }},
    ]
    events = events[:2] + reasoning_events + events[2:]
    for sequence, event in enumerate(events):
        event["sequence_number"] = sequence
    return b"".join(
        f"event: {event['type']}\ndata: ".encode()
        + json.dumps(event, separators=(",", ":")).encode() + b"\n\n"
        for event in events
    )


class BlindEvaluationTest(unittest.TestCase):
    @staticmethod
    def _sha256(path: Path) -> str:
        return hashlib.sha256(path.read_bytes()).hexdigest()

    @staticmethod
    def _write_json(path: Path, value: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(blind._json_bytes(value))

    def test_inventory_hashes_files_larger_than_artifact_read_limit_by_streaming(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            payload = b"inventory payload larger than the patched artifact limit"
            (root / "large.bin").write_bytes(payload)
            with mock.patch.object(blind, "_MAX_ARTIFACT_BYTES", 1):
                inventory = blind._regular_file_inventory(
                    root, label="streaming inventory", require_controller_owner=False,
                )
            self.assertEqual(
                inventory, {"large.bin": hashlib.sha256(payload).hexdigest()},
            )

    def test_expected_report_entry_replays_ingestion_question_stripping(self):
        with tempfile.TemporaryDirectory() as td:
            project = Path(td)
            image = project / "icho_2026_source/image/page.png"
            image.parent.mkdir(parents=True)
            image.write_bytes(b"image")
            row = {"id": "problem", "question": "  stated question\n", "images": ["page.png"]}
            expected = blind._expected_report_entry(
                project=project, bundle_row=row, blind_hash="a" * 64,
            )
            self.assertEqual(expected["question"], "stated question")
            self.assertEqual(expected["blind_record_sha256"], "a" * 64)
            self.assertEqual(
                expected["image_paths"], ["icho_2026_source/image/page.png"],
            )

    def test_structured_failure_diagnostic_requires_exact_private_hash_binding(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            project = root / "project"
            project.mkdir()
            diagnostic = root / "controller" / "gpt-attempt-codex.jsonl"
            diagnostic.parent.mkdir()
            diagnostic.write_bytes(b"preserved raw stdout\n")
            diagnostic.chmod(0o400)
            locator = {
                "path": str(diagnostic), "sha256": self._sha256(diagnostic),
            }
            stderr = root / "controller" / "gpt-attempt-codex.stderr"
            stderr.write_bytes(b"preserved raw stderr\n")
            stderr.chmod(0o400)
            stderr_locator = {
                "path": str(stderr), "sha256": self._sha256(stderr),
            }
            failure = {
                "diagnostic_stdout": locator,
                "diagnostic_stderr": stderr_locator,
            }
            blind._validate_structured_failure_diagnostic(
                project=project, failure=failure, variant="gpt",
            )
            request_locator = {"path": str(root / "controller" / "request.json"), "sha256": "1" * 64}
            receipt = {
                "schema_version": 1, "protocol": blind.PROTOCOL,
                "phase": "structured_provider_transport_failure",
                "variant": "gpt", "target_id": "target", "attempt": 1,
                "adapter": "chatgpt_login_proxy_v1", "request": request_locator,
                "provider_invocation_started": True,
                "status": "failed_without_valid_response",
                "diagnostic_stdout": locator,
                "diagnostic_stderr": stderr_locator,
            }
            receipt_path = root / "controller" / "transport-failure.json"
            self._write_json(receipt_path, receipt)
            receipt_path.chmod(0o400)
            receipt_locator = {
                "path": str(receipt_path), "sha256": self._sha256(receipt_path),
            }
            blind._validate_structured_transport_provenance(
                project=project, runtime={}, aggregate={"variant": "gpt"},
                attempt={
                    "adapter_provenance": {
                        "transport_failure_receipt": receipt_locator,
                    },
                    "adapter": "chatgpt_login_proxy_v1",
                    "status": "transport_error", "target_id": "target",
                    "attempt": 1, "request": request_locator,
                },
                request_path=Path(request_locator["path"]), request_payload=b"{}\n",
                response_path=None, response_payload=None,
                expected_gpt_exchange=receipt_locator,
            )

            raw_sse = root / "controller" / "gpt-attempt-upstream.sse"
            raw_sse.write_bytes(b"data: fixture\n\n")
            raw_sse.chmod(0o400)
            normalized = root / "controller" / "gpt-attempt-normalized.json"
            normalized_value = {"output": [{
                "type": "message", "role": "assistant",
                "content": [
                    {"type": "output_text", "text": "{\"raw_"},
                    {"type": "output_text", "text": "result\":{}}"},
                ],
            }]}
            self._write_json(normalized, normalized_value)
            normalized.chmod(0o400)
            response_evidence = {
                **failure,
                "upstream_raw_sse": {
                    "path": str(raw_sse), "sha256": self._sha256(raw_sse),
                },
                "normalized_response": {
                    "path": str(normalized), "sha256": self._sha256(normalized),
                },
                "response_structure":
                    blind._bounded_structured_gpt_response_structure(normalized_value),
            }
            blind._validate_structured_failure_diagnostic(
                project=project, failure=response_evidence, variant="gpt",
            )
            response_evidence["response_structure"] = {
                **response_evidence["response_structure"], "output_item_count": 2,
            }
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "structure is stale",
            ):
                blind._validate_structured_failure_diagnostic(
                    project=project, failure=response_evidence, variant="gpt",
                )

            failed_sse = root / "controller" / "failed-upstream.sse"
            failed_sse.write_bytes(
                b'event: response.unknown\n'
                b'data: {"type":"response.unknown","sequence_number":0,'
                b'"secret":"sealed-only"}\n\n'
            )
            failed_sse.chmod(0o400)
            failed_headers = root / "controller" / "failed-headers.json"
            self._write_json(failed_headers, {
                "header_names": ["content-type", "x-request-id"],
                "upstream_status": 200,
            })
            failed_headers.chmod(0o400)
            raw_failure = {
                **failure,
                "upstream_raw_sse": {
                    "path": str(failed_sse), "sha256": self._sha256(failed_sse),
                },
                "response_headers": {
                    "path": str(failed_headers), "sha256": self._sha256(failed_headers),
                },
                "response_structure": blind._bounded_chatgpt_sse_structure(
                    failed_sse.read_bytes(),
                ),
            }
            blind._validate_structured_failure_diagnostic(
                project=project, failure=raw_failure, variant="gpt",
            )
            self.assertNotIn("sealed-only", json.dumps(raw_failure["response_structure"]))

            stale = {
                "diagnostic_stdout": locator,
                "diagnostic_stderr": {**stderr_locator, "sha256": "0" * 64},
            }
            with self.assertRaisesRegex(blind.BlindEvaluationError, "hash is stale"):
                blind._validate_structured_failure_diagnostic(
                    project=project, failure=stale, variant="gpt",
                )
            diagnostic.chmod(0o600)
            with self.assertRaisesRegex(blind.BlindEvaluationError, "mode 0400"):
                blind._validate_structured_failure_diagnostic(
                    project=project, failure=failure, variant="gpt",
                )
            diagnostic.chmod(0o400)
            with self.assertRaisesRegex(blind.BlindEvaluationError, "only GPT"):
                blind._validate_structured_failure_diagnostic(
                    project=project, failure=failure, variant="kimi-k3",
                )

    def test_freeze_sse_parser_replays_reasoning_summary_and_rejects_mutations(self):
        def events(raw: bytes) -> list[dict[str, object]]:
            return [
                json.loads(line[6:]) for line in raw.decode().splitlines()
                if line.startswith("data: ") and line != "data: [DONE]"
            ]

        def encode(rows: list[dict[str, object]]) -> bytes:
            for sequence, row in enumerate(rows):
                row["sequence_number"] = sequence
            return b"".join(
                f"event: {row['type']}\ndata: ".encode()
                + json.dumps(row, separators=(",", ":")).encode() + b"\n\n"
                for row in rows
            )

        valid_rows = events(_gpt_reasoning_sse('{"ok":true}', suffix="reasoning"))
        rebuilt, _payload = blind._rebuild_chatgpt_response_from_sse(
            encode(valid_rows),
        )
        self.assertEqual(rebuilt["output"][0]["type"], "reasoning")
        self.assertEqual(
            rebuilt["output"][0]["summary"][0]["type"], "summary_text",
        )

        with_keepalive = json.loads(json.dumps(valid_rows))
        with_keepalive.insert(3, {"type": "keepalive"})
        rebuilt_keepalive, _payload = blind._rebuild_chatgpt_response_from_sse(
            encode(with_keepalive),
        )
        self.assertEqual(rebuilt_keepalive, rebuilt)

        mutations: list[tuple[str, list[dict[str, object]]]] = []
        keepalive_extra = json.loads(json.dumps(with_keepalive))
        keepalive_extra[3]["payload"] = "not-empty"
        mutations.append(("keepalive-extra-field", keepalive_extra))
        keepalive_before_active = json.loads(json.dumps(valid_rows))
        keepalive_before_active.insert(2, {"type": "keepalive"})
        mutations.append(("keepalive-before-active-item", keepalive_before_active))
        missing_done = json.loads(json.dumps(valid_rows))
        missing_done = [
            row for row in missing_done
            if row["type"] != "response.reasoning_summary_part.done"
        ]
        mutations.append(("missing-summary-part-done", missing_done))
        delta_mismatch = json.loads(json.dumps(valid_rows))
        next(
            row for row in delta_mismatch
            if row["type"] == "response.reasoning_summary_text.delta"
        )["delta"] += "x"
        mutations.append(("summary-delta-done-mismatch", delta_mismatch))
        bool_done_index = json.loads(json.dumps(valid_rows))
        next(
            row for row in bool_done_index
            if row["type"] == "response.output_item.done"
            and row["item"]["type"] == "reasoning"
        )["output_index"] = False
        mutations.append(("bool-output-index", bool_done_index))
        bool_summary_index = json.loads(json.dumps(valid_rows))
        next(
            row for row in bool_summary_index
            if row["type"] == "response.reasoning_summary_text.delta"
        )["summary_index"] = False
        mutations.append(("bool-summary-index", bool_summary_index))
        bool_content_index = json.loads(json.dumps(valid_rows))
        next(
            row for row in bool_content_index
            if row["type"] == "response.content_part.added"
        )["content_index"] = False
        mutations.append(("bool-content-index", bool_content_index))

        for label, rows in mutations:
            with self.subTest(label=label):
                with self.assertRaises(blind.BlindEvaluationError):
                    blind._rebuild_chatgpt_response_from_sse(encode(rows))

    def _make_project(self, root: Path) -> dict[str, object]:
        root.chmod(0o755)
        project = root / "project"
        state = project / ".archon"
        candidates = project / "blind_candidates"
        problems = project / "Problems"
        reports = project / "reports" / "source"
        chapters = project / "blueprint" / "src" / "chapters"
        source_images = project / "icho_2026_source" / "image"
        source_raw = project / "icho_2026_source" / "raw"
        controller = root / "controller"
        dependency_root = root / "lake-packages"
        for directory in (
            state,
            candidates,
            problems,
            reports,
            chapters,
            source_images,
            source_raw,
            controller,
            dependency_root,
        ):
            directory.mkdir(parents=True)

        config = {
            "loop": {"domain_profile": {"name": "chemistry"}},
            "answer_blind": {
                "protocol": blind.PROTOCOL,
                "phase": "solve",
                "official_answer_seen": False,
                "isolation": {
                    "filesystem_answer_blind": True,
                    "network_answer_blind": False,
                },
            },
        }
        self._write_json(state / "config.json", config)
        self._write_json(project / ".mcp.json", {"mcpServers": {}})
        (project / "ANSWER_BLIND_PROTOCOL.md").write_text(
            "# Answer-blind protocol\nNo answer-bearing material is available.\n",
            encoding="utf-8",
        )
        (state / "AGENTS.md").write_text(
            "# Solver policy\nUse problem-only evidence.\n", encoding="utf-8"
        )

        record_id = "icho_t1_a1"
        target = problems / "T1A1.lean"
        target.write_text(
            "import IChO2026Chem.Reporting\n"
            "def BlindFixture.power : ℝ := 7043\n"
            "def BlindFixture.rawEnergy : ℝ := BlindFixture.power * 1000000000\n"
            "def BlindFixture.rawEnergyDerivedFromProblemData : Prop := "
            "BlindFixture.rawEnergy = (7043000000000 : ℝ)\n"
            "theorem BlindFixture.rawEnergyResult : "
            "BlindFixture.rawEnergyDerivedFromProblemData ∧ "
            "((7042000000000 : ℝ) ≤ BlindFixture.rawEnergy ∧ "
            "BlindFixture.rawEnergy ≤ (7044000000000 : ℝ)) := by\n"
            "  constructor\n"
            "  · norm_num [BlindFixture.rawEnergyDerivedFromProblemData, "
            "BlindFixture.rawEnergy, BlindFixture.power]\n"
            "  · norm_num [BlindFixture.rawEnergy, BlindFixture.power]\n"
            "theorem BlindFixture.reportedEnergyResult : "
            "IChO2026Chem.Reporting.ReportsAtQuantum "
            "BlindFixture.rawEnergy (7040000000000 : ℝ) "
            "(10000000000 : ℝ) := by\n"
            "  constructor\n"
            "  · norm_num\n"
            "  constructor\n"
            "  · exact ⟨704, by norm_num⟩\n"
            "  · norm_num [BlindFixture.rawEnergy]\n",
            encoding="utf-8",
        )
        (project / "IChO2026Problems.lean").write_text(
            "import Problems.T1A1\n", encoding="utf-8"
        )
        reporting_module = project / "IChO2026Chem" / "Reporting.lean"
        reporting_module.parent.mkdir(parents=True)
        reporting_module.write_text(
            "import Mathlib\nnamespace IChO2026Chem.Reporting\n"
            "def ReportsAtQuantum (raw reported quantum : ℝ) : Prop :=\n"
            "  0 < quantum ∧\n"
            "  (∃ k : ℤ, reported = quantum * k) ∧\n"
            "  if 0 ≤ raw then\n"
            "    reported - quantum / 2 ≤ raw ∧ raw < reported + quantum / 2\n"
            "  else\n"
            "    reported - quantum / 2 < raw ∧ raw ≤ reported + quantum / 2\n"
            "end IChO2026Chem.Reporting\n",
            encoding="utf-8",
        )
        chapter = chapters / "Problems_T1A1.tex"
        chapter.write_text(
            "% archon:chemistry\n"
            "% archon:covers Problems/T1A1.lean\n"
            "% archon:source-report reports/source/T1A1.source.json\n"
            "Problem-only blueprint.\n",
            encoding="utf-8",
        )
        image = source_images / "T1_page-1.png"
        image.write_bytes(b"problem-image")
        problem_pdf = source_raw / "theory_problem.pdf"
        problem_pdf.write_bytes(b"problem-pdf")
        previous: list[dict[str, object]] = []
        bundle_row = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "id": record_id,
            "index": record_id,
            "source_index": "T1.1",
            "problem_id": "T1",
            "part_id": "T1.1",
            "question": "Compute the energy delivered per day.",
            "current_question": "Compute the energy delivered per day.",
            "shared_context": "Use the stated power and duration.",
            "category": "IChO 2026 Theory",
            "dataset": "IChO 2026 official English problem materials",
            "dataset_format": "native",
            "points": 1,
            "paper": "theory",
            "kind": "theory",
            "formalization_ready": True,
            "image": image.name,
            "images": [image.name],
            "previous_parts": previous,
            "source_pdf": problem_pdf.name,
            "source_page": 1,
            "printed_page": 1,
            "problem_assets": [
                {
                    "kind": "problem_page",
                    "path": image.name,
                    "sha256": self._sha256(image),
                },
                {
                    "kind": "problem_pdf",
                    "path": problem_pdf.name,
                    "sha256": self._sha256(problem_pdf),
                },
            ],
            "requested_outputs": [
                {
                    "id": "energy_per_day",
                    "source_requirement": "energy delivered per day",
                    "kind": "numeric",
                    "unit": "J/day",
                    "reporting_policy": REPORTING_POLICY["final_precision"],
                }
            ],
            "reporting_policy": REPORTING_POLICY,
            "measurement_policy": MEASUREMENT_POLICY,
            "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
        }
        bundle = project / "icho_2026_source" / "questions_only.jsonl"
        bundle.write_bytes(blind._json_bytes(bundle_row))
        blind_hash = hashlib.sha256(blind._json_bytes(bundle_row)).hexdigest()

        entry = dict(bundle_row)
        entry.update(
            {
                "blind_record_sha256": blind_hash,
                "image_path": "icho_2026_source/image/T1_page-1.png",
                "image_paths": ["icho_2026_source/image/T1_page-1.png"],
            }
        )
        report = reports / "T1A1.source.json"
        self._write_json(
            report,
            {
                "schema_version": 3,
                "evaluation_mode": "answer_blind",
                "official_answer_seen": False,
                "phase": "solve",
                "blind_record_sha256": blind_hash,
                "output_lean": "Problems/T1A1.lean",
                "domain": "chemistry",
                "entry": entry,
                "previous_parts": previous,
            },
        )

        candidate = candidates / f"{record_id}.json"
        candidate_value: dict[str, object] = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "solve",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "id": record_id,
            "blind_record_sha256": blind_hash,
            "result_kind": "numeric",
            "raw_result": {
                "expression": "7043 * 10^9 from problem-stated power and duration",
                "value": "7.043e12",
                "lean_expression": "BlindFixture.rawEnergy",
                "derivation_spec": "BlindFixture.rawEnergyDerivedFromProblemData",
                "certified_interval": {
                    "lower": "7.042e12",
                    "upper": "7.044e12",
                },
                "unit": "J/day",
            },
            "reported_result": {
                "value": "7.04e12",
                "text": "7.04e12 J/day",
                "lean_expression": "BlindFixture.rawEnergy",
                "unit": "J/day",
                "precision": REPORTING_POLICY["final_precision"],
                "rounding_rule": "half_away_from_zero",
            },
            "reporting_rule_source": REPORTING_POLICY,
            "tolerance_provenance": {
                "measurement_policy": MEASUREMENT_POLICY,
                "derivation": {
                    "kind": "controller_policy_binding",
                    "source": "problem_projection.measurement_policy",
                },
            },
            "candidate_domain_provenance": {
                "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
                "derivation": {
                    "kind": "source_arithmetic",
                    "evidence": ["positive energy derived from stated inputs"],
                    "depends_on": [],
                },
            },
            "lean_declarations": [
                "BlindFixture.rawEnergyResult",
                "BlindFixture.reportedEnergyResult",
            ],
        }
        result_types = expected_numeric_result_types(candidate_value)
        assert result_types is not None
        candidate_value["lean_result_contracts"] = [
            {
                "role": role,
                "declaration": declaration,
                "expected_type": result_types[role],
                "expected_type_sha256": lean_result_type_sha256(result_types[role]),
                "result_payload_sha256": blind_result_payload_sha256(
                    candidate_value, role
                ),
            }
            for role, declaration in zip(
                ("raw_result", "reported_result"),
                candidate_value["lean_declarations"],
                strict=True,
            )
        ]
        self._write_json(candidate, candidate_value)

        contract = build_review_source_contract(project_path=project, target=target)
        self.assertTrue(contract["valid"], contract["errors"])
        provenance = source_contract_provenance(contract)
        def passed_check(evidence: str) -> dict[str, str]:
            return {"status": "passed", "evidence": evidence}

        review = {
            "source_contract": provenance,
            "blind_source_audit": {
                name: passed_check(f"audited {name}")
                for name in (
                    "answer_independence",
                    "raw_derivation",
                    "reporting_rule_source",
                    "tolerance_provenance",
                    "candidate_domain_provenance",
                    "lean_result_binding",
                )
            },
            "contract_audit": {
                name: passed_check(f"audited {name}")
                for name in (
                    "statement_scope",
                    "hypothesis_derivability",
                    "conclusion_alignment",
                    "bridge_completeness",
                )
            },
            "requested_outputs": [
                {
                    "source_requirement": "energy delivered per day",
                    "lean_carrier": "BlindFixture.reportedEnergyResult",
                    "status": "covered",
                    "evidence": "the result theorem covers the scalar output",
                }
            ],
            "blueprint_conflicts": [],
            "image_audit": [
                {
                    "path": "icho_2026_source/image/T1_page-1.png",
                    "sha256": self._sha256(image),
                    "inspected": True,
                    "evidence": "problem page inspected",
                }
            ],
            "chemistry_checks": {
                name: passed_check(f"audited {name}")
                for name in (
                    "chemical_semantics",
                    "formula_mass_consistency",
                    "conservation_laws",
                    "units_dimensions",
                    "numerical_reporting",
                    "structure_stereochemistry",
                    "identification_uniqueness",
                    "answer_smuggling",
                )
            },
        }
        normalized_review = normalized_review_source_certificate(review)
        formal_gate = state / "formalization-review-gate.json"
        proof_gate = state / "proof-review-gate.json"
        self._write_json(
            formal_gate,
            {
                "version": 2,
                "targets": {
                    "Problems/T1A1.lean": {
                        "status": "passed",
                        "certificate": {
                            "schema_version": 2,
                            "checks": {
                                name: passed_check(f"formal Review checked {name}")
                                for name in (
                                    "source_faithfulness",
                                    "derivability",
                                    "abstraction_sufficiency",
                                    "uncertainty_propagation",
                                    "branch_orientation",
                                    "countermodel_resistance",
                                )
                            },
                            "bridge_obligations": [
                                {
                                    "claim": "the source energy expression determines the requested output",
                                    "carrier": "BlindFixture.reportedEnergyResult",
                                    "status": "covered",
                                    "evidence": "the carrier is linked by the reporting theorem",
                                }
                            ],
                            "source_contract": provenance,
                            "blind_review_certificate": normalized_review,
                        },
                    }
                },
            },
        )
        self._write_json(
            proof_gate,
            {
                "version": 2,
                "targets": {
                    "Problems/T1A1.lean": {
                        "status": "solved",
                        "reason": "the target is proved",
                        "evidence": "the declaration compiles with the bound result contracts",
                        "redraft_kind": "not_applicable",
                        "proof_review_schema_version": 1,
                        "proof_review_route": "solved",
                        "source_contract": provenance,
                        "blind_review_certificate": normalized_review,
                    }
                },
            },
        )

        payload_files = {
            "IChO2026Problems.lean": self._sha256(project / "IChO2026Problems.lean"),
            "IChO2026Chem/Reporting.lean": self._sha256(reporting_module),
            "icho_2026_source/image/T1_page-1.png": self._sha256(image),
            "icho_2026_source/questions_only.jsonl": self._sha256(bundle),
            "icho_2026_source/raw/theory_problem.pdf": self._sha256(problem_pdf),
        }
        seed = project / "isolation_manifest.json"
        self._write_json(
            seed,
            {
                "schema_version": 1,
                "protocol": "icho-problem-only-solver-seed-v1",
                "source_revision_disclosed": False,
                "blind_bundle": {
                    "path": "icho_2026_source/questions_only.jsonl",
                    "row_count": 1,
                    "sha256": self._sha256(bundle),
                    "size": len(bundle.read_bytes()),
                },
                "blind_bundle_sha256": self._sha256(bundle),
                "target_ids": [record_id],
                "target_ids_sha256": hashlib.sha256(
                    blind._json_bytes([record_id])
                ).hexdigest(),
                "payload_files": payload_files,
                "payload_sha256": blind._hash_index(payload_files),
                "isolation_claims": {"filesystem": True, "network": False},
            },
        )

        dependency_file = dependency_root / "Mathlib.olean"
        dependency_file.write_bytes(b"trusted-dependency")
        runtime_root = root / "trusted-runtime"
        runtime_root.mkdir()
        runtime = runtime_root / "trusted-lake"
        runtime.write_bytes(b"#!/bin/sh\nexit 0\n")
        runtime.chmod(0o755)
        codex_binary = runtime_root / "codex"
        codex_binary.write_bytes(b"trusted-codex-binary")
        codex_binary.chmod(0o755)
        login_proxy_binary = runtime_root / "run_answer_blind_chatgpt_login_proxy.py"
        login_proxy_binary.write_bytes(b"trusted-login-proxy")
        login_proxy_binary.chmod(0o755)
        stdout_log = controller / "solver.stdout"
        stdout_log.write_bytes(b"solver completed\n")
        invocation_receipt = controller / "solver-invocation.json"
        verifier_receipt = controller / "lean-verifier.json"
        verifier_invocation = controller / "lean-verifier-invocation.json"
        verifier_log = controller / "lean-verifier.log"
        verifier_log.write_bytes(b"verifier completed\n")
        verifier_staging = root / "verifier-staging"
        verifier_staging.mkdir()
        reviewer_staging = root / "reviewer-staging"
        reviewer_staging.mkdir()
        reviewer_staging.chmod(0o700)
        os.chown(reviewer_staging, 1003, 1003)
        sibling_workspace = root / "sibling-workspace"
        sibling_workspace.mkdir()
        verifier_snapshot = root / "verifier-clean-snapshot"
        launch_authorization = controller / "launch-authorization.json"
        model_broker_receipt = controller / "model-broker-ready.json"
        model_broker_transcript = controller / "model-broker-transcript.json"
        artifact_model_broker_receipt = controller / "artifact-model-broker-ready.json"
        artifact_model_broker_transcript = controller / "artifact-model-broker-transcript.json"
        solver_model_broker_receipt = controller / "solver-model-broker-ready.json"
        solver_model_broker_transcript = controller / "solver-model-broker-transcript.json"
        source_review_input = root / "independent-source-first-input"
        artifact_review_input = root / "independent-artifact-review-input"
        source_commitment = controller / "independent-source-first-commitment.json"
        source_records = controller / "independent-source-first-records.json"
        source_review_invocation = controller / "independent-source-first-invocation.json"
        artifact_review_receipt = controller / "independent-artifact-review.json"
        artifact_review_invocation = controller / "independent-artifact-review-invocation.json"
        review_aggregate = controller / "independent-review-aggregate.json"
        source_review_log = controller / "independent-source-first.log"
        artifact_review_log = controller / "independent-artifact-review.log"
        source_review_log.write_bytes(b"independent source-first Review completed\n")
        artifact_review_log.write_bytes(b"independent artifact Review completed\n")
        seal = controller / "freeze-seal.json"

        fixture: dict[str, object] = {
            "root": root,
            "project": project,
            "state": state,
            "candidate_dir": candidates,
            "candidate": candidate,
            "target": target,
            "report": report,
            "chapter": chapter,
            "image": image,
            "problem_pdf": problem_pdf,
            "bundle": bundle,
            "bundle_row": bundle_row,
            "seed": seed,
            "formal_gate": formal_gate,
            "proof_gate": proof_gate,
            "dependency_root": dependency_root,
            "runtime": runtime,
            "codex_binary": codex_binary,
            "login_proxy_binary": login_proxy_binary,
            "runtime_root": runtime_root,
            "stdout_log": stdout_log,
            "invocation_receipt": invocation_receipt,
            "verifier_receipt": verifier_receipt,
            "verifier_invocation": verifier_invocation,
            "verifier_log": verifier_log,
            "verifier_staging": verifier_staging,
            "verifier_snapshot": verifier_snapshot,
            "reviewer_staging": reviewer_staging,
            "sibling_workspace": sibling_workspace,
            "launch_authorization": launch_authorization,
            "model_broker_receipt": model_broker_receipt,
            "model_broker_transcript": model_broker_transcript,
            "artifact_model_broker_receipt": artifact_model_broker_receipt,
            "artifact_model_broker_transcript": artifact_model_broker_transcript,
            "solver_model_broker_receipt": solver_model_broker_receipt,
            "solver_model_broker_transcript": solver_model_broker_transcript,
            "source_review_input": source_review_input,
            "review_input": artifact_review_input,
            "source_commitment": source_commitment,
            "source_records": source_records,
            "source_review_invocation": source_review_invocation,
            "review_receipt": artifact_review_receipt,
            "review_invocation": artifact_review_invocation,
            "review_aggregate": review_aggregate,
            "source_review_log": source_review_log,
            "review_log": artifact_review_log,
            "controller_seal": seal,
            "id": record_id,
            "blind_hash": blind_hash,
        }
        self._refresh_controller_bindings(fixture)
        return fixture

    def _refresh_controller_bindings(
        self, fixture: dict[str, object], *, scope_kind: str = "full"
    ) -> None:
        project = Path(fixture["project"])
        dependency_root = Path(fixture["dependency_root"])
        candidate_path = Path(fixture["candidate"])
        target = Path(fixture["target"])
        record_id = str(fixture["id"])
        runtime = Path(fixture["runtime"])
        runtime_root = Path(fixture["runtime_root"])
        dependency_files = blind._regular_file_inventory(
            dependency_root, label="test dependencies"
        )
        dependency_digest = blind._hash_index(dependency_files)
        runtime_files = blind._regular_file_inventory(
            runtime_root,
            label="test runtime",
            exclude_roots=(dependency_root,),
        )
        runtime_digest = blind._hash_index(runtime_files)
        snapshot_files = blind._project_snapshot_inventory(
            project, dependency_root=dependency_root
        )
        snapshot_digest = blind._hash_index(snapshot_files)
        verifier_snapshot_path = Path(fixture["verifier_snapshot"])
        if verifier_snapshot_path.exists():
            shutil.rmtree(verifier_snapshot_path)
        verifier_snapshot = blind.create_blind_verifier_snapshot(
            project=project,
            dependency_root=dependency_root,
            output=verifier_snapshot_path,
        )
        system_path = Path("/etc/hosts").resolve()
        system_files = {str(system_path): self._sha256(system_path)}
        safe_devices = [
            str(Path(path).resolve())
            for path in ("/dev/null", "/dev/zero", "/dev/random", "/dev/urandom")
            if Path(path).exists()
        ]
        verifier_invocation_path = Path(fixture["verifier_invocation"])
        verifier_staging = Path(fixture["verifier_staging"])
        reviewer_staging = Path(fixture["reviewer_staging"])
        sibling_workspace = Path(fixture["sibling_workspace"])
        required_probe_paths = [
            "/root", "/tmp", "/var/tmp", "/dev/shm", "/proc/1/environ",
            str(verifier_invocation_path.parent), str(sibling_workspace),
        ]
        receipt_probe_paths = [
            *required_probe_paths, f"/proc/{os.getpid()}/environ",
        ]
        authorization = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "landlock_launch_authorization",
            "variant": "gpt",
            "run_id": "run-001",
            "workspace": str(project),
            "runtime_root": str(runtime_root),
            "dependency_root": str(dependency_root),
            "system_inventory": {
                "files": system_files,
                "files_sha256": blind._hash_index(system_files),
            },
            "system_read_only_paths": [str(system_path), *safe_devices],
            "solver_external_read_write_paths": [],
            "verifier_external_read_write_paths": [str(verifier_staging)],
            "reviewer_external_read_write_paths": [str(reviewer_staging)],
            "required_denied_probe_paths": required_probe_paths,
            "allowed_model_broker_tcp_port": 18080,
        }
        authorization_path = Path(fixture["launch_authorization"])
        self._write_json(authorization_path, authorization)
        authorization_sha = self._sha256(authorization_path)

        broker_ready = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "model_broker_ready",
            "variant": "gpt",
            "run_id": "run-001",
            "listen_url": "http://127.0.0.1:18080",
            "upstream_origin": "https://chatgpt.com",
            "allowed_model": "gpt-5.6-sol",
            "request_profile": blind._STRUCTURED_REVIEW_PROFILE,
            "public_dummy_key_sha256": hashlib.sha256(
                b"answer-blind-public-dummy-token"
            ).hexdigest(),
            "broker_uid": 1002,
            "broker_binary_sha256": self._sha256(runtime),
            "started_at": "2026-08-12T00:00:00Z",
        }
        broker_ready_path = Path(fixture["model_broker_receipt"])
        self._write_json(broker_ready_path, broker_ready)
        broker_ready_path.chmod(0o400)
        broker_ready_sha = self._sha256(broker_ready_path)
        broker_transcript = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "model_broker_transcript",
            "variant": "gpt",
            "run_id": "run-001",
            "request_profile": blind._STRUCTURED_REVIEW_PROFILE,
            "ready_receipt_sha256": broker_ready_sha,
            "request_count": 1,
            "request_response_chain_sha256": hashlib.sha256(
                b"request-and-response-hashes-only"
            ).hexdigest(),
            "started_at": "2026-08-12T00:00:00Z",
            "stopped_at": "2026-08-12T00:01:00Z",
            "broker_stopped": True,
        }
        broker_transcript_path = Path(fixture["model_broker_transcript"])
        self._write_json(broker_transcript_path, broker_transcript)
        broker_transcript_path.chmod(0o400)
        broker_transcript_sha = self._sha256(broker_transcript_path)
        solver_broker_ready = {
            **broker_ready,
            "request_profile": blind._STRUCTURED_REQUEST_PROFILE,
            "started_at": "2026-08-12T00:00:10Z",
        }
        solver_broker_ready_path = Path(fixture["solver_model_broker_receipt"])
        self._write_json(solver_broker_ready_path, solver_broker_ready)
        solver_broker_ready_path.chmod(0o400)
        solver_broker_ready_sha = self._sha256(solver_broker_ready_path)
        solver_broker_transcript = {
            **broker_transcript,
            "request_profile": blind._STRUCTURED_REQUEST_PROFILE,
            "ready_receipt_sha256": solver_broker_ready_sha,
            "request_count": 1,
            "request_response_chain_sha256": hashlib.sha256(
                b"solver-request-and-response-hashes-only"
            ).hexdigest(),
            "started_at": "2026-08-12T00:00:10Z",
            "stopped_at": "2026-08-12T00:00:50Z",
        }
        solver_broker_transcript_path = Path(
            fixture["solver_model_broker_transcript"]
        )
        self._write_json(solver_broker_transcript_path, solver_broker_transcript)
        solver_broker_transcript_path.chmod(0o400)
        solver_broker_transcript_sha = self._sha256(
            solver_broker_transcript_path
        )
        artifact_broker_ready = {
            **broker_ready,
            "started_at": "2026-08-12T00:02:00Z",
        }
        artifact_broker_ready_path = Path(
            fixture["artifact_model_broker_receipt"]
        )
        self._write_json(artifact_broker_ready_path, artifact_broker_ready)
        artifact_broker_ready_path.chmod(0o400)
        artifact_broker_ready_sha = self._sha256(artifact_broker_ready_path)
        artifact_broker_transcript = {
            **broker_transcript,
            "ready_receipt_sha256": artifact_broker_ready_sha,
            "request_response_chain_sha256": hashlib.sha256(
                b"artifact-review-request-and-response-hashes-only"
            ).hexdigest(),
            "started_at": "2026-08-12T00:02:00Z",
            "stopped_at": "2026-08-12T00:03:00Z",
        }
        artifact_broker_transcript_path = Path(
            fixture["artifact_model_broker_transcript"]
        )
        self._write_json(
            artifact_broker_transcript_path, artifact_broker_transcript
        )
        artifact_broker_transcript_path.chmod(0o400)
        artifact_broker_transcript_sha = self._sha256(
            artifact_broker_transcript_path
        )

        candidate, candidate_payload = blind._read_json(
            candidate_path, label="test candidate"
        )
        target_payload = target.read_bytes()
        provenance = source_contract_provenance(
            build_review_source_contract(project_path=project, target=target)
        )
        checks = [
            {
                "role": item["role"],
                "declaration": item["declaration"],
                "normalized_type_sha256": item["expected_type_sha256"],
                "result_payload_sha256": item["result_payload_sha256"],
                "axioms": [],
                "compiled": True,
            }
            for item in candidate["lean_result_contracts"]
        ]
        verifier = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": blind.VERIFIER_PHASE,
            "evaluation_mode": "answer_blind",
            "verifier_uid": 1001,
            "network_answer_blind": False,
            "runtime_executable": {
                "path": str(runtime),
                "sha256": self._sha256(runtime),
            },
            "dependency_inventory_sha256": dependency_digest,
            "runtime_inventory_sha256": runtime_digest,
            "snapshot_inventory_sha256": snapshot_digest,
            "scope_ids": [record_id],
            "records": [
                {
                    "id": record_id,
                    "target": target.relative_to(project).as_posix(),
                    "target_sha256": hashlib.sha256(target_payload).hexdigest(),
                    "candidate": candidate_path.relative_to(project).as_posix(),
                    "candidate_sha256": hashlib.sha256(candidate_payload).hexdigest(),
                    "source_contract_sha256": hashlib.sha256(
                        blind._json_bytes(provenance)
                    ).hexdigest(),
                    "result_contracts_sha256": hashlib.sha256(
                        blind._json_bytes(candidate["lean_result_contracts"])
                    ).hexdigest(),
                    "checks": checks,
                }
            ],
            "compiled": True,
            "stdout_sha256": hashlib.sha256(b"verifier stdout").hexdigest(),
            "stderr_sha256": hashlib.sha256(b"").hexdigest(),
        }
        verifier_path = Path(fixture["verifier_receipt"])
        self._write_json(verifier_path, verifier)
        verifier_log = Path(fixture["verifier_log"])
        common_probes = {
            path: {"open_read_denied": True, "errno": 13}
            for path in receipt_probe_paths
        }
        def quiescence(uid: int) -> dict[str, object]:
            return {
                "mechanism": "dedicated_uid_prlimit_pidfd_v1",
                "uid": uid,
                "rlimit_nproc": 64,
                "quiescent_before": True,
                "before_pids": [],
                "prlimit_zero_applied": True,
                "pidfd_kill_used": False,
                "kill_rounds": 0,
                "quiet_period_ms": 500,
                "after_pids": [],
                "quiescent_after": True,
            }
        verifier_wrapper = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "lean_verifier_invocation",
            "verifier_uid": 1001,
            "command_argv": [
                str(runtime_root / "trusted-lake"),
                "blind-verify-lean", "--project", str(verifier_snapshot_path),
                "--candidate-dir", "blind_candidates",
                "--output", str(verifier_path),
                "--runtime-executable", str(runtime),
                "--runtime-root", str(runtime_root),
                "--dependency-root", str(dependency_root),
                "--expected-dependency-inventory-sha256", dependency_digest,
                "--expected-runtime-inventory-sha256", runtime_digest,
                "--expected-snapshot-inventory-sha256", snapshot_digest,
                "--timeout-s", "300", "--scope-id", record_id,
            ],
            "exit_code": 0,
            "solver_stopped": True,
            "descendants_stopped": True,
            "network_answer_blind": False,
            "dependency_inventory_sha256": dependency_digest,
            "runtime_inventory_sha256": runtime_digest,
            "snapshot_inventory_sha256": snapshot_digest,
            "snapshot_root": str(verifier_snapshot_path),
            "dedicated_uid_quiescence": quiescence(1001),
            "verifier_receipt": {
                "path": str(verifier_path),
                "sha256": self._sha256(verifier_path),
            },
            "stdout_log": {
                "path": str(verifier_log),
                "sha256": self._sha256(verifier_log),
                "size": len(verifier_log.read_bytes()),
            },
        }
        self._write_json(verifier_invocation_path, verifier_wrapper)
        verifier_invocation_path.chmod(0o400)

        projection = blind._structured_problem_projection(fixture["bundle_row"])
        projection_path = controller = Path(fixture["controller_seal"]).parent
        projection_path = controller / f"gpt-{record_id}-problem-projection.json"
        self._write_json(projection_path, projection)
        projection_path.chmod(0o400)
        gpt_images, kimi_images = blind._structured_image_parts(
            project=project, row=fixture["bundle_row"]
        )
        request = blind._structured_provider_request(
            variant="gpt", model_id="gpt-5.6-sol", projection=projection,
            gpt_images=gpt_images, kimi_images=kimi_images, diagnostics=[],
        )
        request_path = controller / f"gpt-{record_id}-attempt-1-request.json"
        self._write_json(request_path, request)
        request_path.chmod(0o400)
        submission = {
            "raw_result": candidate["raw_result"],
            "reported_result": {
                field: candidate["reported_result"][field]
                for field in ("value", "text", "lean_expression", "unit")
            },
            "candidate_domain_derivation": candidate[
                "candidate_domain_provenance"
            ]["derivation"],
            "lean_declarations": candidate["lean_declarations"],
            "lean_source": target_payload.decode("utf-8"),
            "blueprint": Path(fixture["chapter"]).read_text(encoding="utf-8"),
        }
        submission_path = controller / f"gpt-{record_id}-attempt-1-submission.json"
        self._write_json(submission_path, submission)
        submission_path.chmod(0o400)
        response, solver_sse = _gpt_response_and_sse(
            blind._json_bytes(submission).decode("utf-8").rstrip("\n"),
            suffix="solver_fixture",
        )
        response_path = controller / f"gpt-{record_id}-attempt-1-response.json"
        self._write_json(response_path, response)
        response_path.chmod(0o400)
        staged = {}
        staged_payloads = {
            "candidate": candidate_payload,
            "lean": target_payload,
            "blueprint": Path(fixture["chapter"]).read_bytes(),
        }
        for name, payload in staged_payloads.items():
            path = controller / f"gpt-{record_id}-attempt-1-stage-{name}"
            path.write_bytes(payload)
            path.chmod(0o400)
            staged[name] = {"path": str(path), "sha256": self._sha256(path)}
        proxy_normalized = controller / "gpt-proxy-normalized-response.json"
        proxy_normalized.write_bytes(response_path.read_bytes())
        proxy_normalized.chmod(0o400)
        proxy_sse = controller / "gpt-proxy-upstream.sse"
        proxy_sse.write_bytes(solver_sse)
        proxy_sse.chmod(0o400)
        proxy_last = controller / "gpt-proxy-last-message.json"
        self._write_json(proxy_last, submission)
        proxy_last.chmod(0o400)
        proxy_jsonl = controller / "gpt-proxy-codex.jsonl"
        proxy_event = {
            "type": "item.completed",
            "item": {
                "type": "agent_message",
                "text": blind._json_bytes(submission).decode().rstrip("\n"),
            },
        }
        proxy_events = (
            {"type": "thread.started", "thread_id": "solver-fixture"},
            {"type": "item.completed", "item": {
                "id": "item_0", "type": "error",
                "message": blind._CODEX_DISABLED_HOST_CONFIRMATION,
            }},
            {"type": "turn.started"},
            proxy_event,
        )
        proxy_jsonl.write_bytes(b"".join(
            blind._json_bytes(item) for item in proxy_events
        ))
        proxy_jsonl.chmod(0o400)
        proxy_stderr = controller / "gpt-proxy-codex.stderr"
        proxy_stderr.write_bytes(b"fixture diagnostic\n")
        proxy_stderr.chmod(0o400)
        proxy_receipt_path = controller / "gpt-login-proxy-receipt.json"
        fixture["solver_proxy_receipt"] = proxy_receipt_path
        proxy_receipt = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "chatgpt_login_proxy_exchange",
            "variant": "gpt",
            "run_id": "run-001",
            "target_id": record_id,
            "attempt": 1,
            "model_id": "gpt-5.6-sol",
            "adapter": "chatgpt_login_proxy_v1",
            "proxy_binary_sha256": self._sha256(
                Path(fixture["login_proxy_binary"])
            ),
            "codex_binary": {
                "path": str(Path(fixture["codex_binary"])),
                "sha256": self._sha256(Path(fixture["codex_binary"])),
            },
            "codex_version": "codex-cli 0.test",
            "command_argv": [
                "codex", "exec", "--json", "--ephemeral",
                "-c", "features.code_mode.enabled=false",
                "-c", "features.code_mode_host=false",
            ],
            "caller_body_sha256": "a" * 64,
            "pre_registered_request": {
                "path": str(request_path), "sha256": self._sha256(request_path),
            },
            "upstream_origin": "https://chatgpt.com",
            "upstream_status": 200,
            "upstream_raw_sse": {
                "path": str(proxy_sse), "sha256": self._sha256(proxy_sse),
            },
            "normalized_response": {
                "path": str(proxy_normalized),
                "sha256": self._sha256(proxy_normalized),
            },
            "caller_header_names": ["authorization", "chatgpt-account-id"],
            "forwarded_header_names": [
                "accept", "authorization", "chatgpt-account-id", "content-type",
            ],
            "completed_event_count": 1,
            "codex_exit_code": 0,
            "codex_jsonl": {
                "path": str(proxy_jsonl), "sha256": self._sha256(proxy_jsonl),
            },
            "codex_stderr": {
                "path": str(proxy_stderr), "sha256": self._sha256(proxy_stderr),
            },
            "codex_last_message": {
                "path": str(proxy_last), "sha256": self._sha256(proxy_last),
            },
            "tool_events": 0,
        }
        self._write_json(proxy_receipt_path, proxy_receipt)
        proxy_receipt_path.chmod(0o400)
        proxy_locator = {
            "path": str(proxy_receipt_path),
            "sha256": self._sha256(proxy_receipt_path),
        }
        artifact_map = {
            "candidate": {
                "path": candidate_path.relative_to(project).as_posix(),
                "sha256": hashlib.sha256(candidate_payload).hexdigest(),
            },
            "lean": {
                "path": target.relative_to(project).as_posix(),
                "sha256": hashlib.sha256(target_payload).hexdigest(),
            },
            "blueprint": {
                "path": Path(fixture["chapter"]).relative_to(project).as_posix(),
                "sha256": self._sha256(Path(fixture["chapter"])),
            },
        }
        attempt = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "structured_solver_attempt",
            "variant": "gpt",
            "model_family": "openai",
            "model_id": "gpt-5.6-sol",
            "run_id": "run-001",
            "target_id": record_id,
            "attempt": 1,
            "previous_attempt_sha256": None,
            "adapter": "chatgpt_login_proxy_v1",
            "adapter_provenance": {
                "proxy_receipt": proxy_locator,
                "normalized_response_sha256": self._sha256(response_path),
                "upstream_raw_sse_sha256": self._sha256(proxy_sse),
                "event_count": 4,
            },
            "request_profile": blind._STRUCTURED_REQUEST_PROFILE,
            "tools_enabled": False,
            "store": False,
            "problem_projection_sha256": self._sha256(projection_path),
            "prior_diagnostics_sha256": hashlib.sha256(
                blind._json_bytes([])
            ).hexdigest(),
            "request": {"path": str(request_path), "sha256": self._sha256(request_path)},
            "response": {"path": str(response_path), "sha256": self._sha256(response_path)},
            "submission": {
                "path": str(submission_path), "sha256": self._sha256(submission_path),
            },
            "constructed_candidate_sha256": self._sha256(candidate_path),
            "staged_artifacts": staged,
            "status": "accepted",
            "diagnostics": [],
            "artifacts": artifact_map,
        }
        attempt["attempt_chain_sha256"] = hashlib.sha256(
            bytes.fromhex("0" * 64) + blind._json_bytes(attempt)
        ).hexdigest()
        invocation_path = Path(fixture["invocation_receipt"])
        self._write_json(invocation_path, attempt)
        invocation_path.chmod(0o400)
        aggregate_path = invocation_path.with_name("structured-solver-aggregate.json")
        aggregate = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "structured_solver_aggregate",
            "variant": "gpt",
            "model_family": "openai",
            "model_id": "gpt-5.6-sol",
            "run_id": "run-001",
            "adapter": "chatgpt_login_proxy_v1",
            "request_profile": blind._STRUCTURED_REQUEST_PROFILE,
            "tools_enabled": False,
            "store": False,
            "scope_ids": [record_id],
            "bundle": {
                "path": str(Path(fixture["bundle"]).resolve()),
                "sha256": self._sha256(Path(fixture["bundle"])),
                "row_count": 1,
                "ids": [record_id],
            },
            "controller_binary_sha256": self._sha256(runtime),
            "transport": {
                "kind": "chatgpt_login_proxy_v1",
                "exchanges": [proxy_locator],
                "exchange_chain_sha256": hashlib.sha256(
                    bytes.fromhex("0" * 64)
                    + bytes.fromhex(proxy_locator["sha256"])
                ).hexdigest(),
            },
            "targets": [{
                "id": record_id,
                "source_report": {
                    "path": str(Path(fixture["report"]).resolve()),
                    "sha256": self._sha256(Path(fixture["report"])),
                },
                "adapter": "chatgpt_login_proxy_v1",
                "problem_projection_sha256": self._sha256(projection_path),
                "prepared_blueprint": None,
                "attempts": [{
                    "path": str(invocation_path),
                    "sha256": self._sha256(invocation_path),
                }],
                "accepted_attempt": 1,
                "final_artifacts": artifact_map,
                "target_chain_sha256": attempt["attempt_chain_sha256"],
            }],
            "all_targets_finalized": True,
            "request_count": 1,
            "request_response_chain_sha256": hashlib.sha256(
                bytes.fromhex("0" * 64)
                + bytes.fromhex(proxy_locator["sha256"])
            ).hexdigest(),
        }
        self._write_json(aggregate_path, aggregate)
        aggregate_path.chmod(0o400)
        fixture["invocation_aggregate"] = aggregate_path
        fixture["structured_projection"] = projection_path
        fixture["structured_request"] = request_path
        fixture["structured_response"] = response_path
        fixture["structured_submission"] = submission_path

        source_review_input = Path(fixture["source_review_input"])
        artifact_review_input = Path(fixture["review_input"])
        for review_root in (source_review_input, artifact_review_input):
            if review_root.exists():
                shutil.rmtree(review_root)
            review_root.mkdir()
        report_relative = Path(fixture["report"]).relative_to(project).as_posix()
        image_relative = Path(fixture["image"]).relative_to(project).as_posix()
        source_record_relative = f"{blind._SOURCE_FIRST_RECORD_DIRECTORY}/{record_id}.json"
        self._write_json(
            source_review_input / source_record_relative,
            blind._source_first_projection(fixture["bundle_row"]),
        )
        source_image = source_review_input / image_relative
        source_image.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(Path(fixture["image"]), source_image)
        source_input_files = blind._regular_file_inventory(
            source_review_input, label="test source-first Review input"
        )
        source_input_digest = blind._hash_index(source_input_files)
        source_review_projection, source_gpt_images, source_kimi_images = (
            blind._structured_review_projection(
                root=source_review_input, files=source_input_files,
                scope_ids=[record_id], source_first=True,
                source_records_sha256=None,
            )
        )
        source_projection_sha = hashlib.sha256(
            blind._json_bytes(source_review_projection)
        ).hexdigest()
        requested_outputs = fixture["bundle_row"]["requested_outputs"]
        committed_output = {
            **requested_outputs[0],
            "derivation_step_ids": ["derive-energy"],
            "result_spec": {
                "kind": "numeric",
                "status": "derived",
                "raw_expression": "7043 * 10^9 from problem-stated power and duration",
                "raw_value": "7.043e12",
                "certified_interval": {
                    "lower": "7.042e12",
                    "upper": "7.044e12",
                },
                "reported_value": "7.04e12",
                "reporting_quantum": "1e10",
                "tie_rule": "half_away_from_zero",
            },
        }
        source_record = {
            "id": record_id,
            "blind_record_sha256": fixture["blind_hash"],
            "source_record_sha256": self._sha256(
                source_review_input / source_record_relative
            ),
            "requested_outputs_sha256": hashlib.sha256(
                blind._json_bytes(requested_outputs)
            ).hexdigest(),
            "status": "passed",
            "givens": [
                {
                    "id": "given-question",
                    "source_locator": "source.current_question",
                    "fact": "the problem asks for energy delivered per day",
                }
            ],
            "derivation_steps": [
                {
                    "id": "derive-energy",
                    "claim": "the requested energy follows from problem-stated data",
                    "depends_on": ["given-question"],
                    "justification": "apply the source-stated physical relation",
                }
            ],
            "output_commitments": [committed_output],
        }
        source_records_semantic = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "independent_source_first_records",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "variant": "gpt",
            "model_family": "openai",
            "model_id": "gpt-5.6-sol",
            "run_id": "run-001",
            "request_profile": blind._STRUCTURED_REVIEW_PROFILE,
            "review_input_inventory_sha256": source_input_digest,
            "review_projection_sha256": source_projection_sha,
            "scope_ids": [record_id],
            "records": [source_record],
        }
        source_records_path = Path(fixture["source_records"])
        self._write_json(source_records_path, source_records_semantic)
        source_records_path.chmod(0o400)
        source_records_sha = self._sha256(source_records_path)
        source_semantic = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "independent_source_first_commitment",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "variant": "gpt",
            "model_family": "openai",
            "model_id": "gpt-5.6-sol",
            "run_id": "run-001",
            "request_profile": blind._STRUCTURED_REVIEW_PROFILE,
            "snapshot_inventory_sha256": snapshot_digest,
            "review_input_inventory_sha256": source_input_digest,
            "review_projection_sha256": source_projection_sha,
            "source_first_precommit_sha256": "0" * 64,
            "source_records_sha256": source_records_sha,
            "scope_ids": [record_id],
            "records": [source_record],
        }
        source_commitment_path = Path(fixture["source_commitment"])
        source_commitment_path.chmod(0o600) if source_commitment_path.exists() else None
        self._write_json(source_commitment_path, source_semantic)
        source_commitment_path.chmod(0o400)
        source_commitment_sha = self._sha256(source_commitment_path)
        source_model_submission = blind._minimal_review_submission_from_semantic(
            source_semantic, source_first=True
        )
        source_model_submission_path = controller / "source-first-model-submission.json"
        self._write_json(source_model_submission_path, source_model_submission)
        source_model_submission_path.chmod(0o400)

        seed_value = json.loads(Path(fixture["seed"]).read_text(encoding="utf-8"))
        review_relatives = set(seed_value["payload_files"])
        review_relatives.update(
            {
                blind.SEED_MANIFEST,
                blind.CONFIG_FILE,
                blind.MCP_FILE,
                blind.PROTOCOL_FILE,
                blind.AGENTS_FILE,
                candidate_path.relative_to(project).as_posix(),
                target.relative_to(project).as_posix(),
                report_relative,
                Path(fixture["chapter"]).relative_to(project).as_posix(),
            }
        )
        for relative in sorted(review_relatives):
            source = project / relative
            destination = artifact_review_input / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        shutil.copyfile(
            source_records_path,
            artifact_review_input / blind._SOURCE_COMMITMENT_INPUT,
        )
        artifact_input_files = blind._regular_file_inventory(
            artifact_review_input, label="test artifact Review input"
        )
        artifact_input_digest = blind._hash_index(artifact_input_files)
        artifact_review_projection, artifact_gpt_images, artifact_kimi_images = (
            blind._structured_review_projection(
                root=artifact_review_input, files=artifact_input_files,
                scope_ids=[record_id], source_first=False,
                source_records_sha256=source_records_sha,
            )
        )
        artifact_projection_sha = hashlib.sha256(
            blind._json_bytes(artifact_review_projection)
        ).hexdigest()
        formal_state_raw = json.loads(
            Path(fixture["formal_gate"]).read_text(encoding="utf-8")
        )["targets"]["Problems/T1A1.lean"]["certificate"]
        formal_state = dict(
            blind._formal_review_certificate({"certificate": formal_state_raw})
        )
        proof_state = json.loads(
            Path(fixture["proof_gate"]).read_text(encoding="utf-8")
        )["targets"]["Problems/T1A1.lean"]
        proof_certificate = {
            field: proof_state[field]
            for field in blind._INDEPENDENT_PROOF_CERTIFICATE_FIELDS
        }
        review_semantic = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "independent_artifact_review",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "variant": "gpt",
            "model_family": "openai",
            "model_id": "gpt-5.6-sol",
            "run_id": "run-001",
            "request_profile": blind._STRUCTURED_REVIEW_PROFILE,
            "snapshot_inventory_sha256": snapshot_digest,
            "review_input_inventory_sha256": artifact_input_digest,
            "review_projection_sha256": artifact_projection_sha,
            "source_records_sha256": source_records_sha,
            "scope_ids": [record_id],
            "records": [
                {
                    "id": record_id,
                    "target": target.relative_to(project).as_posix(),
                    "target_sha256": self._sha256(target),
                    "candidate_sha256": self._sha256(candidate_path),
                    "source_report_sha256": self._sha256(Path(fixture["report"])),
                    "blueprint_sha256": self._sha256(Path(fixture["chapter"])),
                    "source_contract_sha256": hashlib.sha256(
                        blind._json_bytes(provenance)
                    ).hexdigest(),
                    "requested_outputs_sha256": hashlib.sha256(
                        blind._json_bytes(fixture["bundle_row"]["requested_outputs"])
                    ).hexdigest(),
                    "source_commitment_record_sha256": hashlib.sha256(
                        blind._json_bytes(source_record)
                    ).hexdigest(),
                    "source_alignment": {
                        "status": "passed",
                        "evidence": "the Lean carriers implement the committed derivation and outputs",
                    },
                    "formalization_status": "passed",
                    "formalization_certificate": formal_state,
                    "proof_status": "solved",
                    "proof_certificate": proof_certificate,
                }
            ],
        }
        review_receipt_path = Path(fixture["review_receipt"])
        self._write_json(review_receipt_path, review_semantic)
        review_receipt_path.chmod(0o400)
        artifact_model_submission = blind._minimal_review_submission_from_semantic(
            review_semantic, source_first=False
        )
        artifact_model_submission_path = controller / "artifact-model-submission.json"
        self._write_json(artifact_model_submission_path, artifact_model_submission)
        artifact_model_submission_path.chmod(0o400)
        review_adapter = {
            "provider_api": "openai_responses_v1",
            "response_extractor": "openai_responses_single_json_text_v1",
        }
        source_request = blind._structured_review_request(
            variant="gpt", model_id="gpt-5.6-sol",
            projection=source_review_projection, gpt_images=source_gpt_images,
            kimi_images=source_kimi_images, source_first=True,
        )
        source_request_path = controller / "source-first-review-request.json"
        self._write_json(source_request_path, source_request)
        source_request_path.chmod(0o400)
        source_response, _source_sse = _gpt_response_and_sse(
            blind._json_bytes(source_model_submission).decode().rstrip("\n"),
            suffix="source_first_review",
        )
        source_response_path = controller / "source-first-review-response.json"
        self._write_json(source_response_path, source_response)
        source_response_path.chmod(0o400)

        def review_proxy_transport(
            *, pass_name: str, target_id: str, request_path: Path,
            response_path: Path, model_submission: dict[str, object],
        ) -> tuple[dict[str, object], str]:
            normalized_path = controller / f"{pass_name}-normalized-response.json"
            normalized_path.write_bytes(response_path.read_bytes())
            normalized_path.chmod(0o400)
            expected_response, sse_payload = _gpt_response_and_sse(
                blind._json_bytes(model_submission).decode().rstrip("\n"),
                suffix=pass_name.replace("-", "_"),
            )
            self.assertEqual(
                response_path.read_bytes(), blind._json_bytes(expected_response),
            )
            sse_path = controller / f"{pass_name}-upstream.sse"
            sse_path.write_bytes(sse_payload)
            sse_path.chmod(0o400)
            last_path = controller / f"{pass_name}-last-message.json"
            self._write_json(last_path, model_submission)
            last_path.chmod(0o400)
            jsonl_path = controller / f"{pass_name}-codex.jsonl"
            jsonl_path.write_bytes(
                blind._json_bytes({
                    "type": "thread.started", "thread_id": f"{pass_name}-fixture",
                })
                + blind._json_bytes({
                    "type": "item.completed", "item": {
                        "id": "item_0", "type": "error",
                        "message": blind._CODEX_DISABLED_HOST_CONFIRMATION,
                    },
                })
                + blind._json_bytes({"type": "turn.started"})
                + blind._json_bytes({
                    "type": "item.completed",
                    "item": {
                        "type": "agent_message",
                        "text": blind._json_bytes(model_submission).decode().rstrip("\n"),
                    },
                })
            )
            jsonl_path.chmod(0o400)
            stderr_path = controller / f"{pass_name}-codex.stderr"
            stderr_path.write_bytes(b"fixture diagnostic\n")
            stderr_path.chmod(0o400)
            receipt_path = controller / f"{pass_name}-login-proxy-receipt.json"
            receipt = {
                "schema_version": 1, "protocol": blind.PROTOCOL,
                "phase": "chatgpt_login_proxy_exchange", "variant": "gpt",
                "run_id": "run-001", "target_id": target_id, "attempt": 1,
                "model_id": "gpt-5.6-sol", "adapter": "chatgpt_login_proxy_v1",
                "proxy_binary_sha256": self._sha256(
                    Path(fixture["login_proxy_binary"])
                ),
                "codex_binary": {
                    "path": str(Path(fixture["codex_binary"])),
                    "sha256": self._sha256(Path(fixture["codex_binary"])),
                },
                "codex_version": "codex-cli 0.test",
                "command_argv": [
                    "codex", "exec", "--json", "--ephemeral",
                    "-c", "features.code_mode.enabled=false",
                    "-c", "features.code_mode_host=false",
                ],
                "caller_body_sha256": "b" * 64,
                "pre_registered_request": {
                    "path": str(request_path), "sha256": self._sha256(request_path),
                },
                "upstream_origin": "https://chatgpt.com", "upstream_status": 200,
                "upstream_raw_sse": {
                    "path": str(sse_path), "sha256": self._sha256(sse_path),
                },
                "normalized_response": {
                    "path": str(normalized_path),
                    "sha256": self._sha256(normalized_path),
                },
                "caller_header_names": ["authorization", "chatgpt-account-id"],
                "forwarded_header_names": [
                    "accept", "authorization", "chatgpt-account-id", "content-type",
                ],
                "completed_event_count": 1, "codex_exit_code": 0,
                "codex_jsonl": {
                    "path": str(jsonl_path), "sha256": self._sha256(jsonl_path),
                },
                "codex_stderr": {
                    "path": str(stderr_path), "sha256": self._sha256(stderr_path),
                },
                "codex_last_message": {
                    "path": str(last_path), "sha256": self._sha256(last_path),
                },
                "tool_events": 0,
            }
            self._write_json(receipt_path, receipt)
            receipt_path.chmod(0o400)
            locator: dict[str, object] = {
                "path": str(receipt_path), "sha256": self._sha256(receipt_path),
            }
            chain = hashlib.sha256(
                bytes.fromhex("0" * 64) + bytes.fromhex(str(locator["sha256"]))
            ).hexdigest()
            return {
                "kind": "chatgpt_login_proxy_v1", "exchanges": [locator],
                "exchange_chain_sha256": chain,
            }, chain

        source_transport, source_transport_chain = review_proxy_transport(
            pass_name="source-first-review",
            target_id="independent-source-first-review",
            request_path=source_request_path, response_path=source_response_path,
            model_submission=source_model_submission,
        )
        source_wrapper = {
            "schema_version": 1, "protocol": blind.PROTOCOL,
            "phase": "structured_source_first_review_attempt",
            "variant": "gpt", "model_family": "openai",
            "model_id": "gpt-5.6-sol", "run_id": "run-001",
            "request_profile": blind._STRUCTURED_REVIEW_PROFILE,
            "tools_enabled": False, "store": False,
            "scope_ids": [record_id],
            "snapshot_inventory_sha256": snapshot_digest,
            "controller_binary_sha256": self._sha256(runtime),
            "input_inventory": {
                "root": str(source_review_input), "files": source_input_files,
                "files_sha256": source_input_digest,
            },
            "review_projection_sha256": source_projection_sha,
            "adapter_provenance": {
                **review_adapter,
                "response_schema_sha256": hashlib.sha256(blind._json_bytes(
                    blind._structured_review_response_schema(source_first=True)
                )).hexdigest(),
            },
            "adapter": "chatgpt_login_proxy_v1",
            "request": {
                "path": str(source_request_path),
                "sha256": self._sha256(source_request_path),
            },
            "response": {
                "path": str(source_response_path),
                "sha256": self._sha256(source_response_path),
            },
            "model_submission": {
                "path": str(source_model_submission_path),
                "sha256": self._sha256(source_model_submission_path),
            },
            "constructed_semantic_receipt": {
                "path": str(source_commitment_path), "sha256": source_commitment_sha,
            },
            "normalized_response_sha256": self._sha256(source_model_submission_path),
            "transport": source_transport,
            "request_response_chain_sha256": source_transport_chain,
            "status": "accepted",
        }
        precommit_path = controller / "source-first-pre-solver-commitment.json"
        source_precommit = {
            field: source_wrapper[field]
            for field in blind._STRUCTURED_SOURCE_PRECOMMIT_FIELDS
            if field not in {"phase", "finalized_before_solver"}
        }
        source_precommit.update({
            "phase": "structured_source_first_precommit",
            "finalized_before_solver": True,
        })
        self._write_json(precommit_path, source_precommit)
        precommit_path.chmod(0o400)
        precommit_locator = {
            "path": str(precommit_path), "sha256": self._sha256(precommit_path),
        }
        source_semantic["source_first_precommit_sha256"] = precommit_locator[
            "sha256"
        ]
        source_commitment_path.chmod(0o600)
        self._write_json(source_commitment_path, source_semantic)
        source_commitment_path.chmod(0o400)
        source_commitment_sha = self._sha256(source_commitment_path)
        source_wrapper["constructed_semantic_receipt"]["sha256"] = (
            source_commitment_sha
        )
        source_wrapper["source_first_precommit"] = precommit_locator
        source_wrapper["source_records_commitment"] = {
            "path": str(source_records_path), "sha256": source_records_sha,
        }
        source_wrapper_path = Path(fixture["source_review_invocation"])
        self._write_json(source_wrapper_path, source_wrapper)
        source_wrapper_path.chmod(0o400)

        artifact_request = blind._structured_review_request(
            variant="gpt", model_id="gpt-5.6-sol",
            projection=artifact_review_projection, gpt_images=artifact_gpt_images,
            kimi_images=artifact_kimi_images, source_first=False,
        )
        artifact_request_path = controller / "artifact-review-request.json"
        self._write_json(artifact_request_path, artifact_request)
        artifact_request_path.chmod(0o400)
        artifact_response, _artifact_sse = _gpt_response_and_sse(
            blind._json_bytes(artifact_model_submission).decode().rstrip("\n"),
            suffix="artifact_review",
        )
        artifact_response_path = controller / "artifact-review-response.json"
        self._write_json(artifact_response_path, artifact_response)
        artifact_response_path.chmod(0o400)
        artifact_transport, artifact_transport_chain = review_proxy_transport(
            pass_name="artifact-review",
            target_id="independent-artifact-review",
            request_path=artifact_request_path, response_path=artifact_response_path,
            model_submission=artifact_model_submission,
        )
        review_wrapper = {
            **source_wrapper,
            "phase": "structured_artifact_review_attempt",
            "input_inventory": {
                "root": str(artifact_review_input), "files": artifact_input_files,
                "files_sha256": artifact_input_digest,
            },
            "review_projection_sha256": artifact_projection_sha,
            "adapter_provenance": {
                **review_adapter,
                "response_schema_sha256": hashlib.sha256(blind._json_bytes(
                    blind._structured_review_response_schema(source_first=False)
                )).hexdigest(),
            },
            "request": {
                "path": str(artifact_request_path),
                "sha256": self._sha256(artifact_request_path),
            },
            "response": {
                "path": str(artifact_response_path),
                "sha256": self._sha256(artifact_response_path),
            },
            "model_submission": {
                "path": str(artifact_model_submission_path),
                "sha256": self._sha256(artifact_model_submission_path),
            },
            "constructed_semantic_receipt": {
                "path": str(review_receipt_path),
                "sha256": self._sha256(review_receipt_path),
            },
            "normalized_response_sha256": self._sha256(
                artifact_model_submission_path
            ),
            "transport": artifact_transport,
            "request_response_chain_sha256": artifact_transport_chain,
            "source_records_commitment": {
                "path": str(source_records_path), "sha256": source_records_sha,
            },
            "source_first_attempt_sha256": self._sha256(source_wrapper_path),
        }
        review_wrapper.pop("source_first_precommit", None)
        review_invocation_path = Path(fixture["review_invocation"])
        self._write_json(review_invocation_path, review_wrapper)
        review_invocation_path.chmod(0o400)
        review_aggregate_path = Path(fixture["review_aggregate"])
        review_aggregate = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": "structured_independent_review_aggregate",
            "variant": "gpt", "model_family": "openai",
            "model_id": "gpt-5.6-sol", "run_id": "run-001",
            "request_profile": blind._STRUCTURED_REVIEW_PROFILE,
            "tools_enabled": False, "store": False,
            "scope_ids": [record_id],
            "snapshot_inventory_sha256": snapshot_digest,
            "controller_binary_sha256": self._sha256(runtime),
            "source_first_attempt": {
                "path": str(source_wrapper_path),
                "sha256": self._sha256(source_wrapper_path),
            },
            "artifact_review_attempt": {
                "path": str(review_invocation_path),
                "sha256": self._sha256(review_invocation_path),
            },
            "source_commitment_sha256": source_commitment_sha,
            "source_records_sha256": source_records_sha,
            "semantic_review_sha256": self._sha256(review_receipt_path),
            "all_passes_finalized": True,
        }
        self._write_json(review_aggregate_path, review_aggregate)
        review_aggregate_path.chmod(0o400)

        solver_aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
        solver_aggregate["source_first_precommit_sha256"] = precommit_locator[
            "sha256"
        ]
        aggregate_path.chmod(0o600)
        self._write_json(aggregate_path, solver_aggregate)
        aggregate_path.chmod(0o400)
        fixture["source_first_precommit"] = precommit_path

        generated = {
            relative: self._sha256(project / relative)
            for relative in (
                blind.CONFIG_FILE,
                blind.MCP_FILE,
                blind.PROTOCOL_FILE,
                blind.AGENTS_FILE,
            )
        }
        bundle = Path(fixture["bundle"])
        seal = {
            "schema_version": 1,
            "protocol": blind.PROTOCOL,
            "phase": blind.CONTROLLER_PHASE,
            "solver_stopped": True,
            "seed_manifest_sha256": self._sha256(Path(fixture["seed"])),
            "blind_bundle": {
                "path": bundle.relative_to(project).as_posix(),
                "sha256": self._sha256(bundle),
                "row_count": 1,
                "ids": [record_id],
            },
            "freeze_scope": {"kind": scope_kind, "ids": [record_id]},
            "generated_files": generated,
            "dependency_inventory": {
                "root": str(dependency_root),
                "files": dependency_files,
                "files_sha256": dependency_digest,
            },
            "runtime_inventory": {
                "root": str(runtime_root),
                "files": runtime_files,
                "files_sha256": runtime_digest,
            },
            "snapshot_inventory": {
                "files": snapshot_files,
                "files_sha256": snapshot_digest,
            },
            "verifier_snapshot": verifier_snapshot,
            "solver": {
                "model_family": "openai",
                "model_id": "gpt-5.6-sol",
                "run_id": "run-001",
            },
            "isolation": {
                "filesystem_answer_blind": True,
                "network_answer_blind": False,
            },
            "structured_solver_receipt": {
                "path": str(aggregate_path),
                "sha256": self._sha256(aggregate_path),
            },
            "source_first_precommit": precommit_locator,
            "verifier_receipt": {
                "path": str(verifier_invocation_path),
                "sha256": self._sha256(verifier_invocation_path),
            },
            "independent_review_receipt": {
                "path": str(review_aggregate_path),
                "sha256": self._sha256(review_aggregate_path),
            },
        }
        seal_path = Path(fixture["controller_seal"])
        self._write_json(seal_path, seal)
        fixture["controller_seal_sha256"] = self._sha256(seal_path)

    def _reseal_review_proxy(
        self, wrapper: dict[str, object], model_submission: dict[str, object]
    ) -> None:
        transport = wrapper["transport"]
        assert isinstance(transport, dict)
        exchanges = transport["exchanges"]
        assert isinstance(exchanges, list) and len(exchanges) == 1
        proxy_path = Path(exchanges[0]["path"])
        proxy = json.loads(proxy_path.read_text(encoding="utf-8"))
        response_path = Path(wrapper["response"]["path"])
        rebuilt_response, rebuilt_sse = _gpt_response_and_sse(
            blind._json_bytes(model_submission).decode().rstrip("\n"),
            suffix=response_path.stem.replace("-response", "").replace("-", "_"),
        )
        response_path.chmod(0o600)
        self._write_json(response_path, rebuilt_response)
        response_path.chmod(0o400)
        wrapper["response"]["sha256"] = self._sha256(response_path)
        normalized_path = Path(proxy["normalized_response"]["path"])
        normalized_path.chmod(0o600)
        normalized_path.write_bytes(response_path.read_bytes())
        normalized_path.chmod(0o400)
        proxy["normalized_response"]["sha256"] = self._sha256(normalized_path)
        sse_path = Path(proxy["upstream_raw_sse"]["path"])
        sse_path.chmod(0o600)
        sse_path.write_bytes(rebuilt_sse)
        sse_path.chmod(0o400)
        proxy["upstream_raw_sse"]["sha256"] = self._sha256(sse_path)
        proxy["pre_registered_request"]["sha256"] = self._sha256(
            Path(wrapper["request"]["path"])
        )
        last_path = Path(proxy["codex_last_message"]["path"])
        last_path.chmod(0o600)
        self._write_json(last_path, model_submission)
        last_path.chmod(0o400)
        proxy["codex_last_message"]["sha256"] = self._sha256(last_path)
        jsonl_path = Path(proxy["codex_jsonl"]["path"])
        jsonl_path.chmod(0o600)
        jsonl_path.write_bytes(b"".join(blind._json_bytes(item) for item in (
            {"type": "thread.started", "thread_id": "resealed-review-fixture"},
            {"type": "item.completed", "item": {
                "id": "item_0", "type": "error",
                "message": blind._CODEX_DISABLED_HOST_CONFIRMATION,
            }},
            {"type": "turn.started"},
            {"type": "item.completed", "item": {
                "type": "agent_message",
                "text": blind._json_bytes(model_submission).decode().rstrip("\n"),
            }},
        )))
        jsonl_path.chmod(0o400)
        proxy["codex_jsonl"]["sha256"] = self._sha256(jsonl_path)
        proxy_path.chmod(0o600)
        self._write_json(proxy_path, proxy)
        proxy_path.chmod(0o400)
        exchanges[0]["sha256"] = self._sha256(proxy_path)
        chain = hashlib.sha256(
            bytes.fromhex("0" * 64) + bytes.fromhex(exchanges[0]["sha256"])
        ).hexdigest()
        transport["exchange_chain_sha256"] = chain
        wrapper["request_response_chain_sha256"] = chain

    def _reseal_review_chain(self, fixture: dict[str, object]) -> None:
        source_wrapper_path = Path(fixture["source_review_invocation"])
        source_commitment_path = Path(fixture["source_commitment"])
        source_records_path = Path(fixture["source_records"])
        evaluation_wrapper_path = Path(fixture["review_invocation"])
        evaluation_receipt_path = Path(fixture["review_receipt"])
        evaluation_wrapper = json.loads(
            evaluation_wrapper_path.read_text(encoding="utf-8")
        )
        evaluation_wrapper["source_first_attempt_sha256"] = self._sha256(
            source_wrapper_path
        )
        evaluation_wrapper["source_records_commitment"]["sha256"] = self._sha256(
            source_records_path
        )
        evaluation_wrapper["constructed_semantic_receipt"]["sha256"] = self._sha256(
            evaluation_receipt_path
        )
        evaluation_semantic = json.loads(
            evaluation_receipt_path.read_text(encoding="utf-8")
        )
        model_submission = blind._minimal_review_submission_from_semantic(
            evaluation_semantic, source_first=False
        )
        model_path = Path(evaluation_wrapper["model_submission"]["path"])
        model_path.chmod(0o600)
        self._write_json(model_path, model_submission)
        model_path.chmod(0o400)
        evaluation_wrapper["model_submission"]["sha256"] = self._sha256(model_path)
        evaluation_wrapper["normalized_response_sha256"] = self._sha256(model_path)
        response_path = Path(evaluation_wrapper["response"]["path"])
        response = {
            "output": [{"content": [{
                "type": "output_text",
                "text": blind._json_bytes(model_submission).decode().rstrip("\n"),
            }]}]
        }
        response_path.chmod(0o600)
        self._write_json(response_path, response)
        response_path.chmod(0o400)
        evaluation_wrapper["response"]["sha256"] = self._sha256(response_path)
        self._reseal_review_proxy(evaluation_wrapper, model_submission)
        evaluation_wrapper_path.chmod(0o600)
        self._write_json(evaluation_wrapper_path, evaluation_wrapper)
        evaluation_wrapper_path.chmod(0o400)
        aggregate_path = Path(fixture["review_aggregate"])
        aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
        aggregate["source_first_attempt"]["sha256"] = self._sha256(
            source_wrapper_path
        )
        aggregate["artifact_review_attempt"]["sha256"] = self._sha256(
            evaluation_wrapper_path
        )
        aggregate["source_commitment_sha256"] = self._sha256(
            source_commitment_path
        )
        aggregate["source_records_sha256"] = self._sha256(source_records_path)
        aggregate["semantic_review_sha256"] = self._sha256(
            evaluation_receipt_path
        )
        aggregate_path.chmod(0o600)
        self._write_json(aggregate_path, aggregate)
        aggregate_path.chmod(0o400)
        seal_path = Path(fixture["controller_seal"])
        seal = json.loads(seal_path.read_text(encoding="utf-8"))
        seal["independent_review_receipt"]["sha256"] = self._sha256(
            aggregate_path
        )
        self._write_json(seal_path, seal)
        fixture["controller_seal_sha256"] = self._sha256(seal_path)

    def _reseal_source_commitment(self, fixture: dict[str, object]) -> None:
        source_path = Path(fixture["source_commitment"])
        source = json.loads(source_path.read_text(encoding="utf-8"))
        source_records_path = Path(fixture["source_records"])
        source_records = json.loads(
            source_records_path.read_text(encoding="utf-8")
        )
        source_records["records"] = source["records"]
        source_records_path.chmod(0o600)
        self._write_json(source_records_path, source_records)
        source_records_path.chmod(0o400)
        source["source_records_sha256"] = self._sha256(source_records_path)
        source_path.chmod(0o600)
        self._write_json(source_path, source)
        source_path.chmod(0o400)
        source_wrapper_path = Path(fixture["source_review_invocation"])
        source_wrapper = json.loads(source_wrapper_path.read_text(encoding="utf-8"))
        source_wrapper["constructed_semantic_receipt"]["sha256"] = self._sha256(
            source_path
        )
        source_model = blind._minimal_review_submission_from_semantic(
            source, source_first=True
        )
        source_model_path = Path(source_wrapper["model_submission"]["path"])
        source_model_path.chmod(0o600)
        self._write_json(source_model_path, source_model)
        source_model_path.chmod(0o400)
        source_wrapper["model_submission"]["sha256"] = self._sha256(
            source_model_path
        )
        source_wrapper["normalized_response_sha256"] = self._sha256(
            source_model_path
        )
        source_response_path = Path(source_wrapper["response"]["path"])
        source_response_path.chmod(0o600)
        self._write_json(source_response_path, {
            "output": [{"content": [{
                "type": "output_text",
                "text": blind._json_bytes(source_model).decode().rstrip("\n"),
            }]}]
        })
        source_response_path.chmod(0o400)
        source_wrapper["response"]["sha256"] = self._sha256(source_response_path)
        self._reseal_review_proxy(source_wrapper, source_model)
        precommit_path = Path(fixture["source_first_precommit"])
        precommit = {
            field: source_wrapper[field]
            for field in blind._STRUCTURED_SOURCE_PRECOMMIT_FIELDS
            if field not in {"phase", "finalized_before_solver"}
        }
        precommit.update({
            "phase": "structured_source_first_precommit",
            "finalized_before_solver": True,
        })
        precommit_path.chmod(0o600)
        self._write_json(precommit_path, precommit)
        precommit_path.chmod(0o400)
        source_wrapper["source_first_precommit"]["sha256"] = self._sha256(
            precommit_path
        )
        source["source_first_precommit_sha256"] = self._sha256(precommit_path)
        source_path.chmod(0o600)
        self._write_json(source_path, source)
        source_path.chmod(0o400)
        source_wrapper["constructed_semantic_receipt"]["sha256"] = self._sha256(
            source_path
        )
        source_wrapper["source_records_commitment"]["sha256"] = self._sha256(
            source_records_path
        )
        source_wrapper_path.chmod(0o600)
        self._write_json(source_wrapper_path, source_wrapper)
        source_wrapper_path.chmod(0o400)

        solver_aggregate_path = Path(fixture["invocation_aggregate"])
        solver_aggregate = json.loads(
            solver_aggregate_path.read_text(encoding="utf-8")
        )
        solver_aggregate["source_first_precommit_sha256"] = self._sha256(
            precommit_path
        )
        solver_aggregate_path.chmod(0o600)
        self._write_json(solver_aggregate_path, solver_aggregate)
        solver_aggregate_path.chmod(0o400)
        seal_path = Path(fixture["controller_seal"])
        seal = json.loads(seal_path.read_text(encoding="utf-8"))
        seal["source_first_precommit"]["sha256"] = self._sha256(precommit_path)
        seal["structured_solver_receipt"]["sha256"] = self._sha256(
            solver_aggregate_path
        )
        self._write_json(seal_path, seal)
        fixture["controller_seal_sha256"] = self._sha256(seal_path)

        evaluation_root = Path(fixture["review_input"])
        commitment_copy = evaluation_root / blind._SOURCE_COMMITMENT_INPUT
        commitment_copy.write_bytes(source_records_path.read_bytes())
        evaluation_files = blind._regular_file_inventory(
            evaluation_root, label="test rewritten artifact Review input"
        )
        evaluation_digest = blind._hash_index(evaluation_files)
        projection, gpt_images, kimi_images = blind._structured_review_projection(
            root=evaluation_root, files=evaluation_files,
            scope_ids=[str(fixture["id"])], source_first=False,
            source_records_sha256=self._sha256(source_records_path),
        )
        projection_sha = hashlib.sha256(
            blind._json_bytes(projection)
        ).hexdigest()
        semantic_path = Path(fixture["review_receipt"])
        semantic = json.loads(semantic_path.read_text(encoding="utf-8"))
        semantic["source_records_sha256"] = self._sha256(source_records_path)
        semantic["review_input_inventory_sha256"] = evaluation_digest
        semantic["review_projection_sha256"] = projection_sha
        semantic["records"][0]["source_commitment_record_sha256"] = hashlib.sha256(
            blind._json_bytes(source["records"][0])
        ).hexdigest()
        semantic_path.chmod(0o600)
        self._write_json(semantic_path, semantic)
        semantic_path.chmod(0o400)
        evaluation_wrapper_path = Path(fixture["review_invocation"])
        evaluation_wrapper = json.loads(
            evaluation_wrapper_path.read_text(encoding="utf-8")
        )
        evaluation_wrapper["input_inventory"] = {
            "root": str(evaluation_root),
            "files": evaluation_files,
            "files_sha256": evaluation_digest,
        }
        evaluation_wrapper["review_projection_sha256"] = projection_sha
        evaluation_wrapper["source_records_commitment"] = {
            "path": str(source_records_path),
            "sha256": self._sha256(source_records_path),
        }
        request_path = Path(evaluation_wrapper["request"]["path"])
        request_path.chmod(0o600)
        self._write_json(request_path, blind._structured_review_request(
            variant="gpt", model_id="gpt-5.6-sol", projection=projection,
            gpt_images=gpt_images, kimi_images=kimi_images, source_first=False,
        ))
        request_path.chmod(0o400)
        evaluation_wrapper["request"]["sha256"] = self._sha256(request_path)
        evaluation_wrapper_path.chmod(0o600)
        self._write_json(evaluation_wrapper_path, evaluation_wrapper)
        evaluation_wrapper_path.chmod(0o400)
        self._reseal_review_chain(fixture)

    def _reseal_solver_invocation(self, fixture: dict[str, object]) -> None:
        receipt_path = Path(fixture["invocation_receipt"])
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        proxy_path = Path(fixture["solver_proxy_receipt"])
        proxy_sha = self._sha256(proxy_path)
        receipt["adapter_provenance"]["proxy_receipt"]["sha256"] = proxy_sha
        without_chain = dict(receipt)
        without_chain.pop("attempt_chain_sha256", None)
        receipt["attempt_chain_sha256"] = hashlib.sha256(
            bytes.fromhex("0" * 64) + blind._json_bytes(without_chain)
        ).hexdigest()
        receipt_path.chmod(0o600)
        self._write_json(receipt_path, receipt)
        receipt_path.chmod(0o400)
        aggregate_path = Path(fixture["invocation_aggregate"])
        aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
        aggregate["targets"][0]["attempts"][0]["sha256"] = self._sha256(
            receipt_path
        )
        aggregate["targets"][0]["target_chain_sha256"] = receipt[
            "attempt_chain_sha256"
        ]
        aggregate["transport"]["exchanges"][0]["sha256"] = proxy_sha
        exchange_chain = hashlib.sha256(
            bytes.fromhex("0" * 64) + bytes.fromhex(proxy_sha)
        ).hexdigest()
        aggregate["transport"]["exchange_chain_sha256"] = exchange_chain
        aggregate["request_response_chain_sha256"] = exchange_chain
        aggregate_path.chmod(0o600)
        self._write_json(aggregate_path, aggregate)
        aggregate_path.chmod(0o400)
        seal_path = Path(fixture["controller_seal"])
        seal = json.loads(seal_path.read_text(encoding="utf-8"))
        seal["structured_solver_receipt"]["sha256"] = self._sha256(aggregate_path)
        self._write_json(seal_path, seal)
        fixture["controller_seal_sha256"] = self._sha256(seal_path)

    def _prepend_rejected_solver_attempt(
        self, fixture: dict[str, object], *, raw_submission: dict[str, object],
        store_submission: bool,
    ) -> None:
        """Turn the fixture into rejected malformed attempt -> accepted retry."""
        controller = Path(fixture["invocation_aggregate"]).parent
        project = Path(fixture["project"])
        target_id = str(fixture["id"])
        diagnostic = [{
            "kind": "controller_scan",
            "message": "provider response or constructed artifacts failed trusted validation",
        }]
        first_request_path = controller / "gpt-rejected-attempt-1-request.json"
        first_request_path.write_bytes(Path(fixture["structured_request"]).read_bytes())
        first_request_path.chmod(0o400)
        raw_text = blind._json_bytes(raw_submission).decode().rstrip("\n")
        first_response, first_sse = _gpt_response_and_sse(
            raw_text, suffix="rejected_attempt_1",
        )
        first_response_path = controller / "gpt-rejected-attempt-1-response.json"
        self._write_json(first_response_path, first_response)
        first_response_path.chmod(0o400)
        first_submission_locator = None
        if store_submission:
            first_submission_path = controller / "gpt-rejected-attempt-1-submission.json"
            self._write_json(first_submission_path, raw_submission)
            first_submission_path.chmod(0o400)
            first_submission_locator = {
                "path": str(first_submission_path),
                "sha256": self._sha256(first_submission_path),
            }
        normalized_path = controller / "gpt-rejected-attempt-1-normalized.json"
        normalized_path.write_bytes(first_response_path.read_bytes())
        normalized_path.chmod(0o400)
        sse_path = controller / "gpt-rejected-attempt-1-upstream.sse"
        sse_path.write_bytes(first_sse)
        sse_path.chmod(0o400)
        last_path = controller / "gpt-rejected-attempt-1-last-message.json"
        self._write_json(last_path, raw_submission)
        last_path.chmod(0o400)
        jsonl_path = controller / "gpt-rejected-attempt-1-codex.jsonl"
        jsonl_path.write_bytes(b"".join(blind._json_bytes(item) for item in (
            {"type": "thread.started", "thread_id": "rejected-fixture"},
            {"type": "item.completed", "item": {
                "id": "item_0", "type": "error",
                "message": blind._CODEX_DISABLED_HOST_CONFIRMATION,
            }},
            {"type": "turn.started"},
            {"type": "item.completed", "item": {
                "type": "agent_message", "text": raw_text,
            }},
        )))
        jsonl_path.chmod(0o400)
        stderr_path = controller / "gpt-rejected-attempt-1-codex.stderr"
        stderr_path.write_bytes(b"rejected fixture diagnostic\n")
        stderr_path.chmod(0o400)
        existing_proxy_path = Path(fixture["solver_proxy_receipt"])
        existing_proxy = json.loads(existing_proxy_path.read_text(encoding="utf-8"))
        first_proxy = {
            **existing_proxy,
            "attempt": 1,
            "pre_registered_request": {
                "path": str(first_request_path),
                "sha256": self._sha256(first_request_path),
            },
            "upstream_raw_sse": {
                "path": str(sse_path), "sha256": self._sha256(sse_path),
            },
            "normalized_response": {
                "path": str(normalized_path), "sha256": self._sha256(normalized_path),
            },
            "codex_jsonl": {
                "path": str(jsonl_path), "sha256": self._sha256(jsonl_path),
            },
            "codex_stderr": {
                "path": str(stderr_path), "sha256": self._sha256(stderr_path),
            },
            "codex_last_message": {
                "path": str(last_path), "sha256": self._sha256(last_path),
            },
        }
        first_proxy_path = controller / "gpt-rejected-attempt-1-proxy.json"
        self._write_json(first_proxy_path, first_proxy)
        first_proxy_path.chmod(0o400)
        first_proxy_locator = {
            "path": str(first_proxy_path), "sha256": self._sha256(first_proxy_path),
        }
        aggregate_path = Path(fixture["invocation_aggregate"])
        aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
        accepted_path = Path(fixture["invocation_receipt"])
        accepted = json.loads(accepted_path.read_text(encoding="utf-8"))
        first = {
            **accepted,
            "attempt": 1,
            "previous_attempt_sha256": None,
            "adapter_provenance": {
                "proxy_receipt": first_proxy_locator,
                "normalized_response_sha256": self._sha256(first_response_path),
                "upstream_raw_sse_sha256": self._sha256(sse_path),
                "event_count": 4,
            },
            "prior_diagnostics_sha256": hashlib.sha256(blind._json_bytes([])).hexdigest(),
            "request": {
                "path": str(first_request_path), "sha256": self._sha256(first_request_path),
            },
            "response": {
                "path": str(first_response_path), "sha256": self._sha256(first_response_path),
            },
            "submission": first_submission_locator,
            "constructed_candidate_sha256": None,
            "staged_artifacts": None,
            "status": "rejected",
            "diagnostics": diagnostic,
            "artifacts": None,
        }
        first.pop("attempt_chain_sha256", None)
        first_chain = hashlib.sha256(
            bytes.fromhex("0" * 64) + blind._json_bytes(first)
        ).hexdigest()
        first["attempt_chain_sha256"] = first_chain
        first_path = controller / "gpt-rejected-attempt-1.json"
        self._write_json(first_path, first)
        first_path.chmod(0o400)

        projection = json.loads(Path(fixture["structured_projection"]).read_text())
        gpt_images, kimi_images = blind._structured_image_parts(
            project=project, row=fixture["bundle_row"],
        )
        retry_request = blind._structured_provider_request(
            variant="gpt", model_id="gpt-5.6-sol", projection=projection,
            gpt_images=gpt_images, kimi_images=kimi_images,
            diagnostics=diagnostic,
        )
        retry_request_path = Path(fixture["structured_request"])
        retry_request_path.chmod(0o600)
        self._write_json(retry_request_path, retry_request)
        retry_request_path.chmod(0o400)
        existing_proxy["attempt"] = 2
        existing_proxy["pre_registered_request"] = {
            "path": str(retry_request_path), "sha256": self._sha256(retry_request_path),
        }
        existing_proxy_path.chmod(0o600)
        self._write_json(existing_proxy_path, existing_proxy)
        existing_proxy_path.chmod(0o400)
        accepted["attempt"] = 2
        accepted["previous_attempt_sha256"] = self._sha256(first_path)
        accepted["adapter_provenance"]["proxy_receipt"]["sha256"] = self._sha256(
            existing_proxy_path
        )
        accepted["prior_diagnostics_sha256"] = hashlib.sha256(
            blind._json_bytes(diagnostic)
        ).hexdigest()
        accepted["request"] = {
            "path": str(retry_request_path), "sha256": self._sha256(retry_request_path),
        }
        accepted.pop("attempt_chain_sha256", None)
        accepted_chain = hashlib.sha256(
            bytes.fromhex(first_chain) + blind._json_bytes(accepted)
        ).hexdigest()
        accepted["attempt_chain_sha256"] = accepted_chain
        accepted_path.chmod(0o600)
        self._write_json(accepted_path, accepted)
        accepted_path.chmod(0o400)
        accepted_proxy_locator = {
            "path": str(existing_proxy_path), "sha256": self._sha256(existing_proxy_path),
        }
        exchange_chain = "0" * 64
        for item in (first_proxy_locator, accepted_proxy_locator):
            exchange_chain = hashlib.sha256(
                bytes.fromhex(exchange_chain) + bytes.fromhex(item["sha256"])
            ).hexdigest()
        aggregate["transport"] = {
            "kind": "chatgpt_login_proxy_v1",
            "exchanges": [first_proxy_locator, accepted_proxy_locator],
            "exchange_chain_sha256": exchange_chain,
        }
        aggregate["targets"][0]["attempts"] = [
            {"path": str(first_path), "sha256": self._sha256(first_path)},
            {"path": str(accepted_path), "sha256": self._sha256(accepted_path)},
        ]
        aggregate["targets"][0]["accepted_attempt"] = 2
        aggregate["targets"][0]["target_chain_sha256"] = accepted_chain
        aggregate["request_count"] = 2
        aggregate["request_response_chain_sha256"] = exchange_chain
        aggregate_path.chmod(0o600)
        self._write_json(aggregate_path, aggregate)
        aggregate_path.chmod(0o400)
        seal_path = Path(fixture["controller_seal"])
        seal = json.loads(seal_path.read_text(encoding="utf-8"))
        seal["structured_solver_receipt"]["sha256"] = self._sha256(aggregate_path)
        self._write_json(seal_path, seal)
        fixture["controller_seal_sha256"] = self._sha256(seal_path)

    def _freeze(
        self,
        fixture: dict[str, object],
        output: Path,
        *,
        scope_kind: str = "full",
        refresh: bool = True,
    ) -> dict[str, object]:
        if refresh:
            self._refresh_controller_bindings(fixture, scope_kind=scope_kind)
        return blind.freeze_blind_evaluation(
            project=Path(fixture["project"]),
            candidate_dir=Path(fixture["candidate_dir"]),
            output=output,
            controller_seal=Path(fixture["controller_seal"]),
            expected_controller_seal_sha256=str(
                fixture["controller_seal_sha256"]
            ),
        )

    def _grade(
        self,
        fixture: dict[str, object],
        *,
        manifest: Path,
        grader: Path,
        output: Path,
        expected_freeze_sha256: str | None = None,
    ) -> dict[str, object]:
        return blind.grade_blind_evaluation(
            project=Path(fixture["project"]),
            manifest=manifest,
            grader=grader,
            output=output,
            controller_seal=Path(fixture["controller_seal"]),
            expected_controller_seal_sha256=str(
                fixture["controller_seal_sha256"]
            ),
            expected_freeze_sha256=(
                expected_freeze_sha256 or self._sha256(manifest)
            ),
            expected_grader_sha256=self._sha256(grader),
        )

    @staticmethod
    def _grading_override(
        official_answer: str,
        *,
        canonical_answer: str = "1.93 %",
        accepted_legacy_answers: list[str] | None = None,
    ) -> dict[str, object]:
        return {
            "schema_version": 1,
            "official_answer_sha256": hashlib.sha256(
                official_answer.encode("utf-8")
            ).hexdigest(),
            "reason_code": "official_intermediate_rounding",
            "canonical_answer": canonical_answer,
            "accepted_legacy_answers": (
                ["1.94 %"]
                if accepted_legacy_answers is None
                else accepted_legacy_answers
            ),
        }

    def _write_grader(
        self,
        root: Path,
        fixture: dict[str, object],
        *,
        official_answer: str = "7.04e12 J/day",
        grading_override: dict[str, object] | None = None,
    ) -> Path:
        path = root / "external-grader.jsonl"
        row = {
            "id": fixture["id"],
            "blind_record_sha256": fixture["blind_hash"],
            "official_answer": official_answer,
        }
        if grading_override is not None:
            row["grading_override"] = grading_override
        path.write_text(
            json.dumps(row) + "\n",
            encoding="utf-8",
        )
        return path

    def test_freeze_records_controller_model_scope_and_hash_bound_candidate(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            output = Path(td) / "freeze.json"
            manifest = self._freeze(fixture, output)

            self.assertTrue(output.is_file())
            self.assertEqual(output.stat().st_mode & 0o777, 0o400)
            self.assertEqual(manifest["phase"], "freeze")
            self.assertFalse(manifest["official_answer_seen"])
            self.assertEqual(manifest["solver"]["model_family"], "openai")
            self.assertEqual(manifest["solver"]["model_id"], "gpt-5.6-sol")
            self.assertEqual(manifest["solver"]["run_id"], "run-001")
            self.assertEqual(manifest["controller_binding"]["scope_kind"], "full")
            self.assertTrue(manifest["isolation"]["filesystem_answer_blind"])
            self.assertFalse(manifest["isolation"]["network_answer_blind"])
            self.assertEqual(manifest["record_count"], 1)
            record = manifest["records"][0]
            self.assertEqual(record["id"], fixture["id"])
            self.assertEqual(record["blind_record_sha256"], fixture["blind_hash"])
            self.assertEqual(record["formalization_gate_status"], "passed")
            self.assertEqual(record["proof_gate_status"], "solved")
            self.assertEqual(len(record["lean_verifier_record"]["checks"]), 2)

    def test_freeze_review_counts_bound_codex_jsonl_not_sse_events(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            wrapper = json.loads(
                Path(fixture["source_review_invocation"]).read_text(encoding="utf-8")
            )
            exchange_path = Path(wrapper["transport"]["exchanges"][0]["path"])
            exchange = json.loads(exchange_path.read_text(encoding="utf-8"))
            jsonl = Path(exchange["codex_jsonl"]["path"]).read_bytes()
            self.assertEqual(exchange["completed_event_count"], 1)
            self.assertEqual(len([line for line in jsonl.splitlines() if line.strip()]), 4)
            manifest = self._freeze(fixture, Path(td) / "multi-event-freeze.json")
            self.assertEqual(manifest["record_count"], 1)

    def test_kimi_v1_broker_ready_and_messages_provenance_are_canonical(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            project = root / "project"
            controller = root / "controller"
            project.mkdir()
            controller.mkdir()
            broker_hash = "a" * 64
            ready = {
                "schema_version": 1, "protocol": blind.PROTOCOL,
                "phase": "model_broker_ready", "variant": "kimi-k3",
                "run_id": "run-kimi", "listen_url": "http://127.0.0.1:18080/v1",
                "upstream_origin": "https://api.kimi.com",
                "allowed_model": "kimi-k3[1m]",
                "request_profile": blind._STRUCTURED_REQUEST_PROFILE,
                "public_dummy_key_sha256": hashlib.sha256(
                    b"answer-blind-public-dummy-token"
                ).hexdigest(),
                "broker_uid": 1002, "broker_binary_sha256": broker_hash,
                "started_at": "2026-08-12T00:00:00Z",
            }
            ready_path = controller / "broker-ready.json"
            self._write_json(ready_path, ready)
            ready_path.chmod(0o400)
            transcript = {
                "schema_version": 1, "protocol": blind.PROTOCOL,
                "phase": "model_broker_transcript", "variant": "kimi-k3",
                "run_id": "run-kimi",
                "request_profile": blind._STRUCTURED_REQUEST_PROFILE,
                "ready_receipt_sha256": self._sha256(ready_path),
                "request_count": 1,
                "request_response_chain_sha256": "b" * 64,
                "started_at": "2026-08-12T00:00:00Z",
                "stopped_at": "2026-08-12T00:01:00Z", "broker_stopped": True,
            }
            transcript_path = controller / "broker-transcript.json"
            self._write_json(transcript_path, transcript)
            transcript_path.chmod(0o400)
            binding = {
                "ready_receipt": {
                    "path": str(ready_path), "sha256": self._sha256(ready_path),
                },
                "transcript": {
                    "path": str(transcript_path), "sha256": self._sha256(transcript_path),
                },
            }
            runtime = {"files": {"bin/model-broker": broker_hash}}
            blind._load_and_validate_model_broker_binding(
                project=project, binding=binding, variant="kimi-k3",
                run_id="run-kimi", model_id="kimi-k3[1m]", runtime=runtime,
                minimum_requests=1, exact_requests=1,
                request_profile=blind._STRUCTURED_REQUEST_PROFILE,
                label="test Kimi broker",
            )
            request_payload = blind._json_bytes({"model": "kimi-k3[1m]"})
            response_payload = blind._json_bytes({"content": []})
            attempt = {
                "adapter": "structured_broker_http_v1", "status": "accepted",
                "adapter_provenance": {
                    "endpoint": "/v1/messages",
                    "request_sha256": hashlib.sha256(
                        request_payload.rstrip(b"\n")
                    ).hexdigest(),
                    "raw_response_sha256": hashlib.sha256(response_payload).hexdigest(),
                    "reasoning_control": {
                        "provider_field_supported": False,
                        "model_id": "kimi-k3[1m]", "max_tokens": 131072,
                    },
                },
            }
            blind._validate_structured_transport_provenance(
                project=project, runtime=runtime,
                aggregate={"variant": "kimi-k3", "model_id": "kimi-k3[1m]"},
                attempt=attempt, request_path=controller / "request.json",
                request_payload=request_payload, response_path=controller / "response.json",
                response_payload=response_payload, expected_gpt_exchange=None,
            )
            attempt["adapter_provenance"]["endpoint"] = "/messages"
            with self.assertRaisesRegex(blind.BlindEvaluationError, "Kimi adapter provenance"):
                blind._validate_structured_transport_provenance(
                    project=project, runtime=runtime,
                    aggregate={"variant": "kimi-k3", "model_id": "kimi-k3[1m]"},
                    attempt=attempt, request_path=controller / "request.json",
                    request_payload=request_payload,
                    response_path=controller / "response.json",
                    response_payload=response_payload, expected_gpt_exchange=None,
                )

    def test_freeze_replays_rejected_malformed_submission_then_valid_retry(self):
        malformed_cases = {
            "missing-field-no-submission": ({
                field: value for field, value in {
                    **{
                        "raw_result": {}, "reported_result": {},
                        "candidate_domain_derivation": {}, "lean_declarations": [],
                        "lean_source": "", "blueprint": "",
                    }
                }.items() if field != "blueprint"
            }, False),
            "wrong-type-stored-submission": ({
                "raw_result": "not-an-object", "reported_result": {},
                "candidate_domain_derivation": {}, "lean_declarations": [],
                "lean_source": "", "blueprint": "",
            }, True),
        }
        for label, (submission, store_submission) in malformed_cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                self._prepend_rejected_solver_attempt(
                    fixture, raw_submission=submission,
                    store_submission=store_submission,
                )
                manifest = self._freeze(
                    fixture, Path(td) / "retry-freeze.json", refresh=False,
                )
                self.assertEqual(manifest["record_count"], 1)

    def test_root_controller_builds_structured_seal_then_freezes(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = self._make_project(root)
            seal_path = root / "trusted-structured-seal.json"
            seal = blind.create_blind_controller_seal(
                project=fixture["project"],
                bundle=fixture["bundle"],
                structured_solver_receipt=fixture["invocation_aggregate"],
                source_first_precommit=fixture["source_first_precommit"],
                independent_review_receipt=fixture["review_aggregate"],
                verifier_receipt=fixture["verifier_invocation"],
                dependency_root=fixture["dependency_root"],
                runtime_root=fixture["runtime_root"],
                verifier_snapshot=fixture["verifier_snapshot"],
                output=seal_path,
            )
            self.assertEqual(seal_path.stat().st_mode & 0o777, 0o400)
            self.assertEqual(
                seal["source_first_precommit"]["sha256"],
                self._sha256(Path(fixture["source_first_precommit"])),
            )
            fixture["controller_seal"] = seal_path
            fixture["controller_seal_sha256"] = self._sha256(seal_path)
            manifest = self._freeze(
                fixture, root / "trusted-freeze.json", refresh=False
            )
            self.assertEqual(
                manifest["controller_binding"][
                    "source_first_precommit_sha256"
                ],
                seal["source_first_precommit"]["sha256"],
            )

    def test_controller_seal_builder_rejects_solver_precommit_tampering(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = self._make_project(root)
            aggregate_path = Path(fixture["invocation_aggregate"])
            aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
            aggregate["source_first_precommit_sha256"] = "0" * 64
            aggregate_path.chmod(0o600)
            self._write_json(aggregate_path, aggregate)
            aggregate_path.chmod(0o400)
            output = root / "must-not-exist-seal.json"
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "pre-solver source-first commitment"
            ):
                blind.create_blind_controller_seal(
                    project=fixture["project"],
                    bundle=fixture["bundle"],
                    structured_solver_receipt=aggregate_path,
                    source_first_precommit=fixture["source_first_precommit"],
                    independent_review_receipt=fixture["review_aggregate"],
                    verifier_receipt=fixture["verifier_invocation"],
                    dependency_root=fixture["dependency_root"],
                    runtime_root=fixture["runtime_root"],
                    verifier_snapshot=fixture["verifier_snapshot"],
                    output=output,
                )
            self.assertFalse(output.exists())

    def test_freeze_rejects_external_controller_seal_hash_mismatch(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            fixture["controller_seal_sha256"] = "0" * 64
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "controller expectation"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_grade_rejects_unfrozen_input_before_reading_grader(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            missing_manifest = Path(td) / "missing-freeze.json"
            grader = self._write_grader(Path(td), fixture)
            with mock.patch.object(blind, "_read_grader_jsonl") as read_grader:
                with self.assertRaises(blind.BlindEvaluationError):
                    self._grade(
                        fixture,
                        manifest=missing_manifest,
                        grader=grader,
                        output=Path(td) / "grade.json",
                        expected_freeze_sha256="0" * 64,
                    )
            read_grader.assert_not_called()

    def test_grade_detects_snapshot_drift_before_reading_grader(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            manifest = Path(td) / "freeze.json"
            self._freeze(fixture, manifest)
            candidate = Path(fixture["candidate"])
            candidate.write_text(candidate.read_text() + "\n", encoding="utf-8")
            grader = self._write_grader(Path(td), fixture)

            with mock.patch.object(blind, "_read_grader_jsonl") as read_grader:
                with self.assertRaisesRegex(blind.BlindEvaluationError, "drift|differs"):
                    self._grade(
                        fixture,
                        manifest=manifest,
                        grader=grader,
                        output=Path(td) / "grade.json",
                    )
            read_grader.assert_not_called()

    def test_freeze_rejects_candidate_leakage(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            candidate_path = Path(fixture["candidate"])
            candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
            candidate["reporting_rule_source"] = {"officialAnswer": "SECRET"}
            self._write_json(candidate_path, candidate)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "constructed candidate hash is stale"
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_rejects_source_report_not_derived_from_bundle(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            report_path = Path(fixture["report"])
            report = json.loads(report_path.read_text(encoding="utf-8"))
            report["entry"]["current_question"] = "Changed after ingestion"
            self._write_json(report_path, report)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError,
                "deterministic bundle projection|differs from the bundle",
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_rejects_arbitrary_number_with_only_true_theorem(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            target = Path(fixture["target"])
            candidate_path = Path(fixture["candidate"])
            target.write_text(
                "theorem BlindFixture.frozenResult : True := by trivial\n",
                encoding="utf-8",
            )
            candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
            candidate["lean_declarations"] = [
                "BlindFixture.frozenResult",
                "BlindFixture.frozenResultAgain",
            ]
            for index, contract in enumerate(candidate["lean_result_contracts"]):
                contract["declaration"] = candidate["lean_declarations"][index]
                contract["expected_type"] = "True"
                contract["expected_type_sha256"] = lean_result_type_sha256("True")
                contract["result_payload_sha256"] = blind_result_payload_sha256(
                    candidate, contract["role"]
                )
            self._write_json(candidate_path, candidate)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "constructed candidate hash is stale"
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_rejects_posthoc_precision_not_in_source_policy(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            candidate_path = Path(fixture["candidate"])
            candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
            candidate["reported_result"]["precision"] = {
                "kind": "significant_figures",
                "digits": 4,
                "source": "posthoc",
            }
            types = expected_numeric_result_types(candidate)
            assert types is not None
            for contract in candidate["lean_result_contracts"]:
                role = contract["role"]
                contract["expected_type"] = types[role]
                contract["expected_type_sha256"] = lean_result_type_sha256(
                    types[role]
                )
                contract["result_payload_sha256"] = blind_result_payload_sha256(
                    candidate, role
                )
            self._write_json(candidate_path, candidate)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError,
                "constructed candidate hash is stale",
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_bounds_exact_numeric_text_before_decimal_parsing(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            candidate_path = Path(fixture["candidate"])
            candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
            candidate["raw_result"]["value"] = "1e1000000"
            self._write_json(candidate_path, candidate)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "exponent exceeds"
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_rejects_degenerate_or_trivially_forged_raw_spec(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            candidate_path = Path(fixture["candidate"])
            candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
            candidate["raw_result"]["certified_interval"] = {
                "lower": candidate["raw_result"]["value"],
                "upper": candidate["raw_result"]["value"],
            }
            self._write_json(candidate_path, candidate)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "non-degenerate"
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            target = Path(fixture["target"])
            source = target.read_text(encoding="utf-8")
            source = source.replace(
                "def BlindFixture.rawEnergy : ℝ := BlindFixture.power * 1000000000",
                "def BlindFixture.rawEnergy : ℝ := id ((704 : ℝ) / 100)",
            ).replace(
                "def BlindFixture.rawEnergyDerivedFromProblemData : Prop := "
                "BlindFixture.rawEnergy = (7043000000000 : ℝ)",
                "theorem BlindFixture.rawEnergyDerivedFromProblemData : "
                "BlindFixture.rawEnergy = BlindFixture.rawEnergy := rfl",
            )
            target.write_text(source, encoding="utf-8")
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "disguise.*literal|reflexive",
            ):
                blind._validate_lean_target(
                    target,
                    project=Path(fixture["project"]),
                    declarations=[
                        "BlindFixture.rawEnergyResult",
                        "BlindFixture.reportedEnergyResult",
                    ],
                    raw_expression="BlindFixture.rawEnergy",
                    derivation_spec="BlindFixture.rawEnergyDerivedFromProblemData",
                    reported_value="7.04",
                )

        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            target = Path(fixture["target"])
            source = target.read_text(encoding="utf-8").replace(
                "def BlindFixture.rawEnergyDerivedFromProblemData : Prop := "
                "BlindFixture.rawEnergy = (7043000000000 : ℝ)",
                "theorem BlindFixture.rawEnergyDerivedFromProblemData : "
                "BlindFixture.rawEnergy = BlindFixture.rawEnergy := rfl",
            )
            target.write_text(source, encoding="utf-8")
            with self.assertRaisesRegex(blind.BlindEvaluationError, "reflexive"):
                blind._validate_lean_target(
                    target,
                    project=Path(fixture["project"]),
                    declarations=[
                        "BlindFixture.rawEnergyResult",
                        "BlindFixture.reportedEnergyResult",
                    ],
                    raw_expression="BlindFixture.rawEnergy",
                    derivation_spec="BlindFixture.rawEnergyDerivedFromProblemData",
                    reported_value="7.04",
                )

    def test_freeze_rejects_review_login_proxy_tampering(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            attempt_path = Path(fixture["source_review_invocation"])
            attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
            exchange = attempt["transport"]["exchanges"][0]
            proxy_path = Path(exchange["path"])
            proxy = json.loads(proxy_path.read_text(encoding="utf-8"))
            proxy_path.chmod(0o600)
            proxy["tool_events"] = 1
            self._write_json(proxy_path, proxy)
            proxy_path.chmod(0o400)
            exchange["sha256"] = self._sha256(proxy_path)
            chain = hashlib.sha256(
                bytes.fromhex("0" * 64) + bytes.fromhex(exchange["sha256"])
            ).hexdigest()
            attempt["transport"]["exchange_chain_sha256"] = chain
            attempt["request_response_chain_sha256"] = chain
            attempt_path.chmod(0o600)
            self._write_json(attempt_path, attempt)
            attempt_path.chmod(0o400)
            aggregate_path = Path(fixture["review_aggregate"])
            aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
            aggregate["source_first_attempt"]["sha256"] = self._sha256(
                attempt_path
            )
            aggregate_path.chmod(0o600)
            self._write_json(aggregate_path, aggregate)
            aggregate_path.chmod(0o400)
            seal_path = Path(fixture["controller_seal"])
            seal = json.loads(seal_path.read_text(encoding="utf-8"))
            seal["independent_review_receipt"]["sha256"] = self._sha256(
                aggregate_path
            )
            self._write_json(seal_path, seal)
            fixture["controller_seal_sha256"] = self._sha256(seal_path)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "exchange hash|metadata is stale"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_each_gpt_solver_attempt_binds_tool_free_login_proxy_evidence(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            proxy_path = Path(fixture["solver_proxy_receipt"])
            proxy = json.loads(proxy_path.read_text(encoding="utf-8"))
            proxy_path.chmod(0o600)
            proxy["tool_events"] = 1
            self._write_json(proxy_path, proxy)
            proxy_path.chmod(0o400)
            self._reseal_solver_invocation(fixture)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "metadata is stale"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_replays_exact_disabled_host_confirmation_sequence(self):
        for mutation in ("duplicate", "variant", "after-turn"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                proxy_path = Path(fixture["solver_proxy_receipt"])
                proxy = json.loads(proxy_path.read_text(encoding="utf-8"))
                jsonl_path = Path(proxy["codex_jsonl"]["path"])
                events = [
                    json.loads(line) for line in jsonl_path.read_text().splitlines()
                    if line.strip()
                ]
                if mutation == "duplicate":
                    events.insert(2, json.loads(json.dumps(events[1])))
                elif mutation == "variant":
                    events[1]["item"]["message"] += " changed"
                else:
                    events[1], events[2] = events[2], events[1]
                jsonl_path.chmod(0o600)
                jsonl_path.write_bytes(b"".join(
                    blind._json_bytes(item) for item in events
                ))
                jsonl_path.chmod(0o400)
                proxy["codex_jsonl"]["sha256"] = self._sha256(jsonl_path)
                proxy_path.chmod(0o600)
                self._write_json(proxy_path, proxy)
                proxy_path.chmod(0o400)
                self._reseal_solver_invocation(fixture)
                with self.assertRaisesRegex(
                    blind.BlindEvaluationError,
                    "disabled-host|error event|turn.started",
                ):
                    self._freeze(
                        fixture, Path(td) / "freeze.json", refresh=False,
                    )

    def test_freeze_requires_both_code_mode_disables_in_codex_argv(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            proxy_path = Path(fixture["solver_proxy_receipt"])
            proxy = json.loads(proxy_path.read_text(encoding="utf-8"))
            proxy["command_argv"].extend([
                "-c", "features.code_mode_host=true",
            ])
            proxy_path.chmod(0o600)
            self._write_json(proxy_path, proxy)
            proxy_path.chmod(0o400)
            self._reseal_solver_invocation(fixture)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "uniquely disable Code Mode",
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_tampered_bound_codex_stderr(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            proxy_path = Path(fixture["solver_proxy_receipt"])
            proxy = json.loads(proxy_path.read_text(encoding="utf-8"))
            stderr_path = Path(proxy["codex_stderr"]["path"])
            stderr_path.chmod(0o600)
            stderr_path.write_bytes(b"tampered stderr\n")
            stderr_path.chmod(0o400)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "Codex stderr hash is stale"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_independently_rejects_sse_delta_done_mismatch(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            proxy_path = Path(fixture["solver_proxy_receipt"])
            proxy = json.loads(proxy_path.read_text(encoding="utf-8"))
            sse_path = Path(proxy["upstream_raw_sse"]["path"])
            payload = sse_path.read_bytes().replace(
                b'"delta":"', b'"delta":"x', 1,
            )
            sse_path.chmod(0o600)
            sse_path.write_bytes(payload)
            sse_path.chmod(0o400)
            sse_sha = self._sha256(sse_path)
            proxy["upstream_raw_sse"]["sha256"] = sse_sha
            proxy_path.chmod(0o600)
            self._write_json(proxy_path, proxy)
            proxy_path.chmod(0o400)
            receipt_path = Path(fixture["invocation_receipt"])
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["adapter_provenance"]["upstream_raw_sse_sha256"] = sse_sha
            receipt_path.chmod(0o600)
            self._write_json(receipt_path, receipt)
            receipt_path.chmod(0o400)
            self._reseal_solver_invocation(fixture)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "output_text.done differs",
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_source_first_projection_drops_all_solver_artifact_locators(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            bundle_row = dict(fixture["bundle_row"])
            bundle_row.update({
                "output_lean": "Problems/Anchoring.lean",
                "lean_sha256": "a" * 64,
                "candidate": "blind_candidates/anchoring.json",
                "blueprint": "blueprint/src/chapters/Anchoring.tex",
            })
            projection = blind._source_first_projection(bundle_row)
            self.assertEqual(set(projection), blind._SOURCE_FIRST_PROJECTION_FIELDS)
            serialized = json.dumps(projection, sort_keys=True)
            for forbidden in ("output_lean", "lean_sha256", "blind_candidates", "blueprint"):
                self.assertNotIn(forbidden, serialized)

    def test_structured_review_provider_schemas_use_supported_combinators(self):
        def walk(value: object) -> None:
            if isinstance(value, dict):
                self.assertNotIn("oneOf", value)
                self.assertNotIn("uniqueItems", value)
                for child in value.values():
                    walk(child)
            elif isinstance(value, list):
                for child in value:
                    walk(child)

        walk(blind._structured_review_response_schema(source_first=True))
        walk(blind._structured_review_response_schema(source_first=False))

    def test_source_first_prompt_pins_exact_r9_style_source_locators(self):
        record_id = "icho_2026_t4_a8"
        source_record = {
            "id": record_id,
            "current_question": "Calculate the total energy released per day.",
            "shared_context": "The printed methane-flow context.",
            "previous_parts": [{"part_id": "T4-A7"}],
            "images": ["T4_page-3.png", "T4_page-2.png"],
            "reporting_policy": {"final_precision": "three significant figures"},
            "measurement_policy": {"derived_tolerances": "prove from inputs"},
            "candidate_domain_policy": {
                "allowed_sources": ["trusted_general_law"],
            },
            "problem_assets": [{
                "kind": "problem_page", "path": "not-a-locator.png",
            }],
        }
        projection = {
            "phase": "structured_source_first_review",
            "scope_ids": [record_id],
            "files": [
                {
                    "path": f"{blind._SOURCE_FIRST_RECORD_DIRECTORY}/{record_id}.json",
                    "kind": "text",
                    "text": blind._json_bytes(source_record).decode("utf-8"),
                },
                {
                    "path": "icho_2026_source/image/T4_page-3.png",
                    "kind": "image",
                },
                {
                    "path": "icho_2026_source/image/T4_page-2.png",
                    "kind": "image",
                },
            ],
        }
        prompt = blind._structured_review_prompt(
            projection=projection, source_first=True,
        )
        contract_line = next(
            line for line in prompt.splitlines()
            if line.startswith("source_locator_contract=")
        )
        contract = json.loads(contract_line.split("=", 1)[1])
        self.assertEqual(contract, {record_id: [
            "source.current_question",
            "source.shared_context",
            "source.previous_parts",
            "image:T4_page-3.png",
            "image:T4_page-2.png",
        ]})
        self.assertNotIn("image:icho_2026_source/image/T4_page-3.png", contract_line)
        self.assertNotIn("image:not-a-locator.png", contract_line)
        self.assertNotIn("T4_page-3.png, items 4.7–4.8", contract_line)
        self.assertNotIn("Trusted general thermochemical laws", contract_line)
        self.assertNotIn("review_projection.measurement_policy", contract_line)
        self.assertIn("General laws and reasoning belong", prompt)
        self.assertIn("never turn them into givens or source locators", prompt)
        self.assertIn("unit-free exact numeric string", prompt)
        self.assertIn("Never include a unit, Unicode multiplication sign", prompt)
        self.assertIn(
            "certified_interval.lower < raw_value < "
            "certified_interval.upper",
            prompt,
        )
        self.assertIn("Never set both interval bounds equal to raw_value", prompt)
        self.assertIn("keep the whole interval strictly inside", prompt)
        self.assertIn("avoid the anchoring words candidate, artifact", prompt)
        self.assertIn("post-hoc, post hoc, and posthoc", prompt)
        self.assertIn("even in a disclaimer", prompt)
        self.assertIn("Do not infer a missing time basis", prompt)
        self.assertIn("return an underdetermined result_spec", prompt)
        self.assertIn("only for a genuinely missing source constraint", prompt)
        self.assertIn("kind exactly equal to the requested kind", prompt)
        self.assertIn("include exactly reason and remaining_constraints", prompt)
        self.assertIn("do not invent raw, interval, reported", prompt)

    def test_controller_constructs_full_review_semantics_from_minimal_models(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            source = json.loads(
                Path(fixture["source_commitment"]).read_text(encoding="utf-8")
            )
            source_row = source["records"][0]
            rebuilt_source = blind.construct_structured_review_semantic(
                source_first=True,
                model_submission=blind._minimal_review_submission_from_semantic(
                    source, source_first=True
                ),
                controller_records={str(fixture["id"]): {
                    "blind_record_sha256": source_row["blind_record_sha256"],
                    "source_record_sha256": source_row["source_record_sha256"],
                    "requested_outputs": fixture["bundle_row"]["requested_outputs"],
                }},
                scope_ids=[str(fixture["id"])],
                variant=source["variant"], model_family=source["model_family"],
                model_id=source["model_id"], run_id=source["run_id"],
                snapshot_inventory_sha256=source["snapshot_inventory_sha256"],
                review_input_inventory_sha256=source[
                    "review_input_inventory_sha256"
                ],
                review_projection_sha256=source["review_projection_sha256"],
                source_first_precommit_sha256=source[
                    "source_first_precommit_sha256"
                ],
                source_records_sha256=source["source_records_sha256"],
            )
            self.assertEqual(rebuilt_source, source)

            review = json.loads(
                Path(fixture["review_receipt"]).read_text(encoding="utf-8")
            )
            review_row = review["records"][0]
            source_contract = review_row["formalization_certificate"][
                "source_contract"
            ]
            controller_record = {
                key: review_row[key]
                for key in (
                    "target", "target_sha256", "candidate_sha256",
                    "source_report_sha256", "blueprint_sha256",
                    "source_commitment_record_sha256",
                )
            }
            controller_record.update({
                "source_contract": source_contract,
                "requested_outputs": fixture["bundle_row"]["requested_outputs"],
                "images": source_contract["images"],
            })
            rebuilt_review = blind.construct_structured_review_semantic(
                source_first=False,
                model_submission=blind._minimal_review_submission_from_semantic(
                    review, source_first=False
                ),
                controller_records={str(fixture["id"]): controller_record},
                scope_ids=[str(fixture["id"])],
                variant=review["variant"], model_family=review["model_family"],
                model_id=review["model_id"], run_id=review["run_id"],
                snapshot_inventory_sha256=review["snapshot_inventory_sha256"],
                review_input_inventory_sha256=review[
                    "review_input_inventory_sha256"
                ],
                review_projection_sha256=review["review_projection_sha256"],
                source_records_sha256=review["source_records_sha256"],
            )
            self.assertEqual(rebuilt_review, review)

    def test_source_records_pure_validator_rejects_locator_or_policy_forgery(self):
        for mutation, error in (
            (
                lambda value: value["records"][0]["givens"][0].update(
                    {"source_locator": "source.fabricated_field"}
                ),
                "non-source material",
            ),
            (
                lambda value: value["records"][0]["output_commitments"][0][
                    "result_spec"
                ].update({"reporting_quantum": "2e10", "tie_rule": "made_up"}),
                "quantum/tie rule",
            ),
        ):
            with self.subTest(error=error), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                value = json.loads(
                    Path(fixture["source_records"]).read_text(encoding="utf-8")
                )
                mutation(value)
                source_wrapper = json.loads(
                    Path(fixture["source_review_invocation"]).read_text(
                        encoding="utf-8"
                    )
                )
                with self.assertRaisesRegex(blind.BlindEvaluationError, error):
                    blind.validate_structured_source_records(
                        records_commitment=value,
                        bundle_records={str(fixture["id"]): fixture["bundle_row"]},
                        input_files=source_wrapper["input_inventory"]["files"],
                    )

    def test_freeze_rejects_forged_independent_review_or_solver_state_input(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            semantic_path = Path(fixture["review_receipt"])
            semantic = json.loads(semantic_path.read_text(encoding="utf-8"))
            semantic_path.chmod(0o600)
            semantic["records"][0]["formalization_certificate"][
                "blind_review_certificate"
            ]["requested_outputs"] = []
            self._write_json(semantic_path, semantic)
            semantic_path.chmod(0o400)
            self._reseal_review_chain(fixture)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "requested_outputs"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            review_root = Path(fixture["review_input"])
            injected = review_root / ".archon" / "proof-review-gate.json"
            injected.parent.mkdir(parents=True, exist_ok=True)
            injected.write_text('{"forged":true}\n', encoding="utf-8")
            wrapper_path = Path(fixture["review_invocation"])
            wrapper = json.loads(wrapper_path.read_text(encoding="utf-8"))
            review_files = blind._regular_file_inventory(
                review_root, label="tampered Review input"
            )
            wrapper_path.chmod(0o600)
            wrapper["input_inventory"] = {
                "root": str(review_root),
                "files": review_files,
                "files_sha256": blind._hash_index(review_files),
            }
            self._write_json(wrapper_path, wrapper)
            wrapper_path.chmod(0o400)
            self._reseal_review_chain(fixture)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "solver gate/state"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_source_first_review_cannot_see_candidate_lean_or_blueprint(self):
        for key in ("candidate", "target", "chapter", "report"):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                project = Path(fixture["project"])
                source_root = Path(fixture["source_review_input"])
                source = Path(fixture[key])
                relative = source.relative_to(project)
                injected = source_root / relative
                injected.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, injected)
                files = blind._regular_file_inventory(
                    source_root, label="tampered source-first input"
                )
                wrapper_path = Path(fixture["source_review_invocation"])
                wrapper = json.loads(wrapper_path.read_text(encoding="utf-8"))
                wrapper_path.chmod(0o600)
                wrapper["input_inventory"] = {
                    "root": str(source_root),
                    "files": files,
                    "files_sha256": blind._hash_index(files),
                }
                self._write_json(wrapper_path, wrapper)
                wrapper_path.chmod(0o400)
                self._reseal_review_chain(fixture)
                with self.assertRaisesRegex(
                    blind.BlindEvaluationError,
                    "source-first (?:pre-solver commitment sanitized input inventory drift|Review input may contain only)",
                ):
                    self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_source_first_commitment_is_bound_to_predeclared_outputs(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            commitment_path = Path(fixture["source_commitment"])
            commitment = json.loads(commitment_path.read_text(encoding="utf-8"))
            commitment["records"][0]["output_commitments"][0][
                "reporting_policy"
            ] = {
                "kind": "significant_figures",
                "digits": 12,
                "source": "posthoc_candidate_precision",
            }
            commitment_path.chmod(0o600)
            self._write_json(commitment_path, commitment)
            commitment_path.chmod(0o400)
            self._reseal_source_commitment(fixture)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError,
                "exactly cover requested_outputs",
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_source_first_commitment_rejects_candidate_anchored_numeric_spec(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            commitment_path = Path(fixture["source_commitment"])
            commitment = json.loads(commitment_path.read_text(encoding="utf-8"))
            commitment["records"][0]["output_commitments"][0]["result_spec"][
                "raw_expression"
            ] = "use whatever numeric value appears in the candidate artifact"
            commitment_path.chmod(0o600)
            self._write_json(commitment_path, commitment)
            commitment_path.chmod(0o400)
            self._reseal_source_commitment(fixture)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "anchoring language"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_source_first_numeric_binding_accepts_equivalent_bounded_lexemes(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            commitment_path = Path(fixture["source_commitment"])
            commitment = json.loads(commitment_path.read_text(encoding="utf-8"))
            spec = commitment["records"][0]["output_commitments"][0][
                "result_spec"
            ]
            spec["raw_value"] = "7043000000000"
            spec["reported_value"] = "7040000000000"
            commitment_path.chmod(0o600)
            self._write_json(commitment_path, commitment)
            commitment_path.chmod(0o400)
            self._reseal_source_commitment(fixture)

            manifest = self._freeze(
                fixture, Path(td) / "freeze.json", refresh=False
            )
            self.assertEqual(manifest["record_count"], 1)

    def test_source_first_numeric_binding_rejects_interval_or_expression_drift(self):
        mutations = (
            ("certified_interval", {"lower": "7.041e12", "upper": "7.044e12"}),
            (
                "raw_expression",
                "7043 * 10^9 from a different problem-data derivation",
            ),
        )
        for field, value in mutations:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                commitment_path = Path(fixture["source_commitment"])
                commitment = json.loads(
                    commitment_path.read_text(encoding="utf-8")
                )
                commitment["records"][0]["output_commitments"][0][
                    "result_spec"
                ][field] = value
                commitment_path.chmod(0o600)
                self._write_json(commitment_path, commitment)
                commitment_path.chmod(0o400)
                self._reseal_source_commitment(fixture)
                with self.assertRaisesRegex(
                    blind.BlindEvaluationError,
                    "candidate numeric result differs from source-first commitment",
                ):
                    self._freeze(
                        fixture, Path(td) / "freeze.json", refresh=False
                    )

    def test_multi_output_candidate_requires_exact_per_output_raw_reported_maps(self):
        numeric_policy = {
            "kind": "decimal_places", "digits": 2, "source": "question",
        }
        integer_policy = {"kind": "exact_integer", "source": "question"}
        reporting = {
            **REPORTING_POLICY,
            "final_precision": {
                "kind": "per_requested_output", "source": "requested_outputs",
            },
        }
        outputs = [
            {
                "id": "decimal",
                "source_requirement": "a decimal result",
                "kind": "numeric",
                "unit": "mol",
                "reporting_policy": numeric_policy,
            },
            {
                "id": "count",
                "source_requirement": "an integer count",
                "kind": "integer",
                "unit": "",
                "reporting_policy": integer_policy,
            },
        ]
        raw = {
            "decimal": {
                "kind": "numeric", "status": "derived",
                "raw_expression": "7043 / 1000", "raw_value": "7.043",
                "certified_interval": {"lower": "7.042", "upper": "7.044"},
                "reported_value": "7.04", "reporting_quantum": "0.01",
                "tie_rule": "half_away_from_zero",
            },
            "count": {
                "kind": "integer", "status": "derived", "value": "3",
                "proposition": "the source constraints determine three cases",
                "constraints": ["all source cases were enumerated"],
            },
        }
        candidate = {
            "result_kind": "symbolic",
            "raw_result": {"value": raw},
            "reported_result": {
                "value": {
                    "decimal": {"status": "derived", "value": "7.040"},
                    "count": {"status": "derived", "value": "3"},
                },
                "rounding_rule": "half_away_from_zero",
            },
            "reporting_rule_source": reporting,
            "tolerance_provenance": {"measurement_policy": MEASUREMENT_POLICY},
            "candidate_domain_provenance": {
                "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
                "derivation": {"kind": "source_complete"},
            },
        }
        source = {
            "reporting_policy": reporting,
            "requested_outputs": outputs,
            "measurement_policy": MEASUREMENT_POLICY,
            "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
        }
        blind._validate_candidate_source_policies(
            candidate, source_entry=source, record_id="multi"
        )
        candidate["reported_result"]["value"].pop("count")
        with self.assertRaisesRegex(
            blind.BlindEvaluationError, "exactly the requested output IDs"
        ):
            blind._validate_candidate_source_policies(
                candidate, source_entry=source, record_id="multi"
            )

    def test_multi_output_candidate_supports_mixed_partial_underdetermination(self):
        reporting = {
            **REPORTING_POLICY,
            "final_precision": {
                "kind": "per_requested_output", "source": "requested_outputs",
            },
        }
        outputs = [
            {
                "id": "numeric_unknown",
                "source_requirement": "a numeric value if derivable",
                "kind": "numeric",
                "unit": "mol",
                "reporting_policy": {
                    "kind": "significant_figures", "digits": 3,
                    "source": "question",
                },
            },
            {
                "id": "formula",
                "source_requirement": "the governing formula",
                "kind": "formula",
                "unit": "",
                "reporting_policy": {"kind": "exact_symbolic", "source": "question"},
            },
        ]
        candidate = {
            "result_kind": "symbolic",
            "raw_result": {"value": {
                "numeric_unknown": {
                    "kind": "numeric", "status": "underdetermined",
                    "reason": "the source omits one independent quantity",
                    "remaining_constraints": ["the missing quantity must be positive"],
                },
                "formula": {
                    "kind": "formula", "status": "derived",
                    "normalized_result": "n = m / M",
                    "proposition": "amount equals mass divided by molar mass",
                    "constraints": ["molar mass is nonzero"],
                },
            }},
            "reported_result": {
                "value": {
                    "numeric_unknown": {
                        "status": "underdetermined", "value": None,
                    },
                    "formula": {"status": "derived", "value": "n = m / M"},
                },
                "rounding_rule": "half_away_from_zero",
            },
            "reporting_rule_source": reporting,
            "tolerance_provenance": {"measurement_policy": MEASUREMENT_POLICY},
            "candidate_domain_provenance": {
                "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
                "derivation": {"kind": "source_complete"},
            },
        }
        source = {
            "reporting_policy": reporting,
            "requested_outputs": outputs,
            "measurement_policy": MEASUREMENT_POLICY,
            "candidate_domain_policy": CANDIDATE_DOMAIN_POLICY,
        }
        blind._validate_candidate_source_policies(
            candidate, source_entry=source, record_id="mixed"
        )

    def test_artifact_review_must_bind_and_pass_source_first_alignment(self):
        for mutation, error in (
            (
                lambda record: record.update(
                    {"source_commitment_record_sha256": "e" * 64}
                ),
                "does not bind source-first record",
            ),
            (
                lambda record: record["source_alignment"].update(
                    {"status": "failed"}
                ),
                "does not align",
            ),
        ):
            with self.subTest(error=error), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                semantic_path = Path(fixture["review_receipt"])
                semantic = json.loads(semantic_path.read_text(encoding="utf-8"))
                mutation(semantic["records"][0])
                semantic_path.chmod(0o600)
                self._write_json(semantic_path, semantic)
                semantic_path.chmod(0o400)
                self._reseal_review_chain(fixture)
                with self.assertRaisesRegex(blind.BlindEvaluationError, error):
                    self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_lean_target_rejects_custom_elaboration_and_local_imports(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            target = Path(fixture["target"])
            target.write_text(
                "import IChO2026Chem.Reporting\n"
                'local macro "pwn" : term => `(True)\n'
                "theorem BlindFixture.rawEnergyResult : True := by trivial\n"
                "theorem BlindFixture.reportedEnergyResult : True := by trivial\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "extending or executing"
            ):
                blind._validate_lean_target(
                    target,
                    project=Path(fixture["project"]),
                    declarations=[
                        "BlindFixture.rawEnergyResult",
                        "BlindFixture.reportedEnergyResult",
                    ],
                )

            target.write_text(
                "import IChO2026Chem.Reporting\n"
                "@[command_elab Lean.Parser.Command.check] "
                "def BlindFixture.auditCheck : Lean.Elab.Command.CommandElab := "
                "fun _ => do IO.FS.writeFile \"/tmp/PWNED\" \"pwned\"\n"
                "theorem BlindFixture.rawEnergyResult : True := by trivial\n"
                "theorem BlindFixture.reportedEnergyResult : True := by trivial\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "extending or executing"
            ):
                blind._validate_lean_target(
                    target,
                    project=Path(fixture["project"]),
                    declarations=[
                        "BlindFixture.rawEnergyResult",
                        "BlindFixture.reportedEnergyResult",
                    ],
                )

            target.write_text(
                "import IChO2026Chem.Reporting\n"
                "local instance : LE ℝ := ⟨fun _ _ => True⟩\n"
                "theorem BlindFixture.rawEnergyResult : True := by trivial\n"
                "theorem BlindFixture.reportedEnergyResult : True := by trivial\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "extending or executing"
            ):
                blind._validate_lean_target(
                    target,
                    project=Path(fixture["project"]),
                    declarations=[
                        "BlindFixture.rawEnergyResult",
                        "BlindFixture.reportedEnergyResult",
                    ],
                )

            target.write_text(
                "import IChO2026Chem.Reporting\n"
                "@[command_elab Lean.Parser.Command.check] "
                "def auditCheck : CommandElab := fun _ => do "
                'IO.FS.writeFile \"pwned\" \"yes\"\n'
                "theorem BlindFixture.rawEnergyResult : True := by trivial\n"
                "theorem BlindFixture.reportedEnergyResult : True := by trivial\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "extending or executing"
            ):
                blind._validate_lean_target(
                    target,
                    project=Path(fixture["project"]),
                    declarations=[
                        "BlindFixture.rawEnergyResult",
                        "BlindFixture.reportedEnergyResult",
                    ],
                )

            evil = Path(fixture["project"]) / "Mathlib" / "Evil.lean"
            evil.parent.mkdir(exist_ok=True)
            evil.write_text("run_cmd IO.println \"pwn\"\naxiom forged : False\n")
            target.write_text(
                "import Mathlib.Evil\n"
                "theorem BlindFixture.rawEnergyResult : True := by trivial\n"
                "theorem BlindFixture.reportedEnergyResult : True := by trivial\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "unapproved module"
            ):
                blind._validate_lean_target(
                    target,
                    project=Path(fixture["project"]),
                    declarations=[
                        "BlindFixture.rawEnergyResult",
                        "BlindFixture.reportedEnergyResult",
                    ],
                )

    def test_scope_is_controller_authorized_and_candidate_inventory_is_exact(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            output = Path(td) / "pilot-freeze.json"
            manifest = self._freeze(fixture, output, scope_kind="pilot")
            self.assertEqual(manifest["controller_binding"]["scope_kind"], "pilot")

        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            candidate_dir = Path(fixture["candidate_dir"])
            (candidate_dir / "unselected.json").write_text("{}\n", encoding="utf-8")
            with self.assertRaisesRegex(blind.BlindEvaluationError, "unexpected"):
                self._freeze(
                    fixture, Path(td) / "pilot-freeze.json", scope_kind="pilot"
                )

    def test_freeze_rejects_failed_verifier_receipt(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            receipt_path = Path(fixture["verifier_receipt"])
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["compiled"] = False
            self._write_json(receipt_path, receipt)
            wrapper_path = Path(fixture["verifier_invocation"])
            wrapper = json.loads(wrapper_path.read_text(encoding="utf-8"))
            wrapper["verifier_receipt"]["sha256"] = self._sha256(receipt_path)
            self._write_json(wrapper_path, wrapper)
            seal_path = Path(fixture["controller_seal"])
            seal = json.loads(seal_path.read_text(encoding="utf-8"))
            seal["verifier_receipt"]["sha256"] = self._sha256(wrapper_path)
            self._write_json(seal_path, seal)
            fixture["controller_seal_sha256"] = self._sha256(seal_path)

            with self.assertRaisesRegex(blind.BlindEvaluationError, "not passing"):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_invocation_aggregate_chain_tampering(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            aggregate_path = Path(fixture["invocation_aggregate"])
            aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
            aggregate["targets"][0]["target_chain_sha256"] = "f" * 64
            aggregate_path.chmod(0o600)
            self._write_json(aggregate_path, aggregate)
            aggregate_path.chmod(0o400)
            seal_path = Path(fixture["controller_seal"])
            seal = json.loads(seal_path.read_text(encoding="utf-8"))
            seal["structured_solver_receipt"]["sha256"] = self._sha256(
                aggregate_path
            )
            self._write_json(seal_path, seal)
            fixture["controller_seal_sha256"] = self._sha256(seal_path)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "artifact/attempt chain"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_missing_structured_model_attempt(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            aggregate_path = Path(fixture["invocation_aggregate"])
            aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
            aggregate["targets"][0]["attempts"] = []
            aggregate["targets"][0]["accepted_attempt"] = 0
            aggregate_path.chmod(0o600)
            self._write_json(aggregate_path, aggregate)
            aggregate_path.chmod(0o400)
            seal_path = Path(fixture["controller_seal"])
            seal = json.loads(seal_path.read_text(encoding="utf-8"))
            seal["structured_solver_receipt"]["sha256"] = self._sha256(
                aggregate_path
            )
            self._write_json(seal_path, seal)
            fixture["controller_seal_sha256"] = self._sha256(seal_path)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "attempt/acceptance count"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rebuilds_structured_problem_only_request(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            request_path = Path(fixture["structured_request"])
            request = json.loads(request_path.read_text(encoding="utf-8"))
            request["tools"] = [{"type": "web_search"}]
            request_path.chmod(0o600)
            self._write_json(request_path, request)
            request_path.chmod(0o400)
            attempt_path = Path(fixture["invocation_receipt"])
            attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
            attempt["request"]["sha256"] = self._sha256(request_path)
            attempt_path.chmod(0o600)
            self._write_json(attempt_path, attempt)
            attempt_path.chmod(0o400)
            self._reseal_solver_invocation(fixture)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "canonical blind prompt"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_submission_not_derived_from_provider_response(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            submission_path = Path(fixture["structured_submission"])
            submission = json.loads(submission_path.read_text(encoding="utf-8"))
            submission["blueprint"] += "\npost-response replacement"
            submission_path.chmod(0o600)
            self._write_json(submission_path, submission)
            submission_path.chmod(0o400)
            attempt_path = Path(fixture["invocation_receipt"])
            attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
            attempt["submission"]["sha256"] = self._sha256(submission_path)
            attempt_path.chmod(0o600)
            self._write_json(attempt_path, attempt)
            attempt_path.chmod(0o400)
            self._reseal_solver_invocation(fixture)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "not response-derived"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_failed_solver_receipt_even_when_aggregate_is_rehashed(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            receipt_path = Path(fixture["invocation_receipt"])
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["status"] = "rejected"
            receipt["diagnostics"] = [{
                "kind": "lean_compile", "message": "clean compile failed"
            }]
            receipt["artifacts"] = None
            receipt_path.chmod(0o600)
            self._write_json(receipt_path, receipt)
            receipt_path.chmod(0o400)
            self._reseal_solver_invocation(fixture)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "rejected attempt|no accepted"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_runtime_drift_and_aggregate_inventory_tampering(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            Path(fixture["runtime"]).write_bytes(b"tampered trusted runtime\n")
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "runtime inventory drift"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            runtime = Path(fixture["runtime"])
            runtime.unlink()
            runtime.symlink_to("/bin/true")
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "escaping/broken symlink"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            aggregate_path = Path(fixture["invocation_aggregate"])
            aggregate = json.loads(aggregate_path.read_text(encoding="utf-8"))
            aggregate["controller_binary_sha256"] = "e" * 64
            aggregate_path.chmod(0o600)
            self._write_json(aggregate_path, aggregate)
            aggregate_path.chmod(0o400)
            seal_path = Path(fixture["controller_seal"])
            seal = json.loads(seal_path.read_text(encoding="utf-8"))
            seal["structured_solver_receipt"]["sha256"] = self._sha256(aggregate_path)
            self._write_json(seal_path, seal)
            fixture["controller_seal_sha256"] = self._sha256(seal_path)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "controller binary is absent"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_false_dedicated_uid_quiescence(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            wrapper_path = Path(fixture["verifier_invocation"])
            wrapper = json.loads(wrapper_path.read_text(encoding="utf-8"))
            wrapper["dedicated_uid_quiescence"]["quiescent_after"] = False
            self._write_json(wrapper_path, wrapper)
            seal_path = Path(fixture["controller_seal"])
            seal = json.loads(seal_path.read_text(encoding="utf-8"))
            seal["verifier_receipt"]["sha256"] = self._sha256(wrapper_path)
            self._write_json(seal_path, seal)
            fixture["controller_seal_sha256"] = self._sha256(seal_path)
            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "not proven quiescent"
            ):
                self._freeze(fixture, Path(td) / "freeze.json", refresh=False)

    def test_freeze_rejects_failed_formal_check_or_bridge(self):
        for field in ("check", "bridge"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                gate_path = Path(fixture["formal_gate"])
                gate = json.loads(gate_path.read_text(encoding="utf-8"))
                certificate = gate["targets"]["Problems/T1A1.lean"]["certificate"]
                if field == "check":
                    certificate["checks"]["derivability"]["status"] = "failed"
                else:
                    certificate["bridge_obligations"][0]["status"] = "blocked"
                self._write_json(gate_path, gate)
                with self.assertRaisesRegex(
                    blind.BlindEvaluationError, "not passing"
                ):
                    self._freeze(fixture, Path(td) / "freeze.json")

    def test_clean_snapshot_rejects_solver_build_and_compiled_artifacts(self):
        for relative in ("Injected.olean", ".lake/build/evil.bin"):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as td:
                fixture = self._make_project(Path(td))
                path = Path(fixture["project"]) / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"untrusted build output")
                with self.assertRaisesRegex(
                    blind.BlindEvaluationError,
                    "compiled Lean artifact|clean verifier snapshot",
                ):
                    self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_rejects_forged_passing_gate_without_review_coverage(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            gate_path = Path(fixture["formal_gate"])
            gate = json.loads(gate_path.read_text(encoding="utf-8"))
            certificate = gate["targets"]["Problems/T1A1.lean"]["certificate"]
            certificate["blind_review_certificate"]["requested_outputs"] = []
            self._write_json(gate_path, gate)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "requested_outputs"
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_rejects_legacy_batch_gate_that_drops_review_certificate(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            gate_path = Path(fixture["formal_gate"])
            gate = json.loads(gate_path.read_text(encoding="utf-8"))
            current = gate["targets"]["Problems/T1A1.lean"]["certificate"]
            gate["targets"]["Problems/T1A1.lean"]["certificate"] = {
                "schema_version": 2,
                "milestones": [current],
            }
            self._write_json(gate_path, gate)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "batch wrapper"
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_freeze_accepts_exact_single_target_parallel_review_certificate(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            project = Path(fixture["project"])
            state = Path(fixture["state"])
            target = Path(fixture["target"])
            gate_path = Path(fixture["formal_gate"])
            existing = json.loads(gate_path.read_text(encoding="utf-8"))
            current = existing["targets"]["Problems/T1A1.lean"]["certificate"]
            session = state / "proof-journal" / "sessions" / "session_1"
            session.mkdir(parents=True)
            review = {
                **current["blind_review_certificate"],
                "status": "passed",
                "reason": "target-bound parallel Review passed",
                "checks": current["checks"],
                "bridge_obligations": current["bridge_obligations"],
            }
            milestone = {
                "target": {"file": "Problems/T1A1.lean", "theorem": "reportedEnergyResult"},
                "status": "solved",
                "formalization_review": review,
            }
            (session / "milestones.jsonl").write_text(
                json.dumps(milestone) + "\n", encoding="utf-8"
            )
            gate_path.unlink()
            apply_formalization_review(
                state_dir=state,
                project_path=project,
                progress_file=project / ".archon/PROGRESS.md",
                session_dir=session,
                iter_num=1,
                reviewed_objectives=[target],
                max_iterations=1,
            )
            persisted = json.loads(gate_path.read_text(encoding="utf-8"))
            certificate = persisted["targets"]["Problems/T1A1.lean"]["certificate"]
            self.assertEqual(len(certificate["milestones"]), 1)
            self.assertEqual(
                certificate["blind_review_certificate"],
                certificate["milestones"][0]["blind_review_certificate"],
            )

            manifest = self._freeze(fixture, Path(td) / "freeze.json")
            self.assertEqual(manifest["record_count"], 1)

    def test_freeze_rejects_posthoc_narrowed_candidate_domain(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            candidate_path = Path(fixture["candidate"])
            candidate = json.loads(candidate_path.read_text(encoding="utf-8"))
            candidate["candidate_domain_provenance"]["candidate_domain_policy"] = {
                **CANDIDATE_DOMAIN_POLICY,
                "allowed_sources": ["posthoc_singleton"],
            }
            for contract in candidate["lean_result_contracts"]:
                contract["result_payload_sha256"] = blind_result_payload_sha256(
                    candidate, contract["role"]
                )
            self._write_json(candidate_path, candidate)

            with self.assertRaisesRegex(
                blind.BlindEvaluationError, "constructed candidate hash is stale"
            ):
                self._freeze(fixture, Path(td) / "freeze.json")

    def test_nonroot_verifier_entry_point_refuses_root(self):
        if os.geteuid() != 0:
            self.skipTest("test exercises the root refusal path")
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            with self.assertRaisesRegex(blind.BlindEvaluationError, "refuses to run as root"):
                blind.verify_blind_lean(
                    project=fixture["project"],
                    candidate_dir=fixture["candidate_dir"],
                    output=Path(td) / "verifier-output.json",
                    runtime_executable=fixture["runtime"],
                    runtime_root=fixture["runtime_root"],
                    dependency_root=fixture["dependency_root"],
                    expected_dependency_inventory_sha256="0" * 64,
                    expected_runtime_inventory_sha256="0" * 64,
                    expected_snapshot_inventory_sha256="0" * 64,
                    scope_ids=[str(fixture["id"])],
                )

    def test_clean_lean_probe_compiles_source_without_target_olean(self):
        lake = Path("/root/.elan/bin/lake")
        if not lake.exists():
            self.skipTest("Lean/Lake is unavailable")
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            project = root / "project"
            output = root / "verifier-private"
            dependency = root / "dependencies"
            project.mkdir()
            output.mkdir()
            dependency.mkdir()
            (project / "lakefile.toml").write_text(
                'name = "clean_probe"\nversion = "0.1.0"\n'
                '[[lean_lib]]\nname = "IChO2026Chem"\n',
                encoding="utf-8",
            )
            (project / "lean-toolchain").write_text(
                "leanprover/lean4:v4.31.0\n", encoding="utf-8"
            )
            (project / "IChO2026Chem.lean").write_text(
                "theorem chemistrySeed : True := by trivial\n", encoding="utf-8"
            )
            target_payload = (
                "import IChO2026Chem\n"
                "theorem CleanProbe.raw : True := by trivial\n"
                "theorem CleanProbe.reported : True := by exact CleanProbe.raw\n"
            ).encode()
            contracts = [
                {
                    "role": role,
                    "declaration": declaration,
                    "expected_type": "True",
                    "expected_type_sha256": "a" * 64,
                    "result_payload_sha256": "b" * 64,
                }
                for role, declaration in (
                    ("raw_result", "CleanProbe.raw"),
                    ("reported_result", "CleanProbe.reported"),
                )
            ]
            results, _stdout, _stderr = blind._run_clean_lean_result_checks(
                runtime_path=lake,
                project_path=project,
                dependency_path=dependency,
                output_parent=output,
                timeout_s=60,
                pending=[{
                    "id": "T1",
                    "target_payload": target_payload,
                    "contracts": contracts,
                }],
            )
            self.assertEqual(
                [item["axioms"] for item in results["T1"][2]], [[], []]
            )
            self.assertFalse(any(project.rglob("*.olean")))

    def test_freeze_manifest_publication_is_atomic_on_replace_failure(self):
        with tempfile.TemporaryDirectory() as td:
            fixture = self._make_project(Path(td))
            output = Path(td) / "freeze.json"
            self._refresh_controller_bindings(fixture)
            with mock.patch.object(
                blind.os, "replace", side_effect=OSError("simulated crash")
            ):
                with self.assertRaisesRegex(
                    blind.BlindEvaluationError, "atomically publish"
                ):
                    self._freeze(fixture, output, refresh=False)

            self.assertFalse(output.exists())
            self.assertEqual(list(output.parent.glob(f".{output.name}.*")), [])

    def test_post_freeze_grade_is_read_only_for_all_bound_sources(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = self._make_project(root)
            manifest_path = root / "freeze.json"
            manifest = self._freeze(fixture, manifest_path)
            grader = self._write_grader(
                root, fixture, official_answer="7.04e12 J/day"
            )
            protected = [
                Path(fixture[key])
                for key in (
                    "candidate",
                    "target",
                    "report",
                    "chapter",
                    "image",
                    "problem_pdf",
                    "bundle",
                    "seed",
                    "formal_gate",
                    "proof_gate",
                    "controller_seal",
                    "invocation_receipt",
                    "invocation_aggregate",
                    "verifier_receipt",
                    "verifier_invocation",
                    "verifier_log",
                    "launch_authorization",
                    "model_broker_receipt",
                    "model_broker_transcript",
                    "review_receipt",
                    "review_invocation",
                    "review_log",
                )
            ] + [manifest_path]
            before = {path: self._sha256(path) for path in protected}

            grade_path = root / "grade.json"
            grade = self._grade(
                fixture, manifest=manifest_path, grader=grader, output=grade_path
            )

            self.assertEqual(
                grade["results"][0]["result"], "exact_match"
            )
            self.assertEqual(before, {path: self._sha256(path) for path in protected})
            self.assertEqual(manifest, json.loads(manifest_path.read_text()))

    def test_grade_routes_posthoc_rounding_cell_match_to_manual_review(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = self._make_project(root)
            manifest_path = root / "freeze.json"
            self._freeze(fixture, manifest_path)
            grader = self._write_grader(
                root, fixture, official_answer="7.043e12 J/day"
            )

            grade = self._grade(
                fixture,
                manifest=manifest_path,
                grader=grader,
                output=root / "grade.json",
            )
            self.assertEqual(grade["results"][0]["result"], "manual_review")
            self.assertIn(
                "rounding_sensitive", grade["results"][0]["reason"]
            )
            self.assertNotIn("canonical_rounding_match", grade["summary"])

    def test_grade_marks_adjacent_reporting_quanta_rounding_sensitive(self):
        candidate = {
            "result_kind": "numeric",
            "raw_result": {
                "value": "7.034394597164468e12",
                "unit": "J day^-1",
            },
            "reported_result": {
                "value": "7.03e12",
                "text": "7.03e12 J day^-1",
                "unit": "J day^-1",
                "precision": {
                    "kind": "significant_figures",
                    "digits": 3,
                },
            },
        }

        for official_answer in (
            "7.04e12 J day^-1",
            "7.04 × 10^12 J day^-1",
        ):
            with self.subTest(official_answer=official_answer):
                result, reason = blind._grade_one(candidate, official_answer)
                self.assertEqual(result, "manual_review")
                self.assertIn("rounding_sensitive", reason)
                self.assertIn("scientifically equivalent", reason)

    def test_grade_does_not_mark_unrelated_numeric_mismatches_rounding_sensitive(self):
        candidate = {
            "result_kind": "numeric",
            "reported_result": {
                "value": "12.34",
                "unit": "kg",
                "precision": {"kind": "decimal_places", "digits": 2},
            },
        }

        for official_answer in (
            "12.36 kg",
            "12.35 s",
            "12.35 mkg",
            "12.35",
            "12.35 kg at 20 C",
        ):
            with self.subTest(official_answer=official_answer):
                result, reason = blind._grade_one(candidate, official_answer)
                self.assertEqual(result, "manual_review")
                self.assertNotIn("rounding_sensitive", reason)

    def test_grade_does_not_hide_material_mass_fraction_error_as_rounding(self):
        candidate = {
            "result_kind": "numeric",
            "reported_result": {
                "value": "1.86",
                "unit": "%",
                "precision": {
                    "kind": "significant_figures",
                    "digits": 3,
                },
            },
        }

        result, reason = blind._grade_one(candidate, "1.94 %")

        self.assertEqual(result, "manual_review")
        self.assertNotIn("rounding_sensitive", reason)

    def test_grade_uses_both_reporting_quanta_for_rounding_sensitivity(self):
        candidate = {
            "result_kind": "numeric",
            "reported_result": {
                "value": "1.2",
                "unit": "mol",
                "precision": {"kind": "decimal_places", "digits": 1},
            },
        }

        touching_result, touching_reason = blind._grade_one(
            candidate, "1.25 mol"
        )
        separate_result, separate_reason = blind._grade_one(
            candidate, "1.26 mol"
        )

        self.assertEqual(touching_result, "manual_review")
        self.assertIn("rounding_sensitive", touching_reason)
        self.assertEqual(separate_result, "manual_review")
        self.assertNotIn("rounding_sensitive", separate_reason)

    def test_grading_override_handles_multi_number_prose_without_tolerance(self):
        official_answer = (
            "m_cat = 3.95e-4 g; E_photon = 5.1e-19 J; "
            "r_photon = 9.8e16 s^-1; phi = 1.94 %."
        )
        override = self._grading_override(official_answer)

        def candidate(value: str, *, unit: str = "%", text: str | None = None):
            return {
                "result_kind": "numeric",
                "reported_result": {
                    "value": value,
                    "text": text or f"{value} {unit}",
                    "unit": unit,
                    "precision": {
                        "kind": "significant_figures",
                        "digits": 3,
                    },
                },
            }

        unassisted_result, unassisted_reason = blind._grade_one(
            candidate("1.93"), official_answer
        )
        self.assertEqual(unassisted_result, "manual_review")
        self.assertNotIn("rounding_sensitive", unassisted_reason)

        canonical_result, canonical_reason = blind._grade_one(
            candidate("1.93"), official_answer, grading_override=override
        )
        legacy_result, legacy_reason = blind._grade_one(
            candidate("1.94"), official_answer, grading_override=override
        )
        self.assertEqual(canonical_result, "exact_match")
        self.assertIn("canonical_answer", canonical_reason)
        self.assertEqual(legacy_result, "exact_match")
        self.assertIn("accepted_legacy_answer", legacy_reason)

        for rejected in ("1.86", "1.92", "1.95"):
            with self.subTest(rejected=rejected):
                result, reason = blind._grade_one(
                    candidate(rejected),
                    official_answer,
                    grading_override=override,
                )
                self.assertEqual(result, "manual_review")
                self.assertNotIn("grading_override", reason)

    def test_grading_override_ignores_free_form_text_and_requires_matching_unit(self):
        official_answer = "1.93 %"
        override = self._grading_override(official_answer)
        for value in ("1.93", "1.94"):
            with self.subTest(value=value):
                candidate = {
                    "result_kind": "numeric",
                    "reported_result": {
                        "value": value,
                        "text": f"{value} %",
                        "unit": "mol",
                        "precision": {
                            "kind": "significant_figures",
                            "digits": 3,
                        },
                    },
                }
                result, reason = blind._grade_one(
                    candidate,
                    official_answer,
                    grading_override=override,
                )
                self.assertEqual(result, "manual_review")
                self.assertNotIn("grading_override", reason)

    def test_grading_override_schema_is_strict_and_hash_bound(self):
        official_answer = (
            "m_cat = 3.95e-4 g; E_photon = 5.1e-19 J; phi = 1.94 %."
        )
        candidate = {"result_kind": "numeric"}
        valid = self._grading_override(official_answer)
        validated = blind._validated_grading_override(
            valid,
            official_answer=official_answer,
            candidate=candidate,
            record_id="icho_2026_t8_a6",
        )
        self.assertEqual(validated, valid)

        malformed: list[tuple[str, dict[str, object], str]] = []

        unknown = dict(valid)
        unknown["unexpected"] = True
        malformed.append(("unknown", unknown, "unexpected unexpected"))

        wrong_hash = dict(valid)
        wrong_hash["official_answer_sha256"] = "0" * 64
        malformed.append(("wrong hash", wrong_hash, "does not bind official_answer"))

        missing = dict(valid)
        missing.pop("canonical_answer")
        malformed.append(("missing", missing, "missing canonical_answer"))

        bad_version = dict(valid)
        bad_version["schema_version"] = True
        malformed.append(("bad version", bad_version, "schema_version must equal 1"))

        empty_list = dict(valid)
        empty_list["accepted_legacy_answers"] = []
        malformed.append(("empty list", empty_list, "must be a non-empty list"))

        empty_alias = dict(valid)
        empty_alias["accepted_legacy_answers"] = ["  "]
        malformed.append(("empty alias", empty_alias, "must be a non-empty string"))

        duplicate = dict(valid)
        duplicate["accepted_legacy_answers"] = ["1.94 %", "  1.94   %  "]
        malformed.append(("duplicate", duplicate, "contains a duplicate alias"))

        too_many = dict(valid)
        too_many["accepted_legacy_answers"] = [
            f"{index}.00 %"
            for index in range(blind._MAX_GRADING_OVERRIDE_ALIASES + 1)
        ]
        malformed.append(("too many", too_many, "exceeds 8 aliases"))

        for label, value, error in malformed:
            with self.subTest(label=label):
                with self.assertRaisesRegex(blind.BlindEvaluationError, error):
                    blind._validated_grading_override(
                        value,
                        official_answer=official_answer,
                        candidate=candidate,
                        record_id="icho_2026_t8_a6",
                    )

        with self.assertRaisesRegex(
            blind.BlindEvaluationError, "only valid for a numeric candidate"
        ):
            blind._validated_grading_override(
                valid,
                official_answer=official_answer,
                candidate={"result_kind": "symbolic"},
                record_id="icho_2026_t8_a6",
            )

    def test_grade_accepts_hash_bound_legacy_override_end_to_end(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            fixture = self._make_project(root)
            manifest_path = root / "freeze.json"
            self._freeze(fixture, manifest_path)
            official_answer = (
                "raw value 7.034394597164468e12 J/day; "
                "official display 7.03e12 J/day"
            )
            override = self._grading_override(
                official_answer,
                canonical_answer="7.03e12 J/day",
                accepted_legacy_answers=["7.04e12 J/day"],
            )
            grader = self._write_grader(
                root,
                fixture,
                official_answer=official_answer,
                grading_override=override,
            )

            grade = self._grade(
                fixture,
                manifest=manifest_path,
                grader=grader,
                output=root / "grade.json",
            )

            self.assertEqual(grade["results"][0]["result"], "exact_match")
            self.assertIn(
                "accepted_legacy_answer", grade["results"][0]["reason"]
            )

    def test_cli_exposes_phase_separated_controller_commands(self):
        runner = CliRunner()
        freeze_help = runner.invoke(archon_app, ["blind-freeze", "--help"])
        verify_help = runner.invoke(archon_app, ["blind-verify-lean", "--help"])
        grade_help = runner.invoke(archon_app, ["blind-grade", "--help"])
        self.assertEqual(freeze_help.exit_code, 0, freeze_help.output)
        self.assertEqual(verify_help.exit_code, 0, verify_help.output)
        self.assertEqual(grade_help.exit_code, 0, grade_help.output)
        self.assertNotIn("--grader", freeze_help.output)
        self.assertIn("--controller-seal", freeze_help.output)
        self.assertIn("--scope-id", verify_help.output)
        self.assertIn("--grader", grade_help.output)
        self.assertIn("--expected-freeze-sha256", grade_help.output)
        self.assertIn("--expected-grader-sha256", grade_help.output)


if __name__ == "__main__":
    unittest.main()
