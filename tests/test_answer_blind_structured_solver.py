from __future__ import annotations

import importlib.util
import json
import os
import signal
import shutil
import stat
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
import subprocess
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_answer_blind_structured_solver.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_structured_solver", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def _write_root(path: Path, value: object, *, mode: int = 0o400) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(MODULE._pretty(value))
    os.chown(path, 0, 0)
    os.chmod(path, mode)


@unittest.skipUnless(os.geteuid() == 0, "structured controller is root-only")
class StructuredSolverTests(unittest.TestCase):
    def setUp(self) -> None:
        self.maxDiff = None
        self.old_test_validator = os.environ.get("ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR")
        os.environ["ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR"] = "1"
        self.base = Path(tempfile.mkdtemp(prefix="answer-blind-structured-", dir="/var/lib"))
        os.chown(self.base, 0, 0)
        os.chmod(self.base, 0o755)
        self.workspace = self.base / "workspace"
        self.controller = self.base / "controller"
        self.assets = self.base / "assets"
        for path, mode in (
            (self.workspace, 0o755), (self.controller, 0o700), (self.assets, 0o755)
        ):
            path.mkdir(mode=mode)
            os.chown(path, 0, 0)
            os.chmod(path, mode)
        self.image = self.assets / "page.png"
        self.image.write_bytes(b"not-a-real-image-but-hash-bound")
        os.chown(self.image, 0, 0)
        os.chmod(self.image, 0o400)
        self.row = {
            "schema_version": 1,
            "protocol": MODULE.PROTOCOL,
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "id": "icho_2026_t1_a1",
            "question": "Compute the stated quantity.",
            "current_question": "Compute the stated quantity.",
            "shared_context": "Use only the printed data.",
            "previous_parts": [],
            "images": ["page.png"],
            "problem_assets": [{
                "kind": "problem_page", "path": "page.png",
                "sha256": MODULE._file_sha(self.image),
            }],
            "requested_outputs": [{
                "id": "result", "source_requirement": "the quantity",
                "kind": "numeric", "unit": "mol",
                "reporting_policy": {"kind": "significant_figures", "digits": 3},
            }],
            "reporting_policy": {
                "intermediate_rounding": "forbidden",
                "final_precision": {"kind": "significant_figures", "digits": 3},
            },
            "measurement_policy": {"derived_tolerances": "prove from inputs"},
            "candidate_domain_policy": {"allowed_sources": ["problem_text"]},
        }
        self.bundle = self.base / "questions_only.jsonl"
        self.bundle.write_bytes(MODULE._canonical(self.row))
        os.chown(self.bundle, 0, 0)
        os.chmod(self.bundle, 0o400)
        report_path = self.workspace / "reports/source/problem.source.json"
        report_path.parent.mkdir(parents=True)
        _write_root(report_path, {
            "schema_version": 3, "evaluation_mode": "answer_blind",
            "official_answer_seen": False, "phase": "solve",
            "blind_record_sha256": MODULE._sha(MODULE._canonical(self.row)),
            "output_lean": "IChO2026Problems/problem_icho_2026_t1_a1.lean",
            "domain": "chemistry", "entry": self.row, "previous_parts": [],
        })
        self.run_id = "structured-unit-run"
        self.ready = self.controller / "ready.json"
        _write_root(self.ready, {
            "schema_version": 1, "protocol": MODULE.PROTOCOL,
            "phase": "model_broker_ready", "variant": "kimi-k3",
            "run_id": self.run_id, "listen_url": "http://127.0.0.1:18080/v1",
            "upstream_origin": "https://api.kimi.com",
            "allowed_model": "kimi-k3[1m]", "request_profile": MODULE.REQUEST_PROFILE,
            "public_dummy_key_sha256": MODULE._sha(MODULE.PUBLIC_DUMMY_TOKEN.encode()),
            "broker_uid": 65534, "broker_binary_sha256": "1" * 64,
            "started_at": "2026-08-12T00:00:00Z",
        })

    def tearDown(self) -> None:
        shutil.rmtree(self.base)
        if self.old_test_validator is None:
            os.environ.pop("ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR", None)
        else:
            os.environ["ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR"] = self.old_test_validator

    def _semantic_submission(self) -> dict[str, object]:
        return {
            "raw_result": {
                "expression": "printed derivation", "value": "1.234",
                "lean_expression": "Structured.rawResult",
                "derivation_spec": "Structured.rawDerived",
                "certified_interval": {"lower": "1.233", "upper": "1.235"},
                "unit": "mol",
            },
            "reported_result": {
                "value": "1.23", "text": "1.23 mol",
                "lean_expression": "Structured.reportedSpec", "unit": "mol",
            },
            "candidate_domain_derivation": {
                "kind": "problem_text", "evidence": ["printed data"],
                "depends_on": [],
            },
            "lean_declarations": ["Structured.rawResult", "Structured.reportedResult"],
        }

    def _submission(self) -> dict[str, object]:
        return {
            **self._semantic_submission(),
            "lean_source": (
                "import Mathlib\nnamespace Structured\n"
                "def rawResult : ℚ := 1234 / 1000\n"
                "theorem rawDerived : rawResult = 617 / 500 := by norm_num [rawResult]\n"
                "theorem reportedResult : True := by trivial\nend Structured\n"
            ),
            "blueprint": "A source-first derivation with raw and reported results.\n",
        }

    def _transcript(self, *, count: int) -> Path:
        path = self.controller / "transcript.json"
        _write_root(path, {
            "schema_version": 1, "protocol": MODULE.PROTOCOL,
            "phase": "model_broker_transcript", "variant": "kimi-k3",
            "run_id": self.run_id, "request_profile": MODULE.REQUEST_PROFILE,
            "ready_receipt_sha256": MODULE._file_sha(self.ready),
            "request_count": count, "request_response_chain_sha256": "2" * 64,
            "started_at": "2026-08-12T00:00:00Z",
            "stopped_at": "2026-08-12T00:00:01Z", "broker_stopped": True,
        })
        return path

    def test_controller_atomic_write_retries_short_os_write(self) -> None:
        destination = self.controller / "partial-write.json"
        real_write = os.write
        calls = 0

        def partial(descriptor: int, payload: object) -> int:
            nonlocal calls
            calls += 1
            view = memoryview(payload)
            amount = max(1, len(view) // 2)
            return real_write(descriptor, view[:amount])

        with mock.patch.object(MODULE.os, "write", side_effect=partial):
            MODULE._atomic_root_file(destination, b"0123456789abcdef")
        self.assertEqual(destination.read_bytes(), b"0123456789abcdef")
        self.assertGreater(calls, 1)

    def _precommit(
        self, variant: str = "kimi-k3", scope_ids: list[str] | None = None,
    ) -> Path:
        family, model = MODULE.MODELS[variant]
        path = self.controller / f"{variant}-source-first-precommit.json"
        _write_root(path, {
            "schema_version": 1, "protocol": MODULE.PROTOCOL,
            "phase": "structured_source_first_precommit",
            "variant": variant, "model_family": family, "model_id": model,
            "run_id": self.run_id,
            "request_profile": "tool_free_structured_independent_review_v1",
            "tools_enabled": False, "store": False,
            "scope_ids": sorted(scope_ids or [self.row["id"]]),
            "controller_binary_sha256": "a" * 64,
            "input_inventory": {"root": str(self.base), "files": {"x": "b" * 64}, "files_sha256": "c" * 64},
            "review_projection_sha256": "d" * 64,
            "adapter_provenance": {}, "adapter": "fixture",
            "transport": {}, "request": {}, "response": {},
            "model_submission": {}, "normalized_response_sha256": "e" * 64,
            "request_response_chain_sha256": "f" * 64,
            "status": "accepted", "finalized_before_solver": True,
        })
        return path

    def test_mocked_tool_free_iteration_publishes_exact_artifacts_and_chain(self) -> None:
        submission = self._submission()
        calls: list[dict[str, object]] = []

        def provider(_url: str, request: object) -> MODULE.ProviderReply:
            assert isinstance(request, dict)
            calls.append(request)
            return MODULE.ProviderReply(
                MODULE._canonical({"content": [{"type": "text", "text": json.dumps(submission)}]}),
                submission,
            )

        receipt = MODULE.run_structured_solver(
            workspace=self.workspace, controller_dir=self.controller,
            bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
            run_id=self.run_id, broker_ready=self.ready,
            source_first_precommit=self._precommit(),
            broker_transcript=self._transcript(count=1), scope_ids=[self.row["id"]],
            max_attempts=2, provider_call=provider, validator=lambda _payloads: [],
        )
        self.assertEqual(receipt["request_profile"], MODULE.REQUEST_PROFILE)
        self.assertFalse(receipt["tools_enabled"])
        self.assertEqual(calls[0]["tools"], [])
        self.assertNotIn("previous_response_id", calls[0])
        target = receipt["targets"][0]
        self.assertEqual(target["accepted_attempt"], 1)
        for locator in target["final_artifacts"].values():
            artifact = self.workspace / locator["path"]
            self.assertTrue(artifact.is_file())
            self.assertEqual(MODULE._file_sha(artifact), locator["sha256"])
            self.assertEqual(stat.S_IMODE(artifact.stat().st_mode), 0o400)

    def test_rejected_scan_is_hash_chained_and_only_diagnostics_feed_next_call(self) -> None:
        bad = self._submission()
        bad["lean_source"] = "import Mathlib\nrun_cmd IO.println \"escape\"\n"
        good = self._submission()
        replies = [bad, good]
        requests: list[dict[str, object]] = []

        def provider(_url: str, request: object) -> MODULE.ProviderReply:
            assert isinstance(request, dict)
            requests.append(request)
            submission = replies.pop(0)
            return MODULE.ProviderReply(MODULE._canonical({"mock": len(requests)}), submission)

        receipt = MODULE.run_structured_solver(
            workspace=self.workspace, controller_dir=self.controller,
            bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
            run_id=self.run_id, broker_ready=self.ready,
            source_first_precommit=self._precommit(),
            broker_transcript=self._transcript(count=2), scope_ids=[self.row["id"]],
            max_attempts=2, provider_call=provider, validator=lambda _payloads: [],
        )
        target = receipt["targets"][0]
        self.assertEqual(target["accepted_attempt"], 2)
        first = MODULE._load_json(Path(target["attempts"][0]["path"]), label="attempt")
        second = MODULE._load_json(Path(target["attempts"][1]["path"]), label="attempt")
        self.assertEqual(first["status"], "rejected")
        self.assertEqual(first["diagnostics"][0]["kind"], "controller_scan")
        self.assertEqual(second["previous_attempt_sha256"], target["attempts"][0]["sha256"])
        prompt = requests[1]["messages"][0]["content"][0]["text"]
        self.assertIn("controller_scan", prompt)
        self.assertNotIn("7.04", prompt)

    def test_malformed_wrong_type_and_oversize_responses_retry_fail_closed(self) -> None:
        missing = self._submission()
        missing.pop("blueprint")
        wrong_type = self._submission()
        wrong_type["lean_declarations"] = "not-a-list"
        valid = self._submission()
        replies = [missing, wrong_type, "oversize", valid]

        def provider(_url: str, request: object) -> MODULE.ProviderReply:
            assert isinstance(request, dict)
            value = replies.pop(0)
            provenance = {
                "endpoint": "/v1/messages",
                "request_sha256": MODULE._sha(MODULE._canonical(request).rstrip(b"\n")),
                "raw_response_sha256": "",
                "reasoning_control": {
                    "provider_field_supported": False,
                    "model_id": "kimi-k3[1m]",
                    "max_tokens": 131072,
                },
            }
            if value == "oversize":
                raw = b"x" * (MODULE.MAX_PROVIDER_RESPONSE_BYTES + 1)
                provenance["raw_response_sha256"] = MODULE._sha(raw)
                return MODULE.ProviderReply(raw, valid, provenance=provenance)
            assert isinstance(value, dict)
            raw = MODULE._canonical({
                "content": [{"type": "text", "text": json.dumps(value)}],
            })
            provenance["raw_response_sha256"] = MODULE._sha(raw)
            return MODULE.ProviderReply(raw, value, provenance=provenance)

        receipt = MODULE.run_structured_solver(
            workspace=self.workspace, controller_dir=self.controller,
            bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
            run_id=self.run_id, broker_ready=self.ready,
            source_first_precommit=self._precommit(),
            broker_transcript=self._transcript(count=4),
            scope_ids=[self.row["id"]], max_attempts=4,
            provider_call=provider, validator=lambda _payloads: [],
        )
        attempts = [
            MODULE._load_json(Path(locator["path"]), label="retry attempt")
            for locator in receipt["targets"][0]["attempts"]
        ]
        self.assertEqual(
            [attempt["status"] for attempt in attempts],
            ["rejected", "rejected", "transport_error", "accepted"],
        )
        for attempt in attempts[:2]:
            self.assertIsNotNone(attempt["response"])
            self.assertIsNone(attempt["submission"])
            self.assertNotIn("transport_failure_receipt", attempt["adapter_provenance"])
        oversized = attempts[2]
        self.assertIsNone(oversized["response"])
        self.assertIsNone(oversized["submission"])
        self.assertEqual(
            set(oversized["adapter_provenance"]), {"transport_failure_receipt"},
        )
        failure = MODULE._load_json(
            Path(oversized["adapter_provenance"]["transport_failure_receipt"]["path"]),
            label="oversized response failure receipt",
        )
        self.assertEqual(failure["status"], "failed_without_valid_response")
        self.assertEqual(attempts[3]["attempt_chain_sha256"], receipt["targets"][0]["target_chain_sha256"])

    def test_exhausted_target_writes_immutable_incomplete_aggregate(self) -> None:
        bad = self._submission()
        bad["lean_source"] = "import Mathlib\nrun_cmd IO.println \"escape\"\n"

        def provider(_url: str, _request: object) -> MODULE.ProviderReply:
            return MODULE.ProviderReply(MODULE._canonical({"fixture": "bad"}), bad)

        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE.run_structured_solver(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
                run_id=self.run_id, broker_ready=self.ready,
                source_first_precommit=self._precommit(),
                broker_transcript=self._transcript(count=1), scope_ids=[self.row["id"]],
                max_attempts=1, provider_call=provider, validator=lambda _payloads: [],
            )
        path = self.controller / "kimi-k3-structured-solver-incomplete.json"
        failure = MODULE._load_json(path, label="incomplete aggregate")
        self.assertFalse(failure["all_targets_finalized"])
        self.assertEqual(failure["error_code"], "structured_target_incomplete")
        self.assertEqual(len(failure["attempt_receipts"]), 1)
        self.assertEqual(stat.S_IMODE(path.stat().st_mode), 0o400)

    def test_controller_type_error_is_not_retried_as_provider_failure(self) -> None:
        submission = self._submission()
        calls = 0

        def provider(_url: str, _request: object) -> MODULE.ProviderReply:
            nonlocal calls
            calls += 1
            return MODULE.ProviderReply(MODULE._canonical({"fixture": 1}), submission)

        original = MODULE._compose_blueprint

        def broken_controller(**_kwargs: object) -> bytes:
            raise TypeError("controller programming error")

        MODULE._compose_blueprint = broken_controller
        try:
            with self.assertRaisesRegex(TypeError, "controller programming error"):
                MODULE.run_structured_solver(
                    workspace=self.workspace, controller_dir=self.controller,
                    bundle_path=self.bundle, asset_root=self.assets,
                    variant="kimi-k3", run_id=self.run_id,
                    source_first_precommit=self._precommit(),
                    broker_ready=self.ready, broker_transcript=self._transcript(count=1),
                    scope_ids=[self.row["id"]], max_attempts=2,
                    provider_call=provider, validator=lambda _payloads: [],
                )
        finally:
            MODULE._compose_blueprint = original
        self.assertEqual(calls, 1)
        failure = MODULE._load_json(
            self.controller / "kimi-k3-structured-solver-incomplete.json",
            label="controller error incomplete aggregate",
        )
        self.assertFalse(failure["all_targets_finalized"])
        self.assertEqual(failure["attempt_receipts"], [])

    def test_second_target_failure_binds_completed_target_and_all_attempts(self) -> None:
        row2 = json.loads(json.dumps(self.row))
        row2["id"] = "icho_2026_t1_a2"
        row2["current_question"] = "Compute the second stated quantity."
        self.bundle.write_bytes(MODULE._canonical(self.row) + MODULE._canonical(row2))
        report2 = self.workspace / "reports/source/problem2.source.json"
        _write_root(report2, {
            "schema_version": 3, "evaluation_mode": "answer_blind",
            "official_answer_seen": False, "phase": "solve",
            "blind_record_sha256": MODULE._sha(MODULE._canonical(row2)),
            "output_lean": "IChO2026Problems/problem_icho_2026_t1_a2.lean",
            "domain": "chemistry", "entry": row2, "previous_parts": [],
        })
        good = self._submission()
        bad = self._submission()
        bad["lean_source"] = "import Mathlib\naxiom hidden : False\n"

        def provider(_url: str, request: object) -> MODULE.ProviderReply:
            assert isinstance(request, dict)
            prompt = request["messages"][0]["content"][0]["text"]
            submission = bad if "icho_2026_t1_a2" in prompt else good
            return MODULE.ProviderReply(MODULE._canonical({"fixture": "response"}), submission)

        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE.run_structured_solver(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
                run_id=self.run_id, broker_ready=self.ready,
                source_first_precommit=self._precommit(
                    scope_ids=[self.row["id"], row2["id"]]
                ),
                broker_transcript=self._transcript(count=2),
                scope_ids=[self.row["id"], row2["id"]], max_attempts=1,
                provider_call=provider, validator=lambda _payloads: [],
            )
        failure = MODULE._load_json(
            self.controller / "kimi-k3-structured-solver-incomplete.json",
            label="two-target incomplete aggregate",
        )
        self.assertEqual([item["id"] for item in failure["completed_targets"]], [self.row["id"]])
        self.assertEqual(len(failure["attempt_receipts"]), 2)

    def test_prepared_problem_only_blueprint_is_preserved_and_extended(self) -> None:
        submission = self._submission()
        target = "IChO2026Problems/problem_icho_2026_t1_a1.lean"
        report = "reports/source/problem.source.json"
        blueprint = self.workspace / "blueprint/src/chapters/IChO2026Problems_problem_icho_2026_t1_a1.tex"
        blueprint.parent.mkdir(parents=True)
        base = (
            "% --- Archon physics formalization source begin ---\n"
            f"% archon:covers {target}\n"
            f"% archon:source-report {report}\n"
            "\\paragraph{Problem source.}\nProblem-only fixture.\n"
            "\\paragraph{Formalization target.}\nBuild the target.\n"
            "% --- Archon physics formalization source end ---\n"
        ).encode()
        blueprint.write_bytes(base)
        os.chown(blueprint, 0, 0)
        os.chmod(blueprint, 0o400)

        def provider(_url: str, _request: object) -> MODULE.ProviderReply:
            return MODULE.ProviderReply(MODULE._canonical({"fixture": 1}), submission)

        receipt = MODULE.run_structured_solver(
            workspace=self.workspace, controller_dir=self.controller,
            bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
            run_id=self.run_id, broker_ready=self.ready,
            source_first_precommit=self._precommit(),
            broker_transcript=self._transcript(count=1), scope_ids=[self.row["id"]],
            max_attempts=1, provider_call=provider, validator=lambda _payloads: [],
        )
        final = blueprint.read_bytes()
        self.assertIn(b"Problem-only fixture.", final)
        self.assertNotIn(b"Formalization target", final)
        self.assertNotIn(b"Build the target", final)
        self.assertIn(b"% --- Answer-blind structured proof begin ---", final)
        self.assertIn(submission["blueprint"].encode(), final)
        prepared = receipt["targets"][0]["prepared_blueprint"]
        self.assertIsNotNone(prepared)
        self.assertEqual(Path(prepared["path"]).read_bytes(), base)
        self.assertEqual(prepared["sha256"], MODULE._sha(base))
        self.assertEqual(stat.S_IMODE(Path(prepared["path"]).stat().st_mode), 0o400)
        self.assertEqual(
            MODULE._sha(final),
            receipt["targets"][0]["final_artifacts"]["blueprint"]["sha256"],
        )

    @unittest.skipUnless(
        Path("/opt/icho-answer-blind-runtime/venv/bin/python").is_file(),
        "trusted Archon runtime is unavailable",
    )
    def test_physics_formalize_problem_only_chapter_flows_into_structured_solver(self) -> None:
        project = self.base / "prepared-project"
        project.mkdir(mode=0o755)
        (project / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")
        command = """
import sys
from pathlib import Path
from archon.commands.physics_formalize import PhysicsFormalizeCommand
PhysicsFormalizeCommand(
    sys.argv[1], input_jsonl=Path(sys.argv[2]), image_root=Path(sys.argv[3]),
    evaluation_mode='answer_blind', out_dir=Path('IChO2026Problems'),
    report_dir=Path('reports/source'),
    work_dir=Path(sys.argv[1]) / '.archon/physics-formalize/structured-test',
).run()
"""
        completed = subprocess.run(
            ["/opt/icho-answer-blind-runtime/venv/bin/python", "-c", command,
             str(project), str(self.bundle), str(self.assets)],
            cwd=ROOT, env={
                "PYTHONPATH": str(ROOT / "src"), "PYTHONSAFEPATH": "1",
                "PATH": "/opt/icho-answer-blind-runtime/lean-v4.31.0/bin",
                "HOME": str(self.base), "TMPDIR": str(self.base),
                "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
            },
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=60, check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout.decode(errors="replace"))
        report_paths = list((project / "reports/source").glob("*.source.json"))
        chapter_paths = [
            path for path in (project / "blueprint/src/chapters").glob("*.tex")
            if b"Archon physics formalization source begin" in path.read_bytes()
        ]
        self.assertEqual(len(report_paths), 1)
        self.assertEqual(len(chapter_paths), 1)
        report = json.loads(report_paths[0].read_text())
        base_blueprint = chapter_paths[0].read_bytes()
        self.assertNotIn(b"Recorded answer/context", base_blueprint)
        self.assertEqual(base_blueprint.count(b"Archon physics formalization source begin"), 1)
        for directory in (project, project / "reports", project / "reports/source"):
            os.chown(directory, 0, 0)
            os.chmod(directory, 0o755)
        for path in project.rglob("*"):
            if path.is_symlink():
                continue
            os.chown(path, 0, 0)
            os.chmod(path, 0o755 if path.is_dir() else 0o400)
        prepared_controller = self.base / "prepared-controller"
        prepared_controller.mkdir(mode=0o700)
        os.chown(prepared_controller, 0, 0)
        ready = prepared_controller / "ready.json"
        _write_root(ready, {
            "schema_version": 1, "protocol": MODULE.PROTOCOL,
            "phase": "model_broker_ready", "variant": "kimi-k3",
            "run_id": self.run_id, "listen_url": "http://127.0.0.1:18082/v1",
            "upstream_origin": "https://api.kimi.com", "allowed_model": "kimi-k3[1m]",
            "request_profile": MODULE.REQUEST_PROFILE,
            "public_dummy_key_sha256": MODULE._sha(MODULE.PUBLIC_DUMMY_TOKEN.encode()),
            "broker_uid": 65534, "broker_binary_sha256": "1" * 64,
            "started_at": "2026-08-12T00:00:00Z",
        })
        transcript = prepared_controller / "transcript.json"
        _write_root(transcript, {
            "schema_version": 1, "protocol": MODULE.PROTOCOL,
            "phase": "model_broker_transcript", "variant": "kimi-k3",
            "run_id": self.run_id, "request_profile": MODULE.REQUEST_PROFILE,
            "ready_receipt_sha256": MODULE._file_sha(ready), "request_count": 1,
            "request_response_chain_sha256": "4" * 64,
            "started_at": "2026-08-12T00:00:00Z",
            "stopped_at": "2026-08-12T00:00:01Z", "broker_stopped": True,
        })
        submission = self._submission()

        def provider(_url: str, _request: object) -> MODULE.ProviderReply:
            return MODULE.ProviderReply(MODULE._canonical({"fixture": 1}), submission)

        receipt = MODULE.run_structured_solver(
            workspace=project, controller_dir=prepared_controller,
            bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
            run_id=self.run_id, broker_ready=ready, broker_transcript=transcript,
            source_first_precommit=self._precommit(),
            scope_ids=[self.row["id"]], max_attempts=1,
            provider_call=provider, validator=lambda _payloads: [],
        )
        final_blueprint = chapter_paths[0].read_bytes()
        self.assertEqual(final_blueprint.count(b"Archon physics formalization source begin"), 1)
        self.assertEqual(final_blueprint.count(b"Answer-blind structured proof begin"), 1)
        self.assertNotIn(b"sorry", final_blueprint.lower())
        self.assertNotIn(b"autoformaliz", final_blueprint.lower())
        prepared = receipt["targets"][0]["prepared_blueprint"]
        self.assertEqual(prepared["sha256"], MODULE._sha(base_blueprint))
        self.assertEqual(Path(prepared["path"]).read_bytes(), base_blueprint)
        self.assertEqual(report["output_lean"], receipt["targets"][0]["final_artifacts"]["lean"]["path"])

    def test_kimi_internal_broker_lifecycle_stops_before_aggregate(self) -> None:
        submission = self._submission()
        stopped: list[bool] = []

        class Broker:
            @staticmethod
            def start_broker(**_kwargs: object) -> dict[str, object]:
                ready = self.controller / "kimi-k3-model-broker-ready.json"
                _write_root(ready, {
                    "schema_version": 1, "protocol": MODULE.PROTOCOL,
                    "phase": "model_broker_ready", "variant": "kimi-k3",
                    "run_id": self.run_id, "listen_url": "http://127.0.0.1:18081/v1",
                    "upstream_origin": "https://api.kimi.com",
                    "allowed_model": "kimi-k3[1m]", "request_profile": MODULE.REQUEST_PROFILE,
                    "public_dummy_key_sha256": MODULE._sha(MODULE.PUBLIC_DUMMY_TOKEN.encode()),
                    "broker_uid": 65534, "broker_binary_sha256": "1" * 64,
                    "started_at": "2026-08-12T00:00:00Z",
                })
                return {"ready": str(ready), "sha256": MODULE._file_sha(ready)}

            @staticmethod
            def stop_broker(**_kwargs: object) -> Path:
                stopped.append(True)
                ready = self.controller / "kimi-k3-model-broker-ready.json"
                transcript = self.controller / "kimi-k3-model-broker-transcript.json"
                _write_root(transcript, {
                    "schema_version": 1, "protocol": MODULE.PROTOCOL,
                    "phase": "model_broker_transcript", "variant": "kimi-k3",
                    "run_id": self.run_id, "request_profile": MODULE.REQUEST_PROFILE,
                    "ready_receipt_sha256": MODULE._file_sha(ready),
                    "request_count": 1, "request_response_chain_sha256": "3" * 64,
                    "started_at": "2026-08-12T00:00:00Z",
                    "stopped_at": "2026-08-12T00:00:01Z", "broker_stopped": True,
                })
                return transcript

        credential = self.base / "credential"
        credential.write_text("fixture")
        os.chmod(credential, 0o600)

        def provider(_url: str, _request: object) -> MODULE.ProviderReply:
            return MODULE.ProviderReply(MODULE._canonical({"fixture": 1}), submission)

        old_loader = MODULE._load_model_broker_module
        MODULE._load_model_broker_module = lambda: Broker
        try:
            receipt = MODULE.run_structured_solver(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
                run_id=self.run_id, scope_ids=[self.row["id"]], max_attempts=1,
                source_first_precommit=self._precommit(),
                broker_credential_file=credential, broker_user="nobody",
                provider_call=provider, validator=lambda _payloads: [],
            )
        finally:
            MODULE._load_model_broker_module = old_loader
        self.assertEqual(stopped, [True])
        self.assertEqual(receipt["transport"]["kind"], "structured_broker_http_v1")

    def test_invalid_ready_and_stop_failure_write_ledger_and_force_cleanup(self) -> None:
        child_pid: int | None = None

        class BrokenBroker:
            @staticmethod
            def start_broker(**_kwargs: object) -> dict[str, object]:
                nonlocal child_pid
                ready = self.controller / "kimi-k3-model-broker-ready.json"
                _write_root(ready, {
                    "schema_version": 1, "protocol": MODULE.PROTOCOL,
                    "phase": "model_broker_ready", "variant": "kimi-k3",
                    "run_id": self.run_id,
                    "listen_url": "http://127.0.0.1:18083/v1",
                    "upstream_origin": "https://api.kimi.com",
                    "allowed_model": "kimi-k3[1m]",
                    "request_profile": "wrong-profile",
                    "public_dummy_key_sha256": MODULE._sha(
                        MODULE.PUBLIC_DUMMY_TOKEN.encode()
                    ),
                    "broker_uid": 65534, "broker_binary_sha256": "1" * 64,
                    "started_at": "2026-08-12T00:00:00Z",
                })
                child_pid = os.fork()
                if child_pid == 0:
                    signal.signal(signal.SIGTERM, signal.SIG_DFL)
                    signal.pause()
                    os._exit(0)
                state = self.controller / "kimi-k3-model-broker-state.json"
                _write_root(state, {
                    "schema_version": 1, "protocol": MODULE.PROTOCOL,
                    "phase": "model_broker_state", "variant": "kimi-k3",
                    "run_id": self.run_id, "supervisor_pid": child_pid,
                    "supervisor_start_ticks": MODULE._process_start_ticks(child_pid),
                    "lease_parent_pid": os.getpid(), "lease_parent_start_ticks": 1,
                    "worker_pid": child_pid,
                })
                return {"ready": str(ready), "sha256": MODULE._file_sha(ready)}

            @staticmethod
            def stop_broker(**_kwargs: object) -> Path:
                raise RuntimeError("simulated stop failure")

        credential = self.base / "broken-broker-credential"
        credential.write_text("fixture")
        os.chmod(credential, 0o600)
        old_loader = MODULE._load_model_broker_module
        MODULE._load_model_broker_module = lambda: BrokenBroker
        try:
            with self.assertRaises(MODULE.StructuredSolverError):
                MODULE.run_structured_solver(
                    workspace=self.workspace, controller_dir=self.controller,
                    bundle_path=self.bundle, asset_root=self.assets,
                    variant="kimi-k3", run_id=self.run_id,
                    source_first_precommit=self._precommit(),
                    scope_ids=[self.row["id"]], max_attempts=1,
                    broker_credential_file=credential, broker_user="nobody",
                    provider_call=lambda _url, _request: self.fail(
                        "provider must not run after invalid readiness"
                    ),
                    validator=lambda _payloads: [],
                )
            ledger_path = self.controller / "kimi-k3-structured-solver-incomplete.json"
            ledger = MODULE._load_json(ledger_path, label="broker cleanup ledger")
            self.assertEqual(ledger["stage"], "broker_ready_cleanup")
            self.assertEqual(
                ledger["error_code"],
                "model_broker_ready_invalid_and_stop_failed",
            )
            self.assertEqual(
                ledger["source_first_precommit"]["sha256"],
                MODULE._file_sha(self._precommit()),
            )
            assert child_pid is not None
            self.assertEqual(MODULE._process_start_ticks(child_pid), -1)
        finally:
            MODULE._load_model_broker_module = old_loader
            if child_pid is not None and MODULE._process_start_ticks(child_pid) != -1:
                os.kill(child_pid, signal.SIGKILL)
                os.waitpid(child_pid, 0)

    def test_response_schema_and_lean_scanner_fail_closed(self) -> None:
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._validate_lean_source("import Mathlib\naxiom answer : False\n")
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._strict_json(b'{"x":1,"x":2}', label="response")
        schema = MODULE.submission_json_schema()
        self.assertFalse(schema["additionalProperties"])
        self.assertEqual(set(schema["required"]), MODULE.SUBMISSION_FIELDS)
        self.assertNotIn("result_kind", schema["properties"])
        def visit(value: object) -> None:
            if isinstance(value, dict):
                self.assertNotIn("oneOf", value)
                self.assertNotIn("uniqueItems", value)
                for child in value.values():
                    visit(child)
            elif isinstance(value, list):
                for child in value:
                    visit(child)
        visit(schema)
        submission = self._submission()
        submission["result_kind"] = "symbolic"
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._construct_candidate(
                submission, target_id=self.row["id"],
                blind_hash=MODULE._sha(MODULE._canonical(self.row)),
                source_entry=self.row,
            )

    def test_controller_derives_single_underdetermined_and_preserves_null(self) -> None:
        submission = self._submission()
        submission["reported_result"]["value"] = None
        candidate = MODULE._construct_candidate(
            submission, target_id=self.row["id"],
            blind_hash=MODULE._sha(MODULE._canonical(self.row)),
            source_entry=self.row,
        )
        self.assertEqual(candidate["result_kind"], "underdetermined")
        self.assertIn("value", candidate["reported_result"])
        self.assertIsNone(candidate["reported_result"]["value"])

    def test_multi_output_symbolic_producer_matches_freeze_reconstruction(self) -> None:
        from archon.commands import blind_evaluation as blind
        from archon.commands.loop.review_source_contract import (
            validate_blind_result_contracts,
        )

        row = json.loads(json.dumps(self.row))
        row["requested_outputs"] = [
            {
                "id": "count", "source_requirement": "the exact count",
                "kind": "integer", "unit": None,
                "reporting_policy": {"kind": "exact_integer", "source": "question"},
            },
            {
                "id": "class", "source_requirement": "the stated class",
                "kind": "classification", "unit": None,
                "reporting_policy": {"kind": "exact_symbolic", "source": "question"},
            },
        ]
        row["reporting_policy"] = {
            "intermediate_rounding": "forbidden",
            "explicit_precision": "use_only_precision_requested_in_problem",
            "default_final_display": "exact",
            "final_precision": {
                "kind": "per_requested_output", "source": "requested_outputs",
            },
            "tie_rule": "not_applicable",
            "raw_result_required": True,
        }
        self.bundle.write_bytes(MODULE._canonical(row))
        report_path = self.workspace / "reports/source/problem.source.json"
        _write_root(report_path, {
            "schema_version": 3, "evaluation_mode": "answer_blind",
            "official_answer_seen": False, "phase": "solve",
            "blind_record_sha256": MODULE._sha(MODULE._canonical(row)),
            "output_lean": "IChO2026Problems/problem_icho_2026_t1_a1.lean",
            "domain": "chemistry", "entry": row, "previous_parts": [],
        })
        submission = self._submission()
        submission.update({
            "raw_result": {
                "expression": "derive the count and classification from the printed facts",
                "value": {
                    "count": {
                        "kind": "integer", "status": "derived", "value": "3",
                        "proposition": "exactly three cases satisfy the constraints",
                        "constraints": ["exhaustive case split over the printed cases"],
                    },
                    "class": {
                        "kind": "classification", "status": "derived",
                        "normalized_result": "acidic",
                        "proposition": "the printed criterion classifies the sample as acidic",
                        "constraints": ["apply only the criterion stated in the question"],
                    },
                },
                "lean_expression": "StructuredMulti.rawSpec",
                "derivation_spec": "StructuredMulti.rawDerived",
                "certified_interval": None, "unit": None,
            },
            "reported_result": {
                "value": {
                    "count": {"status": "derived", "value": "3"},
                    "class": {"status": "derived", "value": "acidic"},
                },
                "text": "count=3; class=acidic",
                "lean_expression": "StructuredMulti.reportedSpec", "unit": None,
            },
            "lean_declarations": [
                "StructuredMulti.rawContract", "StructuredMulti.reportedContract",
            ],
            "blueprint": "Derive both requested outputs independently from the printed facts.\n",
        })
        initial = MODULE._construct_candidate(
            submission, target_id=row["id"],
            blind_hash=MODULE._sha(MODULE._canonical(row)), source_entry=row,
        )
        contract_types = {
            item["role"]: item["expected_type"]
            for item in initial["lean_result_contracts"]
        }
        submission["lean_source"] = (
            "import Mathlib\nnamespace StructuredMulti\n"
            "def rawSpec : Prop := True\n"
            "def reportedSpec : Prop := True\n"
            "theorem rawContract : " + contract_types["raw_result"]
            + " := by constructor; rfl; trivial\n"
            "theorem reportedContract : " + contract_types["reported_result"]
            + " := by constructor; rfl; trivial\nend StructuredMulti\n"
        )
        expected_candidate = MODULE._construct_candidate(
            submission, target_id=row["id"],
            blind_hash=MODULE._sha(MODULE._canonical(row)), source_entry=row,
        )
        raw_response = MODULE._canonical({
            "content": [{"type": "text", "text": json.dumps(submission)}],
        })

        def provider(_url: str, request: object) -> MODULE.ProviderReply:
            assert isinstance(request, dict)
            return MODULE.ProviderReply(raw_response, submission, provenance={
                "endpoint": "/v1/messages",
                "request_sha256": MODULE._sha(MODULE._canonical(request).rstrip(b"\n")),
                "raw_response_sha256": MODULE._sha(raw_response),
                "reasoning_control": {
                    "provider_field_supported": False,
                    "model_id": "kimi-k3[1m]", "max_tokens": 131072,
                },
            })

        old_shallow = os.environ.pop("ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR", None)
        try:
            receipt = MODULE.run_structured_solver(
                workspace=self.workspace, controller_dir=self.controller,
                bundle_path=self.bundle, asset_root=self.assets, variant="kimi-k3",
                run_id=self.run_id, broker_ready=self.ready,
                source_first_precommit=self._precommit(),
                broker_transcript=self._transcript(count=1),
                scope_ids=[row["id"]], max_attempts=1,
                provider_call=provider, validator=lambda _payloads: [],
            )
        finally:
            if old_shallow is not None:
                os.environ["ANSWER_BLIND_TEST_ALLOW_SHALLOW_VALIDATOR"] = old_shallow
        candidate_path = self.workspace / receipt["targets"][0]["final_artifacts"]["candidate"]["path"]
        candidate = MODULE._strict_json(candidate_path.read_bytes(), label="multi-output candidate")
        self.assertEqual(candidate, expected_candidate)
        self.assertEqual(candidate["result_kind"], "symbolic")
        self.assertEqual(set(candidate["raw_result"]["value"]), {"count", "class"})
        self.assertEqual(set(candidate["reported_result"]["value"]), {"count", "class"})
        self.assertEqual(candidate["reported_result"]["value"]["count"]["value"], "3")
        self.assertEqual(candidate["reported_result"]["value"]["class"]["value"], "acidic")
        self.assertEqual(validate_blind_result_contracts(candidate), [])
        # These are the exact pure reconstruction and policy validators used
        # by freeze when replaying the accepted provider response.
        extracted = blind._structured_submission_from_response(
            blind._strict_json_object(raw_response, label="multi-output response"),
            variant="kimi-k3",
        )
        self.assertEqual(extracted, submission)
        self.assertEqual(
            blind._construct_structured_candidate(
                extracted, target_id=row["id"],
                blind_hash=MODULE._sha(MODULE._canonical(row)), source_entry=row,
            ),
            candidate,
        )
        blind._validate_candidate(
            candidate, expected_id=row["id"],
            expected_blind_hash=MODULE._sha(MODULE._canonical(row)),
        )
        blind._validate_candidate_source_policies(
            candidate, source_entry=row, record_id=row["id"],
        )

    @unittest.skipUnless(
        Path("/opt/icho-answer-blind-runtime/lean-v4.31.0/bin/lake").is_file()
        and Path("/opt/icho-answer-blind-runtime/lake/packages").is_dir(),
        "sealed Lean runtime fixture is unavailable",
    )
    def test_clean_validator_builds_support_from_source_without_solver_oleans(self) -> None:
        seed = ROOT / "icho_2026_run"
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "IChO2026Chem.lean"):
            shutil.copyfile(seed / name, self.workspace / name)
            os.chown(self.workspace / name, 0, 0)
            os.chmod(self.workspace / name, 0o400)
        shutil.copytree(seed / "IChO2026Chem", self.workspace / "IChO2026Chem")
        for path in (self.workspace / "IChO2026Chem").rglob("*"):
            os.chown(path, 0, 0)
            os.chmod(path, 0o500 if path.is_dir() else 0o400)
        scratch = self.base / "lean-scratch"
        scratch.mkdir(mode=0o755)
        os.chown(scratch, 0, 0)
        candidate = {
            "lean_result_contracts": [
                {
                    "declaration": "Structured.rawContract",
                    "expected_type": (
                        "(Structured.rawDerivedFromProblem) ∧ "
                        "(((1233 : ℝ) / 1000) ≤ (Structured.rawCarrier) ∧ "
                        "(Structured.rawCarrier) ≤ ((1235 : ℝ) / 1000))"
                    ),
                },
                {
                    "declaration": "Structured.reportedContract",
                    "expected_type": (
                        "IChO2026Chem.Reporting.ReportsAtQuantum "
                        "(Structured.rawCarrier) ((123 : ℝ) / 100) ((1 : ℝ) / 100)"
                    ),
                },
            ],
        }
        lean = """import IChO2026Chem.Reporting
namespace Structured
noncomputable def rawCarrier : ℝ := 617 / 500
def rawDerivedFromProblem : Prop := rawCarrier = 617 / 500
theorem rawContract :
    rawDerivedFromProblem ∧
      (((1233 : ℝ) / 1000) ≤ rawCarrier ∧ rawCarrier ≤ ((1235 : ℝ) / 1000)) := by
  constructor
  · norm_num [rawDerivedFromProblem, rawCarrier]
  · constructor <;> norm_num [rawCarrier]
theorem reportedContract :
    IChO2026Chem.Reporting.ReportsAtQuantum rawCarrier
      ((123 : ℝ) / 100) ((1 : ℝ) / 100) := by
  rw [IChO2026Chem.Reporting.ReportsAtQuantum]
  refine ⟨by norm_num, ⟨123, by norm_num⟩, ?_⟩
  norm_num [rawCarrier]
end Structured
""".encode("utf-8")
        validator = MODULE.CleanLeanValidator(
            workspace=self.workspace,
            target_relative="IChO2026Problems/CleanFixture.lean",
            runtime_lake=Path("/opt/icho-answer-blind-runtime/lean-v4.31.0/bin/lake"),
            dependency_root=Path("/opt/icho-answer-blind-runtime/lake/packages"),
            verifier_user="nobody", scratch_root=scratch, timeout_s=600,
        )
        diagnostics = validator({
            "candidate": MODULE._canonical(candidate),
            "lean": lean, "blueprint": b"clean source-only fixture\n",
        })
        self.assertEqual(diagnostics, [])

    @unittest.skipUnless(
        Path("/opt/icho-answer-blind-runtime/bin/codex").is_file(),
        "sealed Codex CLI fixture is unavailable",
    )
    def test_codex_tool_free_config_is_accepted_in_strict_mode_without_model_call(self) -> None:
        binary = "/opt/icho-answer-blind-runtime/bin/codex"
        argv = [binary, "--strict-config"]
        for setting in MODULE.CODEX_TOOL_FREE_CONFIG:
            argv.extend(["-c", setting])
        argv.extend(["exec", "--help"])
        completed = subprocess.run(
            argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=30, check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout.decode(errors="replace"))

    def test_gpt_login_proxy_adapter_binds_normalized_upstream_not_caller_body(self) -> None:
        binary = self.base / "codex"
        binary.write_bytes(b"sealed fixture binary")
        os.chown(binary, 0, 0)
        os.chmod(binary, 0o500)
        home = self.base / "codex-home"
        home.mkdir(mode=0o700)
        os.chown(home, 0, 0)
        auth = home / "auth.json"
        auth.write_text('{"access_token":"not-used-by-mock"}')
        os.chown(auth, 0, 0)
        os.chmod(auth, 0o400)
        submission = self._submission()
        normalized = MODULE._canonical({
            "id": "resp_fixture", "status": "completed",
            "output": [{"type": "message", "content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}],
        })
        raw_sse = b"data: normalized-fixture\n\n"
        stderr_log = (
            MODULE.CODEX_STALE_ARG0_WARNING.encode() + b"\n"
            b"Reading additional input from stdin...\n"
            b"failed to refresh model list: HTTP 405\n"
        )

        class FakeProxy:
            base_url = "http://127.0.0.1:19090"

            def __init__(self, **_kwargs: object) -> None:
                pass

            def start(self) -> None:
                pass

            def wait(self, timeout: float = 30) -> object:
                del timeout
                return SimpleNamespace(
                    caller_body_sha256="a" * 64,
                    forwarded_request_sha256=MODULE._file_sha(
                        self_outer.controller / "gpt-icho_2026_t1_a1-attempt-1-request.json"
                    ),
                    upstream_status=200, upstream_raw_sse=raw_sse,
                    normalized_response=normalized,
                    caller_header_names=("authorization", "chatgpt-account-id"),
                    forwarded_header_names=("accept", "authorization", "chatgpt-account-id", "content-type"),
                    completed_event_count=1,
                )

            def close(self) -> None:
                pass

        self_outer = self

        def runner(argv: object, **_kwargs: object) -> subprocess.CompletedProcess[bytes]:
            assert isinstance(argv, list)
            if "--version" in argv:
                return subprocess.CompletedProcess(
                    argv, 0,
                    (MODULE.CODEX_STALE_ARG0_WARNING + "\ncodex-cli 0.147.0\n").encode(),
                    b"",
                )
            self.assertIn("--strict-config", argv)
            config_values = {
                argv[index + 1] for index, item in enumerate(argv[:-1]) if item == "-c"
            }
            self.assertIn("features.view_image=false", config_values)
            self.assertIn("features.code_mode.enabled=false", config_values)
            self.assertIn("features.code_mode_host=false", config_values)
            self.assertIn("features.shell_snapshot=false", config_values)
            self.assertIn("features.skill_search=false", config_values)
            self.assertIn("features.skill_mcp_dependency_install=false", config_values)
            self.assertFalse(any("collaboration_modes" in item for item in config_values))
            self.assertFalse(any(item.startswith("tools.view_image") for item in config_values))
            output = Path(argv[argv.index("-o") + 1])
            output.write_bytes(MODULE._canonical(submission))
            message_event = {"type": "item.completed", "item": {
                "type": "agent_message", "text": json.dumps(submission),
            }}
            events = (
                {"type": "thread.started", "thread_id": "fixture-thread"},
                {"type": "item.completed", "item": {
                    "id": "item_0", "type": "error",
                    "message": MODULE.CODEX_DISABLED_HOST_CONFIRMATION,
                }},
                {"type": "turn.started"},
                message_event,
            )
            self.assertIs(_kwargs["stderr"], subprocess.PIPE)
            return subprocess.CompletedProcess(
                argv, 0, b"".join(MODULE._canonical(item) for item in events), stderr_log,
            )

        def factory(target_id: str, attempt: int, _request: object, _images: object):
            return MODULE.ChatGPTLoginProxyAdapter(
                codex_binary=binary, codex_home=home, controller=self.controller,
                target_id=target_id, attempt=attempt, run_id=self.run_id,
                runner=runner, proxy_factory=FakeProxy,
            )

        receipt = MODULE.run_structured_solver(
            workspace=self.workspace, controller_dir=self.controller,
            bundle_path=self.bundle, asset_root=self.assets, variant="gpt",
            run_id=self.run_id, scope_ids=[self.row["id"]], max_attempts=1,
            source_first_precommit=self._precommit("gpt"),
            provider_factory=factory, validator=lambda _payloads: [],
        )
        self.assertEqual(receipt["adapter"], "chatgpt_login_proxy_v1")
        self.assertEqual(receipt["transport"]["kind"], "chatgpt_login_proxy_v1")
        self.assertEqual(len(receipt["transport"]["exchanges"]), 1)
        attempt = MODULE._load_json(
            Path(receipt["targets"][0]["attempts"][0]["path"]), label="attempt",
        )
        proxy_receipt = MODULE._load_json(
            Path(attempt["adapter_provenance"]["proxy_receipt"]["path"]),
            label="proxy receipt",
        )
        self.assertEqual(proxy_receipt["normalized_response"]["sha256"], MODULE._sha(normalized))
        self.assertEqual(proxy_receipt["caller_body_sha256"], "a" * 64)
        self.assertEqual(proxy_receipt["tool_events"], 0)
        self.assertEqual(attempt["adapter_provenance"]["event_count"], 4)
        stderr_path = Path(proxy_receipt["codex_stderr"]["path"])
        self.assertEqual(stderr_path.read_bytes(), stderr_log)
        self.assertEqual(stat.S_IMODE(stderr_path.stat().st_mode), 0o400)
        self.assertEqual(
            proxy_receipt["codex_stderr"]["sha256"], MODULE._file_sha(stderr_path),
        )

    def test_codex_jsonl_rejects_every_non_json_stdout_line(self) -> None:
        submission = self._submission()
        event = {"type": "item.completed", "item": {
            "type": "agent_message", "text": json.dumps(submission),
        }}
        warning = MODULE.CODEX_STALE_ARG0_WARNING.encode() + b"\n"
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._codex_transport_message(
                warning + MODULE._canonical(event)
            )
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._codex_transport_message(
                b"unexpected warning\n" + MODULE._canonical(event)
            )
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._codex_transport_message(
                MODULE._canonical(event) + warning
            )

    def test_gpt_extractor_concatenates_only_one_assistant_message(self) -> None:
        submission = self._submission()
        encoded = json.dumps(submission)
        split = len(encoded) // 2
        envelope = {
            "output": [{
                "type": "message", "role": "assistant",
                "content": [
                    {"type": "output_text", "text": encoded[:split]},
                    {"type": "output_text", "text": encoded[split:]},
                ],
            }],
        }
        self.assertEqual(MODULE._extract_gpt_submission(envelope), submission)
        for malformed in (
            {"output": envelope["output"] * 2},
            {"output": [{
                "type": "message", "role": "assistant",
                "content": [{"type": "refusal", "refusal": "no"}],
            }]},
            {"output": [{"type": "function_call", "name": "x"}]},
        ):
            with self.subTest(malformed=malformed):
                with self.assertRaises(MODULE.StructuredSolverError):
                    MODULE._extract_gpt_submission(malformed)

    def test_codex_jsonl_allows_only_ordered_disabled_host_confirmation(self) -> None:
        submission = self._submission()
        thread = {"type": "thread.started", "thread_id": "fixture-thread"}
        confirmation = {"type": "item.completed", "item": {
            "id": "item_0", "type": "error",
            "message": MODULE.CODEX_DISABLED_HOST_CONFIRMATION,
        }}
        turn = {"type": "turn.started"}
        message = {"type": "item.completed", "item": {
            "type": "agent_message", "text": json.dumps(submission),
        }}
        encode = lambda events: b"".join(MODULE._canonical(item) for item in events)
        self.assertEqual(
            MODULE._codex_transport_message(
                encode((thread, confirmation, turn, message)),
            ),
            (submission, 4),
        )
        variant = json.loads(json.dumps(confirmation))
        variant["item"]["message"] += " changed"
        for label, events in (
            ("duplicate", (thread, confirmation, confirmation, turn, message)),
            ("variant", (thread, variant, turn, message)),
            ("after-turn", (thread, turn, confirmation, message)),
            ("ordinary-error", (thread, {
                "type": "item.completed", "item": {
                    "id": "item_0", "type": "error", "message": "other",
                },
            }, turn, message)),
        ):
            with self.subTest(label=label):
                with self.assertRaises(MODULE.StructuredSolverError):
                    MODULE._codex_transport_message(encode(events))

    def test_gpt_parse_failure_seals_and_binds_raw_stdout(self) -> None:
        binary = self.base / "codex-diagnostic"
        binary.write_bytes(b"sealed fixture binary")
        os.chown(binary, 0, 0)
        os.chmod(binary, 0o500)
        home = self.base / "codex-diagnostic-home"
        home.mkdir(mode=0o700)
        os.chown(home, 0, 0)
        auth = home / "auth.json"
        auth.write_text('{"access_token":"not-used-by-mock"}')
        os.chown(auth, 0, 0)
        os.chmod(auth, 0o400)

        projection = MODULE._problem_projection(self.row)
        request = MODULE.build_provider_request(
            variant="gpt", model=MODULE.MODELS["gpt"][1],
            projection=projection, gpt_images=[], kimi_images=[],
            prior_diagnostics=[],
        )
        target_id = "diagnostic-target"
        registered = self.controller / f"gpt-{target_id}-attempt-1-request.json"
        MODULE._atomic_root_file(registered, MODULE._canonical(request))
        submission = self._submission()
        normalized = MODULE._canonical({
            "id": "resp_diagnostic", "status": "completed",
            "output": [{"type": "message", "content": [{
                "type": "output_text", "text": json.dumps(submission),
            }]}],
        })
        raw_stdout = b"unrecognized-but-preserved-line\n"
        raw_stderr = b"Reading additional input from stdin...\n"

        class FakeProxy:
            base_url = "http://127.0.0.1:19091"

            def __init__(self, **_kwargs: object) -> None:
                pass

            def start(self) -> None:
                pass

            def wait(self, timeout: float = 30) -> object:
                del timeout
                return SimpleNamespace(
                    caller_body_sha256="a" * 64,
                    forwarded_request_sha256=MODULE._file_sha(registered),
                    upstream_status=200, upstream_raw_sse=b"fixture",
                    normalized_response=normalized,
                    caller_header_names=("authorization", "chatgpt-account-id"),
                    forwarded_header_names=(
                        "accept", "authorization", "chatgpt-account-id", "content-type",
                    ),
                    completed_event_count=1,
                )

            def close(self) -> None:
                pass

        def runner(argv: object, **_kwargs: object) -> subprocess.CompletedProcess[bytes]:
            assert isinstance(argv, list)
            if "--version" in argv:
                return subprocess.CompletedProcess(argv, 0, b"codex-cli 0.147.0\n", b"")
            output = Path(argv[argv.index("-o") + 1])
            output.write_bytes(MODULE._canonical(submission))
            return subprocess.CompletedProcess(argv, 0, raw_stdout, raw_stderr)

        adapter = MODULE.ChatGPTLoginProxyAdapter(
            codex_binary=binary, codex_home=home, controller=self.controller,
            target_id=target_id, attempt=1, run_id=self.run_id,
            runner=runner, proxy_factory=FakeProxy,
        )
        with self.assertRaises(MODULE.ProviderInvocationError) as raised:
            adapter("", request)
        failure_locator = raised.exception.receipt
        failure = MODULE._load_json(
            Path(failure_locator["path"]), label="parse failure receipt",
        )
        diagnostic = failure["diagnostic_stdout"]
        diagnostic_path = Path(diagnostic["path"])
        self.assertEqual(
            diagnostic_path,
            self.controller / f"gpt-{target_id}-attempt-1-codex.jsonl",
        )
        self.assertEqual(diagnostic_path.read_bytes(), raw_stdout)
        self.assertEqual(stat.S_IMODE(diagnostic_path.stat().st_mode), 0o400)
        self.assertEqual(diagnostic["sha256"], MODULE._file_sha(diagnostic_path))
        stderr_diagnostic = failure["diagnostic_stderr"]
        stderr_path = Path(stderr_diagnostic["path"])
        self.assertEqual(stderr_path.read_bytes(), raw_stderr)
        self.assertEqual(stat.S_IMODE(stderr_path.stat().st_mode), 0o400)
        self.assertEqual(
            stderr_diagnostic["sha256"], MODULE._file_sha(stderr_path),
        )
        self.assertEqual(
            Path(failure["upstream_raw_sse"]["path"]).read_bytes(), b"fixture",
        )
        self.assertEqual(
            Path(failure["normalized_response"]["path"]).read_bytes(), normalized,
        )
        self.assertEqual(
            failure["response_structure"],
            MODULE._bounded_gpt_response_structure(json.loads(normalized)),
        )

    def test_gpt_proxy_normalization_failure_seals_raw_sse_evidence(self) -> None:
        binary = self.base / "codex-normalization-failure"
        binary.write_bytes(b"sealed fixture binary")
        os.chown(binary, 0, 0)
        os.chmod(binary, 0o500)
        home = self.base / "codex-normalization-home"
        home.mkdir(mode=0o700)
        os.chown(home, 0, 0)
        auth = home / "auth.json"
        auth.write_text('{"access_token":"not-used-by-mock"}')
        os.chown(auth, 0, 0)
        os.chmod(auth, 0o400)
        request = MODULE.build_provider_request(
            variant="gpt", model=MODULE.MODELS["gpt"][1],
            projection=MODULE._problem_projection(self.row),
            gpt_images=[], kimi_images=[], prior_diagnostics=[],
        )
        target_id = "normalization-failure"
        registered = self.controller / f"gpt-{target_id}-attempt-1-request.json"
        MODULE._atomic_root_file(registered, MODULE._canonical(request))
        raw_sse = (
            b'event: response.unknown\n'
            b'data: {"type":"response.unknown","sequence_number":0,'
            b'"secret_text":"must-remain-only-in-sealed-raw-evidence"}\n\n'
        )
        proxy_module = MODULE._load_login_proxy_module()

        class FakeProxy:
            base_url = "http://127.0.0.1:19092"

            def __init__(self, **_kwargs: object) -> None:
                self.failure_evidence = SimpleNamespace(
                    upstream_status=200,
                    upstream_raw_response=raw_sse,
                    response_header_names=("content-type", "x-request-id"),
                    response_structure=proxy_module.bounded_sse_structure(raw_sse),
                )

            def start(self) -> None:
                pass

            def wait(self, timeout: float = 30) -> object:
                del timeout
                raise RuntimeError("sanitized normalization failure")

            def close(self) -> None:
                pass

        stdout = b'{"type":"thread.started","thread_id":"fixture"}\n'
        stderr = b"sanitized stderr\n"

        def runner(argv: object, **_kwargs: object) -> subprocess.CompletedProcess[bytes]:
            assert isinstance(argv, list)
            if "--version" in argv:
                return subprocess.CompletedProcess(argv, 0, b"codex-cli 0.147.0\n", b"")
            return subprocess.CompletedProcess(argv, 1, stdout, stderr)

        adapter = MODULE.ChatGPTLoginProxyAdapter(
            codex_binary=binary, codex_home=home, controller=self.controller,
            target_id=target_id, attempt=1, run_id=self.run_id,
            runner=runner, proxy_factory=FakeProxy,
        )
        with self.assertRaises(MODULE.ProviderInvocationError) as raised:
            adapter("", request)
        failure = MODULE._load_json(
            Path(raised.exception.receipt["path"]), label="normalization failure",
        )
        raw_path = Path(failure["upstream_raw_sse"]["path"])
        self.assertEqual(raw_path.read_bytes(), raw_sse)
        self.assertEqual(stat.S_IMODE(raw_path.stat().st_mode), 0o400)
        self.assertEqual(failure["upstream_raw_sse"]["sha256"], MODULE._file_sha(raw_path))
        self.assertEqual(
            Path(failure["diagnostic_stdout"]["path"]).read_bytes(), stdout,
        )
        self.assertEqual(
            Path(failure["diagnostic_stderr"]["path"]).read_bytes(), stderr,
        )
        serialized_failure = json.dumps(failure)
        self.assertNotIn("must-remain-only", serialized_failure)
        self.assertEqual(failure["response_structure"]["event_types"], ["response.unknown"])

    def test_codex_version_parser_allows_only_the_one_known_warning(self) -> None:
        self.assertEqual(
            MODULE._codex_version_from_output(
                (MODULE.CODEX_STALE_ARG0_WARNING + "\ncodex-cli 0.147.0\n").encode()
            ),
            "codex-cli 0.147.0",
        )
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._codex_version_from_output(
                b"unexpected warning\ncodex-cli 0.147.0\n"
            )
        with self.assertRaises(MODULE.StructuredSolverError):
            MODULE._codex_version_from_output(
                (MODULE.CODEX_STALE_ARG0_WARNING + "\n" +
                 MODULE.CODEX_STALE_ARG0_WARNING + "\ncodex-cli 0.147.0\n").encode()
            )


if __name__ == "__main__":
    unittest.main()
