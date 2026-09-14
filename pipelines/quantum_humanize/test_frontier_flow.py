"""Coverage-planning integration controls using only local scripted agents.

Baseline checks are mocked by the shared fixture. Synthetic frontier data and
review verdicts below do not establish any mathematical result.
"""

import hashlib
import json
import unittest

from pipelines.quantum_humanize import test_flow as fake
from pipelines.quantum_humanize import test_integration as integration
from pipelines.quantum_humanize import test_optimized as optimized


FRONTIER_MARKER = "PRIVATE FRONTIER PARTITION ATTACHMENT, NOT A PROOF"
GAP_MARKER = "SYNTHETIC FRONTIER GAP: a still-unbounded acoustic patch"


def frontier(session, **changes):
    refs = fake.candidate(session)["dependencies"]
    result = {
        "obligation_id": "self_audit", "partition_argument": FRONTIER_MARKER,
        "partition_dependencies": refs, "partition_gaps": [], "parameters": [], "conditions": [],
        "cells": [{
            "id": "open_patch", "placements": ["synthetic_local_selector"],
            "source_labels": "Original source labels are not reduced by this synthetic fixture",
            "temporal_signs": "Retain the original signs", "outputs": "Retain all original outputs",
            "region": "Synthetic local region only", "boundary_and_overlap": "Not yet justified",
            "localization": "No global localization claim is made", "status": "open", "bound": None,
            "gap": GAP_MARKER, "dependencies": refs,
        }],
    }
    result.update(changes)
    return result


def planned(session, *, frontier_data=None, next_tasks=(), **changes):
    result = optimized.composed(session, next_tasks=next_tasks, **changes)
    result["frontier"] = frontier(session) if frontier_data is None else frontier_data
    return result


class FrontierFlowTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped
    assert_proof_copies = integration.IntegrationTests.assert_proof_copies
    reviewing = optimized.OptimizedTests.reviewing
    assert_fresh_pair = optimized.OptimizedTests.assert_fresh_pair

    def execute(self, script=None, **changes):
        changes.setdefault("optimize", True)
        changes.setdefault("integrate", True)
        changes.setdefault("coverage_planning", True)
        return fake.FlowTests.execute(self, script, **changes)

    def report(self, work, record):
        self.assertEqual(record["frontier_report"], f"frontier-report-{record['round']}.json")
        result = json.loads((work / record["frontier_report"]).read_text())
        self.assertEqual(result["candidate_sha256"], record["sha256"])
        self.assertEqual(result["frontier_sha256"], fake.pipeline.digest(result["frontier"]))
        self.assertIs(result["attachment_mathematically_reviewed"], False)
        self.assertIs(result["analysis"]["trusted_proof"], False)
        self.assertIs(result["analysis"]["coverage_complete"], False)
        self.assertIs(result["analysis"]["coverage"]["partition_verified"], False)
        return result

    def assert_private_frontier_is_not_review_evidence(self, script):
        for call in script.calls:
            entries = json.loads((call.session.cwd / "_snapshot.json").read_text())["files"]
            self.assertFalse(any("frontier-report-" in entry["path"] for entry in entries))
            if call.role.startswith("reviewer_"):
                self.assertNotIn(FRONTIER_MARKER, call.prompt)
                self.assertNotIn(GAP_MARKER, call.prompt)
                self.assertNotIn("frontier-report-", call.prompt)
            for entry in integration.proofs(call.session):
                body = (call.session.cwd / entry["path"]).read_text()
                self.assertNotIn(FRONTIER_MARKER, body)
                self.assertNotIn(GAP_MARKER, body)

    def test_coverage_planning_defaults_on_without_changing_old_integration_schema(self):
        self.assertTrue(fake.pipeline.Config().coverage_planning)
        old = fake.pipeline.Integration.model_json_schema()
        self.assertEqual(set(old["properties"]), {"candidate", "next_tasks"})
        self.assertEqual(set(old["required"]), {"candidate", "next_tasks"})
        planned = fake.pipeline.PlannedIntegration.model_json_schema()
        self.assertEqual(set(planned["properties"]), {"candidate", "next_tasks", "frontier"})
        self.assertEqual(set(planned["required"]), set(planned["properties"]))
        stack = [planned]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("type") == "object":
                    self.assertEqual(set(node["required"]), set(node["properties"]))
                    self.assertIs(node["additionalProperties"], False)
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)

    def test_disabling_coverage_or_optimization_keeps_the_previous_response_schemas(self):
        for options, shape, answer in (
            ({"coverage_planning": False}, fake.pipeline.Integration, optimized.composed),
            ({"optimize": False}, fake.pipeline.Candidate, integration.combination),
        ):
            with self.subTest(options=options):
                script = fake.Script(solver=[integration.local], integrator=[answer])
                work, summary = self.execute(script, **options)
                calls = [call for call in script.calls if call.role == "integrator"]
                self.assertEqual(len(calls), 1)
                self.assertIs(calls[0].schema, shape)
                self.assertTrue(summary["integrations"][0]["status"].startswith("reviewed_"))
                self.assertEqual(list(work.glob("frontier-report-*.json")), [])
                self.assertFalse(summary["research_goal_proved"])
                self.assert_stopped()

    def test_actual_kinetic_keeps_integration_schema_even_with_coverage_planning_enabled(self):
        # Extend only this test-owned corpus with the actual obligation's inputs;
        # the production prepare/snapshot/dependency gates are still exercised.
        archive = json.loads((self.repo / "MANIFEST.json").read_text())
        for name in fake.pipeline.OBLIGATIONS["actual_kinetic"]["inputs"]:
            if not (self.repo / name).exists():
                data = ("# Synthetic actual-kinetic control fixture\n" + name + "\n").encode()
                (self.repo / name).write_bytes(data)
                archive["files"].append({"path": name, "exportedSha256": hashlib.sha256(data).hexdigest(),
                                         "bytes": len(data)})
        (self.repo / "MANIFEST.json").write_text(json.dumps(archive))
        self.before = self.source_files()
        script = fake.Script(
            solver=[lambda session: integration.local(session, obligation_id="actual_kinetic")],
            integrator=[lambda session: optimized.composed(session, obligation_id="actual_kinetic")],
        )
        work, summary = self.execute(script, obligation="actual_kinetic", coverage_planning=True)
        calls = [call for call in script.calls if call.role == "integrator"]
        self.assertEqual(len(calls), 1)
        self.assertIs(calls[0].schema, fake.pipeline.Integration)
        record = summary["integrations"][0]
        self.assertTrue(record["status"].startswith("reviewed_"))
        self.assertNotIn("frontier_report", record)
        self.assertEqual(list(work.glob("frontier-report-*.json")), [])
        self.assert_fresh_pair(script, record["sha256"])
        self.assertEqual(self.source_files(), self.before)
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_enabled_planning_rejects_an_integration_answer_missing_its_required_frontier(self):
        script = fake.Script(solver=[integration.local], integrator=[optimized.composed])
        work, summary = self.execute(script)
        calls = [call for call in script.calls if call.role == "integrator"]
        self.assertEqual(len(calls), 1)
        self.assertIs(calls[0].schema, fake.pipeline.PlannedIntegration)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        self.assertEqual(summary["latest_integration"], "")
        self.assertFalse(any(record.get("proof_path") for record in summary["integrations"]))
        failures = [json.loads(path.read_text()) for path in work.glob("call-*/failure.json")]
        self.assertTrue(any(failure["kind"] == "invalid_schema" for failure in failures))
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_valid_report_tasks_precede_model_tasks_only_after_composition_dual_review(self):
        fallback = "LOWER PRIORITY MODEL-SUGGESTED TASK"
        private_review = "PRIVATE EARLIER REVIEW MUST NOT REACH NEW REVIEWERS"
        seen = {}

        def compose(session):
            result = planned(session, next_tasks=[optimized.task(session, fallback)])
            entry = self.assert_proof_copies(session)[0]
            ref = {"path": entry["path"], "sha256": entry["sha256"], "section": "Full local draft"}
            result["frontier"]["partition_dependencies"] = [ref]
            result["frontier"]["cells"][0]["dependencies"] = [ref]
            seen["manifest"] = json.loads((session.cwd / "_snapshot.json").read_text())
            seen["frontier"] = result["frontier"]
            return result

        def assigned_frontier_task(session):
            assignment = session.prompts[-1].rsplit("\nResearch assignment", 1)[1]
            self.assertIn(GAP_MARKER, assignment)
            self.assertNotIn(fallback, assignment)
            refs = seen["frontier"]["cells"][0]["dependencies"]
            entries = self.assert_proof_copies(session)
            self.assertTrue(any(entry["path"] == refs[0]["path"] and entry["sha256"] == refs[0]["sha256"]
                                for entry in entries))
            return None

        def assigned_model_task(session):
            assignment = session.prompts[-1].rsplit("\nResearch assignment", 1)[1]
            self.assertIn(fallback, assignment)
            self.assertNotIn(GAP_MARKER, assignment)
            return None

        script = fake.Script(
            solver=[integration.local, None, assigned_frontier_task, assigned_model_task],
            integrator=[compose],
            reviewer_a=[lambda session: fake.review(session, explanation=private_review), fake.DEFAULT],
        )
        work, summary = self.execute(script, attempts=2, rounds=2)
        record = summary["integrations"][0]
        result = self.report(work, record)
        self.assertEqual(result["frontier"], seen["frontier"])
        self.assertEqual(result["input_manifest_sha256"], fake.pipeline.digest(seen["manifest"]))
        self.assertEqual(result["analysis"]["validation_errors"], [])
        self.assertEqual(len(result["analysis"]["tasks"]), 1)
        self.assertEqual(record["next_tasks"][0], result["analysis"]["tasks"][0])
        self.assertEqual(record["next_tasks"][1]["objective"], fallback)
        self.assert_fresh_pair(script, record["sha256"])
        self.assertEqual(json.loads((work / "round-context-2.json").read_text())["next_tasks"],
                         record["next_tasks"])
        self.assertTrue(record["status"].startswith("reviewed_"))
        for call in script.calls:
            if call.role.startswith("reviewer_"):
                self.assertNotIn(private_review, call.prompt)
        self.assert_private_frontier_is_not_review_evidence(script)
        self.assertEqual(self.source_files(), self.before)
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_frontier_referencing_the_not_yet_admitted_composition_cannot_generate_tasks(self):
        seen = {}

        def future_reference(session):
            result = planned(session)
            body = ("# Proof candidate — untrusted, not formal certification\n\n```json\n"
                    + fake.pipeline.canonical(result["candidate"]) + "\n```\n").encode()
            sha = hashlib.sha256(body).hexdigest()
            seen["future_path"] = integration.PROOF_PREFIX + sha + ".md"
            self.assertFalse(any(entry["path"] == seen["future_path"] for entry in integration.proofs(session)))
            result["frontier"]["partition_dependencies"] = [{
                "path": seen["future_path"], "sha256": sha, "section": "Unavailable current composition",
            }]
            return result

        def next_solver(session):
            self.assertNotIn(GAP_MARKER, session.prompts[-1])
            self.assertTrue(any(entry["path"] == seen["future_path"] for entry in self.assert_proof_copies(session)))
            return None

        script = fake.Script(solver=[integration.local, next_solver], integrator=[future_reference])
        work, summary = self.execute(script, rounds=2)
        record = summary["integrations"][0]
        result = self.report(work, record)
        self.assertTrue(result["analysis"]["validation_errors"])
        self.assertEqual(result["analysis"]["tasks"], [])
        self.assertEqual(record["next_tasks"], [])
        # Equality proves the rejected reference was the genuinely future file,
        # not a conveniently wrong hash unrelated to the accepted composition.
        self.assertEqual(record["proof_path"], seen["future_path"])
        self.assertTrue(record["status"].startswith("reviewed_"))
        self.assert_fresh_pair(script, record["sha256"])
        self.assert_private_frontier_is_not_review_evidence(script)
        self.assert_stopped()

    def test_rejected_composition_keeps_its_report_but_forwards_no_frontier_tasks(self):
        private_fault = "PRIVATE COMPOSITION FAULT, MENDER ONLY"
        rejected_task = "MODEL TASK FROM THE REJECTED COMPOSITION"

        def reject(session):
            return fake.review(session, verdict="gap", first_fault="Synthetic local gluing fault",
                               explanation=private_fault, repair="Supply a separately reviewed revision")

        def next_solver(session):
            self.assertNotIn(GAP_MARKER, session.prompts[-1])
            self.assertNotIn(rejected_task, session.prompts[-1])
            self.assertNotIn(private_fault, session.prompts[-1])
            return None

        script = fake.Script(
            solver=[integration.local, None, next_solver], mender=[None],
            integrator=[lambda session: planned(session, next_tasks=[optimized.task(session, rejected_task)])],
            reviewer_b=[fake.DEFAULT, reject],
        )
        work, summary = self.execute(script, attempts=2, rounds=2)
        record = summary["integrations"][0]
        result = self.report(work, record)
        self.assertEqual(result["analysis"]["validation_errors"], [])
        self.assertTrue(result["analysis"]["tasks"])
        self.assertEqual(record["status"], "needs_repair")
        self.assertEqual(record.get("next_tasks", []), [])
        self.assertNotIn("proof_path", record)
        self.assertEqual(summary["latest_integration"], "")
        self.assertEqual(json.loads((work / "round-context-2.json").read_text())["next_tasks"], [])
        self.assertEqual(script.role_calls["mender"], 1)
        for call in script.calls:
            if call.role == "mender":
                self.assertIn(private_fault, call.prompt)
            else:
                self.assertNotIn(private_fault, call.prompt)
        self.assert_private_frontier_is_not_review_evidence(script)
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_unknown_constants_or_infeasible_declared_powers_are_planning_not_proof(self):
        for status in ("unknown", "infeasible"):
            with self.subTest(status=status):
                def compose(session):
                    table = frontier(session)
                    cell = table["cells"][0]
                    cell.update(status="bounded", gap="", bound={
                        "time_power": "1" if status == "unknown" else "3", "log_power": "0",
                        "cutoff_powers": [], "constant_policy": "unknown" if status == "unknown" else "uniform",
                        "unknown_dependencies": ["UNQUANTIFIED LOCAL CONSTANT"] if status == "unknown" else [],
                        "norm": "Synthetic original norm", "window_and_limits": "Original window and N-first order",
                        "hypothesis_conditions": [], "dependencies": cell["dependencies"],
                    })
                    return planned(session, frontier_data=table)

                script = fake.Script(solver=[integration.local], integrator=[compose])
                work, summary = self.execute(script)
                record = summary["integrations"][0]
                result = self.report(work, record)
                self.assertEqual(result["analysis"]["validation_errors"], [])
                self.assertEqual(result["analysis"]["cutoffs"]["status"], status)
                self.assertTrue(result["analysis"]["tasks"])
                self.assertTrue(all(task["objective"].startswith("UNVERIFIED RESEARCH TARGET:")
                                    for task in result["analysis"]["tasks"]))
                self.assertEqual(record["status"], "reviewed_sublemma_pending_manual_integration")
                self.assertEqual(summary["status"], "round_limit_reached")
                self.assertFalse(summary["research_goal_proved"])
                self.assert_fresh_pair(script, record["sha256"])
                self.assert_private_frontier_is_not_review_evidence(script)
                body = (work / "proofs" / record["proof_path"].rsplit("/", 1)[-1]).read_text()
                self.assertNotIn("UNQUANTIFIED LOCAL CONSTANT", body)
                self.assertNotIn("cutoffs", body)
                self.assert_stopped()

    def test_changing_only_the_frontier_changes_report_hash_not_candidate_review_hash(self):
        hashes = []
        frontier_hashes = []
        for partition in ("FIRST UNTRUSTED PARTITION DESCRIPTION", "SECOND UNTRUSTED PARTITION DESCRIPTION"):
            script = fake.Script(solver=[integration.local], integrator=[lambda session: planned(
                session, frontier_data=frontier(session, partition_argument=partition))])
            work, summary = self.execute(script)
            record = summary["integrations"][0]
            result = self.report(work, record)
            hashes.append(record["sha256"])
            frontier_hashes.append(result["frontier_sha256"])
            self.assert_fresh_pair(script, record["sha256"])
            for call in self.reviewing(script, record["sha256"]):
                self.assertNotIn(partition, call.prompt)
            self.assert_stopped()
        self.assertEqual(hashes[0], hashes[1])
        self.assertNotEqual(frontier_hashes[0], frontier_hashes[1])


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
