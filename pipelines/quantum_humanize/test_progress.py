"""Incremental integration controls; synthetic fixtures establish no mathematics."""

import json
from types import SimpleNamespace
import unittest

from pipelines.quantum_humanize import _progress as progress, _strategy as strategy
from pipelines.quantum_humanize import test_flow as fake, test_closure as closure
from pipelines.quantum_humanize import test_integration as integration
from pipelines.quantum_humanize import test_frontier_flow as planning


REF = {"path": "comparison.md", "sha256": "a" * 64, "section": "Full draft"}


class ProgressTests(unittest.TestCase):
    def test_controller_markers_are_repaired_without_stripping_mathematics(self):
        for text in ("current navigation has zero cells", "partition_gaps has 13 entries",
                     "gap_" + "a" * 64, "Cumulative accounting has three cells"):
            candidate = SimpleNamespace(claim="U = S union H union E", argument=text)
            self.assertTrue(progress.navigation_errors(candidate))
            self.assertEqual(candidate.argument, text)
        self.assertFalse(progress.navigation_errors(SimpleNamespace(
            claim="Partition into acoustic cells", argument="The complement is uncontrolled; N(T) = 13.")))

    def delta(self, **changes):
        return progress.Progress.model_validate({
            "kind": "stronger_bound", "baseline": REF, "previous_statement": "Old bound T^2",
            "improved_statement": "New bound T^1.9", "justification": "Synthetic derivation", **changes})

    def test_frozen_comparison_dependency_and_visible_mathematical_delta_required(self):
        delta = self.delta()
        candidate = SimpleNamespace(dependencies=[delta.baseline],
            argument="Old bound T^2\nNew bound T^1.9\nSynthetic derivation")
        self.assertEqual(progress.progress_errors(delta, candidate, REF), [])
        self.assertTrue(progress.progress_errors(self.delta(baseline={**REF, "sha256": "b" * 64}), candidate, REF))
        self.assertTrue(progress.progress_errors(self.delta(kind="initial"), candidate, REF))
        self.assertTrue(progress.progress_errors(delta, candidate, None))
        candidate.dependencies = []
        self.assertTrue(progress.progress_errors(delta, candidate, REF))
        candidate.dependencies = [delta.baseline]
        candidate.argument = "Just a rewritten old claim"
        self.assertEqual(len(progress.progress_errors(delta, candidate, REF)), 3)

    def test_identical_statements_cannot_claim_a_delta(self):
        delta = self.delta(improved_statement="Old  bound T^2")
        candidate = SimpleNamespace(dependencies=[delta.baseline],
            argument="Old bound T^2 Old  bound T^2 Synthetic derivation")
        self.assertIn("identical mathematical statements do not establish a delta",
                      progress.progress_errors(delta, candidate, REF))

    def test_focus_prefers_new_full_drafts_and_rotates_without_certifying_excerpts(self):
        candidates = {str(i): SimpleNamespace(claim="Full claim " + str(i)) for i in range(20)}
        hashes = {p: "a" * 64 for p in candidates}
        first = progress.focused_inputs(candidates, hashes, "0", {"19"}, {}, ["18"])
        self.assertEqual([item["reference"]["path"] for item in first[:2]], ["19", "18"])
        self.assertEqual(len(first), 8)
        self.assertTrue(all(not item["trusted_proof"] for item in first))
        attempts = {item["reference"]["path"]: 1 for item in first}
        second = progress.focused_inputs(candidates, hashes, "0", set(), attempts, [])
        self.assertFalse(set(attempts) & {item["reference"]["path"] for item in second})

    def test_focused_deferral_creates_bounded_compatibility_task(self):
        ref = SimpleNamespace(path="new.md")
        assembly = SimpleNamespace(deferred_pieces=[SimpleNamespace(reference=ref, reason="Missing selector bound")])
        tasks = progress.compatibility_tasks([{"reference": {**REF, "path": "new.md"}}], assembly, REF, "self_audit")
        self.assertEqual(len(tasks), 1)
        self.assertIn("Missing selector bound", tasks[0]["objective"])
        self.assertEqual([r["path"] for r in tasks[0]["dependencies"]], ["new.md", "comparison.md"])
        self.assertIn("explicit old/new", tasks[0]["success_criterion"])

    def test_queue_preserves_overflow_and_shares_slots(self):
        groups = [[f"explicit{i}" for i in range(2)], [f"compat{i}" for i in range(8)],
                  [f"automatic{i}" for i in range(8)]]
        entries = [{"task": task, "status": "queued", "priority_group": group}
                   for group, tasks in enumerate(groups) for task in tasks]
        tasks = progress.pending_tasks(entries)
        self.assertEqual(len(tasks), 18)
        self.assertTrue(set(groups[0]).issubset(tasks[:8]))
        self.assertEqual(tasks[:3], ["explicit0", "compat0", "automatic0"])
        entries[0]["status"] = "dispatched"
        self.assertNotIn("explicit0", progress.pending_tasks(entries))

    def test_old_positive_audits_cannot_hide_two_rounds_without_progress(self):
        records = [{"round": i, "status": "reviewed_sublemma_pending_manual_integration",
                    "assembly_status": "dual_reviewed_assembly_pending_manual_check",
                    "mathematical_progress": False} for i in (1, 2)]
        self.assertEqual(strategy.review_trigger(3, 1, records, 3),
                         "two_integrations_without_mathematical_progress")
        records[-1]["mathematical_progress"] = True
        self.assertEqual(strategy.review_trigger(3, 1, records, 3), "")


class ProgressFlowTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped
    execute = closure.ClosureTests.execute

    def test_unavailable_comparison_or_focus_is_rejected_before_model_calls(self):
        for options in ({"integration_baseline": "missing.md"},
                        {"integration_focus_inputs": ["missing.md"]}):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, "canonical"):
                self.execute(fake.Script(), **options)
            self.assertEqual(self.script.calls, [])

    def test_navigation_contaminated_composition_is_mended_before_any_review(self):
        dirty = "current navigation has zero cells"

        def compose(session):
            return closure.composed(session, argument=dirty)

        def mend(session):
            self.assertIn("Move controller-only navigation assertions", session.prompts[-1])
            return integration.local(session, claim="Synthetic repaired composition")

        script = fake.Script(solver=[closure.local_a, closure.local_b], integrator=[compose, None], mender=[mend])
        _, summary = self.execute(script, rounds=2)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "repair_required")
        self.assertEqual(record["reviews"], [])
        self.assertTrue(script.role_calls["mender"])
        reviews = [call for call in script.calls if call.role.startswith("reviewer_")]
        self.assertTrue(all(dirty not in call.prompt for call in reviews))
        self.assertEqual(len([call for call in reviews if "Synthetic repaired composition" in call.prompt]), 2)

    def test_navigation_in_local_draft_is_repaired_without_audit_only_loop(self):
        script = fake.Script(solver=[lambda s: integration.local(s, argument="partition_gaps has three entries")],
                             mender=[closure.local_a], integrator=[None])
        _, summary = self.execute(script, attempts=1)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        self.assertFalse(summary["research_goal_proved"])

    def test_editorial_integration_does_not_advance_best_or_receive_new_votes(self):
        def unchanged(session):
            result = closure.composed(session, argument="Editorial rewording of the same union")
            result["progress"]["kind"] = "none"
            return result
        script = fake.Script(solver=[closure.local_a, closure.local_b,
                                    lambda s: integration.local(s, claim="Synthetic local C"), None],
                             integrator=[closure.composed, unchanged])
        work, summary = self.execute(script, rounds=2)
        first, second = summary["integrations"]
        self.assertTrue(first["mathematical_progress"])
        self.assertEqual(second["status"], "no_mathematical_progress")
        self.assertFalse(second["mathematical_progress"])
        self.assertEqual(second["reviews"], [])
        self.assertNotIn("proof_path", second)
        self.assertEqual(summary["latest_integration"], first["proof_path"])
        self.assertEqual(json.loads((work / "integration-focus-2.json").read_text())["baseline"]["path"],
                         first["proof_path"])

    def test_claimed_delta_requires_fresh_audits_and_rejection_preserves_best(self):
        def reject_delta(session):
            if "SYNTHETIC STRICTLY STRONGER MATHEMATICAL BOUND" in session.prompts[-1]:
                return fake.negative(session)
            return fake.review(session)
        script = fake.Script(solver=[closure.local_a, closure.local_b,
                                    lambda s: integration.local(s, claim="Synthetic local C"), None],
            integrator=[closure.composed, closure.composed], reviewer_a=[reject_delta] * 5)
        _, summary = self.execute(script, rounds=2)
        first, second = summary["integrations"]
        self.assertEqual(second["status"], "needs_repair")
        self.assertEqual(len(second["reviews"]), 2)
        self.assertFalse(second["mathematical_progress"])
        self.assertEqual(summary["latest_integration"], first["proof_path"])

    def test_dual_reviewed_delta_advances_comparison_with_full_baseline_dependency(self):
        script = fake.Script(solver=[closure.local_a, closure.local_b,
                                    lambda s: integration.local(s, claim="Synthetic local C"), None],
                             integrator=[closure.composed, closure.composed])
        _, summary = self.execute(script, rounds=2)
        first, second = summary["integrations"]
        self.assertEqual(second["comparison_path"], first["proof_path"])
        self.assertTrue(second["mathematical_progress"])
        self.assertEqual(summary["latest_integration"], second["proof_path"])
        self.assertNotEqual(first["sha256"], second["sha256"])
        self.assertTrue(all(r["candidate_sha256"] == second["sha256"] for r in second["reviews"]))

    def test_explicit_tasks_survive_eight_automatic_tasks_and_overflow_is_saved(self):
        def compose(session):
            frontier = planning.frontier(session)
            cell = frontier["cells"][0]
            frontier["cells"] = [{**cell, "id": f"patch{i}", "region": f"Synthetic region {i}",
                                  "gap": f"Synthetic gap {i}"} for i in range(8)]
            tasks = [{"obligation_id": "self_audit", "objective": f"EXPLICIT INTEGRATION TASK {i}",
                      "success_criterion": "Synthetic compatibility check", "dependencies": cell["dependencies"]}
                     for i in range(2)]
            return closure.composed(session, frontier_data=frontier, next_tasks=tasks)
        script = fake.Script(solver=[closure.local_a, closure.local_b] + [None] * 8,
                             integrator=[compose, None])
        work, _ = self.execute(script, rounds=2, attempts=8, parallelism=8)
        entries = json.loads((work / "research-tasks-final.json").read_text())
        explicit = [e for e in entries if e["priority_group"] == 0]
        self.assertEqual(len(entries), 10)
        self.assertTrue(all(e["status"] == "dispatched" for e in explicit))
        self.assertTrue(any(e["status"] == "queued" for e in entries))
        self.assertLessEqual(script.max_active, 8)


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
