"""Semantic planner wiring and failure containment; no native calls or proof claims."""

import asyncio
import hashlib
import json
import unittest

from pipelines.quantum_humanize import test_flow as fake, test_integration as integration
from pipelines.quantum_humanize import test_strategy as routes


MARKER = "PRIVATE DISPATCH RATIONALE NOT MATHEMATICAL EVIDENCE"


def navigation(session):
    return json.JSONDecoder().raw_decode(
        session.prompts[-1].split("UNVERIFIED DISPATCH CONTEXT:\n", 1)[1])[0]


def plan(session, *, count=1, retire=True):
    context = navigation(session)
    dependency = fake.candidate(session)["dependencies"][0]
    return {
        "assessment": MARKER,
        "tasks": [{"obligation_id": "self_audit", "objective": f"Merged bounded target {i}",
                   "success_criterion": f"Only the missing applicability step {i}, not old geometry",
                   "dependencies": [dependency]} for i in range(count)],
        "retire_task_ids": [item["id"] for item in context["proposals"]] if retire else [],
    }


class DispatchTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped

    def execute(self, script=None, **changes):
        options = {"optimize": True, "integration_closure": True, "dispatch_review": True,
                   "attempts": 2, "audit_continuations": 0}
        options.update(changes)
        result = fake.FlowTests.execute(self, script, **options)
        self.assertEqual(self.source_files(), self.before)
        self.assert_stopped()
        return result

    def test_schema_has_only_plan_and_basic_envelope_fields(self):
        schema = fake.pipeline.DispatchReview.model_json_schema()
        self.assertEqual(set(schema["properties"]), {"assessment", "tasks", "retire_task_ids"})
        stack = [schema]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("type") == "object":
                    self.assertFalse(node["additionalProperties"])
                    self.assertEqual(set(node["required"]), set(node["properties"]))
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)

    def test_one_semantic_plan_can_reduce_lanes_without_generic_backfill(self):
        script = fake.Script(dispatcher=[plan], solver=[integration.local])
        work, summary = self.execute(script, attempts=8)
        self.assertEqual(script.role_calls["dispatcher"], 1)
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        record = json.loads((work / "dispatch-review-1.json").read_text())
        self.assertEqual(record["status"], "planning_only")
        self.assertEqual(record["navigation"]["available_solver_slots"], 8)
        self.assertEqual(len(record["dispatched_task_ids"]), 1)
        entries = json.loads((work / "research-tasks-final.json").read_text())
        self.assertEqual(sum(e["status"] == "superseded_by_dispatch_review" for e in entries), 8)
        self.assertFalse(summary["research_goal_proved"])
        for call in script.calls:
            if call.role in {"solver", "reviewer_a", "reviewer_b"}:
                self.assertNotIn(MARKER, call.prompt)
        self.assertIn("Merged bounded target", next(c.prompt for c in script.calls if c.role == "solver"))

    def test_empty_plan_leaves_lanes_idle_and_is_not_proof(self):
        script = fake.Script(dispatcher=[lambda s: plan(s, count=0)])
        _, summary = self.execute(script)
        self.assertEqual(script.role_calls["solver"], 0)
        self.assertEqual(summary["candidates"], [])
        self.assertFalse(summary["research_goal_proved"])

    def test_unavailable_or_malformed_plan_never_bypasses_review(self):
        for answer in (None, {"tasks": []}):
            with self.subTest(answer=answer):
                script = fake.Script(dispatcher=[answer])
                work, _ = self.execute(script)
                self.assertEqual(script.role_calls["solver"], 0)
                record = json.loads((work / "dispatch-review-1.json").read_text())
                self.assertEqual(record["status"], "output_unavailable")

    def test_only_structural_scope_reference_and_budget_errors_block_plan(self):
        def wrong_id(answer):
            answer["retire_task_ids"] = ["invented ID"]

        def wrong_hash(answer):
            answer["tasks"][0]["dependencies"][0]["sha256"] = "0" * 64

        def wrong_goal(answer):
            answer["tasks"][0]["obligation_id"] = "actual_kinetic"

        def overflow(answer):
            answer["tasks"] *= 3

        for mutate in (wrong_id, wrong_hash, wrong_goal, overflow):
            def invalid(session):
                answer = plan(session)
                mutate(answer)
                return answer
            with self.subTest(mutate=mutate.__name__):
                script = fake.Script(dispatcher=[invalid])
                work, _ = self.execute(script)
                self.assertEqual(script.role_calls["solver"], 0)
                record = json.loads((work / "dispatch-review-1.json").read_text())
                self.assertEqual(record["status"], "invalid_plan")
                self.assertTrue(record["errors"])
                self.assertEqual(json.loads((work / "research-tasks-final.json").read_text()), [])

    def test_fput_coverage_planning_is_rejected(self):
        from pydantic import ValidationError
        with self.assertRaises(ValidationError):
            fake.pipeline.Config(coverage_planning=True)

    def test_previous_decision_and_maintenance_are_visible_without_cancelling_repair(self):
        observed = []

        def first(session):
            observed.append(navigation(session))
            return plan(session)

        def unavailable(session):
            observed.append(navigation(session))
            return None

        script = fake.Script(dispatcher=[first, unavailable], solver=[lambda s: integration.local(
            s, unproved_steps=["Synthetic pending repair"])], mender=[None, None])
        _, summary = self.execute(script, rounds=2)
        self.assertEqual(len(observed), 2)
        self.assertIn(MARKER, observed[1]["previous_dispatch_review"]["review"]["assessment"])
        self.assertTrue(any(item["kind"] == "repair" for item in observed[1]["reserved_work"]))
        self.assertEqual(script.role_calls["mender"], 2)
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertLessEqual(script.max_active, 2)
        self.assertEqual(len(summary["dispatch_reviews"]), 2)

    def test_reserved_strategy_lane_is_visible_and_not_counted_as_local_slot(self):
        seen = []

        def dispatch(session):
            seen.append(navigation(session))
            return plan(session)

        script = fake.Script(strategist=[lambda s: routes.proposal(s, targets=("self_audit",))], dispatcher=[dispatch],
                             solver=[routes.draft] * 2, integrator=[None])
        _, _ = self.execute(script, attempts=4, strategy_review=True, integrate=True)
        self.assertEqual(seen[0]["available_solver_slots"], 3)
        self.assertEqual(seen[0]["reserved_work"][0]["kind"], "strategy_exploration")
        self.assertEqual(script.role_calls["solver"], 2)

    def test_restart_proposals_are_semantically_merged_and_omitted_tasks_survive(self):
        ref = {"path": fake.pipeline.COMMON_INPUTS[0],
               "sha256": hashlib.sha256((self.repo / fake.pipeline.COMMON_INPUTS[0]).read_bytes()).hexdigest(),
               "section": "Synthetic frozen source"}
        tasks = [{"obligation_id": "self_audit", "objective": objective,
                  "success_criterion": "Check the same transport condition", "dependencies": [ref]}
                 for objective in ("Tube transport audit", "Audit applicability of the tube bound", "Distinct complement")]
        seed = self.runs / "research-tasks.json"
        fake.pipeline.save_new(seed, tasks)

        def merge(session):
            context = navigation(session)
            self.assertEqual(len(context["proposals"]), 3)
            result = plan(session)
            result["retire_task_ids"] = [item["id"] for item in context["proposals"][:2]]
            return result

        script = fake.Script(dispatcher=[merge], solver=[integration.local])
        work, _ = self.execute(script, research_task_inputs=[str(seed)])
        entries = json.loads((work / "research-tasks-final.json").read_text())
        self.assertEqual(sum(e["status"] == "superseded_by_dispatch_review" for e in entries), 2)
        self.assertTrue(any(e["status"] == "queued" and e["task"]["objective"] == "Distinct complement"
                            for e in entries))
        self.assertEqual(script.role_calls["solver"], 1)

    def test_restart_task_path_and_scope_are_checked_before_calls(self):
        with self.assertRaisesRegex(ValueError, "inside the run area"):
            self.execute(research_task_inputs=[str(self.repo / "outside.json")])
        self.assertEqual(self.script.calls, [])

    def test_interrupted_dispatch_keeps_reserved_repair_for_restart(self):
        script = fake.Script(dispatcher=[plan, asyncio.CancelledError()],
                             solver=[lambda s: integration.local(s, unproved_steps=["Pending repair"])],
                             mender=[None])
        with self.assertRaises(asyncio.CancelledError):
            self.execute(script, rounds=2)
        work = next(self.runs.glob("run-*"))
        pending = json.loads((work / "pending-repairs-final.json").read_text())
        self.assertEqual(len(pending), 1)
        self.assertEqual(pending[0]["candidate"]["unproved_steps"], ["Pending repair"])
        self.assert_stopped()

    def test_explicit_opt_out_keeps_legacy_dispatch(self):
        script = fake.Script(solver=[integration.local] * 2)
        work, _ = self.execute(script, dispatch_review=False)
        self.assertEqual(script.role_calls["dispatcher"], 0)
        self.assertEqual(script.role_calls["solver"], 2)
        self.assertFalse((work / "dispatch-review-1.json").exists())

    def test_insufficient_call_budget_does_not_spend_or_bypass_plan(self):
        script = fake.Script()
        work, _ = self.execute(script, max_calls=3)
        record = json.loads((work / "dispatch-review-1.json").read_text())
        self.assertEqual(record["status"], "skipped_low_call_budget")
        self.assertEqual(script.role_calls["dispatcher"], 0)
        self.assertEqual(script.role_calls["solver"], 0)


if __name__ == "__main__":
    unittest.main()
