"""Route-review policy and real scheduler tests; synthetic, zero native model calls."""

import json
import re
import unittest

from pipelines.quantum_humanize import _strategy as strategy
from pipelines.quantum_humanize import test_flow as fake


MARKER = "PRIVATE ROUTE GUIDANCE NOT A PROOF"


def proposal(session, *, targets=("r3_r5_leading",), decision="explore_alternative"):
    dependency = fake.candidate(session)["dependencies"][0]
    return {
        "assessment": MARKER,
        "necessity": "route_specific",
        "decision": decision,
        "alternatives": [{"route": "Synthetic signed-sum route", "expected_gain": "Test necessity",
                          "obstruction": "Synthetic missing global bound"}],
        "tasks": [{"obligation_id": target, "objective": "Synthetic exploration of " + target,
                   "success_criterion": "Derive a scoped synthetic lemma",
                   "stop_criterion": "Stop after one attempt with an explicit obstruction",
                   "dependencies": [dependency]} for target in targets],
        "literature_requests": ["Synthetic missing primary source, not an accepted citation"],
    }


def draft(session, **changes):
    obligation = re.search(r"Obligation ID: ([a-z0-9_]+)", session.prompts[-1]).group(1)
    return fake.candidate(session, obligation_id=obligation, scope="sublemma",
                          claim="Synthetic new lemma " + session.agent.name, **changes)


def script_with_routes(*targets):
    return fake.Script(strategist=[lambda s: proposal(s, targets=targets)] * 20,
                       solver=[draft] * 160, integrator=[None] * 20)


class PolicyTests(unittest.TestCase):
    def test_strict_schema_and_bounded_tasks(self):
        stack = [strategy.StrategyReview.model_json_schema()]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("type") == "object":
                    self.assertEqual(set(node["required"]), set(node["properties"]))
                    self.assertFalse(node["additionalProperties"])
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)
        schema = strategy.StrategyReview.model_json_schema()
        self.assertEqual(schema["properties"]["tasks"]["maxItems"], 2)

    def test_startup_periodic_and_two_unsuccessful_integrations(self):
        self.assertEqual(strategy.review_trigger(1, 0, [], 3), "startup")
        self.assertEqual(strategy.review_trigger(3, 1, [], 3), "")
        self.assertEqual(strategy.review_trigger(4, 1, [], 3), "periodic")
        failures = [{"round": n, "status": "needs_repair"} for n in (1, 2)]
        self.assertEqual(strategy.review_trigger(3, 1, failures, 3), "two_unsuccessful_integrations")
        self.assertEqual(strategy.review_trigger(4, 3, failures, 3), "")

    def test_success_resets_failure_streak_but_new_lemma_is_not_assembly(self):
        results = [{"round": 1, "status": "needs_repair"},
                   {"round": 2, "status": "reviewed_sublemma_pending_manual_integration"}]
        self.assertEqual(strategy.review_trigger(3, 1, results, 3), "")
        results[1]["assembly_status"] = "new_lemma_only"
        self.assertEqual(strategy.review_trigger(3, 1, results, 3), "two_unsuccessful_integrations")
        results[1]["assembly_status"] = "dual_reviewed_assembly_pending_manual_check"
        self.assertEqual(strategy.review_trigger(3, 1, results, 3), "")

    def test_exploration_never_consumes_all_multi_lane_slots(self):
        for attempts in range(2, 9):
            self.assertLess(strategy.exploration_slots(attempts, 1), attempts)
            self.assertLessEqual(strategy.exploration_slots(attempts, 1), 2)
        self.assertEqual(strategy.exploration_slots(8, 1), 2)
        self.assertEqual([strategy.exploration_slots(1, n) for n in range(1, 5)], [1, 0, 1, 0])

    def test_defaults_and_interval_bounds(self):
        self.assertTrue(fake.pipeline.Config().strategy_review)
        self.assertEqual(fake.pipeline.Config().strategy_interval, 3)
        self.assertEqual(fake.pipeline.Config().parallelism, 8)
        for value in (1, 21):
            with self.assertRaises(ValueError):
                fake.pipeline.Config(strategy_interval=value)


class StrategyFlowTests(unittest.TestCase):
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped

    def setUp(self):
        fake.FlowTests.setUp(self)
        # Test-owned temporary files only. Add the frozen route catalog inputs.
        for obligation in fake.pipeline.OBLIGATIONS.values():
            for name in obligation["inputs"]:
                path = self.repo / name
                if not path.exists():
                    path.write_text("# Synthetic strategy source\n" + name + "\n")
        self.before = self.source_files()

    def execute(self, script=None, **changes):
        options = dict(optimize=True, integrate=True, integration_closure=True,
                       strategy_review=True, attempts=4, parallelism=8)
        options.update(changes)
        result = fake.FlowTests.execute(self, script or script_with_routes("r3_r5_leading"), **options)
        self.assertEqual(self.source_files(), self.before)
        self.assert_stopped()
        return result

    def test_startup_routes_two_of_eight_lanes_with_own_blind_audits(self):
        script = script_with_routes("r3_r5_leading", "actual_kinetic")
        work, summary = self.execute(script, attempts=8)
        self.assertEqual(len(summary["candidates"]), 6)
        self.assertEqual(len(summary["strategy_candidates"]), 2)
        self.assertEqual({r["obligation_id"] for r in summary["strategy_candidates"]},
                         {"r3_r5_leading", "actual_kinetic"})
        self.assertEqual(script.max_active, 8)
        self.assertEqual(script.role_calls["strategist"], 1)
        for record in summary["strategy_candidates"]:
            self.assertEqual(len(record["reviews"]), 2)
            self.assertIn("proof_path", record)
        for call in script.calls:
            if call.role.startswith("reviewer_"):
                self.assertNotIn(MARKER, call.prompt)
                self.assertNotIn("UNVERIFIED RESEARCH ASSIGNMENT", call.prompt)
                self.assertFalse(any("strategy-review" in p.name for p in call.session.cwd.iterdir()))
        report = json.loads((work / "strategy-review-1.json").read_text())
        self.assertEqual(report["status"], "planning_only")
        self.assertFalse(report["trusted_proof"])
        self.assertFalse(summary["research_goal_proved"])

    def test_alternative_selected_obligation_does_not_finish_primary(self):
        def selected(session):
            result = draft(session)
            if result["obligation_id"] != "self_audit":
                result["scope"] = "selected_obligation"
            return result
        script = script_with_routes("r3_r5_leading")
        script.queues["solver"].clear()
        script.queues["solver"].extend([selected] * 8)
        _, summary = self.execute(script)
        self.assertEqual(summary["strategy_candidates"][0]["status"],
                         "reviewed_candidate_pending_manual_integration")
        self.assertEqual(summary["status"], "round_limit_reached")
        self.assertEqual(summary["latest_integration"], "")

    def test_strategy_results_feed_full_proofs_to_integrator(self):
        script = script_with_routes("r3_r5_leading")
        _, summary = self.execute(script)
        path = summary["strategy_candidates"][0]["proof_path"]
        call = next(c for c in script.calls if c.role == "integrator")
        self.assertTrue((call.session.cwd / path).is_file())
        self.assertNotIn(MARKER, call.prompt)

    def test_invalid_target_or_hash_rejects_entire_plan_and_preserves_local_lanes(self):
        for defect in ("target", "hash", "decision"):
            def invalid(session):
                result = proposal(session)
                if defect == "target":
                    result["tasks"][0]["obligation_id"] = "change_physics"
                elif defect == "hash":
                    result["tasks"][0]["dependencies"][0]["sha256"] = "0" * 64
                else:
                    result["decision"] = "continue_local"
                return result
            with self.subTest(defect=defect):
                script = script_with_routes("r3_r5_leading")
                script.queues["strategist"].clear()
                script.queues["strategist"].append(invalid)
                work, summary = self.execute(script)
                report = json.loads((work / "strategy-review-1.json").read_text())
                self.assertEqual(report["status"], "invalid_plan")
                self.assertEqual(summary["strategy_candidates"], [])
                self.assertEqual(len(summary["candidates"]), 4)

    def test_missing_route_input_is_not_silently_assumed(self):
        name = fake.pipeline.OBLIGATIONS["actual_kinetic"]["inputs"][0]
        # Rename only a test-owned fixture, preserving its content for inspection.
        (self.repo / name).rename(self.repo / (name + ".unavailable"))
        self.before = self.source_files()
        work, summary = self.execute(script_with_routes("actual_kinetic"))
        report = json.loads((work / "strategy-review-1.json").read_text())
        self.assertEqual(report["status"], "invalid_plan")
        self.assertEqual(summary["strategy_candidates"], [])

    def test_wrong_candidate_obligation_never_accepted(self):
        def wrong(session):
            return fake.candidate(session, claim="Synthetic wrong-obligation candidate " + session.agent.name,
                                  scope="sublemma")
        script = script_with_routes("actual_kinetic")
        script.queues["solver"].clear()
        script.queues["solver"].extend([wrong] * 8)
        _, summary = self.execute(script)
        result = summary["strategy_candidates"][0]
        self.assertEqual(result["status"], "invalid_evidence")
        self.assertEqual(result["reviews"], [])
        self.assertNotIn("proof_path", result)

    def test_incomplete_strategy_audit_never_promoted_or_called_math_failure(self):
        def incomplete(session):
            if "Obligation ID: actual_kinetic" in session.prompts[-1]:
                return fake.review(session, verdict="inconclusive", first_fault="Audit unfinished",
                                   dependencies_checked=False)
            return fake.review(session)
        script = script_with_routes("actual_kinetic")
        script.queues["reviewer_a"] = fake.deque([incomplete] * 16)
        _, summary = self.execute(script)
        result = summary["strategy_candidates"][0]
        self.assertEqual(result["status"], "audit_pending")
        self.assertNotIn("proof_path", result)
        self.assertEqual(summary["audit_recheck_pairs"], 1)

    def test_missing_strategy_output_falls_back_to_full_local_work(self):
        script = script_with_routes("actual_kinetic")
        script.queues["strategist"] = fake.deque([None])
        work, summary = self.execute(script)
        self.assertEqual(len(summary["candidates"]), 4)
        self.assertEqual(summary["strategy_candidates"], [])
        self.assertEqual(json.loads((work / "strategy-review-1.json").read_text())["status"], "output_unavailable")

    def test_two_failed_integrations_trigger_review_and_exact_task_is_not_repeated(self):
        script = script_with_routes("r3_r5_leading")
        work, summary = self.execute(script, rounds=3)
        self.assertEqual(script.role_calls["strategist"], 2)
        self.assertEqual(json.loads((work / "strategy-review-3.json").read_text())["trigger"],
                         "two_unsuccessful_integrations")
        self.assertEqual(len(summary["strategy_candidates"]), 1)
        prompt = [c.prompt for c in script.calls if c.role == "strategist"][-1]
        self.assertIn("reviewed_sublemma_pending_manual_integration", prompt)

    def test_no_optimize_or_no_integrate_disables_strategy(self):
        for options in ({"strategy_review": False}, {"optimize": False}, {"integrate": False}):
            with self.subTest(options=options):
                script = script_with_routes("actual_kinetic")
                _, summary = self.execute(script, **options)
                self.assertEqual(script.role_calls["strategist"], 0)
                self.assertFalse(summary["strategy_review_enabled"])

    def test_periodic_review_without_failed_integrations(self):
        from pipelines.quantum_humanize.test_integration import combination
        script = script_with_routes("r3_r5_leading")
        script.queues["integrator"] = fake.deque([
            lambda s: {"candidate": combination(s, claim="Synthetic combination " + s.agent.name),
                       "next_tasks": []}] * 4)
        work, _ = self.execute(script, attempts=2, rounds=4)
        self.assertEqual(script.role_calls["strategist"], 2)
        self.assertEqual(json.loads((work / "strategy-review-4.json").read_text())["trigger"], "periodic")

    def test_pause_retains_but_does_not_dispatch_queued_exploration(self):
        script = script_with_routes("r3_r5_leading", "actual_kinetic")
        script.queues["strategist"] = fake.deque([
            lambda s: proposal(s, targets=("r3_r5_leading", "actual_kinetic")),
            lambda s: proposal(s, targets=(), decision="pause_exploration")])
        work, summary = self.execute(script, attempts=1, rounds=3, strategy_interval=2)
        self.assertEqual(len(summary["strategy_candidates"]), 1)
        entries = json.loads((work / "strategy-tasks-final.json").read_text())
        self.assertEqual(len(entries), 2)
        self.assertEqual(entries[1]["status"], "deferred_by_strategy")

    def test_failure_feedback_reaches_strategy_but_not_future_reviewers(self):
        private_fault = "PRIVATE EXPLORATION FAULT SENTINEL"
        def negative(session):
            if "Obligation ID: r3_r5_leading" in session.prompts[-1]:
                return fake.review(session, verdict="gap", first_fault=private_fault,
                                   full_claim_checked=False)
            return fake.review(session)
        script = script_with_routes("r3_r5_leading")
        script.queues["reviewer_a"] = fake.deque([negative] * 30)
        script.queues["strategist"] = fake.deque([
            proposal, lambda s: proposal(s, targets=("actual_kinetic",))])
        _, summary = self.execute(script, rounds=3)
        planners = [c for c in script.calls if c.role == "strategist"]
        self.assertIn(private_fault, planners[1].prompt)
        self.assertEqual(summary["strategy_candidates"][0]["status"], "needs_repair")
        for call in script.calls:
            if call.role.startswith("reviewer_") or call.role == "solver":
                self.assertNotIn(private_fault, call.prompt)

    def test_strategy_costs_share_original_call_budget(self):
        work, summary = self.execute(max_calls=3)
        self.assertLessEqual(summary["calls"], 3)
        self.assertEqual(json.loads((work / "strategy-review-1.json").read_text())["status"],
                         "skipped_low_call_budget")
        self.assertFalse(summary["research_goal_proved"])

    def test_threshold_task_is_available_without_forcing_phase_partition(self):
        _, summary = self.execute(script_with_routes("thermalization_threshold"))
        record = summary["strategy_candidates"][0]
        self.assertEqual(record["obligation_id"], "thermalization_threshold")
        self.assertIn("proof_path", record)

    def test_explicit_cross_route_restart_input_is_material_not_inherited_votes(self):
        work, summary = self.execute(script_with_routes("actual_kinetic"))
        name = summary["strategy_candidates"][0]["proof_path"]
        destination = self.repo / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((work / "proofs" / destination.name).read_bytes())
        script = script_with_routes()
        script.queues["strategist"] = fake.deque([
            lambda s: proposal(s, targets=(), decision="continue_local")])
        _, summary = self.execute(script, extra_inputs=[name])
        self.assertEqual(summary["strategy_candidates"], [])
        self.assertFalse(summary["research_goal_proved"])
        planner = next(c for c in script.calls if c.role == "strategist")
        self.assertTrue((planner.session.cwd / name).is_file())
        self.assertNotIn("Scripted review response", (planner.session.cwd / name).read_text())


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
