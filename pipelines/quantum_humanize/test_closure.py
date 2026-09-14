"""Closure/re-audit regressions: synthetic local agents, no native calls or mathematics."""

import json
import unittest

from pipelines.quantum_humanize import test_flow as fake
from pipelines.quantum_humanize import test_integration as integration
from pipelines.quantum_humanize import test_frontier_flow as planning
from pipelines.quantum_humanize import _assembly as assembly


def composed(session, *, kind="assembly", **changes):
    result = planning.planned(session, **changes)
    contract = {
        "kind": kind,
        "pieces": result["candidate"]["dependencies"],
        "deferred_pieces": [],
        "partition_identity": "SYNTHETIC IDENTITY: U = A disjoint-union B disjoint-union E.",
        "uncovered_region": "SYNTHETIC COMPLEMENT: E remains uncontrolled.",
        "overlap_argument": "SYNTHETIC OVERLAP: selector modulus is at most one.",
        "cutoff_argument": "SYNTHETIC PARAMETERS: declared powers only, no global proof.",
        "gap_updates": [],
    }
    result["assembly"] = contract
    result["candidate"]["argument"] += "\n" + "\n".join(
        contract[k] for k in ("partition_identity", "uncovered_region", "overlap_argument", "cutoff_argument"))
    marker = "INTEGRATION DELTA CONTEXT:\n"
    context = json.JSONDecoder().raw_decode(session.prompts[-1].split(marker, 1)[1])[0]
    baseline = context["baseline"]
    result["progress"] = {
        "kind": "stronger_bound" if baseline else "initial", "baseline": baseline,
        "previous_statement": "SYNTHETIC PREVIOUS MATHEMATICAL BOUND" if baseline else "",
        "improved_statement": "SYNTHETIC STRICTLY STRONGER MATHEMATICAL BOUND" if baseline else "",
        "justification": "SYNTHETIC DELTA DERIVATION, NOT A REAL PROOF" if baseline else "",
    }
    if baseline:
        result["candidate"]["argument"] += "\n" + "\n".join(
            result["progress"][key] for key in ("previous_statement", "improved_statement", "justification"))
    return result


def local_a(session):
    return integration.local(session, claim="SYNTHETIC LOCAL A")


def local_b(session):
    return integration.local(session, claim="SYNTHETIC LOCAL B")


def incomplete(session):
    return fake.review(session, verdict="inconclusive", first_fault="Audit reading not completed",
                       explanation="PRIVATE UNFINISHED AUDIT, NOT A MATHEMATICAL DEFECT",
                       dependencies_checked=False, full_claim_checked=False)


class ClosureTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped

    def execute(self, script=None, **changes):
        options = {"optimize": True, "integrate": True, "coverage_planning": True,
                   "integration_closure": True, "attempts": 2, "audit_continuations": 0}
        options.update(changes)
        result = fake.FlowTests.execute(self, script, **options)
        self.assertEqual(self.source_files(), self.before)
        self.assert_stopped()
        return result

    def test_new_contract_schema_is_strict_and_old_schema_is_unchanged(self):
        self.assertTrue(fake.pipeline.Config().integration_closure)
        self.assertEqual(set(fake.pipeline.PlannedIntegration.model_json_schema()["properties"]),
                         {"candidate", "next_tasks", "frontier"})
        schema = fake.pipeline.AssemblyIntegration.model_json_schema()
        self.assertEqual(set(schema["properties"]), {"candidate", "next_tasks", "frontier", "assembly", "progress"})
        stack = [schema]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("type") == "object":
                    self.assertEqual(set(node["required"]), set(node["properties"]))
                    self.assertFalse(node["additionalProperties"])
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)

    def test_assembly_requires_two_pieces_and_the_argument_is_reviewed_not_the_table(self):
        script = fake.Script(solver=[local_a, local_b], integrator=[composed])
        work, summary = self.execute(script)
        record = summary["integrations"][0]
        self.assertEqual(record["assembly_status"], "dual_reviewed_assembly_pending_manual_check")
        self.assertEqual(summary["latest_integration"], record["proof_path"])
        self.assertFalse(summary["research_goal_proved"])
        self.assertTrue((work / "coverage-ledger-1.json").is_file())
        for call in script.calls:
            if call.role.startswith("reviewer_"):
                self.assertNotIn(planning.FRONTIER_MARKER, call.prompt)
                self.assertNotIn("Cumulative UNVERIFIED coverage", call.prompt)
                if "Synthetic combined claim" in call.prompt:
                    self.assertIn("SYNTHETIC IDENTITY", call.prompt)
                    self.assertIn("SYNTHETIC COMPLEMENT", call.prompt)
        self.assertEqual(len(record["research_tasks"]), 1)

    def test_single_piece_mislabeled_as_assembly_is_not_accepted(self):
        script = fake.Script(solver=[local_a], integrator=[composed])
        _, summary = self.execute(script, attempts=1)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "assembly_contract_invalid")
        self.assertTrue(any("two distinct" in error for error in record["contract_errors"]))
        self.assertNotIn("proof_path", record)
        self.assertEqual(script.role_calls["reviewer_a"], 1)

    def test_unmentioned_input_proof_blocks_the_assembly_contract(self):
        def omitted(session):
            result = composed(session)
            result["assembly"]["pieces"].pop()
            return result
        _, summary = self.execute(fake.Script(solver=[local_a, local_b], integrator=[omitted]))
        record = summary["integrations"][0]
        self.assertIn("every available proof must be used or explicitly deferred", record["contract_errors"])
        self.assertEqual(record["status"], "assembly_contract_invalid")

    def test_explicit_deferral_accounts_for_inputs_but_does_not_prove_their_region(self):
        def deferred(session):
            result = composed(session)
            ref = result["assembly"]["pieces"].pop()
            result["assembly"]["deferred_pieces"] = [{"reference": ref, "reason": "Overlap still unresolved"}]
            return result
        script = fake.Script(solver=[local_a, local_b, lambda s: integration.local(s, claim="LOCAL C")],
                             integrator=[deferred])
        work, summary = self.execute(script, attempts=3)
        self.assertEqual(summary["integrations"][0]["contract_errors"], [])
        ledger = json.loads((work / "coverage-ledger-final.json").read_text())
        self.assertFalse(ledger["coverage_complete"])
        self.assertTrue(all(g["status"] == "open" for g in ledger["gaps"].values()))

    def test_argument_hidden_only_in_contract_is_not_accepted(self):
        def hidden(session):
            result = composed(session)
            result["candidate"]["argument"] = "No assembled argument here"
            return result
        _, summary = self.execute(fake.Script(solver=[local_a, local_b], integrator=[hidden]))
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "assembly_contract_invalid")
        self.assertEqual(len(record["contract_errors"]), 4)

    def test_discovery_can_be_reviewed_but_does_not_complete_assembly_or_stop_the_run(self):
        script = fake.Script(solver=[local_a], integrator=[lambda s: composed(
            s, kind="new_lemma", scope="selected_obligation")])
        _, summary = self.execute(script, attempts=1)
        record = summary["integrations"][0]
        self.assertEqual(record["assembly_status"], "new_lemma_only")
        self.assertIn("proof_path", record)
        self.assertEqual(summary["latest_integration"], "")
        self.assertEqual(summary["status"], "round_limit_reached")
        self.assertTrue(summary["integration_pending"])

    def test_valid_research_tasks_escape_failed_composition_without_its_body_or_votes(self):
        private = "REJECTED COMPOSITION BODY MUST REMAIN PRIVATE"
        assigned = []

        def reject(session):
            if private in session.prompts[-1]:
                return fake.negative(session)
            return fake.review(session)

        def solve_task(session):
            assigned.append(session.prompts[-1])
            self.assertIn(planning.GAP_MARKER, session.prompts[-1])
            self.assertIn("UNVERIFIED RESEARCH TARGET", session.prompts[-1])
            self.assertNotIn(private, session.prompts[-1])
            for entry in integration.proofs(session):
                self.assertNotIn(private, (session.cwd / entry["path"]).read_text())
            return None

        script = fake.Script(solver=[local_a, local_b, solve_task],
                             integrator=[lambda s: composed(s, argument=private)],
                             reviewer_a=[reject] * 3, mender=[None])
        work, summary = self.execute(script, rounds=2)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "needs_repair")
        self.assertNotIn("proof_path", record)
        self.assertEqual(len(assigned), 1)
        self.assertEqual(summary["latest_integration"], "")
        tasks = json.loads((work / "research-tasks-final.json").read_text())
        self.assertEqual(tasks[0]["status"], "dispatched")
        self.assertFalse(tasks[0]["trusted_proof"])

    def test_blocked_assembly_has_tasks_but_no_claim_reviews_or_admission(self):
        script = fake.Script(solver=[local_a, local_b], integrator=[lambda s: composed(s, kind="blocked")])
        _, summary = self.execute(script)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "assembly_blocked")
        self.assertEqual(record["reviews"], [])
        self.assertTrue(record["research_tasks"])
        self.assertNotIn("proof_path", record)
        self.assertEqual(script.role_calls["reviewer_a"], 2)

    def test_table_correction_is_bounded_separate_and_does_not_rewrite_candidate(self):
        seen = {}

        def invalid(session):
            result = composed(session)
            result["frontier"]["obligation_id"] = "r5_global"
            seen["candidate"] = result["candidate"]
            return result

        def correct_table(session):
            self.assertIn("Repair only", session.prompts[-1])
            return planning.frontier(session)

        work, summary = self.execute(fake.Script(solver=[local_a, local_b], integrator=[invalid, correct_table]))
        record = summary["integrations"][0]
        self.assertEqual(record["frontier_report"], "frontier-repair-1.json")
        self.assertEqual(json.loads((work / "integration-candidate-1.json").read_text()), seen["candidate"])
        before = json.loads((work / "frontier-report-1.json").read_text())
        after = json.loads((work / "frontier-repair-1.json").read_text())
        self.assertTrue(before["analysis"]["validation_errors"])
        self.assertEqual(after["analysis"]["validation_errors"], [])
        requests = [json.loads(p.read_text()) for p in work.glob("call-*/request.json")]
        self.assertEqual(sum(r["role"] == "frontier_repair" for r in requests), 1)
        self.assertEqual(record["assembly_status"], "dual_reviewed_assembly_pending_manual_check")

    def test_failed_table_correction_is_not_assumed_valid_and_does_not_generate_tasks(self):
        def invalid(session):
            result = composed(session)
            result["frontier"]["obligation_id"] = "r5_global"
            return result
        script = fake.Script(solver=[local_a, local_b], integrator=[invalid, lambda s: planning.frontier(
            s, obligation_id="r5_global")])
        work, summary = self.execute(script)
        record = summary["integrations"][0]
        self.assertEqual(script.role_calls["integrator"], 2)
        self.assertEqual(record["assembly_status"], "planning_invalid")
        self.assertEqual(record["research_tasks"], [])
        self.assertEqual(summary["latest_integration"], "")
        self.assertEqual(json.loads((work / "coverage-ledger-final.json").read_text())["cells"], {})

    def test_incomplete_audit_gets_fresh_blind_pair_not_a_mender(self):
        script = fake.Script(solver=[local_a], reviewer_a=[incomplete, fake.DEFAULT])
        work, summary = self.execute(script, attempts=1, integrate=False)
        self.assertEqual(script.role_calls["reviewer_a"], 2)
        self.assertEqual(script.role_calls["reviewer_b"], 2)
        self.assertEqual(script.role_calls["mender"], 0)
        self.assertEqual(summary["audit_recheck_pairs"], 1)
        self.assertTrue(summary["candidates"][0]["status"].startswith("reviewed_"))
        reviews = [c for c in script.calls if c.role.startswith("reviewer_")]
        self.assertEqual(len({id(c.session) for c in reviews}), 4)
        self.assertEqual(len({c.prompt for c in reviews}), 1)
        for c in reviews:
            self.assertNotIn("PRIVATE UNFINISHED AUDIT", c.prompt)
            self.assertEqual(c.schema.model_json_schema()["properties"]["candidate_sha256"]["const"],
                             summary["candidates"][0]["sha256"])
        self.assertEqual(len(json.loads((work / "audit-pair-001.json").read_text())["passes"]), 2)

    def test_hash_protocol_failure_is_not_silently_rewritten_or_sent_to_mender(self):
        script = fake.Script(solver=[local_a], reviewer_a=[lambda s: fake.review(s, candidate_sha256="0" * 64)])
        work, summary = self.execute(script, attempts=1, integrate=False)
        self.assertEqual(script.role_calls["mender"], 0)
        self.assertTrue(summary["candidates"][0]["status"].startswith("reviewed_"))
        failures = [json.loads(p.read_text()) for p in work.glob("call-*/failure.json")]
        self.assertTrue(any(f["kind"] == "invalid_schema" for f in failures))
        raw = [p.read_text() for p in work.glob("call-*/raw-response.json")]
        self.assertTrue(any("0" * 64 in text for text in raw))

    def test_exhausted_incomplete_audit_is_carried_unchanged_to_next_round(self):
        script = fake.Script(solver=[local_a], reviewer_a=[incomplete, incomplete, fake.DEFAULT])
        work, summary = self.execute(script, attempts=1, integrate=False, rounds=2)
        first, second = summary["candidates"]
        self.assertEqual(first["status"], "audit_pending")
        self.assertEqual(first["sha256"], second["sha256"])
        self.assertTrue(second["status"].startswith("reviewed_"))
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(script.role_calls["mender"], 0)
        self.assertEqual(summary["pending_audits"], 0)
        pending = json.loads((work / "pending-audits-1.json").read_text())
        self.assertEqual(len(pending), 1)
        self.assertFalse(pending[0]["trusted_proof"])

    def test_math_gap_uses_mender_without_audit_only_retries(self):
        script = fake.Script(solver=[local_a], reviewer_a=[fake.negative], mender=[None])
        _, summary = self.execute(script, attempts=1, integrate=False)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(summary["audit_recheck_pairs"], 0)

    def test_reaudit_obeys_shared_call_budget(self):
        script = fake.Script(solver=[local_a], reviewer_a=[incomplete])
        _, summary = self.execute(script, attempts=1, integrate=False, max_calls=4)
        self.assertEqual(summary["calls"], 4)
        self.assertEqual(summary["status"], "call_budget_exhausted")
        self.assertFalse(any(r["status"].startswith("reviewed_") for r in summary["candidates"]))

    def test_cumulative_candidate_navigation_survives_an_empty_round(self):
        script = fake.Script(solver=[local_a, None, None], integrator=[lambda s: composed(s, kind="new_lemma"), None, None])
        work, _ = self.execute(script, attempts=1, rounds=3)
        second = json.loads((work / "round-context-2.json").read_text())
        third = json.loads((work / "round-context-3.json").read_text())
        self.assertEqual(second["coverage_ledger_total"], 1)
        self.assertEqual(second["coverage_ledger"], third["coverage_ledger"])

    def test_unchanged_discovery_does_not_create_an_integration_self_loop(self):
        seen = {}
        def first(session):
            seen["answer"] = composed(session, kind="new_lemma")
            return seen["answer"]
        script = fake.Script(solver=[local_a, None, None],
                             integrator=[first, lambda s: seen["answer"]])
        _, summary = self.execute(script, attempts=1, rounds=3)
        self.assertEqual(script.role_calls["integrator"], 2)
        self.assertEqual(summary["integrations"][1]["status"], "duplicate_candidate")
        self.assertFalse(summary["integration_pending"])

    def test_reaudit_cannot_see_a_proof_admitted_after_its_original_epoch(self):
        observed = []
        counts = {"reviewer_a": 0, "reviewer_b": 0}
        def audit(session):
            if "SYNTHETIC LOCAL A" in session.prompts[-1]:
                role = session.agent.role
                counts[role] += 1
                observed.append((role, counts[role], integration.proofs(session)))
                if role == "reviewer_a" and counts[role] <= 2:
                    return incomplete(session)
            return fake.review(session)
        script = fake.Script(solver=[local_a, local_b, None],
                             reviewer_a=[audit] * 4, reviewer_b=[audit] * 4,
                             integrator=[None, None])
        _, summary = self.execute(script, integrate=True, rounds=2)
        self.assertEqual(len([r for r in summary["candidates"] if r["status"].startswith("reviewed_")]), 2)
        self.assertEqual(counts, {"reviewer_a": 3, "reviewer_b": 3})
        self.assertTrue(all(not proofs for _, _, proofs in observed))
        self.assertEqual(script.role_calls["mender"], 0)

    def test_successful_reaudit_of_composition_still_requires_fresh_assembly(self):
        count = []
        def audit(session):
            if "Synthetic combined claim" in session.prompts[-1]:
                count.append(1)
                if len(count) <= 2:
                    return incomplete(session)
            return fake.review(session)
        script = fake.Script(solver=[local_a, local_b, None], integrator=[composed, None],
                             reviewer_a=[audit] * 6)
        work, summary = self.execute(script, rounds=2)
        self.assertEqual(summary["integrations"][0]["status"], "audit_pending")
        self.assertEqual(summary["latest_integration"], "")
        self.assertTrue(any(r["round"] == 2 and r["status"].startswith("reviewed_")
                            for r in summary["candidates"]))
        self.assertEqual(script.role_calls["mender"], 0)
        self.assertEqual(len(json.loads((work / "pending-audits-1.json").read_text())), 1)

    def test_unknown_constant_never_counts_as_a_shared_cutoff_success(self):
        def unknown(session):
            result = composed(session)
            refs = result["frontier"]["partition_dependencies"]
            cell = result["frontier"]["cells"][0]
            cell.update(status="bounded", gap="Still missing a uniform constant", bound={
                "time_power": "1", "log_power": "0", "cutoff_powers": [],
                "constant_policy": "unknown", "unknown_dependencies": ["C_delta not quantified"],
                "norm": "Synthetic L1", "window_and_limits": "Original window", "hypothesis_conditions": [],
                "dependencies": refs,
            })
            return result
        _, summary = self.execute(fake.Script(solver=[local_a, local_b], integrator=[unknown]))
        record = summary["integrations"][0]
        self.assertEqual(record["assembly_status"], "cutoff_plan_unresolved")
        self.assertEqual(summary["latest_integration"], "")
        self.assertTrue(record["research_tasks"])

    def test_nonexistent_task_dependency_cannot_become_a_research_assignment(self):
        def forged(session):
            result = composed(session, kind="blocked")
            result["next_tasks"] = [{"obligation_id": "self_audit", "objective": "FORGED TASK",
                "success_criterion": "No actual evidence", "dependencies": [
                    {"path": "invented.md", "sha256": "0" * 64, "section": "Unavailable"}]}]
            return result
        _, summary = self.execute(fake.Script(solver=[local_a, local_b], integrator=[forged]))
        record = summary["integrations"][0]
        self.assertTrue(record["task_errors"])
        self.assertTrue(all(t["task"]["objective"] != "FORGED TASK" for t in record["research_tasks"]))

    def test_assembly_ledger_reaches_only_integrator_and_retains_omitted_previous_gap(self):
        seen = {}
        def first(session):
            result = composed(session)
            seen["first_gap"] = result["frontier"]["cells"][0]["gap"]
            return result
        def second(session):
            self.assertIn("Cumulative UNVERIFIED coverage", session.prompts[-1])
            self.assertIn('"gap_', session.prompts[-1])
            result = composed(session)
            result["candidate"]["claim"] = "Second synthetic assembly"
            result["frontier"]["cells"][0]["gap"] = "New outstanding gap"
            return result
        script = fake.Script(solver=[local_a, local_b, lambda s: integration.local(s, claim="LOCAL C"), None],
                             integrator=[first, second])
        work, _ = self.execute(script, rounds=2)
        ledger = json.loads((work / "coverage-ledger-final.json").read_text())
        self.assertEqual(len(ledger["cells"]), 1)
        self.assertEqual(len(ledger["gaps"]), 2)
        self.assertTrue(all(g["status"] == "open" for g in ledger["gaps"].values()))
        for call in script.calls:
            if call.role.startswith("reviewer_"):
                self.assertNotIn("Cumulative UNVERIFIED coverage", call.prompt)
                self.assertNotIn(planning.GAP_MARKER, call.prompt)


class LedgerTests(unittest.TestCase):
    def frontier(self):
        refs = [{"path": "source.md", "sha256": "a" * 64, "section": "Synthetic source"}]
        return fake.pipeline.Frontier.model_validate({
            "obligation_id": "self_audit", "partition_argument": "Synthetic partition",
            "partition_dependencies": refs, "partition_gaps": ["Original global gap"],
            "parameters": [], "conditions": [], "cells": [{
                "id": "first", "placements": ["p1"], "source_labels": "s", "temporal_signs": "all",
                "outputs": "all", "region": "original region", "boundary_and_overlap": "unknown",
                "localization": "bounded by one", "status": "open", "bound": None,
                "gap": "Local gap", "dependencies": refs,
            }],
        })

    def test_stable_geometry_ids_survive_renaming_and_no_omission_closes_gaps(self):
        ledger = assembly.empty_ledger()
        first = self.frontier()
        assembly.retain_frontier(ledger, first, 1, "1" * 64, "needs_repair")
        ids = set(ledger["cells"])
        gaps = set(ledger["gaps"])
        second = self.frontier()
        second.cells[0].id = "renamed"
        second.partition_gaps = []
        assembly.retain_frontier(ledger, second, 2, "2" * 64, "reviewed_sublemma")
        self.assertEqual(set(ledger["cells"]), ids)
        self.assertEqual(set(ledger["gaps"]), gaps)
        self.assertTrue(all(g["status"] == "open" for g in ledger["gaps"].values()))
        self.assertEqual(len(ledger["rounds"]), 2)
        self.assertFalse(ledger["coverage_complete"])

    def test_reusing_local_id_cannot_overwrite_a_different_region(self):
        ledger = assembly.empty_ledger()
        frontier = self.frontier()
        assembly.retain_frontier(ledger, frontier, 1, "1" * 64, "needs_repair")
        frontier.cells[0].region = "different region"
        assembly.retain_frontier(ledger, frontier, 2, "2" * 64, "needs_repair")
        self.assertEqual(len(ledger["cells"]), 2)

    def test_prompt_view_limits_are_explicit_and_do_not_delete_history(self):
        ledger = assembly.empty_ledger()
        for i in range(40):
            f = self.frontier()
            f.cells[0].region = f"region {i}"
            assembly.retain_frontier(ledger, f, i + 1, "1" * 64, "unverified")
        view = assembly.ledger_view(ledger)
        self.assertEqual(view["total_cells"], 40)
        self.assertEqual(view["omitted_cells"], 8)
        self.assertEqual(len(ledger["cells"]), 40)
        self.assertGreater(view["omitted_gaps"], 0)
        self.assertFalse(view["coverage_complete"])


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
