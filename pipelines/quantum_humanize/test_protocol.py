"""Metadata recovery regressions; synthetic fixtures, no native calls or proof evidence."""

import copy
import json
import unittest

from pipelines.quantum_humanize import _protocol as protocol
from pipelines.quantum_humanize import _frontier as frontier
from pipelines.quantum_humanize import test_frontier as data
from pipelines.quantum_humanize import test_flow as fake
from pipelines.quantum_humanize import test_closure as closure
from pipelines.quantum_humanize import test_optimized as optimized


def confirmations(issues, **changes):
    return {"confirmations": [dict(index=item["index"], path=item["path"], confirmed=True,
        section="Confirmed synthetic source section", explanation="Synthetic confirmation, not proof", **changes)
        for item in issues]}


def confirm(session):
    issues = json.loads(session.prompts[-1].split("Mismatched references:\n", 1)[1])
    return confirmations(issues)


def wrong_hash(session):
    result = closure.composed(session)
    # The contract aliases this dependency too: both typed occurrences must be fixed.
    result["candidate"]["dependencies"][0]["sha256"] = "0" * 64
    return result


class ProtocolTests(unittest.TestCase):
    def bad_frontier(self):
        return frontier.Frontier.model_validate(data._fixture(
            parameters=[data._parameter()], conditions=[data._condition()],
            cells=[data._cell(bound=data._bound(hypothesis_conditions=["cap", "Keep the original phase"]))]))

    def repaired_frontier(self, original):
        result = original.model_copy(deep=True)
        result.cells[0].bound.hypothesis_conditions = ["cap"]
        result.partition_gaps += protocol.retained_hypotheses(original)
        return result

    def test_confirmation_schema_is_closed_and_requires_all_fields(self):
        stack = [protocol.ReferenceRepair.model_json_schema()]
        while stack:
            node = stack.pop()
            if isinstance(node, dict):
                if node.get("type") == "object":
                    self.assertEqual(set(node["required"]), set(node["properties"]))
                    self.assertFalse(node["additionalProperties"])
                stack.extend(node.values())
            elif isinstance(node, list):
                stack.extend(node)

    def test_references_are_typed_and_all_nested_occurrences_are_confirmed(self):
        original = self.bad_frontier()
        for _, ref in protocol.references(original):
            ref.sha256 = "0" * 64
        before = original.model_dump()
        issues = protocol.reference_issues(original, data.MANIFEST)
        self.assertEqual(len(issues), 4)
        repaired, errors = protocol.apply_confirmations(original, issues,
            protocol.ReferenceRepair.model_validate(confirmations(issues)))
        self.assertEqual(errors, [])
        self.assertEqual(original.model_dump(), before)
        self.assertEqual(protocol.reference_issues(repaired, data.MANIFEST), [])
        for _, ref in protocol.references(repaired):
            ref.sha256 = "0" * 64
            ref.section = data._evidence()["section"]
        self.assertEqual(repaired, original)

    def test_known_correct_references_need_no_confirmation(self):
        self.assertEqual(protocol.reference_issues(self.bad_frontier(), data.MANIFEST), [])

    def test_incomplete_duplicate_denied_or_substituted_confirmation_is_atomic(self):
        original = self.bad_frontier()
        for _, ref in protocol.references(original):
            ref.sha256 = "0" * 64
        issues = protocol.reference_issues(original, data.MANIFEST)
        answer = confirmations(issues)
        variants = []
        missing = copy.deepcopy(answer)
        missing["confirmations"].pop()
        variants.append(missing)
        duplicate = copy.deepcopy(answer)
        duplicate["confirmations"][-1] = duplicate["confirmations"][0]
        variants.append(duplicate)
        for field, value in (("confirmed", False), ("path", "invented.md"), ("index", 999)):
            changed = copy.deepcopy(answer)
            changed["confirmations"][0][field] = value
            variants.append(changed)
        for reply in variants:
            with self.subTest(reply=reply):
                repaired, errors = protocol.apply_confirmations(original, issues,
                    protocol.ReferenceRepair.model_validate(reply))
                self.assertIs(repaired, original)
                self.assertTrue(errors)

    def test_unknown_path_cannot_be_bound_even_with_confirmation(self):
        original = self.bad_frontier()
        original.partition_dependencies[0].path = "invented.md"
        issues = protocol.reference_issues(original, data.MANIFEST)
        repaired, errors = protocol.apply_confirmations(original, issues,
            protocol.ReferenceRepair.model_validate(confirmations(issues)))
        self.assertIs(repaired, original)
        self.assertTrue(errors)

    def test_qualitative_premises_survive_and_make_feasible_algebra_unknown(self):
        original = self.bad_frontier()
        repaired = self.repaired_frontier(original)
        self.assertEqual(protocol.frontier_repair_errors(original, repaired, data.OBLIGATION), [])
        report = frontier.analyze_frontier(repaired, data.MANIFEST, data.OBLIGATION)
        self.assertEqual(report["validation_errors"], [])
        self.assertEqual(report["cutoffs"]["algebra"]["status"], "feasible")
        self.assertEqual(report["cutoffs"]["status"], "unknown")
        self.assertTrue(any("Keep the original phase" in task["objective"] for task in report["tasks"]))
        self.assertFalse(report["trusted_proof"])

    def test_cannot_erase_a_bad_reference_by_dropping_its_premise(self):
        original = self.bad_frontier()
        repaired = self.repaired_frontier(original)
        repaired.partition_gaps = []
        self.assertTrue(protocol.frontier_repair_errors(original, repaired, data.OBLIGATION))

    def test_cannot_change_geometry_bound_conditions_or_old_gaps(self):
        original = self.bad_frontier()
        original.partition_gaps = ["Old unresolved partition gap"]
        for mutation in (
            lambda x: x.conditions.clear(),
            lambda x: x.parameters.clear(),
            lambda x: x.cells.clear(),
            lambda x: setattr(x.cells[0], "region", "A larger region"),
            lambda x: setattr(x.cells[0].bound, "time_power", "0"),
            lambda x: x.cells[0].bound.hypothesis_conditions.clear(),
            lambda x: x.partition_gaps.remove("Old unresolved partition gap"),
            lambda x: setattr(x, "partition_argument", "New argument"),
        ):
            with self.subTest(mutation=mutation):
                repaired = self.repaired_frontier(original)
                mutation(repaired)
                self.assertTrue(protocol.frontier_repair_errors(original, repaired, data.OBLIGATION))

    def test_only_target_obligation_may_be_restored(self):
        original = self.bad_frontier()
        original.obligation_id = "r5_global"
        repaired = self.repaired_frontier(original)
        repaired.obligation_id = data.OBLIGATION
        self.assertEqual(protocol.frontier_repair_errors(original, repaired, data.OBLIGATION), [])
        self.assertTrue(protocol.frontier_repair_errors(original, repaired, "self_audit"))


class ProtocolFlowTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped
    execute = closure.ClosureTests.execute

    def test_confirmed_hash_changes_only_metadata_then_gets_two_fresh_reviews(self):
        script = fake.Script(solver=[closure.local_a, closure.local_b], integrator=[wrong_hash, confirm])
        work, summary = self.execute(script)
        record = summary["integrations"][0]
        self.assertTrue(record["status"].startswith("reviewed_"))
        old = json.loads((work / "integration-candidate-1.json").read_text())
        new = json.loads((work / record["repaired_candidate_path"]).read_text())
        self.assertNotEqual(fake.pipeline.digest(old), record["sha256"])
        self.assertEqual(fake.pipeline.digest(new), record["sha256"])
        for field in old.keys() - {"dependencies"}:
            self.assertEqual(old[field], new[field])
        self.assertEqual([r["path"] for r in old["dependencies"]], [r["path"] for r in new["dependencies"]])
        self.assertEqual(len(record["reviews"]), 2)
        self.assertTrue(all(r["candidate_sha256"] == record["sha256"] for r in record["reviews"]))
        repairs = json.loads((work / record["reference_repair"]["artifact"]).read_text())
        self.assertFalse(repairs["trusted_proof"])
        self.assertEqual(len(repairs["issues"]), 2)
        reviewers = [call for call in script.calls if call.role.startswith("reviewer_")
                     and "Synthetic combined claim" in call.prompt]
        self.assertEqual(len(reviewers), 2)
        self.assertIsNot(reviewers[0].session, reviewers[1].session)
        for call in reviewers:
            self.assertNotIn("Mismatched references", call.prompt)
            self.assertNotIn("Synthetic confirmation, not proof", call.prompt)
        requests = [json.loads(p.read_text()) for p in work.glob("call-*/request.json")]
        request = next(r for r in requests if r["role"] == "reference_repair")
        self.assertEqual(request["timeout_seconds"], fake.pipeline.Config().turn_timeout_seconds)
        self.assertEqual(script.role_calls["mender"], 0)

    def test_denied_confirmation_stops_before_audits_or_mender(self):
        def denied(session):
            reply = confirm(session)
            reply["confirmations"][0]["confirmed"] = False
            return reply
        script = fake.Script(solver=[closure.local_a, closure.local_b], integrator=[wrong_hash, denied])
        work, summary = self.execute(script)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "protocol_repair_failed")
        self.assertFalse(summary["integration_pending"])
        self.assertEqual(record["reviews"], [])
        self.assertEqual(record["research_tasks"], [])
        self.assertEqual(script.role_calls["mender"], 0)
        self.assertEqual(len(list(work.glob("reference-repair-*.json"))), 1)

    def test_missing_confirmation_stays_failed(self):
        script = fake.Script(solver=[closure.local_a, closure.local_b], integrator=[wrong_hash, None])
        _, summary = self.execute(script)
        self.assertEqual(summary["integrations"][0]["status"], "protocol_repair_failed")
        self.assertEqual(script.role_calls["integrator"], 2)

    def test_unknown_attachment_path_blocks_without_guessing_or_extra_calls(self):
        def bad(session):
            result = closure.composed(session)
            result["frontier"]["partition_dependencies"][0]["path"] = "invented.md"
            return result
        script = fake.Script(solver=[closure.local_a, closure.local_b], integrator=[bad])
        _, summary = self.execute(script)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "protocol_repair_failed")
        self.assertEqual(script.role_calls["integrator"], 1)
        self.assertEqual(record["research_tasks"], [])

    def test_same_failed_output_is_confirmed_only_once_even_after_new_local_proof(self):
        seen = {}
        def frozen(session):
            if not seen:
                seen.update(wrong_hash(session))
            return seen
        script = fake.Script(solver=[closure.local_a, closure.local_b,
            lambda s: closure.local_a(s) | {"claim": "SYNTHETIC LOCAL C"}, None],
            integrator=[frozen, None, frozen])
        work, summary = self.execute(script, rounds=2)
        self.assertEqual(len(summary["integrations"]), 2)
        self.assertTrue(all(r["status"] == "protocol_repair_failed" for r in summary["integrations"]))
        self.assertEqual(len(list(work.glob("reference-repair-*.json"))), 1)
        self.assertEqual(script.role_calls["integrator"], 3)

    def test_hash_and_prose_errors_are_repaired_but_do_not_complete_the_assembly(self):
        seen = {}
        def bad(session):
            result = wrong_hash(session)
            cell = result["frontier"]["cells"][0]
            cell.update(status="bounded", bound=data._bound(
                dependencies=result["frontier"]["partition_dependencies"],
                hypothesis_conditions=["Use all original phase charts"]))
            seen["frontier"] = copy.deepcopy(result["frontier"])
            return result
        def fix_table(session):
            table = frontier.Frontier.model_validate(seen["frontier"])
            table.partition_gaps += protocol.retained_hypotheses(table)
            table.cells[0].bound.hypothesis_conditions = []
            return table.model_dump()
        script = fake.Script(solver=[closure.local_a, closure.local_b], integrator=[bad, confirm, fix_table])
        work, summary = self.execute(script)
        record = summary["integrations"][0]
        self.assertTrue(record["status"].startswith("reviewed_"))
        self.assertEqual(record["assembly_status"], "cutoff_plan_unresolved")
        self.assertEqual(summary["latest_integration"], "")
        report = json.loads((work / record["frontier_report"]).read_text())
        self.assertEqual(report["analysis"]["cutoffs"]["status"], "unknown")
        self.assertTrue(any("Use all original phase charts" in g for g in report["frontier"]["partition_gaps"]))

    def test_frontier_premise_deletion_is_rejected_without_reviews_or_repeated_integration(self):
        seen = {}
        def bad(session):
            result = closure.composed(session)
            result["frontier"]["cells"][0].update(status="bounded", bound=data._bound(
                dependencies=result["frontier"]["partition_dependencies"],
                hypothesis_conditions=["Do not erase this premise"]))
            seen.update(copy.deepcopy(result["frontier"]))
            return result
        def erase(session):
            seen["cells"][0]["bound"]["hypothesis_conditions"] = []
            return seen
        script = fake.Script(solver=[closure.local_a, closure.local_b, None, None], integrator=[bad, erase])
        work, summary = self.execute(script, rounds=2)
        self.assertEqual(len(summary["integrations"]), 1)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "protocol_repair_failed")
        self.assertEqual(record["reviews"], [])
        self.assertEqual(script.role_calls["mender"], 0)
        attempt = json.loads((work / "frontier-repair-attempt-1.json").read_text())
        self.assertTrue(attempt["preservation_errors"])

    def test_non_table_integration_also_confirms_and_reaudits(self):
        def bad(session):
            result = optimized.composed(session)
            result["candidate"]["dependencies"][0]["sha256"] = "0" * 64
            return result
        script = fake.Script(solver=[closure.local_a, closure.local_b], integrator=[bad, confirm])
        _, summary = self.execute(script, coverage_planning=False)
        record = summary["integrations"][0]
        self.assertTrue(record["status"].startswith("reviewed_"))
        self.assertEqual(len(record["reviews"]), 2)
        self.assertIn("repaired_candidate_path", record)


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
