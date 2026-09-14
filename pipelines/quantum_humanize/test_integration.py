"""Real-flow integration controls with local deterministic fake agents only.

Baseline mathematical checks are mocked by the shared fixture. Every claim and
verdict below is synthetic; these tests establish no mathematical conclusion.
"""

import hashlib
import json
from pathlib import Path
import unittest
from unittest import mock

from pipelines.quantum_humanize import test_flow as fake


PROOF_PREFIX = "docs/proof-"


def proofs(session):
    manifest = json.loads((session.cwd / "_snapshot.json").read_text())
    return [entry for entry in manifest["files"] if entry["path"].startswith(PROOF_PREFIX)]


def local(session, **changes):
    values = {"scope": "sublemma", "claim": "Synthetic independently reviewed local claim"}
    values.update(changes)
    return fake.candidate(session, **values)


def combination(session, **changes):
    entries = proofs(session)
    if not entries:
        raise AssertionError("Integrator did not receive the actual accepted proof files")
    values = {
        "scope": "sublemma", "claim": "Synthetic combined claim",
        "argument": "Synthetic complete combination argument, not a mathematical result.",
        "dependencies": [dict(path=entry["path"], sha256=entry["sha256"], section="Full candidate")
                         for entry in entries],
        "remaining_obligations": ["Synthetic global obligation is still open"],
    }
    values.update(changes)
    return fake.candidate(session, **values)


class IntegrationTests(unittest.TestCase):
    # Reuse setup and the fake Agent interface without inheriting all FlowTests.
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped

    def execute(self, script=None, **changes):
        changes.setdefault("integrate", True)
        return fake.FlowTests.execute(self, script, **changes)

    def assert_proof_copies(self, session):
        entries = proofs(session)
        for entry in entries:
            data = (session.cwd / entry["path"]).read_bytes()
            sha = hashlib.sha256(data).hexdigest()
            self.assertEqual(entry["sha256"], sha)
            self.assertEqual(entry["bytes"], len(data))
            self.assertEqual(entry["path"], PROOF_PREFIX + sha + ".md")
        return entries

    def assert_no_integrated_proof(self, summary):
        self.assertFalse(summary["research_goal_proved"])
        self.assertEqual(summary["latest_integration"], "")
        self.assertFalse(any(record.get("proof_path") for record in summary["integrations"]))

    def test_full_arguments_cross_rounds_and_combination_receives_fresh_blind_dual_reviews(self):
        local_argument = "COMPLETE LOCAL ARGUMENT " * 180
        combined_argument = "COMPLETE INTEGRATED ARGUMENT " * 170
        private_review = "PRIVATE PREVIOUS REVIEW EXPLANATION"
        seen = {}

        def first_integration(session):
            entries = self.assert_proof_copies(session)
            self.assertEqual(len(entries), 1)
            body = (session.cwd / entries[0]["path"]).read_text()
            self.assertIn(local_argument, body)
            self.assertIn(fake.pipeline.COMMON_INPUTS[0], body)
            seen["local_path"] = entries[0]["path"]
            return combination(session, argument=combined_argument)

        def next_solver(session):
            entries = self.assert_proof_copies(session)
            self.assertEqual(len(entries), 2)
            integrated = next(entry for entry in entries
                              if combined_argument in (session.cwd / entry["path"]).read_text())
            seen["first_integration_path"] = integrated["path"]
            self.assertIn(integrated["path"], session.prompts[-1])
            self.assertIn(local_argument, (session.cwd / seen["local_path"]).read_text())
            return local(session, claim="Synthetic second-round local claim", dependencies=[{
                "path": integrated["path"], "sha256": integrated["sha256"], "section": "Full proof",
            }])

        def second_integration(session):
            self.assertEqual(len(self.assert_proof_copies(session)), 3)
            return combination(session, scope="selected_obligation",
                               argument="Synthetic final integrated full-obligation argument.",
                               remaining_obligations=[])

        script = fake.Script(
            solver=[lambda session: local(session, argument=local_argument), next_solver],
            integrator=[first_integration, second_integration],
            reviewer_a=[lambda session: fake.review(session, explanation=private_review)] * 4,
        )
        work, summary = self.execute(script, rounds=20)
        self.assertEqual(summary["status"], "reviewed_candidate_pending_manual_integration")
        self.assertFalse(summary["research_goal_proved"])
        self.assertEqual(script.role_calls, {"reader": 1, "solver": 2, "reviewer_a": 4,
                                             "reviewer_b": 4, "integrator": 2})
        self.assertEqual(script.max_active, 2)
        self.assertEqual(len(summary["integrations"]), 2)
        first, second = summary["integrations"]
        self.assertEqual(first["status"], "reviewed_sublemma_pending_manual_integration")
        self.assertEqual(second["status"], "reviewed_candidate_pending_manual_integration")
        self.assertEqual(first["proof_path"], seen["first_integration_path"])
        self.assertEqual(summary["latest_integration"], second["proof_path"])
        for number, record in enumerate((first, second), 1):
            self.assertEqual(json.loads((work / f"integration-{number}.json").read_text()), record)
            answer = json.loads((work / f"integration-candidate-{number}.json").read_text())
            self.assertEqual(fake.pipeline.digest(answer), record["sha256"])
            self.assertEqual([result["candidate_sha256"] for result in record["reviews"]],
                             [record["sha256"], record["sha256"]])
            reviewing = [call for call in script.calls if call.role.startswith("reviewer_")
                         and "Candidate SHA256: " + record["sha256"] in call.prompt]
            self.assertEqual(len(reviewing), 2)
            self.assertEqual({call.role for call in reviewing}, {"reviewer_a", "reviewer_b"})
            self.assertEqual(len({id(call.session) for call in reviewing}), 2)
        context = json.loads((work / "round-context-2.json").read_text())
        self.assertEqual(context["latest_integration"], first["proof_path"])
        for call in script.calls:
            if call.role.startswith("reviewer_"):
                self.assertNotIn(private_review, call.prompt)
                self.assertNotIn("coverage_ledger", call.prompt)
                self.assertNotIn(self.agents.integrator.name, call.prompt)
                self.assertNotIn(self.agents.solver.name, call.prompt)
            if call.role == "integrator":
                self.assertIs(call.schema, fake.pipeline.Candidate)
                schema = call.schema.model_json_schema()
                self.assertEqual(set(schema["required"]), set(schema["properties"]))
                self.assertIn("remaining_obligations", schema["required"])
        self.assertEqual(self.source_files(), self.before)
        self.assertFalse((self.repo / second["proof_path"]).exists())
        self.assert_stopped()

    def test_selected_single_draft_does_not_skip_integration_or_stop_on_combined_sublemma(self):
        script = fake.Script(solver=[fake.DEFAULT, None], integrator=[combination])
        work, summary = self.execute(script, rounds=2)
        self.assertEqual(script.role_calls["solver"], 2)
        self.assertEqual(script.role_calls["integrator"], 1)
        self.assertEqual(summary["status"], "round_limit_reached")
        self.assertEqual(summary["candidates"][0]["status"],
                         "reviewed_candidate_pending_manual_integration")
        self.assertEqual(summary["integrations"][0]["status"],
                         "reviewed_sublemma_pending_manual_integration")
        self.assertTrue((work / "round-2.json").is_file())
        self.assertFalse((work / "integration-2.json").exists())
        self.assertFalse(summary["research_goal_proved"])

    def test_rejected_combination_never_reaches_the_next_round_proof_library(self):
        marker = "REJECTED INTEGRATION BODY MUST NOT BECOME AN INPUT"
        cases = (
            ({}, None, "review_incomplete"),
            ({}, lambda session: fake.negative(session, "wrong"), "needs_repair"),
            ({}, lambda session: fake.review(session, candidate_sha256="0" * 64), "review_hash_mismatch"),
            ({}, lambda session: fake.review(session, dependencies_checked=False), "review_incomplete"),
            ({"evidence": "finite_algebra"}, fake.DEFAULT, "partial_or_finite_evidence_only"),
            ({"unproved_steps": ["A gap inside the combined claim"]}, fake.DEFAULT,
             "partial_or_finite_evidence_only"),
        )
        for changes, answer, status in cases:
            with self.subTest(status=status, changes=changes):
                def next_solver(session):
                    entries = self.assert_proof_copies(session)
                    self.assertEqual(len(entries), 1)
                    self.assertTrue(all(marker not in (session.cwd / entry["path"]).read_text()
                                        for entry in entries))
                    return None

                script = fake.Script(
                    solver=[local, next_solver],
                    integrator=[lambda session, changes=changes: combination(
                        session, argument=marker, **changes)],
                    reviewer_b=[fake.DEFAULT, answer],
                )
                work, summary = self.execute(script, rounds=2)
                self.assert_no_integrated_proof(summary)
                self.assertEqual(summary["integrations"][0]["status"], status)
                self.assertEqual(json.loads((work / "round-context-2.json").read_text())["latest_integration"], "")
                self.assertIn(marker, (work / "integration-candidate-1.json").read_text())
                self.assertEqual(script.role_calls["mender"], 0)
                self.assert_stopped()

    def test_invalid_combination_dependency_is_rejected_before_expensive_reviews(self):
        def invalid(session):
            result = combination(session)
            result["dependencies"][0]["sha256"] = "0" * 64
            return result

        script = fake.Script(solver=[local, None], integrator=[invalid])
        work, summary = self.execute(script, rounds=2)
        self.assert_no_integrated_proof(summary)
        self.assertEqual(summary["integrations"][0]["status"], "invalid_evidence")
        self.assertEqual(summary["integrations"][0]["reviews"], [])
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        self.assertTrue((work / "integration-candidate-1.json").is_file())

    def test_same_batch_future_proof_cannot_retroactively_validate_a_solver_dependency(self):
        captured = {}

        def first(session):
            return local(session, claim="The first draft will later enter the proof library")

        def future_dependency(session):
            # Predict the documented full-candidate serialization. The post-run
            # equality below proves this really is the later admitted file, not
            # merely an unrelated invented path with a conveniently wrong hash.
            data = ("# Proof candidate — untrusted, not formal certification\n\n```json\n"
                    + fake.pipeline.canonical(first(session)) + "\n```\n").encode("utf-8")
            sha = hashlib.sha256(data).hexdigest()
            captured["path"] = PROOF_PREFIX + sha + ".md"
            self.assertEqual(proofs(session), [])
            return local(session, claim="A second draft citing an unavailable peer proof", dependencies=[{
                "path": captured["path"], "sha256": sha, "section": "Predicted full candidate",
            }])

        script = fake.Script(solver=[first, future_dependency], integrator=[None])
        _, summary = self.execute(script, attempts=2)
        first_record, second_record = summary["candidates"]
        self.assertEqual(first_record["proof_path"], captured["path"])
        self.assertEqual(second_record["status"], "invalid_evidence")
        self.assertEqual(second_record["reviews"], [])
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        integrator_call = next(call for call in script.calls if call.role == "integrator")
        self.assertEqual([entry["path"] for entry in proofs(integrator_call.session)], [captured["path"]])

    def test_failed_later_combination_keeps_previous_integration_and_its_full_dependencies(self):
        accepted_marker = "ACCEPTED EARLIER COMBINATION WITH FULL DEPENDENCIES"
        rejected_marker = "REJECTED LATER COMBINATION MUST NOT REPLACE THE ACCEPTED ONE"
        seen = {}

        def third_solver(session):
            entries = self.assert_proof_copies(session)
            texts = {entry["path"]: (session.cwd / entry["path"]).read_text() for entry in entries}
            self.assertEqual(len(texts), 3)
            self.assertFalse(any(rejected_marker in value for value in texts.values()))
            prior = next(path for path, body in texts.items() if accepted_marker in body)
            seen["latest"] = prior
            self.assertIn(prior, session.prompts[-1])
            # The first local lemma remains available: the accepted integration
            # still cites it, even after another independently accepted local draft.
            self.assertTrue(any("First local dependency" in value for value in texts.values()))
            return None

        script = fake.Script(
            solver=[lambda session: local(session, claim="First local dependency"),
                    lambda session: local(session, claim="Second newly accepted local claim"), third_solver],
            integrator=[lambda session: combination(session, argument=accepted_marker),
                        lambda session: combination(session, argument=rejected_marker)],
            reviewer_b=[fake.DEFAULT, fake.DEFAULT, fake.DEFAULT,
                        lambda session: fake.negative(session, "wrong")],
        )
        work, summary = self.execute(script, rounds=3)
        self.assertEqual(len(summary["integrations"]), 2)
        first, second = summary["integrations"]
        self.assertTrue(first.get("proof_path"))
        self.assertFalse(second.get("proof_path"))
        self.assertEqual(summary["latest_integration"], first["proof_path"])
        self.assertEqual(seen["latest"], first["proof_path"])
        self.assertEqual(json.loads((work / "round-context-3.json").read_text())["latest_integration"],
                         first["proof_path"])
        self.assertFalse(summary["research_goal_proved"])

    def test_no_qualified_local_proof_means_no_integrator_call(self):
        for changes in ({"evidence": "finite_algebra"}, {"unproved_steps": ["Local gap"]},
                        {"obligation_id": "actual_kinetic"}):
            with self.subTest(changes=changes):
                script = fake.Script(solver=[lambda session, changes=changes: local(session, **changes)])
                work, summary = self.execute(script)
                self.assertEqual(script.role_calls["integrator"], 0)
                self.assertEqual(summary["integrations"], [])
                self.assertEqual(summary["latest_integration"], "")
                self.assertEqual(list(work.glob("integration-*.json")), [])

    def test_exact_repeated_draft_does_not_add_a_proof_or_rerun_integration(self):
        seen = []

        def repeated(session):
            seen.append(self.assert_proof_copies(session))
            return local(session)

        script = fake.Script(solver=[repeated, repeated], integrator=[combination])
        work, summary = self.execute(script, rounds=2)
        self.assertEqual(seen[0], [])
        self.assertEqual(len(seen[1]), 2)
        self.assertEqual(script.role_calls["integrator"], 1)
        self.assertEqual(len(summary["integrations"]), 1)
        self.assertEqual(summary["candidates"][0]["sha256"], summary["candidates"][1]["sha256"])
        self.assertFalse((work / "integration-2.json").exists())
        self.assertEqual(summary["latest_integration"], summary["integrations"][0]["proof_path"])

    def test_shared_call_budget_cannot_accept_an_unreviewed_or_single_reviewed_combination(self):
        for max_calls in (5, 6):
            with self.subTest(max_calls=max_calls):
                script = fake.Script(solver=[local], integrator=[combination])
                _, summary = self.execute(script, max_calls=max_calls)
                self.assertEqual(summary["status"], "call_budget_exhausted")
                self.assertEqual(summary["calls"], max_calls)
                self.assertEqual(len(script.calls), max_calls)
                self.assertEqual(script.role_calls["integrator"], 1)
                self.assert_no_integrated_proof(summary)
                self.assert_stopped()

    def test_integrator_output_counts_toward_the_same_soft_token_budget(self):
        script = fake.Script(solver=[local], integrator=[fake.Turn(combination, output=10)])
        _, summary = self.execute(script, output_token_budget=5)
        self.assertEqual(summary["status"], "output_budget_exhausted")
        self.assertEqual(summary["calls"], 5)
        self.assertEqual(summary["output_tokens_reported"], 14)
        self.assert_no_integrated_proof(summary)
        self.assert_stopped()

    def test_integrator_timeout_exhaustion_keeps_local_proof_and_cleans_every_worker(self):
        script = fake.Script(solver=[local], integrator=[fake.HANG, fake.HANG])
        _, summary = self.execute(script, integrator_timeout_seconds=0.2)
        self.assertEqual(summary["status"], "round_limit_reached")
        self.assertEqual(summary["calls"], 6)
        self.assertEqual(summary["timed_out_calls"], 2)
        self.assertEqual(summary["timeout_retry_calls"], 1)
        self.assertTrue(summary["candidates"][0].get("proof_path"))
        self.assert_no_integrated_proof(summary)
        calls = [call for call in script.calls if call.role == "integrator"]
        self.assertEqual(len(calls), 2)
        for call in calls:
            failure = json.loads((call.session.cwd.parent / "failure.json").read_text())
            self.assertEqual(failure["kind"], "turn_timeout")
            self.assertIn(call.session, script.cancelled)
        self.assert_stopped()

    def test_integrator_cleanup_failure_discards_its_answer_before_review(self):
        original_close, original_stop = fake.FakeSession.close, fake.FakeAgent.stop

        def failed_close(session):
            original_close(session)
            if session.agent.role == "integrator":
                raise RuntimeError("Synthetic integrator close failure")

        def failed_stop(agent):
            original_stop(agent)
            if agent.role == "integrator" and agent.parent is not None:
                raise RuntimeError("Synthetic integrator stop failure")

        for target, name, replacement in ((fake.FakeSession, "close", failed_close),
                                          (fake.FakeAgent, "stop", failed_stop)):
            with self.subTest(name=name), mock.patch.object(target, name, new=replacement):
                script = fake.Script(solver=[local], integrator=[combination])
                _, summary = self.execute(script)
                self.assertEqual(summary["status"], "cleanup_incomplete")
                self.assert_no_integrated_proof(summary)
                self.assertEqual(script.role_calls["reviewer_a"], 1)
                self.assertEqual(script.role_calls["reviewer_b"], 1)
                self.assert_stopped()

    def test_combination_reviewer_cleanup_failure_prevents_proof_admission(self):
        marker = "COMBINATION THAT MUST FAIL CLEANUP"
        original_close, original_stop = fake.FakeSession.close, fake.FakeAgent.stop

        def matches(agent):
            return (agent.role == "reviewer_b" and agent.parent is not None and agent.sessions
                    and marker in agent.sessions[0].prompts[-1])

        def failed_close(session):
            original_close(session)
            if matches(session.agent):
                raise RuntimeError("Synthetic integrated-review close failure")

        def failed_stop(agent):
            original_stop(agent)
            if matches(agent):
                raise RuntimeError("Synthetic integrated-review stop failure")

        for target, name, replacement in ((fake.FakeSession, "close", failed_close),
                                          (fake.FakeAgent, "stop", failed_stop)):
            with self.subTest(name=name), mock.patch.object(target, name, new=replacement):
                script = fake.Script(solver=[local], integrator=[lambda session: combination(
                    session, argument=marker)])
                _, summary = self.execute(script)
                self.assertEqual(summary["status"], "cleanup_incomplete")
                self.assert_no_integrated_proof(summary)
                self.assertEqual(script.role_calls["reviewer_a"], 2)
                self.assertEqual(script.role_calls["reviewer_b"], 2)
                self.assert_stopped()

    def test_proof_copy_tampering_is_detected_against_merged_manifest(self):
        captured = {}

        def tamper(session):
            entry = self.assert_proof_copies(session)[0]
            result = combination(session)
            target = session.cwd / entry["path"]
            captured.update(path=target, data=target.read_bytes(), name=Path(entry["path"]).name)
            target.write_bytes(b"Synthetic tampered accepted proof")
            return result

        with self.assertRaisesRegex(RuntimeError, "session input copy changed"):
            self.execute(fake.Script(solver=[local], integrator=[tamper]))
        self.assertEqual(self.source_files(), self.before)
        work = next(self.runs.glob("run-*"))
        summary = json.loads((work / "summary.json").read_text())
        self.assertEqual(summary["status"], "session_input_integrity_failure")
        self.assert_no_integrated_proof(summary)
        original_copies = [path for path in work.rglob(captured["name"]) if path != captured["path"]]
        self.assertTrue(original_copies)
        self.assertTrue(all(path.read_bytes() == captured["data"] for path in original_copies))
        self.assert_stopped()

    def test_integrator_cannot_share_the_solver_role_object(self):
        self.agents = self.agents._replace(integrator=self.agents.solver)
        with self.assertRaisesRegex(ValueError, "eight separate"):
            self.execute()
        self.assertEqual(self.script.calls, [])
        self.baseline.assert_not_called()

    def test_twenty_round_limit_is_executed_without_unrequested_integrator_calls(self):
        script = fake.Script(solver=[None] * 20)
        work, summary = self.execute(script, rounds=20)
        self.assertEqual(summary["status"], "round_limit_reached")
        self.assertEqual(script.role_calls, {"reader": 1, "solver": 20})
        self.assertEqual(summary["calls"], 21)
        self.assertEqual(summary["integrations"], [])
        self.assertTrue((work / "round-20.json").is_file())
        self.assertFalse((work / "round-21.json").exists())
        self.assert_stopped()


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
