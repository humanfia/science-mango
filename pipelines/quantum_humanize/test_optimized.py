"""Event-driven tests of optimized scheduling, with no model/backend calls.

The shared fixture mocks baseline checks. All claims, arguments, and reviews
are synthetic control-flow data, not mathematical evidence.
"""

import asyncio
import hashlib
import json
import unittest
from unittest import mock

from pipelines.quantum_humanize import test_flow as fake
from pipelines.quantum_humanize import test_integration as integration


def composed(session, *, next_tasks=(), **changes):
    return {"candidate": integration.combination(session, **changes),
            "next_tasks": list(next_tasks)}


def task(session, objective="SYNTHETIC NEXT TASK", **changes):
    dependency = fake.candidate(session)["dependencies"][0]
    result = {
        "obligation_id": "self_audit", "objective": objective,
        "success_criterion": "SYNTHETIC SUCCESS CRITERION: prove only the stated local claim",
        "dependencies": [dependency],
    }
    result.update(changes)
    return result


class OptimizedTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped
    assert_proof_copies = integration.IntegrationTests.assert_proof_copies

    def execute(self, script=None, **changes):
        changes.setdefault("optimize", True)
        return fake.FlowTests.execute(self, script, **changes)

    def reviewing(self, script, sha):
        return [call for call in script.calls if call.role.startswith("reviewer_")
                and "Candidate SHA256: " + sha + "\n" in call.prompt]

    def assert_fresh_pair(self, script, sha):
        calls = self.reviewing(script, sha)
        self.assertEqual({call.role for call in calls}, {"reviewer_a", "reviewer_b"})
        self.assertEqual(len(calls), 2)
        self.assertEqual(len({id(call.session) for call in calls}), 2)

    def seed_candidate(self, **changes):
        name = fake.pipeline.COMMON_INPUTS[0]
        result = {
            "obligation_id": "self_audit", "scope": "sublemma", "evidence": "analytic_draft",
            "claim": "Synthetic restarted draft, not an accepted proof",
            "argument": "OLD FAILED DRAFT FROM AN EXPLICIT REPAIR FILE",
            "dependencies": [{"path": name, "section": "Fixture",
                              "sha256": hashlib.sha256((self.repo / name).read_bytes()).hexdigest()}],
            "unproved_steps": ["Old internal gap"], "remaining_obligations": [],
        }
        result.update(changes)
        return result

    def test_both_early_reviews_can_finish_before_the_late_solver_returns(self):
        reviewed = asyncio.Event()
        events = []
        early_reviews = []

        async def late(session):
            events.append("late started")
            # A batch barrier deadlocks this dependency; no timing comparison is
            # used to assert success. wait_for only bounds a broken test.
            await asyncio.wait_for(reviewed.wait(), 5)
            events.append("late returned")
            return integration.local(session, claim="LATE CLAIM")

        def audit(session):
            if "EARLY CLAIM" in session.prompts[-1]:
                early_reviews.append(session.agent.role)
                events.append(session.agent.role + " reviewed early")
                if len(early_reviews) == 2:
                    reviewed.set()
            return fake.review(session)

        script = fake.Script(
            solver=[lambda session: integration.local(session, claim="EARLY CLAIM"), late],
            reviewer_a=[audit, audit], reviewer_b=[audit, audit],
        )
        _, summary = self.execute(script, attempts=2, parallelism=2)
        self.assertEqual(len(early_reviews), 2)
        self.assertLess(events.index("reviewer_a reviewed early"), events.index("late returned"))
        self.assertLess(events.index("reviewer_b reviewed early"), events.index("late returned"))
        self.assertEqual(script.max_active, 2)
        self.assertEqual(len(summary["candidates"]), 2)
        self.assertTrue(all(record["status"].startswith("reviewed_")
                            for record in summary["candidates"]))
        self.assert_stopped()

    def test_declared_internal_gap_goes_to_mender_before_any_reviewer(self):
        seen = {}

        def original(session):
            answer = integration.local(session, claim="ORIGINAL WITH INTERNAL GAP",
                                       unproved_steps=["SYNTHETIC INTERNAL GAP"])
            seen["original"] = fake.pipeline.digest(answer)
            return answer

        def mend(session):
            self.assertFalse(any(call.role.startswith("reviewer_") for call in self.script.calls))
            self.assertIn("SYNTHETIC INTERNAL GAP", session.prompts[-1])
            answer = integration.local(session, claim="REPAIRED CLAIM", argument="Complete new draft")
            seen["repair"] = fake.pipeline.digest(answer)
            return answer

        script = fake.Script(solver=[original], mender=[mend])
        _, summary = self.execute(script)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assertEqual(self.reviewing(script, seen["original"]), [])
        self.assert_fresh_pair(script, seen["repair"])
        self.assertNotEqual(seen["original"], seen["repair"])
        self.assertTrue(any(record["sha256"] == seen["repair"]
                            and record["status"].startswith("reviewed_")
                            for record in summary["candidates"]))
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_only_one_immediate_repair_and_pending_repairs_replace_next_solver_slots(self):
        turns = [lambda session, index=index: integration.local(
            session, claim=f"Distinct rejected original {index}") for index in range(8)]
        script = fake.Script(
            solver=turns, mender=[None] * 9,
            reviewer_a=[fake.negative] * 8, reviewer_b=[fake.negative] * 8,
        )
        _, summary = self.execute(script, attempts=8, parallelism=8, rounds=2)
        self.assertEqual(script.role_calls["solver"], 8)
        self.assertEqual(script.role_calls["mender"], 9)
        self.assertEqual(script.role_calls["reviewer_a"], 8)
        self.assertEqual(script.role_calls["reviewer_b"], 8)
        self.assertLessEqual(script.max_active, 8)
        self.assertFalse(any(record["status"].startswith("reviewed_")
                             for record in summary["candidates"]))
        attempts = [sum(f"Distinct rejected original {index}" in call.prompt
                        for call in script.calls if call.role == "mender") for index in range(8)]
        self.assertEqual(sorted(attempts), [1] * 7 + [2])
        self.assert_stopped()

    def test_a_still_incomplete_revision_is_not_recursively_repaired_in_the_same_round(self):
        script = fake.Script(
            solver=[lambda session: integration.local(session, unproved_steps=["Original gap"])],
            mender=[lambda session: integration.local(session, claim="Still incomplete repair",
                                                       unproved_steps=["Remaining internal gap"])],
        )
        _, summary = self.execute(script)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 0)
        self.assertEqual(script.role_calls["reviewer_b"], 0)
        self.assertFalse(any(record["status"].startswith("reviewed_")
                             for record in summary["candidates"]))
        self.assert_stopped()

    def test_exact_duplicates_get_no_new_reviews_or_success_records(self):
        script = fake.Script(solver=[integration.local] * 4)
        _, summary = self.execute(script, attempts=2, rounds=2)
        self.assertEqual(script.role_calls["solver"], 4)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        records = summary["candidates"]
        self.assertEqual(len(records), 4)
        self.assertEqual(sum(record["status"].startswith("reviewed_") for record in records), 1)
        duplicates = [record for record in records if "duplicate" in record["status"]]
        self.assertEqual(len(duplicates), 3)
        self.assertTrue(all(not record.get("reviews") and not record.get("proof_path")
                            for record in duplicates))
        self.assert_stopped()

    def test_an_identical_failed_revision_is_not_reviewed_again_or_promoted(self):
        script = fake.Script(solver=[integration.local, None], mender=[integration.local],
                             reviewer_a=[fake.negative], reviewer_b=[fake.negative])
        _, summary = self.execute(script, rounds=2)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        self.assertFalse(any(record["status"].startswith("reviewed_")
                             for record in summary["candidates"]))
        self.assert_stopped()

    def test_a_solver_repeating_a_prior_definite_failure_gets_no_new_reviews(self):
        script = fake.Script(
            solver=[integration.local, None, integration.local], mender=[None, None],
            reviewer_a=[fake.negative],
        )
        _, summary = self.execute(script, attempts=2, rounds=2)
        self.assertEqual(script.role_calls["solver"], 3)
        self.assertEqual(script.role_calls["mender"], 2)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        duplicates = [record for record in summary["candidates"]
                      if record["status"] == "duplicate_candidate"]
        self.assertEqual(len(duplicates), 1)
        self.assertEqual(duplicates[0]["round"], 2)
        self.assertEqual(duplicates[0]["reviews"], [])
        self.assertNotIn("proof_path", duplicates[0])
        self.assertFalse(any(record["status"].startswith("reviewed_")
                             for record in summary["candidates"]))
        self.assert_stopped()

    def test_invalid_future_dependency_can_be_retried_after_it_becomes_an_actual_input(self):
        availability = []
        seen = {}

        def first(session):
            return integration.local(session, claim="First admitted local draft for next-round use")

        def future(session):
            data = ("# Proof candidate — untrusted, not formal certification\n\n```json\n"
                    + fake.pipeline.canonical(first(session)) + "\n```\n").encode()
            sha = hashlib.sha256(data).hexdigest()
            path = integration.PROOF_PREFIX + sha + ".md"
            availability.append(any(entry["path"] == path for entry in integration.proofs(session)))
            answer = integration.local(session, claim="Retry exactly when the dependency is available",
                                       dependencies=[{"path": path, "sha256": sha, "section": "Full proof"}])
            seen["sha"] = fake.pipeline.digest(answer)
            seen["path"] = path
            return answer

        script = fake.Script(solver=[first, future, future, None], integrator=[None, None])
        _, summary = self.execute(script, attempts=2, rounds=2, integrate=True)
        self.assertEqual(availability, [False, True])
        records = [record for record in summary["candidates"] if record["sha256"] == seen["sha"]]
        self.assertEqual([record["round"] for record in records], [1, 2])
        self.assertEqual(records[0]["status"], "invalid_evidence")
        self.assertEqual(records[0]["reviews"], [])
        self.assertTrue(records[1]["status"].startswith("reviewed_"))
        self.assertTrue(records[1]["proof_path"])
        self.assertEqual(summary["candidates"][0]["proof_path"], seen["path"])
        self.assert_fresh_pair(script, seen["sha"])
        self.assertEqual(script.role_calls["reviewer_a"], 2)
        self.assertEqual(script.role_calls["reviewer_b"], 2)
        self.assert_stopped()

    def test_early_reviews_do_not_admit_a_future_proof_into_late_solver_inputs(self):
        reviewed = asyncio.Event()
        count = []
        seen = {}

        def early(session):
            return integration.local(session, claim="Early proof is not available until batch admission")

        def audit(session):
            count.append(session.agent.role)
            if len(count) == 2:
                reviewed.set()
            return fake.review(session)

        async def late(session):
            await asyncio.wait_for(reviewed.wait(), 5)
            self.assertEqual(integration.proofs(session), [])
            data = ("# Proof candidate — untrusted, not formal certification\n\n```json\n"
                    + fake.pipeline.canonical(early(session)) + "\n```\n").encode()
            sha = hashlib.sha256(data).hexdigest()
            seen["path"] = integration.PROOF_PREFIX + sha + ".md"
            return integration.local(session, claim="Forbidden same-batch future citation", dependencies=[{
                "path": seen["path"], "sha256": sha, "section": "Not yet available",
            }])

        script = fake.Script(solver=[early, late], reviewer_a=[audit], reviewer_b=[audit],
                             integrator=[None])
        _, summary = self.execute(script, attempts=2, parallelism=2, integrate=True)
        self.assertEqual(len(count), 2)
        accepted = [record for record in summary["candidates"] if record.get("proof_path")]
        rejected = [record for record in summary["candidates"] if record["status"] == "invalid_evidence"]
        self.assertEqual([record["proof_path"] for record in accepted], [seen["path"]])
        self.assertEqual(len(rejected), 1)
        self.assertEqual(rejected[0]["reviews"], [])
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        self.assert_stopped()

    def test_late_cleanup_failure_blocks_admission_of_already_reviewed_early_draft(self):
        reviewed = asyncio.Event()
        count = []

        def audit(session):
            count.append(session.agent.role)
            if len(count) == 2:
                reviewed.set()
            return fake.review(session)

        async def late(session):
            session.fail_stop = True
            await asyncio.wait_for(reviewed.wait(), 5)
            return None

        original_stop = fake.FakeAgent.stop

        def broken_stop(agent):
            original_stop(agent)
            if any(getattr(session, "fail_stop", False) for session in agent.sessions):
                raise RuntimeError("Synthetic late cleanup failure")

        script = fake.Script(solver=[integration.local, late], reviewer_a=[audit], reviewer_b=[audit])
        with mock.patch.object(fake.FakeAgent, "stop", broken_stop):
            work, summary = self.execute(script, attempts=2, integrate=True)
        self.assertEqual(len(count), 2)
        self.assertEqual(summary["status"], "cleanup_incomplete")
        self.assertTrue(summary["cleanup_errors"])
        self.assertFalse(any(record["status"].startswith("reviewed_") or record.get("proof_path")
                             for record in summary["candidates"]))
        self.assertEqual(script.role_calls["integrator"], 0)
        self.assertEqual(list((work / "proofs").glob("*.md")), [])
        self.assert_stopped()

    def test_immediate_repair_and_reviews_obey_the_same_call_and_token_limits(self):
        for settings in ({"max_calls": 3}, {"output_token_budget": 3}):
            with self.subTest(settings=settings):
                script = fake.Script(
                    solver=[lambda session: integration.local(session, unproved_steps=["Repair first"])],
                    mender=[integration.local],
                )
                _, summary = self.execute(script, parallelism=1, **settings)
                self.assertEqual(script.role_calls["reader"], 1)
                self.assertEqual(script.role_calls["solver"], 1)
                self.assertEqual(script.role_calls["mender"], 1)
                self.assertEqual(script.role_calls["reviewer_a"], 0)
                self.assertEqual(script.role_calls["reviewer_b"], 0)
                self.assertEqual(summary["calls"], 3)
                self.assertIn("budget", summary["status"])
                self.assertFalse(any(record.get("proof_path") for record in summary["candidates"]))
                self.assert_stopped()

    def test_hanging_immediate_mender_is_retained_without_halting_the_run(self):
        script = fake.Script(
            solver=[lambda session: integration.local(session, unproved_steps=["Repair first"])],
            mender=[fake.HANG, fake.HANG],
        )
        _, summary = self.execute(script, turn_timeout_seconds=0.3)
        self.assertEqual(summary["status"], "round_limit_reached")
        self.assertEqual(script.role_calls["mender"], 2)
        self.assertEqual(len(script.cancelled), 2)
        self.assertTrue(all(session.agent.role == "mender" for session in script.cancelled))
        self.assertEqual(summary["timed_out_calls"], 2)
        self.assertEqual(summary["timeout_retry_calls"], 1)
        self.assert_stopped()

    def test_simultaneous_declared_gaps_reserve_only_one_immediate_repair_slot(self):
        script = fake.Script(
            solver=[lambda session, index=index: integration.local(
                session, claim=f"Declared-gap draft {index}", unproved_steps=[f"Gap {index}"])
                    for index in range(8)],
            mender=[None],
        )
        _, summary = self.execute(script, attempts=8, parallelism=8)
        self.assertEqual(script.role_calls["solver"], 8)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 0)
        self.assertEqual(script.role_calls["reviewer_b"], 0)
        self.assertLessEqual(script.max_active, 8)
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_validated_integration_tasks_are_assigned_with_real_dependencies_next_round(self):
        objective = "DYNAMIC VERIFIED TASK: extend only the uncovered acoustic patch"
        bad_obligation = "REJECT THIS OTHER OBLIGATION TASK"
        bad_hash = "REJECT THIS UNAVAILABLE DEPENDENCY TASK"
        seen = {}

        def integrate(session):
            entry = self.assert_proof_copies(session)[0]
            dependency = {"path": entry["path"], "sha256": entry["sha256"], "section": "Full proof"}
            good = task(session, objective, dependencies=[dependency])
            seen["task"] = good
            return composed(session, next_tasks=[
                good, good,
                task(session, bad_obligation, obligation_id="r3_b_remaining"),
                task(session, bad_hash, dependencies=[dict(dependency, sha256="0" * 64)]),
            ])

        def next_solver(session):
            self.assertIn(objective, session.prompts[-1])
            self.assertIn(seen["task"]["success_criterion"], session.prompts[-1])
            dependency = seen["task"]["dependencies"][0]
            entries = self.assert_proof_copies(session)
            self.assertTrue(any(entry["path"] == dependency["path"]
                                and entry["sha256"] == dependency["sha256"] for entry in entries))
            self.assertIn(dependency["path"], session.prompts[-1])
            self.assertIn(dependency["sha256"], session.prompts[-1])
            return None

        script = fake.Script(solver=[integration.local, None, next_solver, None], integrator=[integrate])
        work, summary = self.execute(script, attempts=2, rounds=2, integrate=True)
        self.assertEqual(script.role_calls["solver"], 4)
        record = summary["integrations"][0]
        self.assertTrue(record["status"].startswith("reviewed_"))
        self.assertEqual(record["next_tasks"], [seen["task"]])
        self.assertTrue(record["task_errors"])
        self.assert_fresh_pair(script, record["sha256"])
        self.assertEqual(json.loads((work / "round-context-2.json").read_text())["next_tasks"],
                         [seen["task"]])
        for call in script.calls:
            if call.role == "integrator":
                self.assertIs(call.schema, fake.pipeline.Integration)
            if call.role in ("solver", "reviewer_a", "reviewer_b"):
                self.assertNotIn(bad_obligation, call.prompt)
                self.assertNotIn(bad_hash, call.prompt)
            if call.role.startswith("reviewer_"):
                self.assertNotIn(objective, call.prompt)
        self.assertEqual(self.source_files(), self.before)
        self.assert_stopped()

    def test_failed_integration_is_only_an_untrusted_mender_job_not_a_solver_task_or_proof(self):
        rejected = "FAILED COMPOSITION FULL ARGUMENT"
        private_fault = "PRIVATE NEGATIVE INTEGRATION REVIEW FOR MENDER ONLY"
        rejected_task = "TASK FROM FAILED INTEGRATION MUST NOT BE ASSIGNED"
        repaired = "NEW REPAIRED COMPOSITION ARGUMENT"
        seen = {}

        def integrate(session):
            return composed(session, argument=rejected,
                            next_tasks=[task(session, rejected_task)])

        def reject(session):
            return fake.review(session, verdict="gap", first_fault="Synthetic gluing gap",
                               explanation=private_fault, repair="Rebuild the full composition")

        def mend(session):
            self.assertIn(rejected, session.prompts[-1])
            self.assertIn(private_fault, session.prompts[-1])
            self.assertIn("untrusted", session.prompts[-1].lower())
            entries = self.assert_proof_copies(session)
            self.assertEqual(len(entries), 1)
            self.assertTrue(all(rejected not in (session.cwd / entry["path"]).read_text()
                                for entry in entries))
            result = integration.local(session, claim="Repaired local composition", argument=repaired)
            seen["repair_sha"] = fake.pipeline.digest(result)
            return result

        script = fake.Script(solver=[integration.local], integrator=[integrate, None], mender=[mend],
                             reviewer_b=[fake.DEFAULT, reject, fake.DEFAULT])
        work, summary = self.execute(script, rounds=2, integrate=True)
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assertEqual(script.role_calls["integrator"], 2)
        self.assertEqual(summary["latest_integration"], "")
        self.assertFalse(any(record.get("proof_path") for record in summary["integrations"]))
        self.assert_fresh_pair(script, seen["repair_sha"])
        context = json.loads((work / "round-context-2.json").read_text())
        self.assertEqual(context["next_tasks"], [])
        self.assertNotIn(rejected, json.dumps(context))
        self.assertNotIn(private_fault, json.dumps(context))
        pending = (work / "pending-repairs-1.json").read_text()
        self.assertIn(rejected, pending)
        self.assertIn(private_fault, pending)
        self.assertEqual([job["kind"] for job in json.loads(pending)], ["integration"])
        final_inputs = [call for call in script.calls if call.role == "integrator"][-1].session
        bodies = [(final_inputs.cwd / entry["path"]).read_text()
                  for entry in self.assert_proof_copies(final_inputs)]
        self.assertTrue(any(repaired in body for body in bodies))
        self.assertFalse(any(rejected in body for body in bodies))
        for call in script.calls:
            if call.role != "mender":
                self.assertNotIn(private_fault, call.prompt)
                self.assertNotIn(rejected_task, call.prompt)
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_selected_single_candidate_still_requires_a_separate_composition_and_dual_review(self):
        script = fake.Script(solver=[fake.DEFAULT], integrator=[lambda session: composed(
            session, scope="selected_obligation", remaining_obligations=[])])
        _, summary = self.execute(script, rounds=20, integrate=True)
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(script.role_calls["integrator"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 2)
        self.assertEqual(script.role_calls["reviewer_b"], 2)
        self.assertEqual(summary["status"], "reviewed_candidate_pending_manual_integration")
        record = summary["integrations"][0]
        self.assert_fresh_pair(script, record["sha256"])
        self.assertEqual(summary["latest_integration"], record["proof_path"])
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_invalid_composition_dependency_is_not_reviewed_or_imported(self):
        def invalid(session):
            result = composed(session)
            result["candidate"]["dependencies"][0]["sha256"] = "0" * 64
            return result

        script = fake.Script(solver=[integration.local], integrator=[invalid])
        _, summary = self.execute(script, integrate=True)
        record = summary["integrations"][0]
        self.assertEqual(record["status"], "invalid_evidence")
        self.assertEqual(record["reviews"], [])
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        self.assertNotIn("proof_path", record)
        self.assertEqual(summary["latest_integration"], "")
        self.assert_stopped()

    def test_integration_reviews_cannot_exceed_the_shared_call_budget(self):
        script = fake.Script(solver=[integration.local], integrator=[composed])
        _, summary = self.execute(script, integrate=True, max_calls=5)
        self.assertEqual(summary["calls"], 5)
        self.assertEqual(script.role_calls["integrator"], 1)
        self.assertEqual(script.role_calls["reviewer_a"], 1)
        self.assertEqual(script.role_calls["reviewer_b"], 1)
        self.assertEqual(summary["latest_integration"], "")
        self.assertFalse(any(record.get("proof_path") for record in summary["integrations"]))
        self.assert_stopped()

    def test_explicit_restart_repair_is_hashed_and_supplied_only_to_a_mender(self):
        original = self.seed_candidate()
        private_fault = "PRIVATE RESTART FEEDBACK MUST STAY WITH THE MENDER"
        path = self.runs / "explicit-repair-input.json"
        data = json.dumps([{"candidate": original, "fault": private_fault, "kind": "integration"}]).encode()
        path.write_bytes(data)
        seen = {}

        def mend(session):
            self.assertIn(original["argument"], session.prompts[-1])
            self.assertIn(private_fault, session.prompts[-1])
            self.assertEqual(integration.proofs(session), [])
            self.assertFalse(any(item.name == path.name for item in session.cwd.rglob("*")))
            answer = integration.local(session, claim="New repair of explicit restart draft")
            seen["sha"] = fake.pipeline.digest(answer)
            return answer

        script = fake.Script(solver=[None], mender=[mend], integrator=[None])
        work, summary = self.execute(script, attempts=2, integrate=True,
                                     repair_inputs=[str(path.relative_to(self.repo))])
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(script.role_calls["mender"], 1)
        self.assert_fresh_pair(script, seen["sha"])
        audit = json.loads((work / "restart-repairs.json").read_text())
        self.assertIs(audit["trusted_proofs"], False)
        self.assertEqual(audit["jobs"], 1)
        self.assertEqual(audit["inputs"], [{"path": str(path.relative_to(self.repo)),
                                           "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}])
        for call in script.calls:
            if call.role != "mender":
                self.assertNotIn(private_fault, call.prompt)
                self.assertNotIn(original["argument"], call.prompt)
            self.assertFalse(any(entry["path"].endswith(path.name)
                                 for entry in json.loads((call.session.cwd / "_snapshot.json").read_text())["files"]))
        self.assertEqual(path.read_bytes(), data)
        self.assertEqual(self.source_files(), self.before)
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_unsafe_restart_path_or_invalid_dependencies_fail_before_any_agent_call(self):
        for invalid_dependencies in (False, True):
            with self.subTest(invalid_dependencies=invalid_dependencies):
                original = self.seed_candidate()
                if invalid_dependencies:
                    original["dependencies"][0]["sha256"] = "0" * 64
                    path = self.runs / "bad-restart-evidence.json"
                else:
                    path = self.repo.parent / "outside-run-area.json"
                path.write_text(json.dumps([{"candidate": original, "fault": "Synthetic fault",
                                             "kind": "integration"}]))
                script = fake.Script()
                with self.assertRaises(ValueError):
                    self.execute(script, repair_inputs=[str(path)])
                self.assertEqual(script.calls, [])
                self.assertEqual(script.workers, [])
                self.assert_stopped()

    def test_interrupted_initial_restart_repair_preserves_the_original_job_and_stops_workers(self):
        for stage in ("mender", "new_review"):
            with self.subTest(stage=stage):
                original = self.seed_candidate()
                fault = "Restart fault that must survive interruption"
                seed = {"candidate": original, "fault": fault, "kind": "integration"}
                path = self.runs / f"interrupt-restart-{stage}.json"
                path.write_text(json.dumps([seed]))
                exception = RuntimeError if stage == "mender" else asyncio.CancelledError
                script = fake.Script(
                    mender=[exception("Synthetic interruption") if stage == "mender" else
                            lambda session: integration.local(session, claim="Unfinished new revision")],
                    reviewer_a=[exception("Synthetic interruption")] if stage == "new_review" else [],
                )
                previous = set(self.runs.glob("run-*"))
                with self.assertRaises(exception):
                    self.execute(script, integrate=True, repair_inputs=[str(path)])
                created = set(self.runs.glob("run-*")) - previous
                self.assertEqual(len(created), 1)
                work = created.pop()
                pending = json.loads((work / "pending-repairs-final.json").read_text())
                self.assertEqual(pending, [seed])
                self.assertEqual(script.role_calls["solver"], 0)
                self.assertEqual(script.role_calls["mender"], 1)
                self.assertEqual(script.role_calls["integrator"], 0)
                if stage == "new_review":
                    self.assertEqual(script.role_calls["reviewer_a"], 1)
                    self.assertEqual(script.role_calls["reviewer_b"], 1)
                summary = json.loads((work / "summary.json").read_text())
                self.assertEqual(summary["status"], "interrupted_or_failed")
                self.assertFalse(summary["research_goal_proved"])
                self.assertFalse(any(record["status"].startswith("reviewed_")
                                     for record in summary["candidates"]))
                self.assertEqual(list((work / "proofs").glob("*.md")), [])
                self.assertEqual(list(work.glob("candidate-[0-9]*.json")), [])
                self.assert_stopped()

    def test_interrupted_immediate_repair_preserves_original_not_partial_new_reviews(self):
        for stage in ("mender", "new_review"):
            with self.subTest(stage=stage):
                seen = {}

                def original(session):
                    answer = integration.local(session, claim="Original immediate-repair draft",
                                               unproved_steps=["Internal gap before interruption"])
                    seen["original"] = answer
                    return answer

                exception = RuntimeError if stage == "mender" else asyncio.CancelledError
                script = fake.Script(
                    solver=[original],
                    mender=[exception("Synthetic interruption") if stage == "mender" else
                            lambda session: integration.local(session, claim="Partially audited new repair")],
                    reviewer_a=[exception("Synthetic interruption")] if stage == "new_review" else [],
                )
                previous = set(self.runs.glob("run-*"))
                with self.assertRaises(exception):
                    self.execute(script, integrate=True)
                created = set(self.runs.glob("run-*")) - previous
                self.assertEqual(len(created), 1)
                work = created.pop()
                pending = json.loads((work / "pending-repairs-final.json").read_text())
                self.assertEqual(len(pending), 1)
                self.assertEqual(pending[0]["candidate"], seen["original"])
                self.assertEqual(pending[0]["kind"], "candidate")
                self.assertIn("Internal gap before interruption", pending[0]["fault"])
                self.assertNotIn("reviews", pending[0])
                self.assertEqual(script.role_calls["mender"], 1)
                self.assertEqual(script.role_calls["integrator"], 0)
                if stage == "new_review":
                    self.assertEqual(script.role_calls["reviewer_a"], 1)
                    self.assertEqual(script.role_calls["reviewer_b"], 1)
                summary = json.loads((work / "summary.json").read_text())
                self.assertEqual(summary["status"], "interrupted_or_failed")
                self.assertFalse(summary["research_goal_proved"])
                self.assertFalse(any(record["status"].startswith("reviewed_")
                                     for record in summary["candidates"]))
                self.assertEqual(list((work / "proofs").glob("*.md")), [])
                self.assertEqual(list(work.glob("candidate-[0-9]*.json")), [])
                self.assert_stopped()

    def test_optimized_native_schemas_require_every_nested_property(self):
        for shape in (fake.pipeline.Integration, fake.pipeline.NextTask):
            with self.subTest(shape=shape.__name__):
                stack = [shape.model_json_schema()]
                while stack:
                    node = stack.pop()
                    if isinstance(node, dict):
                        if node.get("type") == "object":
                            self.assertEqual(set(node["required"]), set(node["properties"]))
                            self.assertIs(node["additionalProperties"], False)
                        stack.extend(node.values())
                    elif isinstance(node, list):
                        stack.extend(node)


if __name__ == "__main__":
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
