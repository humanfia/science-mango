"""Bounded deadline/retry controls, using local fake sessions and no backend.

Baseline mathematics is mocked. Most timeout paths are injected deterministically;
the real-deadline case asserts cancellation/cleanup, never elapsed-time thresholds.
"""

import asyncio
import json
from types import SimpleNamespace
import unittest
from unittest import mock

from pipelines.quantum_humanize import test_flow as fake
from pipelines.quantum_humanize import test_integration as integration
from pipelines.quantum_humanize import test_optimized as optimized


def expire(session):
    raise TimeoutError("Synthetic deadline: private backend diagnostic must not be copied")


class TimeoutTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped
    execute = fake.FlowTests.execute

    def test_retry_configuration_defaults_and_bounds(self):
        config = fake.pipeline.Config()
        self.assertEqual(config.turn_timeout_seconds, 1800)
        self.assertEqual(config.integrator_timeout_seconds, 1800)
        self.assertEqual(config.timeout_retries, 1)
        for retries in (0, 1, 2):
            fake.pipeline.Config(timeout_retries=retries)
        for changes in ({"timeout_retries": -1}, {"timeout_retries": 3},
                        {"integrator_timeout_seconds": 0}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                fake.pipeline.Config(**changes)

    def test_default_ordinary_deadline_is_recorded_for_both_reviewers(self):
        work, _ = self.execute(fake.Script())
        reviewers = [call for call in self.script.calls
                     if call.role in {"reviewer_a", "reviewer_b"}]
        self.assertEqual({call.role for call in reviewers}, {"reviewer_a", "reviewer_b"})
        for call in reviewers:
            for name in ("request.json", "activity.json"):
                record = json.loads((call.session.cwd.parent / name).read_text())
                self.assertEqual(record["timeout_seconds"], 1800)
        self.assert_stopped()

    def test_timeout_retries_in_a_fresh_cleaned_session_with_identical_prompt_schema_and_inputs(self):
        def recovered(session):
            prior = [call for call in self.script.calls if call.role == "solver"][0]
            self.assertIsNot(prior.session, session)
            self.assertIsNot(prior.session.agent, session.agent)
            self.assertNotEqual(prior.session.cwd, session.cwd)
            self.assertTrue(prior.session.closed)
            self.assertGreater(prior.session.agent.stops, 0)
            self.assertTrue(all(agent.stops == 0 for agent in self.agents))
            self.assertEqual(prior.prompt, session.prompts[-1])
            self.assertEqual((prior.session.cwd / "_snapshot.json").read_bytes(),
                             (session.cwd / "_snapshot.json").read_bytes())
            return fake.candidate(session)

        script = fake.Script(solver=[expire, recovered])
        work, summary = self.execute(script, timeout_retries=1)
        solvers = [call for call in script.calls if call.role == "solver"]
        self.assertEqual(len(solvers), 2)
        self.assertIs(solvers[0].schema, solvers[1].schema)
        self.assertEqual(summary["calls"], 5)
        self.assertEqual(summary["timed_out_calls"], 1)
        self.assertEqual(summary["timeout_retry_calls"], 1)
        self.assertEqual(summary["status"], "reviewed_candidate_pending_manual_integration")
        failures = [json.loads(path.read_text()) for path in work.glob("call-*/failure.json")]
        self.assertEqual([value["kind"] for value in failures], ["turn_timeout"])
        self.assertIsNone(json.loads((solvers[0].session.cwd.parent / "response.json").read_text()))
        self.assertIsNotNone(json.loads((solvers[1].session.cwd.parent / "response.json").read_text()))
        requests = [json.loads((call.session.cwd.parent / "request.json").read_text()) for call in solvers]
        self.assertEqual([request["retry_index"] for request in requests], [0, 1])
        self.assertEqual(requests[0]["retry_of"], "")
        self.assertEqual(requests[1]["retry_of"], solvers[0].session.cwd.parent.name)
        activities = [json.loads((call.session.cwd.parent / "activity.json").read_text()) for call in solvers]
        self.assertEqual([value["status"] for value in activities], ["turn_timeout", "completed"])
        self.assertEqual(self.source_files(), self.before)
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_exhausting_one_lane_does_not_globally_stop_a_peer_or_exceed_parallelism(self):
        second_timeout = asyncio.Event()
        expirations = []

        def fail_lane(session):
            expirations.append(session)
            if len(expirations) == 2:
                second_timeout.set()
            return expire(session)

        async def peer(session):
            await asyncio.wait_for(second_timeout.wait(), 3)
            self.assertTrue(all(agent.stops == 0 for agent in self.agents))
            return fake.candidate(session, claim="The independent peer completes normally")

        script = fake.Script(solver=[fail_lane, peer, fail_lane])
        _, summary = self.execute(script, attempts=2, parallelism=2,
                                  timeout_retries=1, turn_timeout_seconds=10)
        self.assertEqual(len(expirations), 2)
        self.assertEqual(script.role_calls["solver"], 3)
        self.assertEqual(script.max_active, 2)
        self.assertEqual(summary["status"], "reviewed_candidate_pending_manual_integration")
        self.assertEqual(len(summary["candidates"]), 1)
        self.assertEqual(summary["calls"], 6)
        self.assert_stopped()

    def test_timeout_retry_limit_is_exact_and_exhaustion_returns_a_local_failure(self):
        for retries in (0, 1, 2):
            with self.subTest(retries=retries):
                script = fake.Script(solver=[expire] * (retries + 1))
                work, summary = self.execute(script, timeout_retries=retries)
                self.assertEqual(script.role_calls["solver"], retries + 1)
                self.assertEqual(summary["calls"], retries + 2)
                self.assertEqual(summary["status"], "round_limit_reached")
                self.assertEqual(summary["candidates"], [])
                failures = [json.loads(path.read_text()) for path in work.glob("call-*/failure.json")]
                self.assertEqual([value["kind"] for value in failures], ["turn_timeout"] * (retries + 1))
                self.assert_stopped()

    def test_real_deadline_cancels_and_closes_only_the_expired_session_before_retry(self):
        def second(session):
            self.assertEqual(len(self.script.cancelled), 1)
            old = self.script.cancelled[0]
            self.assertTrue(old.closed)
            self.assertGreater(old.agent.stops, 0)
            self.assertTrue(all(agent.stops == 0 for agent in self.agents))
            return None

        script = fake.Script(solver=[fake.HANG, second])
        _, summary = self.execute(script, timeout_retries=1, turn_timeout_seconds=0.2)
        self.assertEqual(script.role_calls["solver"], 2)
        self.assertEqual(len(script.cancelled), 1)
        self.assertEqual(summary["status"], "round_limit_reached")
        self.assert_stopped()

    def test_retries_obey_the_existing_call_and_reported_token_budgets(self):
        def spent_timeout(session):
            session.agent.output += 3
            return expire(session)

        for settings, answer, status in (
            ({"max_calls": 2}, expire, "call_budget_exhausted"),
            ({"output_token_budget": 4}, spent_timeout, "output_budget_exhausted"),
        ):
            with self.subTest(settings=settings):
                script = fake.Script(solver=[answer, fake.DEFAULT])
                _, summary = self.execute(script, timeout_retries=2, **settings)
                self.assertEqual(script.role_calls["solver"], 1)
                self.assertEqual(summary["calls"], 2)
                self.assertEqual(summary["status"], status)
                self.assertEqual(summary["candidates"], [])
                if "output_token_budget" in settings:
                    self.assertEqual(summary["output_tokens_reported"], 4)
                self.assert_stopped()

    def test_integrator_and_its_retry_use_the_separate_deadline(self):
        original_wait = asyncio.wait
        observed = []

        async def observe(awaitables, *, timeout):
            observed.append(timeout)
            return await original_wait(awaitables, timeout=timeout)

        script = fake.Script(solver=[integration.local], integrator=[expire, optimized.composed])
        # Replace only the pipeline's clock binding, not asyncio's real clock.
        # Every supplied deadline is now exact, without elapsed-time assertions.
        with mock.patch.object(fake.pipeline, "time", SimpleNamespace(monotonic=lambda: 1000.0)), \
                mock.patch.object(fake.pipeline.asyncio, "wait", observe):
            _, summary = self.execute(script, integrate=True, optimize=True, timeout_retries=1,
                                      turn_timeout_seconds=11, integrator_timeout_seconds=23)
        self.assertEqual(observed.count(23), 2)
        self.assertEqual(observed.count(11), 6)
        self.assertEqual(len(observed), 8)
        integrators = [call for call in script.calls if call.role == "integrator"]
        self.assertEqual(len(integrators), 2)
        self.assertEqual(integrators[0].prompt, integrators[1].prompt)
        self.assertIs(integrators[0].schema, integrators[1].schema)
        self.assertEqual(summary["calls"], 8)
        self.assertTrue(summary["integrations"][0]["status"].startswith("reviewed_"))
        self.assert_stopped()

    def test_retry_freezes_proof_inputs_once_even_if_the_driver_library_grows(self):
        holder = {}

        def first(session):
            # This direct Driver test deliberately changes an otherwise valid
            # library between attempts. No historical draft is thereby certified.
            draft = fake.pipeline.Candidate.model_validate(fake.candidate(session))
            holder["new_path"] = holder["driver"].add_proof(draft)
            self.assertEqual(integration.proofs(session), [])
            return expire(session)

        def second(session):
            self.assertEqual(integration.proofs(session), [])
            self.assertTrue(any(entry["path"] == holder["new_path"]
                                for entry in holder["driver"].available_manifest()["files"]))
            return fake.candidate(session)

        self.script = fake.Script(solver=[first, second])
        self.agents = self.make_agents(self.script)
        config = fake.pipeline.Config(repo=str(self.repo), live=True, timeout_retries=1,
                                      summary_integration=False)
        repo, work, manifest, _ = fake.pipeline.prepare(config, "Synthetic frozen retry test")
        driver = fake.pipeline.Driver(self.agents, config, repo, work, manifest)
        holder["driver"] = driver
        try:
            answer = asyncio.run(driver.call(self.agents.solver, "solver", "One frozen prompt",
                                             fake.pipeline.Candidate))
        finally:
            driver.stop("fixture_finished")
        self.assertIsInstance(answer, fake.pipeline.Candidate)
        self.assertEqual(driver.calls, 2)
        calls = self.script.calls
        expected_prompt = fake.pipeline.INPUT_ACCESS_POLICY + "\n\nOne frozen prompt"
        self.assertEqual([call.prompt for call in calls], [expected_prompt] * 2)
        requests = [json.loads((call.session.cwd.parent / "request.json").read_text()) for call in calls]
        self.assertEqual(requests[0]["input_manifest_sha256"], requests[1]["input_manifest_sha256"])
        self.assertEqual(self.source_files(), self.before)
        self.assert_stopped()

    def test_cleanup_failure_on_a_timeout_is_global_and_prevents_retry(self):
        for cleanup in ("close", "stop"):
            with self.subTest(cleanup=cleanup):
                original_close = fake.FakeSession.close
                original_stop = fake.FakeAgent.stop

                def broken_close(session):
                    original_close(session)
                    if session.agent.role == "solver":
                        raise RuntimeError("Synthetic close failure after timeout")

                def broken_stop(agent):
                    original_stop(agent)
                    if agent.parent is not None and agent.role == "solver":
                        raise RuntimeError("Synthetic stop failure after timeout")

                patch = (mock.patch.object(fake.FakeSession, "close", broken_close) if cleanup == "close"
                         else mock.patch.object(fake.FakeAgent, "stop", broken_stop))
                script = fake.Script(solver=[expire, fake.DEFAULT])
                with patch:
                    _, summary = self.execute(script, timeout_retries=2)
                self.assertEqual(script.role_calls["solver"], 1)
                self.assertEqual(summary["status"], "cleanup_incomplete")
                self.assertTrue(summary["cleanup_errors"])
                self.assertEqual(summary["candidates"], [])
                self.assert_stopped()

    def test_input_tampering_on_a_timed_out_attempt_halts_without_retry(self):
        def changed(session):
            (session.cwd / fake.pipeline.COMMON_INPUTS[0]).write_text("Synthetic session-only tampering")
            return expire(session)

        script = fake.Script(solver=[changed, fake.DEFAULT])
        with self.assertRaises(RuntimeError):
            self.execute(script, timeout_retries=2)
        summary = json.loads(next(self.runs.glob("run-*/summary.json")).read_text())
        self.assertEqual(summary["status"], "session_input_integrity_failure")
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(self.source_files(), self.before)
        self.assert_stopped()

    def test_unrecoverable_failure_is_never_retried(self):
        script = fake.Script(solver=[fake.pipeline.Unrecoverable(9, ["synthetic backend"]), fake.DEFAULT])
        _, summary = self.execute(script, timeout_retries=2)
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(summary["status"], "backend_unrecoverable")
        self.assert_stopped()

    def test_external_cancellation_propagates_and_cleans_up_without_retry(self):
        async def cancelled(session):
            asyncio.current_task().cancel()
            await asyncio.sleep(0)

        script = fake.Script(solver=[cancelled, fake.DEFAULT])
        with self.assertRaises(asyncio.CancelledError):
            self.execute(script, timeout_retries=2)
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(len(script.cancelled), 1)
        summary = json.loads(next(self.runs.glob("run-*/summary.json")).read_text())
        self.assertEqual(summary["status"], "interrupted_or_failed")
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_a_late_answer_after_suppressed_cancellation_is_raw_only_and_never_promoted(self):
        marker = "LATE ANSWER MUST NOT BECOME A CANDIDATE"

        async def late(session):
            try:
                await asyncio.Future()
            except asyncio.CancelledError:
                return fake.candidate(session, claim=marker)

        script = fake.Script(solver=[late, None])
        work, summary = self.execute(script, timeout_retries=1, turn_timeout_seconds=0.2)
        self.assertEqual(script.role_calls["solver"], 2)
        self.assertEqual(summary["timed_out_calls"], 1)
        self.assertEqual(summary["timeout_retry_calls"], 1)
        self.assertEqual(summary["candidates"], [])
        expired = next(call.session.cwd.parent for call in script.calls if call.role == "solver")
        self.assertIn(marker, (expired / "raw-response.json").read_text())
        self.assertIsNone(json.loads((expired / "response.json").read_text()))
        self.assertEqual(list(work.glob("candidate-*.json")), [])
        self.assert_stopped()

    def test_unrecoverable_failure_during_timeout_cleanup_prevents_retry(self):
        async def late_failure(session):
            try:
                await asyncio.Future()
            except asyncio.CancelledError:
                raise fake.pipeline.Unrecoverable(19, ["synthetic late backend failure"])

        script = fake.Script(solver=[late_failure, fake.DEFAULT])
        work, summary = self.execute(script, timeout_retries=2, turn_timeout_seconds=0.2)
        self.assertEqual(script.role_calls["solver"], 1)
        self.assertEqual(summary["timed_out_calls"], 1)
        self.assertEqual(summary["timeout_retry_calls"], 0)
        self.assertEqual(summary["status"], "backend_unrecoverable")
        expired = next(call.session.cwd.parent for call in script.calls if call.role == "solver")
        self.assertEqual(json.loads((expired / "failure.json").read_text()),
                         {"kind": "backend_unrecoverable", "exitcode": 19})
        self.assertEqual(list(work.glob("candidate-*.json")), [])
        self.assert_stopped()

    def test_activity_heartbeat_counts_only_own_events_and_never_copies_event_text(self):
        emitted = asyncio.Event()
        release = asyncio.Event()
        holder = {}
        secrets = ("SECRET EVENT BODY", "SECRET UNKNOWN EVENT KIND", "SECRET FOREIGN EVENT BODY")
        original_wait = asyncio.wait

        async def noisy(session):
            holder["session"] = session
            initial = json.loads((session.cwd.parent / "activity.json").read_text())
            self.assertEqual(initial["status"], "running")
            for kind in ("begins", "reasoning", "text", "tool", "took", "ends"):
                session.emit(kind, secrets[0])
            session.emit(secrets[1], secrets[0])
            session.emit("result", secrets[2], heard_session=None)
            session.emit("result", secrets[2], emitter=object())
            emitted.set()
            await release.wait()
            return None

        async def heartbeat(awaitables, *, timeout):
            if self.script.workers[-1].role == "solver":
                await emitted.wait()
                if not holder.get("heartbeat"):
                    holder["heartbeat"] = True
                    # Deterministically model a polling interval elapsing, while
                    # the scripted answer remains blocked on an explicit event.
                    return set(), set(awaitables)
                interim = json.loads((holder["session"].cwd.parent / "activity.json").read_text())
                self.assertEqual(interim["status"], "running")
                self.assertEqual(interim["event_counts"]["reasoning"], 1)
                self.assertEqual(interim["event_counts"]["result"], 0)
                self.assertEqual(interim["event_counts"]["other"], 1)
                release.set()
            return await original_wait(awaitables, timeout=timeout)

        script = fake.Script(solver=[noisy])
        with mock.patch.object(fake.pipeline.asyncio, "wait", heartbeat):
            work, summary = self.execute(script)
        self.assertTrue(holder["heartbeat"])
        path = holder["session"].cwd.parent / "activity.json"
        raw = path.read_text()
        value = json.loads(raw)
        self.assertEqual(set(value), {
            "role", "status", "started_at", "updated_at", "elapsed_seconds", "timeout_seconds",
            "retry_index", "retry_of", "last_event_at", "last_event_age_seconds", "event_counts", "caution",
        })
        self.assertEqual(value["role"], "solver")
        self.assertEqual(value["status"], "no_result")
        self.assertEqual(value["event_counts"], {kind: 1 for kind in (
            "begins", "reasoning", "text", "tool", "took", "ends", "result", "other",
        )})
        self.assertIsNotNone(value["last_event_at"])
        self.assertGreaterEqual(value["last_event_age_seconds"], 0)
        self.assertGreaterEqual(value["elapsed_seconds"], 0)
        self.assertIn("not verified mathematical progress", value["caution"])
        for secret in secrets:
            self.assertNotIn(secret, raw)
        self.assertEqual(list(work.glob("call-*/.activity-*")), [])
        self.assertEqual(summary["timed_out_calls"], 0)
        self.assert_stopped()

    def test_pending_integration_survives_exhausted_timeouts_without_new_proofs_and_then_clears(self):
        script = fake.Script(solver=[integration.local] * 3,
                             integrator=[fake.HANG, fake.HANG, optimized.composed])
        work, summary = self.execute(
            script, optimize=True, integrate=True, coverage_planning=False,
            rounds=3, timeout_retries=1, integrator_timeout_seconds=0.2,
        )
        self.assertEqual(script.role_calls["solver"], 3)
        self.assertEqual(script.role_calls["integrator"], 3)
        self.assertEqual(script.role_calls["reviewer_a"], 2)
        self.assertEqual(script.role_calls["reviewer_b"], 2)
        self.assertEqual(summary["timed_out_calls"], 2)
        self.assertEqual(summary["timeout_retry_calls"], 1)
        self.assertIs(summary["integration_pending"], False)
        self.assertEqual([record["status"] for record in summary["candidates"]], [
            "reviewed_sublemma_pending_manual_integration", "duplicate_candidate", "duplicate_candidate",
        ])
        first, second = summary["integrations"]
        self.assertEqual([first["round"], second["round"]], [1, 2])
        self.assertEqual(first["status"], "review_incomplete")
        self.assertEqual(first["reviews"], [])
        self.assertNotIn("proof_path", first)
        self.assertEqual(second["status"], "reviewed_sublemma_pending_manual_integration")
        self.assertEqual(summary["latest_integration"], second["proof_path"])
        self.assertTrue((work / "round-3.json").is_file())
        self.assertFalse((work / "integration-3.json").exists())
        # Successful composition is not itself a new solver contribution that
        # should trigger another integration forever on the next duplicate round.
        self.assertEqual(len(list((work / "proofs").glob("*.md"))), 2)
        self.assertEqual(len(script.cancelled), 2)
        self.assertTrue(all(session.agent.role == "integrator" for session in script.cancelled))
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()

    def test_pending_integration_after_review_timeouts_requires_two_entirely_new_reviews(self):
        old_vote = "FIRST INTEGRATION REVIEW: THIS VOTE MUST NOT BE REUSED"
        new_vote = "SECOND INTEGRATION: FRESH REVIEW FROM A"

        def fresh_a(session):
            self.assertNotIn(old_vote, session.prompts[-1])
            return fake.review(session, explanation=new_vote)

        script = fake.Script(
            solver=[integration.local] * 2,
            integrator=[optimized.composed] * 2,
            reviewer_a=[fake.DEFAULT, lambda session: fake.review(session, explanation=old_vote), fresh_a],
            reviewer_b=[fake.DEFAULT, fake.HANG, fake.HANG, fake.DEFAULT],
        )
        _, summary = self.execute(
            script, optimize=True, integrate=True, coverage_planning=False,
            rounds=2, timeout_retries=1, turn_timeout_seconds=1,
        )
        self.assertEqual(script.role_calls["solver"], 2)
        self.assertEqual(script.role_calls["integrator"], 2)
        self.assertEqual(script.role_calls["reviewer_a"], 3)
        self.assertEqual(script.role_calls["reviewer_b"], 4)
        self.assertEqual(summary["timed_out_calls"], 2)
        self.assertEqual(summary["timeout_retry_calls"], 1)
        self.assertIs(summary["integration_pending"], False)
        self.assertEqual(summary["candidates"][1]["status"], "duplicate_candidate")
        first, second = summary["integrations"]
        self.assertEqual([first["round"], second["round"]], [1, 2])
        self.assertEqual(first["sha256"], second["sha256"])
        self.assertEqual(first["status"], "review_incomplete")
        self.assertEqual(first["reviews"][0]["explanation"], old_vote)
        self.assertIsNone(first["reviews"][1])
        self.assertNotIn("proof_path", first)
        self.assertEqual(second["status"], "reviewed_sublemma_pending_manual_integration")
        self.assertEqual(second["reviews"][0]["explanation"], new_vote)
        self.assertEqual([value["candidate_sha256"] for value in second["reviews"]],
                         [second["sha256"]] * 2)
        reviews = [call for call in script.calls if call.role.startswith("reviewer_")
                   and "Candidate SHA256: " + second["sha256"] + "\n" in call.prompt]
        self.assertEqual(len(reviews), 5)  # first A + expired B/B, then fresh A/B
        self.assertEqual(len({id(call.session) for call in reviews}), 5)
        self.assertEqual({call.role for call in reviews[-2:]}, {"reviewer_a", "reviewer_b"})
        self.assertTrue(all(old_vote not in call.prompt for call in reviews))
        self.assertEqual(summary["latest_integration"], second["proof_path"])
        self.assertFalse(summary["research_goal_proved"])
        self.assert_stopped()


if __name__ == "__main__":
    unittest.main()
