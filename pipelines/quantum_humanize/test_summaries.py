"""Bounded summary/batch control tests; no native calls or mathematical certification."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from pipelines.quantum_humanize import _summaries as summaries
from pipelines.quantum_humanize import test_closure as closure, test_flow as fake
from pipelines.quantum_humanize import test_integration as integration


def summary_fields(**changes):
    return {**{field: "SYNTHETIC SUMMARY " + field for field in summaries.Summary.model_fields}, **changes}


def local(session, *, claim="Synthetic local summary candidate", **changes):
    return {**integration.local(session, claim=claim), "summary": summary_fields(**changes)}


def batch(session, **changes):
    result = closure.composed(session, **changes)
    marker = "\nBATCH ROOT INVENTORY (path -> exact file-byte SHA256):\n"
    roots = json.JSONDecoder().raw_decode(session.prompts[-1].split(marker, 1)[1])[0]
    refs = [ref for ref in result["candidate"]["dependencies"] if ref["path"] in roots]
    result["candidate"]["dependencies"] = refs
    result["assembly"]["pieces"] = refs
    result["summary"] = summary_fields()
    return result


class CacheTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="fput-summary-fixture-")
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name)
        (self.repo / ".humanize-quantum-runs").mkdir()
        self.candidate = fake.pipeline.Candidate(obligation_id="self_audit", scope="sublemma",
            evidence="analytic_draft", claim="Synthetic claim " * 70, argument="Full synthetic argument",
            dependencies=[fake.pipeline.Reference(path="source.md", sha256="a" * 64, section="Full")],
            unproved_steps=[], remaining_obligations=["Synthetic complement " * 60])
        self.data = fake.pipeline.proof_bytes(self.candidate)
        self.ref = {"path": fake.pipeline.proof_path(self.data),
                    "sha256": hashlib.sha256(self.data).hexdigest(), "section": "Full"}

    def test_legacy_cache_is_incomplete_and_does_not_rewrite_proof(self):
        record = summaries.cache(self.repo, self.ref, self.candidate)
        self.assertEqual(fake.pipeline.proof_bytes(self.candidate), self.data)
        self.assertEqual(record.source, "legacy_excerpt")
        self.assertEqual(set(record.truncated_fields), {"claim", "uncovered"})
        self.assertIn("cutoffs_and_constant_losses", record.unknown_fields)
        self.assertFalse(record.trusted_proof)
        self.assertEqual(record.dependencies[0].sha256, "a" * 64)

    def test_same_sha_reuses_cache_without_new_writes_or_votes(self):
        record = summaries.cache(self.repo, self.ref, self.candidate, summary_fields())
        with mock.patch.object(summaries, "_write_new", side_effect=AssertionError("cache rewritten")):
            again = summaries.cache(self.repo, self.ref, self.candidate, summary_fields(bound="A changed summary"))
        self.assertEqual(again, record)
        self.assertEqual(again.source, "author_fields")
        self.assertFalse(again.trusted_proof)

    def test_cache_rejects_mismatched_dependency_binding_and_symlink(self):
        summaries.cache(self.repo, self.ref, self.candidate)
        changed = self.candidate.model_copy(deep=True)
        changed.dependencies[0].sha256 = "b" * 64
        with self.assertRaisesRegex(ValueError, "exact full candidate"):
            summaries.cache(self.repo, self.ref, changed)
        link_ref = {**self.ref, "sha256": "c" * 64}
        (self.repo / ".humanize-quantum-runs/summary-cache-v1" / ("c" * 64 + ".json")).symlink_to(
            self.repo / "missing.json")
        with self.assertRaises((OSError, ValueError)):
            summaries.cache(self.repo, link_ref, self.candidate)

    def test_view_is_bounded_navigation_not_a_dependency_graph_or_acceptance(self):
        record = summaries.cache(self.repo, self.ref, self.candidate, summary_fields())
        view = summaries.view(record)
        self.assertNotIn("dependencies", view)
        self.assertEqual(view["dependency_count"], 1)
        self.assertFalse(view["trusted_proof"])
        with self.assertRaises(ValueError):
            summaries.Summary.model_validate(summary_fields(bound="x" * 601))

    def test_reading_index_trim_keeps_obligation_constraints_and_cautions(self):
        text = ("OBLIGATION\nAvailable required-reading index (including explicitly selected new inputs):\n"
                "ALL ARCHIVE FILES\n_snapshot.json lists exact hashes.\nCAUTIONS")
        trimmed = summaries.trim_reading_index(text)
        self.assertIn("OBLIGATION", trimmed)
        self.assertIn("CAUTIONS", trimmed)
        self.assertNotIn("ALL ARCHIVE FILES", trimmed)

    def test_strict_native_schema_includes_summary_without_changing_candidate(self):
        self.assertNotIn("summary", fake.pipeline.Candidate.model_json_schema()["properties"])
        for cls in (fake.pipeline.SummarizedCandidate, fake.pipeline.SummarizedAssembly):
            schema = cls.model_json_schema()
            self.assertIn("summary", schema["properties"])
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


class SummaryFlowTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped

    def execute(self, script=None, **changes):
        return closure.ClosureTests.execute(self, script, summary_integration=True, **changes)

    def test_same_calls_generate_and_dual_review_summary_but_store_unchanged_candidate_format(self):
        script = fake.Script(solver=[lambda s: local(s, claim="Local A"),
                                     lambda s: local(s, claim="Local B")], integrator=[batch])
        work, result = self.execute(script)
        self.assertEqual(script.role_calls, {"reader": 1, "solver": 2, "reviewer_a": 3,
                                             "reviewer_b": 3, "integrator": 1})
        self.assertTrue(result["integrations"][0]["mathematical_progress"])
        for call in script.calls:
            if call.role.startswith("reviewer_"):
                self.assertIn("AUTHOR SUMMARY FOR THIS EXACT CANDIDATE", call.prompt)
                self.assertIn("FULL argument", call.prompt)
        for path in (work / "proofs").glob('*.md'):
            data = path.read_bytes()
            candidate = fake.pipeline.Candidate.model_validate_json(data.decode().split('```json\n', 1)[1][:-5])
            self.assertNotIn("summary", candidate.model_dump())
            self.assertEqual(data, fake.pipeline.proof_bytes(candidate))
            cached = json.loads((self.runs / "summary-cache-v1" / (hashlib.sha256(data).hexdigest() + ".json")).read_text())
            self.assertEqual(cached["source"], "author_fields")
            self.assertFalse(cached["trusted_proof"])

    def test_eight_drafts_use_three_roots_and_retain_the_rest_without_model_deferrals(self):
        seen = {}
        def compose(session):
            marker = "INTEGRATION DELTA CONTEXT:\n"
            seen.update(json.JSONDecoder().raw_decode(session.prompts[-1].split(marker, 1)[1])[0])
            self.assertEqual(len(integration.proofs(session)), 8)
            self.assertNotIn("EVERY available full proof", session.prompts[-1])
            return batch(session)
        script = fake.Script(solver=[lambda s, i=i: local(s, claim=f"Unique local {i}") for i in range(8)],
                             integrator=[compose])
        work, result = self.execute(script, attempts=8, parallelism=8)
        self.assertEqual(len(seen["focus"]), 3)
        self.assertTrue(all("summary" in item for item in seen["focus"]))
        self.assertTrue(result["integrations"][0]["mathematical_progress"])
        inventory = json.loads((work / "integration-inventory-1.json").read_text())
        self.assertEqual(len(inventory["drafts"]), 8)
        outside = [item for item in inventory["drafts"] if item["batch_state"] == "outside_batch_retained"]
        self.assertEqual(len(outside), 5)
        self.assertTrue(all(item["latest_assessment"] == "unassessed_queued" for item in outside))
        self.assertLessEqual(script.max_active, 8)

    def test_false_summary_blocks_admission_and_is_not_cached_as_a_reviewed_draft(self):
        def review(session):
            self.assertIn("FALSE SUMMARY MARKER", session.prompts[-1])
            return fake.negative(session)
        script = fake.Script(solver=[lambda s: local(s, bound="FALSE SUMMARY MARKER")],
                             reviewer_a=[review], mender=[None])
        work, result = self.execute(script, attempts=1)
        self.assertEqual(result["candidates"][0]["status"], "needs_repair")
        self.assertEqual(list((work / "proofs").glob('*.md')), [])
        self.assertEqual(list((self.runs / "summary-cache-v1").glob('*.json')), [])

    def test_outside_batch_root_is_rejected_but_supporting_dependencies_remain_accessible(self):
        def outside(session):
            result = batch(session)
            roots = {ref["path"] for ref in result["assembly"]["pieces"]}
            extra = next(entry for entry in integration.proofs(session) if entry["path"] not in roots)
            ref = {"path": extra["path"], "sha256": extra["sha256"], "section": "Full"}
            result["assembly"]["pieces"].append(ref)
            return result
        script = fake.Script(solver=[lambda s, i=i: local(s, claim=f"Local {i}") for i in range(4)],
                             integrator=[outside])
        _, result = self.execute(script, attempts=4)
        self.assertEqual(result["integrations"][0]["status"], "assembly_contract_invalid")
        self.assertEqual(result["integrations"][0]["reviews"], [])

    def test_duplicate_candidate_cannot_replace_the_summary_already_sent_for_audit(self):
        script = fake.Script(solver=[lambda s: local(s, bound="FIRST SUMMARY"),
                                     lambda s: local(s, bound="SECOND SUMMARY")], integrator=[None])
        work, _ = self.execute(script)
        reviews = [c for c in script.calls if c.role.startswith("reviewer_")]
        self.assertEqual(len(reviews), 2)
        self.assertTrue(all("FIRST SUMMARY" in c.prompt and "SECOND SUMMARY" not in c.prompt for c in reviews))
        data = next((work / "proofs").glob('*.md')).read_bytes()
        cache = json.loads((self.runs / "summary-cache-v1" / (hashlib.sha256(data).hexdigest() + ".json")).read_text())
        self.assertEqual(cache["summary"]["bound"], "FIRST SUMMARY")

    def test_supporting_dependency_outside_batch_is_available_but_not_a_root_piece(self):
        def supporting(session):
            result = batch(session)
            result["assembly"]["pieces"] = list(result["assembly"]["pieces"])
            roots = {ref["path"] for ref in result["assembly"]["pieces"]}
            extra = next(entry for entry in integration.proofs(session) if entry["path"] not in roots)
            self.assertTrue((session.cwd / extra["path"]).is_file())
            result["candidate"]["dependencies"].append(
                {"path": extra["path"], "sha256": extra["sha256"], "section": "Full supporting dependency"})
            return result
        script = fake.Script(solver=[lambda s, i=i: local(s, claim=f"Local {i}") for i in range(4)],
                             integrator=[supporting])
        _, result = self.execute(script, attempts=4)
        self.assertTrue(result["integrations"][0]["mathematical_progress"])

    def test_unselected_batches_are_processed_even_without_new_solver_proofs(self):
        script = fake.Script(solver=[lambda s, i=i: local(s, claim=f"Local {i}") for i in range(6)] + [None] * 6,
                             integrator=[batch, batch])
        work, result = self.execute(script, attempts=6, rounds=2)
        self.assertEqual(len(result["integrations"]), 2)
        first = json.loads((work / "integration-focus-1.json").read_text())
        second = json.loads((work / "integration-focus-2.json").read_text())
        paths = lambda data: {item["reference"]["path"] for item in data["focus"]}
        self.assertFalse(paths(first) & paths(second))
        self.assertEqual(len(paths(first) | paths(second)), 6)

    def test_comparison_and_omitted_gap_survive_next_batch_without_reusing_old_votes(self):
        script = fake.Script(solver=[lambda s: local(s, claim="Local A"), lambda s: local(s, claim="Local B"),
                                     lambda s: local(s, claim="Local C"), None], integrator=[batch, batch])
        work, result = self.execute(script, rounds=2)
        first, second = result["integrations"]
        self.assertEqual(second["comparison_path"], first["proof_path"])
        self.assertTrue(second["mathematical_progress"])
        delta = json.loads((work / "integration-focus-2.json").read_text())
        self.assertEqual(delta["baseline_summary"]["reference"]["path"], first["proof_path"])
        self.assertFalse(delta["baseline_summary"]["trusted_proof"])
        ledger = json.loads((work / "coverage-ledger-final.json").read_text())
        self.assertTrue(ledger["gaps"])
        self.assertFalse(ledger["coverage_complete"])
        self.assertTrue(all(r['candidate_sha256'] == second['sha256'] for r in second['reviews']))


if __name__ == '__main__':
    unittest.main()

# Upstream fixture helpers; FPUT-specific scenarios are not adapted tests.
__test__ = False
