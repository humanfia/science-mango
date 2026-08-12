from __future__ import annotations

import asyncio
import importlib.util
import io
import json
import os
import sys
import tempfile
import types
import unittest
from collections.abc import Callable
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_answer_blind_gpt_campaign.py"
SPEC = importlib.util.spec_from_file_location("answer_blind_gpt_campaign", SCRIPT)
assert SPEC and SPEC.loader
CAMPAIGN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CAMPAIGN
SPEC.loader.exec_module(CAMPAIGN)


class _Stdout:
    def __init__(self) -> None:
        self.buffer = io.BytesIO()


class _MemoryIndex:
    def __init__(self) -> None:
        self.item: dict[str, object] = {}
        self.stages: dict[str, dict[str, object]] = {}

    async def update_item(self, _record_id: str, **changes: object) -> None:
        self.item.update(changes)

    async def stage(
        self, _record_id: str, stage: str, stage_value: dict[str, object]
    ) -> None:
        self.stages[stage] = dict(stage_value)


@unittest.skipUnless(os.geteuid() == 0, "campaign controller is root-only")
class GPTCampaignTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="gpt-campaign-")
        self.base = Path(self.temporary.name)
        self.seed = self.base / "seed"
        self.seed.mkdir(mode=0o700)
        self.ids = tuple(f"icho_2026_t{index:02d}_a1" for index in range(1, 33))
        self.rows = {record_id: self._row(record_id) for record_id in self.ids}
        bundle = self.seed / "icho_2026_source/questions_only.jsonl"
        bundle.parent.mkdir(parents=True)
        bundle.write_bytes(b"".join(CAMPAIGN._json_bytes(self.rows[item]) for item in self.ids))
        (self.seed / "icho_2026_source/image").mkdir()
        (self.seed / "icho_2026_source/image/page.png").write_bytes(b"problem-page")
        (self.seed / "IChO2026Chem.lean").write_text(
            "namespace IChO2026Chem\nend IChO2026Chem\n", encoding="utf-8"
        )
        (self.seed / "isolation_manifest.json").write_text("{}\n", encoding="utf-8")
        for record_id in self.ids:
            report = self.seed / f"reports/icho/problem_{record_id}.source.json"
            report.parent.mkdir(parents=True, exist_ok=True)
            relative = report.relative_to(self.seed).as_posix()
            blind_hash = CAMPAIGN._canonical_sha(self.rows[record_id])
            entry = {
                **self.rows[record_id],
                "blind_record_sha256": blind_hash,
                "question": str(self.rows[record_id]["question"]).strip(),
                "image": "page.png",
                "image_path": "icho_2026_source/image/page.png",
                "image_paths": ["icho_2026_source/image/page.png"],
            }
            report.write_bytes(
                CAMPAIGN._json_bytes(
                    {
                        "schema_version": 3,
                        "command": "physics-formalize",
                        "domain": "chemistry",
                        "proof_mode": "chemistry",
                        "prover_mode": "chemistry-formalize",
                        "path_base": "project",
                        "project_path": ".",
                        "source_report": relative,
                        "output_lean": f"IChO2026Problems/problem_{record_id}.lean",
                        "problem_id": self.rows[record_id]["problem_id"],
                        "part_id": self.rows[record_id]["part_id"],
                        "previous_parts": [],
                        "lean_search_packages": ["Mathlib", "Physlib", "Chemistry"],
                        "status": "prepared",
                        "next_stage": "autoformalize",
                        "evaluation_mode": "answer_blind",
                        "official_answer_seen": False,
                        "phase": "solve",
                        "blind_record_sha256": blind_hash,
                        "entry": entry,
                    }
                )
            )
        os.chmod(self.seed, 0o700)
        self.bundle_payload, parsed_rows = CAMPAIGN._bundle_rows(bundle)
        self.assertEqual(parsed_rows, self.rows)
        self.reports = CAMPAIGN._source_reports(self.seed, self.rows)
        self.seed_inventory = CAMPAIGN._plain_seed_inventory(self.seed)

        self.runtime = self.base / "runtime"
        self.dependency = self.base / "dependency"
        self.codex_home = self.base / "codex-home"
        self.campaign_root = self.base / "campaign"
        for directory in (self.runtime, self.dependency, self.codex_home):
            directory.mkdir(mode=0o755)
        paths = {
            "campaign": self.runtime / "bin/answer-blind-gpt-campaign",
            "review": self.runtime / "bin/answer-blind-independent-review",
            "solver": self.runtime / "bin/answer-blind-structured-solver",
            "verifier": self.runtime / "bin/answer-blind-verifier",
            "archon": self.runtime / "bin/archon",
            "codex": self.runtime / "bin/codex",
            "lake": self.runtime / "lean-v4.31.0/bin/lake",
        }
        for path in paths.values():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
            os.chmod(path, 0o555)
        self.lanes = tuple(
            CAMPAIGN.Lane(
                number=index,
                user=f"verifier{index}",
                uid=10000 + index,
                gid=10000 + index,
                scratch_root=self.base / f"scratch-{index}",
            )
            for index in range(1, 5)
        )
        for lane in self.lanes:
            lane.scratch_root.mkdir(mode=0o755)
        self.config = CAMPAIGN.Config(
            campaign_id="unit-full32",
            campaign_root=self.campaign_root,
            seed_workspace=self.seed,
            runtime_root=self.runtime,
            dependency_root=self.dependency,
            codex_home=self.codex_home,
            singleton_lock=self.base / "campaign-singleton.lock",
            verifier_users=tuple(lane.user for lane in self.lanes),
            verifier_scratch_roots=tuple(lane.scratch_root for lane in self.lanes),
            concurrency=4,
            max_attempts=4,
            stage_timeout_s=100,
            verifier_timeout_s=50,
        )
        self.binding = CAMPAIGN.Binding(
            config=self.config,
            ids=self.ids,
            bundle_ids=self.ids,
            rows=self.rows,
            orchestrator_sha256=CAMPAIGN._file_sha(SCRIPT),
            bundle_relative=CAMPAIGN.PurePosixPath(
                "icho_2026_source/questions_only.jsonl"
            ),
            bundle_sha256=CAMPAIGN._sha(self.bundle_payload),
            seed_inventory=self.seed_inventory,
            seed_inventory_sha256=CAMPAIGN._hash_index(self.seed_inventory),
            runtime_inventory_sha256="1" * 64,
            dependency_inventory_sha256="2" * 64,
            source_reports=self.reports,
            runtime_bins=paths,
            lanes=self.lanes,
            parent_campaign=None,
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def _row(record_id: str) -> dict[str, object]:
        return {
            "schema_version": 1,
            "protocol": "icho-answer-blind-v1",
            "evaluation_mode": "answer_blind",
            "official_answer_seen": False,
            "phase": "solve",
            "id": record_id,
            "problem_id": record_id.split("_")[2],
            "part_id": "A1",
            "current_question": f"Compute {record_id}.",
            "shared_context": "Use the printed data.",
            "question": f"Use the printed data.\n\nCompute {record_id}.\n",
            "previous_parts": [],
            "image": "page.png",
            "images": ["page.png"],
            "problem_assets": [],
            "requested_outputs": [{"id": "result", "kind": "numeric"}],
            "reporting_policy": {"intermediate_rounding": "forbidden"},
            "measurement_policy": {"uncertainty": "exact"},
            "candidate_domain_policy": {"allowed_sources": ["problem_text"]},
        }

    def _sealed_parent_index(
        self, *, name: str, failed_ids: tuple[str, ...]
    ) -> Path:
        parent_root = self.base / name
        parent_config = CAMPAIGN.dataclasses.replace(
            self.config,
            campaign_id=f"unit-{name}",
            campaign_root=parent_root,
            parent_campaign_index=None,
            scope_ids=(),
        )
        parent_binding = CAMPAIGN.dataclasses.replace(
            self.binding,
            config=parent_config,
            ids=self.ids,
            bundle_ids=self.ids,
            parent_campaign=None,
        )
        CAMPAIGN._mkdir_layout(parent_binding)
        value = CAMPAIGN._initial_index(parent_binding)
        failed = set(failed_ids)
        for row in value["items"]:
            if row["id"] in failed:
                row["status"] = "failed"
                row["stages"] = {
                    "source-first": {
                        "status": "failed",
                        "argv": ["/bin/false"],
                    }
                }
                row["error"] = {
                    "stage": "source-first",
                    "type": "StageError",
                    "message": "fixture failure",
                }
            else:
                controller = Path(row["controller"])
                controller.mkdir()
                seal = controller / "gpt-freeze-authorization.json"
                frozen = controller / "gpt-frozen-manifest.json"
                seal.write_bytes(f"sealed-controller:{row['id']}\n".encode())
                frozen.write_bytes(f"sealed-freeze:{row['id']}\n".encode())
                seal.chmod(0o400)
                frozen.chmod(0o400)
                row["status"] = "succeeded"
                row["stages"] = {
                    stage: {"status": "succeeded", "argv": ["/bin/true"]}
                    for stage in CAMPAIGN.STAGES
                }
                row["controller_seal_sha256"] = CAMPAIGN._file_sha(seal)
                row["freeze_manifest_sha256"] = CAMPAIGN._file_sha(frozen)
                row["error"] = None
        value["summary"] = {
            "pending": 0,
            "running": 0,
            "succeeded": len(self.ids) - len(failed),
            "failed": len(failed),
        }
        value["status"] = "failed" if failed else "succeeded"
        value["completed_at"] = value["updated_at"]
        value["integrity_error"] = None
        index_path = parent_root / "campaign-index.json"
        CAMPAIGN._atomic_index(index_path, value, final=True)
        CAMPAIGN._publish_index_sidecar(index_path)
        return index_path

    def _sealed_retry_parent_index(
        self,
        *,
        name: str,
        parent_index: Path,
        parent_failed_ids: tuple[str, ...],
        failed_ids: tuple[str, ...],
    ) -> Path:
        retry_root = self.base / name
        retry_config = CAMPAIGN.dataclasses.replace(
            self.config,
            campaign_id=f"unit-{name}",
            campaign_root=retry_root,
            parent_campaign_index=parent_index,
            scope_ids=parent_failed_ids,
        )
        execution_ids, parent = CAMPAIGN._load_parent_campaign(
            config=retry_config,
            bundle_ids=self.ids,
            bundle_sha256=self.binding.bundle_sha256,
            campaign_root=retry_root,
        )
        retry_binding = CAMPAIGN.dataclasses.replace(
            self.binding,
            config=retry_config,
            ids=execution_ids,
            bundle_ids=self.ids,
            parent_campaign=parent,
        )
        CAMPAIGN._mkdir_layout(retry_binding)
        value = CAMPAIGN._initial_index(retry_binding)
        failed = set(failed_ids)
        for row in value["items"]:
            if row["id"] in failed:
                row["status"] = "failed"
                row["stages"] = {
                    "source-first": {"status": "failed", "argv": ["/bin/false"]}
                }
                row["error"] = {
                    "stage": "source-first",
                    "type": "StageError",
                    "message": "fixture retry failure",
                }
                continue
            controller = Path(row["controller"])
            controller.mkdir()
            seal = controller / "gpt-freeze-authorization.json"
            frozen = controller / "gpt-frozen-manifest.json"
            seal.write_bytes(f"retry-controller:{row['id']}\n".encode())
            frozen.write_bytes(f"retry-freeze:{row['id']}\n".encode())
            seal.chmod(0o400)
            frozen.chmod(0o400)
            row["status"] = "succeeded"
            row["stages"] = {
                stage: {"status": "succeeded", "argv": ["/bin/true"]}
                for stage in CAMPAIGN.STAGES
            }
            row["controller_seal_sha256"] = CAMPAIGN._file_sha(seal)
            row["freeze_manifest_sha256"] = CAMPAIGN._file_sha(frozen)
            row["error"] = None
        value["summary"] = {
            "pending": 0,
            "running": 0,
            "succeeded": len(execution_ids) - len(failed),
            "failed": len(failed),
        }
        value["status"] = "failed" if failed else "succeeded"
        value["completed_at"] = value["updated_at"]
        value["integrity_error"] = None
        index_path = retry_root / "campaign-index.json"
        CAMPAIGN._atomic_index(index_path, value, final=True)
        CAMPAIGN._publish_index_sidecar(index_path)
        return index_path

    @staticmethod
    def _rewrite_sealed_index(
        index_path: Path,
        transform: Callable[[dict[str, object]], None],
        *,
        publish_sidecar: bool = True,
    ) -> None:
        value = json.loads(index_path.read_text(encoding="utf-8"))
        transform(value)
        sidecar = index_path.with_suffix(index_path.suffix + ".sha256")
        sidecar.unlink()
        CAMPAIGN._atomic_index(index_path, value, final=True)
        if publish_sidecar:
            CAMPAIGN._publish_index_sidecar(index_path)

    def test_workspace_copy_keeps_full_bundle_and_exactly_one_source_report(self) -> None:
        item = CAMPAIGN._item_paths(self.binding, self.ids[7], 8)
        CAMPAIGN._mkdir_layout(self.binding)
        CAMPAIGN._prepare_workspace(self.binding, item)
        bundle_lines = [
            json.loads(line)
            for line in item.bundle.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
        self.assertEqual(len(bundle_lines), 32)
        self.assertEqual({row["id"] for row in bundle_lines}, set(self.ids))
        reports = list((item.workspace / "reports").rglob("*.source.json"))
        self.assertEqual(
            reports,
            [item.workspace.joinpath(*item.source_report_relative.parts)],
        )
        report = json.loads(reports[0].read_text(encoding="utf-8"))
        self.assertEqual(report["entry"]["id"], self.ids[7])
        self.assertTrue(self.rows[self.ids[7]]["question"].endswith("\n"))
        self.assertEqual(
            report["entry"]["question"],
            self.rows[self.ids[7]]["question"].strip(),
        )
        self.assertEqual(
            report["blind_record_sha256"],
            CAMPAIGN._canonical_sha(self.rows[self.ids[7]]),
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "reuse"):
            CAMPAIGN._prepare_workspace(self.binding, item)

    def test_commands_cover_full_chain_and_bind_pilot_scope(self) -> None:
        item = CAMPAIGN._item_paths(self.binding, self.ids[0], 1)
        commands = CAMPAIGN._commands(self.binding, item, self.lanes[0])
        self.assertEqual([stage for stage, _argv in commands], list(CAMPAIGN.STAGES))
        by_stage = dict(commands)
        for stage, argv in commands:
            self.assertTrue(any(item.record_id in token for token in argv), stage)
            self.assertNotIn(str(self.seed / "icho_2026_source/questions_only.jsonl"), argv)
        self.assertIn(str(item.bundle), by_stage["source-first"])
        self.assertIn(str(item.bundle), by_stage["solver"])
        self.assertIn("{snapshot_inventory_sha256}", by_stage["artifact-finalize"])
        self.assertIn("--scope-kind", by_stage["seal-pilot"])
        self.assertEqual(
            by_stage["seal-pilot"][by_stage["seal-pilot"].index("--scope-kind") + 1],
            "pilot",
        )
        self.assertIn("{controller_seal_sha256}", by_stage["freeze"])
        self.assertEqual(
            by_stage["verifier"][by_stage["verifier"].index("--verifier-user") + 1],
            self.lanes[0].user,
        )

    def test_initial_index_binds_32_ids_inputs_model_and_final_digests(self) -> None:
        index = CAMPAIGN._initial_index(self.binding)
        self.assertEqual(
            index["execution_scope"],
            {"kind": "full32", "ids": list(self.ids)},
        )
        self.assertIsNone(index["parent_campaign_index"])
        self.assertEqual(index["bundle"]["ids"], list(self.ids))
        self.assertEqual(index["bundle"]["row_count"], 32)
        self.assertEqual(index["bundle"]["sha256"], self.binding.bundle_sha256)
        self.assertEqual(index["runtime"]["inventory_sha256"], "1" * 64)
        self.assertEqual(index["dependency"]["inventory_sha256"], "2" * 64)
        self.assertEqual(index["model"]["id"], "gpt-5.6-sol")
        self.assertEqual(len(index["items"]), 32)
        for item in index["items"]:
            self.assertEqual(item["status"], "pending")
            self.assertIn("controller_seal_sha256", item)
            self.assertIn("freeze_manifest_sha256", item)
            self.assertIsNone(item["controller_seal_sha256"])
            self.assertIsNone(item["freeze_manifest_sha256"])

    def test_terminal_parent_failed_subset_builds_fresh_exact_execution_scope(
        self,
    ) -> None:
        failed = (self.ids[2], self.ids[10], self.ids[20])
        parent_index = self._sealed_parent_index(
            name="parent-positive", failed_ids=failed
        )
        selected = (failed[0], failed[2])
        retry_config = CAMPAIGN.dataclasses.replace(
            self.config,
            campaign_id="unit-retry",
            parent_campaign_index=parent_index,
            scope_ids=selected,
        )
        execution_ids, parent = CAMPAIGN._load_parent_campaign(
            config=retry_config,
            bundle_ids=self.ids,
            bundle_sha256=self.binding.bundle_sha256,
            campaign_root=self.campaign_root,
        )
        self.assertEqual(execution_ids, selected)
        self.assertIsNotNone(parent)
        assert parent is not None
        retry_binding = CAMPAIGN.dataclasses.replace(
            self.binding,
            config=retry_config,
            ids=execution_ids,
            parent_campaign=parent,
        )
        index = CAMPAIGN._initial_index(retry_binding)
        self.assertEqual(index["bundle"]["row_count"], 32)
        self.assertEqual(index["bundle"]["ids"], list(self.ids))
        self.assertEqual(
            index["execution_scope"],
            {"kind": "failed_subset_retry", "ids": list(selected)},
        )
        self.assertEqual(index["summary"]["pending"], 2)
        self.assertEqual([row["id"] for row in index["items"]], list(selected))
        self.assertEqual([row["ordinal"] for row in index["items"]], [3, 21])
        self.assertEqual(
            [row["run_id"] for row in index["items"]],
            [
                f"unit-retry-03-{selected[0]}",
                f"unit-retry-21-{selected[1]}",
            ],
        )
        locator = index["parent_campaign_index"]
        self.assertEqual(locator["path"], str(parent_index))
        self.assertEqual(locator["sha256"], CAMPAIGN._file_sha(parent_index))
        self.assertRegex(locator["sidecar"]["sha256"], r"^[0-9a-f]{64}$")
        for row in index["items"]:
            self.assertTrue(Path(row["workspace"]).is_relative_to(self.campaign_root))
            self.assertFalse(Path(row["workspace"]).is_relative_to(parent_index.parent))

        document = CAMPAIGN._dry_run_document(retry_binding)
        self.assertEqual(document["item_count"], 2)
        self.assertEqual(document["bundle_ids"], list(self.ids))
        self.assertEqual([row["id"] for row in document["items"]], list(selected))
        self.assertTrue(
            all(
                [command["stage"] for command in row["commands"]]
                == list(CAMPAIGN.STAGES)
                for row in document["items"]
            )
        )

    def test_retry_accepts_sealed_legacy_full32_parent_schema(self) -> None:
        failed = (self.ids[6], self.ids[12])
        parent_index = self._sealed_parent_index(
            name="parent-legacy-full32", failed_ids=failed
        )

        def make_legacy(value: dict[str, object]) -> None:
            value.pop("execution_scope")
            value.pop("parent_campaign_index")

        self._rewrite_sealed_index(parent_index, make_legacy)
        retry_config = CAMPAIGN.dataclasses.replace(
            self.config,
            campaign_id="unit-legacy-retry",
            parent_campaign_index=parent_index,
            scope_ids=(failed[1],),
        )
        execution_ids, parent = CAMPAIGN._load_parent_campaign(
            config=retry_config,
            bundle_ids=self.ids,
            bundle_sha256=self.binding.bundle_sha256,
            campaign_root=self.campaign_root,
        )
        self.assertEqual(execution_ids, (failed[1],))
        assert parent is not None
        self.assertEqual(parent.campaign_id, "unit-parent-legacy-full32")
        self.assertEqual(len(parent.lineage), 1)

    def test_subset_execution_reuses_lane_barrier_for_selected_items_only(self) -> None:
        failed = (self.ids[1], self.ids[9], self.ids[30])
        parent_index = self._sealed_parent_index(
            name="parent-barrier", failed_ids=failed
        )
        retry_config = CAMPAIGN.dataclasses.replace(
            self.config,
            campaign_id="unit-retry-barrier",
            parent_campaign_index=parent_index,
            scope_ids=failed,
        )
        execution_ids, parent = CAMPAIGN._load_parent_campaign(
            config=retry_config,
            bundle_ids=self.ids,
            bundle_sha256=self.binding.bundle_sha256,
            campaign_root=self.campaign_root,
        )
        retry_binding = CAMPAIGN.dataclasses.replace(
            self.binding,
            config=retry_config,
            ids=execution_ids,
            parent_campaign=parent,
        )
        pre: list[tuple[int, str]] = []
        post: list[tuple[int, str]] = []

        async def fake_pre(**kwargs: object) -> bool:
            item = kwargs["item"]
            pre.append((item.ordinal, item.record_id))
            return True

        async def fake_post(**kwargs: object) -> None:
            self.assertEqual(len(pre), len(failed))
            item = kwargs["item"]
            post.append((item.ordinal, item.record_id))

        with (
            mock.patch.object(CAMPAIGN, "_run_pre_verifier_item", side_effect=fake_pre),
            mock.patch.object(CAMPAIGN, "_run_post_verifier_item", side_effect=fake_post),
        ):
            asyncio.run(CAMPAIGN._execute(retry_binding, _MemoryIndex()))
        expected = [(2, failed[0]), (10, failed[1]), (31, failed[2])]
        self.assertEqual(pre, expected)
        self.assertCountEqual(post, expected)

    def test_successful_subset_index_finalizes_against_subset_not_32_items(self) -> None:
        failed = (self.ids[4], self.ids[17])
        parent_index = self._sealed_parent_index(
            name="parent-subset-finalize", failed_ids=failed
        )
        retry_config = CAMPAIGN.dataclasses.replace(
            self.config,
            campaign_id="unit-retry-finalize",
            parent_campaign_index=parent_index,
            scope_ids=failed,
        )
        execution_ids, parent = CAMPAIGN._load_parent_campaign(
            config=retry_config,
            bundle_ids=self.ids,
            bundle_sha256=self.binding.bundle_sha256,
            campaign_root=self.campaign_root,
        )
        retry_binding = CAMPAIGN.dataclasses.replace(
            self.binding,
            config=retry_config,
            ids=execution_ids,
            parent_campaign=parent,
        )
        CAMPAIGN._mkdir_layout(retry_binding)
        value = CAMPAIGN._initial_index(retry_binding)
        for row in value["items"]:
            controller = Path(row["controller"])
            controller.mkdir()
            seal = controller / "gpt-freeze-authorization.json"
            frozen = controller / "gpt-frozen-manifest.json"
            seal.write_bytes(b"sealed-controller\n")
            frozen.write_bytes(b"sealed-freeze\n")
            seal.chmod(0o400)
            frozen.chmod(0o400)
            row["status"] = "succeeded"
            row["stages"] = {
                stage: {"status": "succeeded", "argv": ["/bin/true"]}
                for stage in CAMPAIGN.STAGES
            }
            row["controller_seal_sha256"] = CAMPAIGN._file_sha(seal)
            row["freeze_manifest_sha256"] = CAMPAIGN._file_sha(frozen)
            row["error"] = None
        index_path = self.campaign_root / "campaign-index.json"
        CAMPAIGN._atomic_index(index_path, value)
        writer = CAMPAIGN.IndexWriter(index_path, value)
        asyncio.run(writer.finalize())
        self.assertEqual(writer.value["status"], "succeeded")
        self.assertIsNone(writer.value["integrity_error"])
        self.assertEqual(
            writer.value["summary"],
            {"pending": 0, "running": 0, "succeeded": 2, "failed": 0},
        )
        self.assertEqual(index_path.stat().st_mode & 0o777, 0o400)

    def test_finalize_never_marks_failed_plus_nonterminal_items_clean(self) -> None:
        for nonterminal_status in ("pending", "running", "awaiting_verifier"):
            with self.subTest(status=nonterminal_status):
                root = self.base / f"finalize-{nonterminal_status}"
                config = CAMPAIGN.dataclasses.replace(
                    self.config, campaign_root=root
                )
                binding = CAMPAIGN.dataclasses.replace(
                    self.binding, config=config
                )
                CAMPAIGN._mkdir_layout(binding)
                value = CAMPAIGN._initial_index(binding)
                value["items"][0]["status"] = "failed"
                value["items"][0]["error"] = {
                    "stage": "source-first",
                    "type": "StageError",
                    "message": "fixture failure",
                }
                value["items"][1]["status"] = nonterminal_status
                path = root / "campaign-index.json"
                CAMPAIGN._atomic_index(path, value)
                writer = CAMPAIGN.IndexWriter(path, value)
                asyncio.run(writer.finalize())
                self.assertEqual(writer.value["status"], "failed")
                self.assertEqual(
                    writer.value["integrity_error"],
                    "campaign finalized with nonterminal items",
                )
                self.assertEqual(path.stat().st_mode & 0o777, 0o400)

    def test_retry_of_retry_recursively_binds_lineage_and_rejects_ancestor_reuse(
        self,
    ) -> None:
        r1_failed = (self.ids[5], self.ids[23])
        r1 = self._sealed_parent_index(
            name="lineage-r1", failed_ids=r1_failed
        )
        r2_failed = (r1_failed[1],)
        r2 = self._sealed_retry_parent_index(
            name="lineage-r2",
            parent_index=r1,
            parent_failed_ids=r1_failed,
            failed_ids=r2_failed,
        )
        r3_config = CAMPAIGN.dataclasses.replace(
            self.config,
            campaign_id="unit-lineage-r3",
            campaign_root=self.base / "lineage-r3",
            parent_campaign_index=r2,
            scope_ids=r2_failed,
        )
        execution_ids, parent = CAMPAIGN._load_parent_campaign(
            config=r3_config,
            bundle_ids=self.ids,
            bundle_sha256=self.binding.bundle_sha256,
            campaign_root=r3_config.campaign_root,
        )
        self.assertEqual(execution_ids, r2_failed)
        assert parent is not None
        self.assertEqual(
            [receipt.index_path for receipt in parent.lineage], [r2, r1]
        )
        self.assertEqual(
            len({receipt.campaign_id for receipt in parent.lineage}), 2
        )

        reused_id = CAMPAIGN.dataclasses.replace(
            r3_config, campaign_id=f"unit-{r1.parent.name}"
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "ID.*reused"):
            CAMPAIGN._load_parent_campaign(
                config=reused_id,
                bundle_ids=self.ids,
                bundle_sha256=self.binding.bundle_sha256,
                campaign_root=reused_id.campaign_root,
            )

        nested_root = CAMPAIGN.dataclasses.replace(
            r3_config, campaign_root=r1.parent / "nested-r3"
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "disjoint"):
            CAMPAIGN._load_parent_campaign(
                config=nested_root,
                bundle_ids=self.ids,
                bundle_sha256=self.binding.bundle_sha256,
                campaign_root=nested_root.campaign_root,
            )

    def test_parent_retry_preflight_rejects_unsealed_or_unsafe_state(self) -> None:
        failed = (self.ids[3], self.ids[8])

        def load(
            parent_index: Path | None, scope: tuple[str, ...], *, root: Path | None = None
        ) -> tuple[tuple[str, ...], object]:
            config = CAMPAIGN.dataclasses.replace(
                self.config,
                campaign_id="unit-retry-negative",
                parent_campaign_index=parent_index,
                scope_ids=scope,
            )
            return CAMPAIGN._load_parent_campaign(
                config=config,
                bundle_ids=self.ids,
                bundle_sha256=self.binding.bundle_sha256,
                campaign_root=root or self.campaign_root,
            )

        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "requires --parent"):
            load(None, failed)
        parent_no_scope = self._sealed_parent_index(
            name="parent-no-scope", failed_ids=failed
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "at least one"):
            load(parent_no_scope, ())
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "canonical bundle order"):
            load(parent_no_scope, tuple(reversed(failed)))
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "unique safe"):
            load(parent_no_scope, (failed[0], failed[0]))
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "parent failed"):
            load(parent_no_scope, (self.ids[0],))
        subset_ids, _parent = load(parent_no_scope, (failed[0],))
        self.assertEqual(subset_ids, (failed[0],))
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "disjoint"):
            load(
                parent_no_scope,
                failed,
                root=parent_no_scope.parent / "nested-retry",
            )

        wrong_mode = self._sealed_parent_index(
            name="parent-wrong-mode", failed_ids=failed
        )
        wrong_mode.chmod(0o600)
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "mode-0400"):
            load(wrong_mode, failed)

        missing_sidecar = self._sealed_parent_index(
            name="parent-no-sidecar", failed_ids=failed
        )
        missing_sidecar.with_suffix(missing_sidecar.suffix + ".sha256").unlink()
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "cannot open.*sidecar"):
            load(missing_sidecar, failed)

        bad_sidecar = self._sealed_parent_index(
            name="parent-bad-sidecar", failed_ids=failed
        )
        sidecar = bad_sidecar.with_suffix(bad_sidecar.suffix + ".sha256")
        sidecar.chmod(0o600)
        sidecar.write_text(f"{'0' * 64}  {bad_sidecar.name}\n", encoding="ascii")
        sidecar.chmod(0o400)
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "does not bind"):
            load(bad_sidecar, failed)

        integrity_error = self._sealed_parent_index(
            name="parent-integrity-error", failed_ids=failed
        )
        self._rewrite_sealed_index(
            integrity_error,
            lambda value: value.update(integrity_error="fixture drift"),
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "clean terminal"):
            load(integrity_error, failed)

        running = self._sealed_parent_index(
            name="parent-running", failed_ids=failed
        )
        self._rewrite_sealed_index(
            running,
            lambda value: value.update(status="running", completed_at=None),
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "clean terminal"):
            load(running, failed)

        pending = self._sealed_parent_index(
            name="parent-pending", failed_ids=failed
        )

        def make_pending(value: dict[str, object]) -> None:
            value["items"][0]["status"] = "pending"
            value["summary"] = {
                "pending": 1,
                "running": 0,
                "succeeded": 29,
                "failed": 2,
            }

        self._rewrite_sealed_index(pending, make_pending)
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "pending or running"):
            load(pending, failed)

    def test_parent_success_artifacts_must_exist_be_0400_and_match_hashes(self) -> None:
        failed = (self.ids[7],)

        def load(parent: Path) -> None:
            config = CAMPAIGN.dataclasses.replace(
                self.config,
                campaign_id=f"retry-{parent.parent.name}",
                parent_campaign_index=parent,
                scope_ids=failed,
            )
            CAMPAIGN._load_parent_campaign(
                config=config,
                bundle_ids=self.ids,
                bundle_sha256=self.binding.bundle_sha256,
                campaign_root=self.campaign_root,
            )

        missing = self._sealed_parent_index(
            name="parent-missing-artifact", failed_ids=failed
        )
        missing_artifact = (
            missing.parent
            / "controllers"
            / self.ids[0]
            / "gpt-frozen-manifest.json"
        )
        missing_artifact.unlink()
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "cannot open"):
            load(missing)

        wrong_mode = self._sealed_parent_index(
            name="parent-artifact-mode", failed_ids=failed
        )
        mode_artifact = (
            wrong_mode.parent
            / "controllers"
            / self.ids[0]
            / "gpt-freeze-authorization.json"
        )
        mode_artifact.chmod(0o600)
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "mode-0400"):
            load(wrong_mode)

        hash_drift = self._sealed_parent_index(
            name="parent-artifact-hash", failed_ids=failed
        )
        drift_artifact = (
            hash_drift.parent
            / "controllers"
            / self.ids[0]
            / "gpt-frozen-manifest.json"
        )
        drift_artifact.chmod(0o600)
        drift_artifact.write_bytes(b"drifted-but-sealed\n")
        drift_artifact.chmod(0o400)
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "hash drifted"):
            load(hash_drift)

    def test_failed_stage_stops_item_and_does_not_reuse_later_stages(self) -> None:
        item = CAMPAIGN._item_paths(self.binding, self.ids[0], 1)
        item.workspace.mkdir(parents=True)
        item.controller.mkdir(parents=True)
        item.log_root.mkdir(parents=True)
        called: list[str] = []

        async def fake_stage(**kwargs: object) -> None:
            stage = str(kwargs["stage"])
            called.append(stage)
            if stage == "solver":
                raise CAMPAIGN.StageError(stage, "fixture solver failure")

        index = _MemoryIndex()
        with (
            mock.patch.object(CAMPAIGN, "_prepare_workspace", return_value=None),
            mock.patch.object(CAMPAIGN, "_run_stage", side_effect=fake_stage),
        ):
            ready = asyncio.run(
                CAMPAIGN._run_pre_verifier_item(
                    binding=self.binding,
                    item=item,
                    solver_lane=self.lanes[0],
                    solver_lane_lock=asyncio.Lock(),
                    index=index,
                )
            )
        self.assertFalse(ready)
        self.assertEqual(called, ["source-first", "solver"])
        self.assertEqual(index.item["status"], "failed")
        self.assertEqual(index.item["error"]["stage"], "solver")
        self.assertNotIn("artifact-submit", called)

    def test_solver_uid_and_scratch_lanes_are_mutually_exclusive(self) -> None:
        binding = CAMPAIGN.dataclasses.replace(
            self.binding,
            config=CAMPAIGN.dataclasses.replace(self.config, concurrency=32),
        )
        active_by_user = {lane.user: 0 for lane in self.lanes}
        maximum_by_user = {lane.user: 0 for lane in self.lanes}
        active_total = 0
        maximum_total = 0

        async def fake_stage(**kwargs: object) -> None:
            nonlocal active_total, maximum_total
            if kwargs["stage"] != "solver":
                return
            argv = list(kwargs["argv"])
            user = argv[argv.index("--verifier-user") + 1]
            active_by_user[user] += 1
            active_total += 1
            maximum_by_user[user] = max(
                maximum_by_user[user], active_by_user[user]
            )
            maximum_total = max(maximum_total, active_total)
            await asyncio.sleep(0.005)
            active_by_user[user] -= 1
            active_total -= 1

        async def fake_post(**_kwargs: object) -> None:
            return None

        with (
            mock.patch.object(CAMPAIGN, "_prepare_workspace", return_value=None),
            mock.patch.object(CAMPAIGN, "_run_stage", side_effect=fake_stage),
            mock.patch.object(CAMPAIGN, "_run_post_verifier_item", side_effect=fake_post),
        ):
            asyncio.run(CAMPAIGN._execute(binding, _MemoryIndex()))
        self.assertEqual(maximum_by_user, {lane.user: 1 for lane in self.lanes})
        self.assertEqual(maximum_total, 4)

    def test_successful_controller_with_process_group_residue_is_killed_and_failed(
        self,
    ) -> None:
        item = CAMPAIGN._item_paths(self.binding, self.ids[0], 1)
        item.workspace.mkdir(parents=True)
        item.controller.mkdir(parents=True)
        item.log_root.mkdir(parents=True)
        index = _MemoryIndex()
        with self.assertRaisesRegex(CAMPAIGN.StageError, "left descendants"):
            asyncio.run(
                CAMPAIGN._run_stage(
                    binding=self.binding,
                    item=item,
                    index=index,
                    stage="source-first",
                    argv=["/bin/sh", "-c", "sleep 60 & exit 0"],
                )
            )
        stage = index.stages["source-first"]
        self.assertEqual(stage["status"], "failed")
        self.assertEqual(stage["exit_code"], 0)
        self.assertIn("left descendants", stage["controller_error"]["message"])

    def test_all_model_halves_cross_barrier_before_four_final_uid_lanes(self) -> None:
        binding = CAMPAIGN.dataclasses.replace(
            self.binding,
            config=CAMPAIGN.dataclasses.replace(self.config, concurrency=32),
        )
        pre_completed = 0
        post_active = 0
        maximum_post_active = 0

        async def fake_pre(**_kwargs: object) -> bool:
            nonlocal pre_completed
            await asyncio.sleep(0.001)
            pre_completed += 1
            return True

        async def fake_post(**_kwargs: object) -> None:
            nonlocal post_active, maximum_post_active
            self.assertEqual(pre_completed, 32)
            post_active += 1
            maximum_post_active = max(maximum_post_active, post_active)
            await asyncio.sleep(0.002)
            post_active -= 1

        with (
            mock.patch.object(CAMPAIGN, "_run_pre_verifier_item", side_effect=fake_pre),
            mock.patch.object(CAMPAIGN, "_run_post_verifier_item", side_effect=fake_post),
        ):
            asyncio.run(CAMPAIGN._execute(binding, _MemoryIndex()))
        self.assertEqual(pre_completed, 32)
        self.assertEqual(maximum_post_active, 4)

    def test_subprocess_environment_disables_runtime_bytecode_and_cache_is_rejected(self) -> None:
        environment = CAMPAIGN._command_environment(self.binding)
        self.assertEqual(environment["PYTHONDONTWRITEBYTECODE"], "1")
        self.assertEqual(environment["PYTHONNOUSERSITE"], "1")
        CAMPAIGN._assert_runtime_cache_free(self.runtime)
        cache = self.runtime / "venv/lib/python3.14/site-packages/pkg/__pycache__"
        cache.mkdir(parents=True)
        (cache / "module.cpython-314.pyc").write_bytes(b"generated")
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "generated cache"):
            CAMPAIGN._assert_runtime_cache_free(self.runtime)

    def test_dry_run_prints_plan_and_never_dispatches_campaign(self) -> None:
        output = _Stdout()
        argv = [
            "--campaign-id",
            self.config.campaign_id,
            "--campaign-root",
            str(self.campaign_root),
            "--runtime-root",
            str(self.runtime),
            "--dry-run",
        ]
        with (
            mock.patch.object(CAMPAIGN, "preflight", return_value=self.binding),
            mock.patch.object(CAMPAIGN, "run_campaign") as run,
            mock.patch.object(sys, "stdout", output),
        ):
            self.assertEqual(CAMPAIGN.main(argv), 0)
        run.assert_not_called()
        document = json.loads(output.buffer.getvalue())
        self.assertFalse(document["would_invoke_models"])
        self.assertEqual(document["item_count"], 32)
        self.assertEqual(len(document["items"]), 32)
        self.assertEqual(
            [command["stage"] for command in document["items"][0]["commands"]],
            list(CAMPAIGN.STAGES),
        )

    def test_cli_parses_explicit_parent_and_repeated_retry_scope(self) -> None:
        parent = self.base / "parent-cli/campaign-index.json"
        args = CAMPAIGN._parser().parse_args(
            [
                "--campaign-id",
                "unit-cli-retry",
                "--campaign-root",
                str(self.campaign_root),
                "--runtime-root",
                str(self.runtime),
                "--parent-campaign-index",
                str(parent),
                "--scope-id",
                self.ids[2],
                "--scope-id",
                self.ids[7],
                "--preflight",
            ]
        )
        config = CAMPAIGN._config(args)
        self.assertEqual(config.parent_campaign_index, parent)
        self.assertEqual(config.scope_ids, (self.ids[2], self.ids[7]))

    def test_preflight_rejects_existing_campaign_root_before_any_dispatch(self) -> None:
        self.campaign_root.mkdir()
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "never reused"):
            CAMPAIGN.preflight(self.config)

    def test_orchestrator_must_be_the_runtime_inventory_member(self) -> None:
        libexec = self.runtime / "libexec"
        libexec.mkdir()
        installed = libexec / "run_answer_blind_gpt_campaign.py"
        installed.write_bytes(SCRIPT.read_bytes())
        installed.chmod(0o444)
        interpreter = self.runtime / "python/bin/python3"
        interpreter.parent.mkdir(parents=True)
        interpreter.write_bytes(b"runtime-python")
        interpreter.chmod(0o555)
        relative = CAMPAIGN.RUNTIME_ORCHESTRATOR.as_posix()
        interpreter_relative = interpreter.relative_to(self.runtime).as_posix()
        inventory = {
            relative: CAMPAIGN._file_sha(installed),
            interpreter_relative: CAMPAIGN._file_sha(interpreter),
        }
        safe_flags = types.SimpleNamespace(
            isolated=1,
            ignore_environment=1,
            safe_path=True,
            no_user_site=1,
            dont_write_bytecode=1,
        )
        self.assertEqual(
            CAMPAIGN._orchestrator_runtime_binding(
                script_path=installed,
                runtime=self.runtime,
                inventory=inventory,
                executable=interpreter,
                startup_flags=safe_flags,
            ),
            (inventory[relative], inventory[interpreter_relative]),
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "sealed runtime entry"):
            CAMPAIGN._orchestrator_runtime_binding(
                script_path=SCRIPT,
                runtime=self.runtime,
                inventory=inventory,
                executable=interpreter,
                startup_flags=safe_flags,
            )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "absent or stale"):
            CAMPAIGN._orchestrator_runtime_binding(
                script_path=installed,
                runtime=self.runtime,
                inventory={
                    relative: "0" * 64,
                    interpreter_relative: inventory[interpreter_relative],
                },
                executable=interpreter,
                startup_flags=safe_flags,
            )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "outside"):
            CAMPAIGN._orchestrator_runtime_binding(
                script_path=installed,
                runtime=self.runtime,
                inventory=inventory,
                executable=Path(sys.executable),
                startup_flags=safe_flags,
            )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "interpreter.*stale"):
            CAMPAIGN._orchestrator_runtime_binding(
                script_path=installed,
                runtime=self.runtime,
                inventory={**inventory, interpreter_relative: "0" * 64},
                executable=interpreter,
                startup_flags=safe_flags,
            )
        for field in (
            "isolated",
            "ignore_environment",
            "safe_path",
            "no_user_site",
            "dont_write_bytecode",
        ):
            flags = types.SimpleNamespace(
                isolated=1,
                ignore_environment=1,
                safe_path=True,
                no_user_site=1,
                dont_write_bytecode=1,
            )
            setattr(flags, field, False)
            with self.subTest(flag=field), self.assertRaisesRegex(
                CAMPAIGN.CampaignError, "-I -B"
            ):
                CAMPAIGN._orchestrator_runtime_binding(
                    script_path=installed,
                    runtime=self.runtime,
                    inventory=inventory,
                    executable=interpreter,
                    startup_flags=flags,
                )

    def test_source_report_preflight_rejects_noncanonical_or_leaky_fields(self) -> None:
        path = self.seed.joinpath(*self.reports[self.ids[0]][0].parts)
        report = json.loads(path.read_text(encoding="utf-8"))
        report["answer"] = "must not enter a blind report"
        path.write_bytes(CAMPAIGN._json_bytes(report))
        with self.assertRaisesRegex(
            CAMPAIGN.CampaignError, "non-canonical top-level schema"
        ):
            CAMPAIGN._source_reports(self.seed, self.rows)

    def test_bundle_preflight_rejects_recursive_answer_key_fields(self) -> None:
        rows = {record_id: dict(row) for record_id, row in self.rows.items()}
        rows[self.ids[0]]["official_solution"] = "forbidden"
        path = self.base / "leaky-questions.jsonl"
        path.write_bytes(
            b"".join(CAMPAIGN._json_bytes(rows[item]) for item in self.ids)
        )
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "forbidden solver key"):
            CAMPAIGN._bundle_rows(path)

    def test_finalize_rejects_nonterminal_or_incomplete_32_item_index(self) -> None:
        self.campaign_root.mkdir()
        index_path = self.campaign_root / "campaign-index.json"
        value = CAMPAIGN._initial_index(self.binding)
        CAMPAIGN._atomic_index(index_path, value)
        writer = CAMPAIGN.IndexWriter(index_path, value)
        asyncio.run(writer.finalize())
        self.assertEqual(writer.value["status"], "failed")
        self.assertEqual(
            writer.value["integrity_error"],
            "campaign finalized with nonterminal items",
        )

        second_path = self.campaign_root / "incomplete-index.json"
        incomplete = CAMPAIGN._initial_index(self.binding)
        for row in incomplete["items"]:
            row["status"] = "succeeded"
            row["controller_seal_sha256"] = "a" * 64
            row["freeze_manifest_sha256"] = "b" * 64
            row["stages"] = {
                stage: {"status": "succeeded", "argv": ["/bin/true"]}
                for stage in CAMPAIGN.STAGES[:-1]
            }
        CAMPAIGN._atomic_index(second_path, incomplete)
        incomplete_writer = CAMPAIGN.IndexWriter(second_path, incomplete)
        asyncio.run(incomplete_writer.finalize())
        self.assertEqual(incomplete_writer.value["status"], "failed")
        self.assertIn(
            "does not bind every stage",
            incomplete_writer.value["integrity_error"],
        )

    def test_exception_path_publishes_final_index_sidecar(self) -> None:
        async def fail_after_final_index(
            _binding: CAMPAIGN.Binding, writer: CAMPAIGN.IndexWriter
        ) -> None:
            await writer.finalize(integrity_error="fixture orchestrator failure")
            raise RuntimeError("fixture crash")

        with (
            mock.patch.object(CAMPAIGN, "preflight", return_value=self.binding),
            mock.patch.object(
                CAMPAIGN, "_execute_and_finalize", new=fail_after_final_index
            ),
            self.assertRaisesRegex(RuntimeError, "fixture crash"),
        ):
            CAMPAIGN.run_campaign(self.config)
        index_path = self.campaign_root / "campaign-index.json"
        sidecar = self.campaign_root / "campaign-index.json.sha256"
        self.assertTrue(index_path.is_file())
        self.assertTrue(sidecar.is_file())
        self.assertEqual(sidecar.stat().st_mode & 0o777, 0o400)
        self.assertEqual(
            sidecar.read_text(encoding="ascii"),
            f"{CAMPAIGN._file_sha(index_path)}  {index_path.name}\n",
        )

    def test_absolute_path_validation_rejects_dangling_symlink(self) -> None:
        dangling = self.base / "dangling-campaign"
        dangling.symlink_to(self.base / "absent-target", target_is_directory=True)
        with self.assertRaisesRegex(CAMPAIGN.CampaignError, "symlink"):
            CAMPAIGN._safe_absolute(dangling, label="campaign root")

    def test_singleton_lock_rejects_second_controller(self) -> None:
        with CAMPAIGN._campaign_lock(self.config.singleton_lock):
            with self.assertRaisesRegex(CAMPAIGN.CampaignError, "singleton lock"):
                CAMPAIGN._assert_singleton_available(self.config.singleton_lock)
            with self.assertRaisesRegex(CAMPAIGN.CampaignError, "another campaign"):
                with CAMPAIGN._campaign_lock(self.config.singleton_lock):
                    self.fail("nested campaign lock unexpectedly succeeded")


if __name__ == "__main__":
    unittest.main()
