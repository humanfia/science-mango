"""Tests for benchmark-local LeanExplore overlay indexes."""

from __future__ import annotations

import asyncio
import tempfile
import unittest
from pathlib import Path

from lean_explore.models import SearchResponse, SearchResult

from archon.commands.tooling.lean_explore_overlay import (
    CompositeLeanExploreService,
    ProjectOverlayIndex,
)
from archon.commands.tooling.project_lean_index import build_project_index


class ProjectLeanIndexTests(unittest.TestCase):
    def test_lake_dependency_sources_keep_their_lean_module_name(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            project = Path(temp_dir)
            source = project / ".lake/packages/crnt-lean/CRNT/Basic/Reaction.lean"
            source.parent.mkdir(parents=True)
            source.write_text(
                "namespace CRNT\n\n/-- A reaction. -/\n"
                "structure Reaction where\n  source : Nat\n\nend CRNT\n",
                encoding="utf-8",
            )

            payload = build_project_index(
                project,
                source_roots=[source.parent.parent.parent],
                package="Chemistry",
                output_path=project / ".archon/lean-explore/project-index.json",
            )

            self.assertEqual(payload["declarations"][0]["name"], "CRNT.Reaction")
            self.assertEqual(
                payload["declarations"][0]["module"], "CRNT.Basic.Reaction"
            )

    def _index(self, root: Path) -> Path:
        source = root / "QBench" / "Base.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "@[expose] public section\n"
            "namespace QBench\n\n"
            "noncomputable section\n"
            "section Inner\n"
            "/-- A normalized quantum state. -/\n"
            "def normalizedState (x : Nat) : Prop := x = x\n\n"
            "theorem normalizedState_self (x : Nat) : normalizedState x := by\n"
            "  rfl\n\n"
            "end Inner\n"
            "end\n"
            "end QBench\n"
            "end\n",
            encoding="utf-8",
        )
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
        output = root / ".archon" / "lean-explore" / "project-index.json"
        payload = build_project_index(
            root,
            source_roots=[Path("QBench/Base.lean")],
            package="QBench",
            output_path=output,
            repo_url="https://github.com/example/QBench",
            commit="abc123",
        )
        self.assertEqual(payload["declaration_count"], 2)
        self.assertEqual(
            [item["name"] for item in payload["declarations"]],
            ["QBench.normalizedState", "QBench.normalizedState_self"],
        )
        self.assertEqual(payload["lean_toolchain"], "leanprover/lean4:v4.31.0")
        self.assertIn("/blob/abc123/QBench/Base.lean#L", payload["declarations"][0]["source_link"])
        return output

    def test_build_and_search_project_index(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            index_path = self._index(Path(directory))
            overlay = ProjectOverlayIndex(index_path)

            matches = overlay.search(
                "normalized quantum state",
                limit=5,
                packages=["Mathlib", "QBench"],
            )

        self.assertTrue(matches)
        self.assertLess(matches[0].id, 0)
        self.assertEqual(matches[0].name, "QBench.normalizedState")
        self.assertEqual(
            overlay.search("normalized", limit=5, packages=["Mathlib"]),
            [],
        )

    def test_composite_service_prioritizes_overlay_and_routes_ids(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            overlay = ProjectOverlayIndex(self._index(Path(directory)))

            class BaseService:
                async def search(self, **_kwargs) -> SearchResponse:
                    return SearchResponse(
                        query="normalized",
                        results=[
                            SearchResult(
                                id=7,
                                name="Mathlib.normalized",
                                module="Mathlib",
                                docstring=None,
                                source_text="theorem normalized : True := by trivial",
                                source_link="https://example.invalid",
                                dependencies=None,
                                informalization="**Normalized.** Mathlib result.",
                            )
                        ],
                        count=1,
                    )

                async def get_by_id(self, declaration_id: int) -> SearchResult | None:
                    if declaration_id == 7:
                        return (await self.search()).results[0]
                    return None

            service = CompositeLeanExploreService(BaseService(), overlay)
            response = asyncio.run(
                service.search(
                    "normalized",
                    limit=5,
                    rerank_top=0,
                    packages=["Mathlib", "QBench"],
                )
            )
            project_result = response.results[0]
            fetched = asyncio.run(service.get_by_id(project_result.id))

        self.assertEqual(project_result.name, "QBench.normalizedState")
        self.assertEqual(response.results[-1].name, "Mathlib.normalized")
        self.assertIsNotNone(fetched)
        self.assertEqual(fetched.name, project_result.name)


if __name__ == "__main__":
    unittest.main()
