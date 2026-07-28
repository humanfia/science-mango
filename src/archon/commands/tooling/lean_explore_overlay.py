"""LeanExplore MCP backend combining the global index with a project overlay."""

from __future__ import annotations

import argparse
import json
import logging
import re
import time
from pathlib import Path
from typing import Iterable

from lean_explore.models import SearchResponse, SearchResult


_TOKEN_RE = re.compile(r"[A-Za-z0-9_']+")


def _tokens(text: str) -> list[str]:
    spaced = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", text)
    return [token.lower() for token in _TOKEN_RE.findall(spaced)]


class ProjectOverlayIndex:
    """In-memory lexical index over one benchmark-local Lean Base library."""

    def __init__(self, path: Path) -> None:
        self.path = path.resolve()
        payload = json.loads(self.path.read_text(encoding="utf-8"))
        if payload.get("schema_version") != 1:
            raise ValueError(f"unsupported project index schema: {self.path}")
        self.package = str(payload.get("package") or "").strip()
        self.metadata = payload
        self._by_id: dict[int, SearchResult] = {}
        self._search_text: dict[int, tuple[str, str, str]] = {}
        for offset, declaration in enumerate(payload.get("declarations", []), 1):
            declaration_id = -offset
            dependencies = declaration.get("dependencies")
            result = SearchResult(
                id=declaration_id,
                name=str(declaration["name"]),
                module=str(declaration["module"]),
                docstring=declaration.get("docstring"),
                source_text=str(declaration.get("source_text") or ""),
                source_link=str(declaration.get("source_link") or ""),
                dependencies=(
                    json.dumps(dependencies, ensure_ascii=False)
                    if isinstance(dependencies, list)
                    else dependencies
                ),
                informalization=declaration.get("informalization"),
            )
            self._by_id[declaration_id] = result
            self._search_text[declaration_id] = (
                result.name.lower(),
                result.module.lower(),
                " ".join(
                    str(value or "")
                    for value in (
                        result.docstring,
                        result.informalization,
                        result.source_text,
                    )
                ).lower(),
            )

    def accepts_packages(self, packages: Iterable[str] | None) -> bool:
        if not packages:
            return True
        accepted = set(packages)
        module_prefix = self.package.split(".", 1)[0]
        return self.package in accepted or module_prefix in accepted

    def search(
        self,
        query: str,
        *,
        limit: int,
        packages: Iterable[str] | None,
    ) -> list[SearchResult]:
        if not self.accepts_packages(packages):
            return []
        query_text = query.strip().lower()
        query_tokens = _tokens(query)
        scored: list[tuple[float, str, SearchResult]] = []
        for declaration_id, result in self._by_id.items():
            name, module, body = self._search_text[declaration_id]
            score = 0.0
            if query_text and query_text == name:
                score += 200.0
            elif query_text and query_text in name:
                score += 80.0
            for token in query_tokens:
                if token in name:
                    score += 18.0
                if token in module:
                    score += 5.0
                if token in body:
                    score += 2.0
            if score:
                scored.append((score, result.name, result))
        scored.sort(key=lambda item: (-item[0], item[1]))
        return [result for _, _, result in scored[: max(0, limit)]]

    def get_by_id(self, declaration_id: int) -> SearchResult | None:
        return self._by_id.get(declaration_id)


class CompositeLeanExploreService:
    """Service interface expected by the upstream LeanExplore MCP tools."""

    def __init__(self, base_service, overlay: ProjectOverlayIndex) -> None:
        self.base_service = base_service
        self.overlay = overlay

    async def search(
        self,
        query: str,
        limit: int = 20,
        rerank_top: int | None = 50,
        packages: list[str] | None = None,
    ) -> SearchResponse:
        started = time.monotonic()
        overlay_results = self.overlay.search(
            query,
            limit=limit,
            packages=packages,
        )
        base_packages = packages
        if packages and self.overlay.accepts_packages(packages):
            overlay_names = {
                self.overlay.package,
                self.overlay.package.split(".", 1)[0],
            }
            remaining = [item for item in packages if item not in overlay_names]
            base_packages = remaining or None
            run_base = bool(remaining)
        else:
            run_base = True

        base_results: list[SearchResult] = []
        if run_base:
            response = await self.base_service.search(
                query=query,
                limit=limit,
                rerank_top=rerank_top,
                packages=base_packages,
            )
            base_results = list(response.results)

        merged: list[SearchResult] = []
        seen: set[str] = set()
        for result in [*overlay_results, *base_results]:
            if result.name in seen:
                continue
            seen.add(result.name)
            merged.append(result)
            if len(merged) >= limit:
                break
        return SearchResponse(
            query=query,
            results=merged,
            count=len(merged),
            processing_time_ms=int((time.monotonic() - started) * 1000),
        )

    async def get_by_id(self, declaration_id: int) -> SearchResult | None:
        if declaration_id < 0:
            return self.overlay.get_by_id(declaration_id)
        return await self.base_service.get_by_id(declaration_id)

    async def close(self) -> None:
        engine = getattr(getattr(self.base_service, "engine", None), "engine", None)
        if engine is not None:
            await engine.dispose()


def serve(index_path: Path, host: str, port: int) -> None:
    from lean_explore.mcp import tools as _registered_tools  # noqa: F401
    from lean_explore.mcp.app import mcp_app
    from lean_explore.search import SearchEngine, Service

    overlay = ProjectOverlayIndex(index_path)
    base = Service(engine=SearchEngine(use_local_data=False))
    mcp_app._lean_explore_backend_service = CompositeLeanExploreService(
        base,
        overlay,
    )
    mcp_app.settings.host = host
    mcp_app.settings.port = port
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )
    mcp_app.run(transport="streamable-http")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Serve global LeanExplore plus a project-local overlay."
    )
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, required=True)
    args = parser.parse_args()
    serve(args.index, args.host, args.port)


if __name__ == "__main__":
    main()
