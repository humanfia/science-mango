#!/usr/bin/env python3
"""Serve hosted Mathlib/Physlib search plus the local chemistry overlay."""

from __future__ import annotations

import logging
import os
from pathlib import Path

from archon.commands.tooling.lean_explore_overlay import (
    CompositeLeanExploreService,
    ProjectOverlayIndex,
)
from lean_explore.api import ApiClient
from lean_explore.mcp import tools as _registered_tools  # noqa: F401
from lean_explore.mcp.app import mcp_app


def main() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )
    project = Path(os.environ.get("ARCHON_PROJECT_PATH", Path(__file__).parents[1]))
    index_path = project / ".archon/lean-explore/project-index.json"
    overlay = ProjectOverlayIndex(index_path)
    mcp_app._lean_explore_backend_service = CompositeLeanExploreService(
        ApiClient(), overlay
    )
    mcp_app.settings.host = "127.0.0.1"
    mcp_app.settings.port = 8765
    mcp_app.run(transport="streamable-http")


if __name__ == "__main__":
    main()
