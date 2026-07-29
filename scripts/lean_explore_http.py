#!/usr/bin/env python3
"""Run the cached LeanExplore backend as a shared streamable-HTTP MCP server."""

import logging

from lean_explore.config import Config
from lean_explore.mcp import tools as _registered_tools  # noqa: F401
from lean_explore.mcp.app import mcp_app
from lean_explore.search import SearchEngine, Service


def main() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )
    if not Config.DATABASE_PATH.exists():
        raise FileNotFoundError(
            f"LeanExplore database not found: {Config.DATABASE_PATH}"
        )

    engine = SearchEngine(use_local_data=False)
    mcp_app._lean_explore_backend_service = Service(engine=engine)
    mcp_app.settings.host = "127.0.0.1"
    mcp_app.settings.port = 8765
    mcp_app.run(transport="streamable-http")


if __name__ == "__main__":
    main()
