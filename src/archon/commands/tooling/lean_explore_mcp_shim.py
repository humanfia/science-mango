"""Compatibility launcher for the official LeanExplore MCP server.

The current ``lean-explore mcp serve`` entry point has two sharp edges in the
environment Archon uses:

* LeanExplore's MCP tool module imports ``TypedDict`` from ``typing``. Pydantic
  v2 rejects that on Python < 3.12 when building FastMCP schemas; it requires
  ``typing_extensions.TypedDict`` instead.
* The LeanExplore CLI checks ``LEANEXPLORE_API_KEY`` but does not pass the env
  value down to ``lean_explore.mcp.server --api-key``.

This shim keeps the public MCP server and tools intact while fixing both at the
launcher boundary. It is intentionally small and can go away when upstream
LeanExplore no longer needs the compatibility layer.
"""

from __future__ import annotations

import argparse
import logging
import os
import sys
from pathlib import Path


def _patch_typed_dict_for_pydantic() -> None:
    """Make LeanExplore MCP's ``from typing import TypedDict`` Pydantic-safe."""
    if sys.version_info >= (3, 12):
        return
    try:
        import typing
        from typing_extensions import TypedDict as ExtensionsTypedDict
    except Exception:
        return
    typing.TypedDict = ExtensionsTypedDict  # type: ignore[attr-defined]


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Archon compatibility launcher for LeanExplore MCP."
    )
    # Accept the official CLI's leading words too, so this shim can be used as
    # a drop-in ``lean_explore_bin`` command if needed.
    parser.add_argument("prefix", nargs="*", help=argparse.SUPPRESS)
    parser.add_argument(
        "--backend",
        choices=("api", "local"),
        default="api",
        help="LeanExplore backend to use.",
    )
    parser.add_argument(
        "--api-key",
        default=None,
        help="LeanExplore API key. Prefer LEANEXPLORE_API_KEY env instead.",
    )
    parser.add_argument(
        "--log-level",
        choices=("DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"),
        default="ERROR",
    )
    return parser


def _init_backend(backend: str, api_key: str | None):
    if backend == "api":
        key = api_key or os.environ.get("LEANEXPLORE_API_KEY") or _project_env_api_key()
        if not key:
            raise RuntimeError(
                "API key required for LeanExplore MCP api backend. "
                "Set LEANEXPLORE_API_KEY or use --api-key."
            )
        from lean_explore.api import ApiClient

        return ApiClient(api_key=key)

    from lean_explore.config import Config

    if not Config.DATABASE_PATH.exists():
        raise RuntimeError(
            "LeanExplore local backend data is missing. Run "
            "`lean-explore data fetch` first, or use --backend api with "
            "LEANEXPLORE_API_KEY."
        )

    from lean_explore.search import SearchEngine, Service

    return Service(engine=SearchEngine(use_local_data=False))


def _project_env_api_key(env: dict[str, str] | None = None) -> str | None:
    """Read LEANEXPLORE_API_KEY from a project-local `.archon/.env`.

    Codex's MCP launcher does not reliably inherit the parent process
    environment. Passing the secret in `mcp_servers.*.env` would put it in the
    `codex exec -c ...` argv, so the launcher passes only `ARCHON_PROJECT_PATH`
    and this shim loads the project-local env file in-process.
    """
    src = env if env is not None else os.environ
    project = src.get("ARCHON_PROJECT_PATH") or os.getcwd()
    path = Path(project) / ".archon" / ".env"
    try:
        lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    except OSError:
        return None
    for raw in lines:
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        if key.strip() != "LEANEXPLORE_API_KEY":
            continue
        value = value.strip().strip('"').strip("'")
        return value or None
    return None


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    logging.basicConfig(
        level=getattr(logging, args.log_level, logging.ERROR),
        stream=sys.stderr,
    )

    # Drop optional "mcp serve" prefix when invoked as a lean-explore binary
    # replacement. argparse keeps it in ``prefix`` only because the options are
    # the real contract here.
    prefix = [p.lower() for p in args.prefix]
    if prefix and prefix != ["mcp", "serve"]:
        print(
            "Unsupported LeanExplore MCP shim prefix: " + " ".join(args.prefix),
            file=sys.stderr,
        )
        return 2

    _patch_typed_dict_for_pydantic()

    try:
        # Import tools only after the TypedDict compatibility patch; importing
        # this module registers the FastMCP tools.
        from lean_explore.mcp import tools  # noqa: F401
        from lean_explore.mcp.app import mcp_app

        backend = _init_backend(args.backend, args.api_key)
        mcp_app._lean_explore_backend_service = backend
        mcp_app.run(transport="stdio")
    except Exception as exc:
        logging.exception("LeanExplore MCP shim failed")
        print(f"LeanExplore MCP shim failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
