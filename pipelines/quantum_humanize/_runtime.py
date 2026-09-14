"""Read-only provenance check for the pinned humanize installation."""

import importlib.metadata
import json
import subprocess
import sys
from pathlib import Path
from urllib.parse import unquote, urlparse

from ._tasks import UPSTREAM_COMMIT


def runtime_pin():
    """Check the installed package's provenance without printing credential URLs."""
    dist = importlib.metadata.distribution("hmz")
    direct = json.loads(dist.read_text("direct_url.json") or "{}")
    commit = direct.get("vcs_info", {}).get("commit_id")
    parsed = urlparse(direct.get("url", ""))
    if parsed.scheme == "file":
        source = Path(unquote(parsed.path))
        commit = subprocess.check_output(
            ["git", "-C", str(source), "rev-parse", "HEAD"], text=True, timeout=10
        ).strip()
        dirty = subprocess.run(
            ["git", "-C", str(source), "diff", "--quiet", "HEAD", "--",
             "src", "pyproject.toml", "uv.lock"], timeout=10, check=False
        )
        if dirty.returncode:
            raise ValueError("humanize runtime has local tracked code changes")
        extra = subprocess.check_output(
            ["git", "-C", str(source), "ls-files", "--others", "--exclude-standard", "--", "src"],
            text=True, timeout=10,
        )
        if extra.strip():
            raise ValueError("humanize runtime has untracked source files")
    if commit != UPSTREAM_COMMIT:
        raise ValueError("hmz must be installed from the pinned upstream commit")
    return {"hmz_version": dist.version, "upstream_commit": commit, "python": sys.version.split()[0]}
