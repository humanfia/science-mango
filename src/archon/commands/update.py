"""Update Archon by re-running the remote install script."""

import subprocess

from archon import log


def update() -> None:
    """Update Archon to the latest version."""
    log.step("Fetching and running the Archon install script...")
    r = subprocess.run(
        ["bash", "-c",
         "curl -sSL https://raw.githubusercontent.com/frenzymath/Archon/refs/heads/main/install.sh | bash"],
        text=True,
    )
    if r.returncode != 0:
        log.error("Update failed — the install script exited with an error.")
        raise SystemExit(r.returncode)
    log.success("Archon updated successfully.")
    log.warn(
        "If you created a project with an older version of Archon, consider "
        "re-running `archon init` in your project directory to ensure no "
        "template files are outdated."
    )