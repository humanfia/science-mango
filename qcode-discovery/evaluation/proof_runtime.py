"""Canonical runtime identity for every proof-producing code path."""

from __future__ import annotations

import importlib.metadata
import platform
from typing import Any, Mapping


PROOF_RUNTIME_SCHEMA_VERSION = 1
SOLVER_RUNTIME_PACKAGES = (
    "numpy",
    "ortools",
    "qldpc",
    "scipy",
    "highspy",
)
KNOWN_ANSWER_RUNTIME_PACKAGES = ("numpy", "scipy", "qldpc")


def _package_version(name: str) -> str | None:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return None


def proof_runtime_fingerprint() -> dict[str, Any]:
    """Return one strict, JSON-serializable identity for proof runtimes."""

    return {
        "schema_version": PROOF_RUNTIME_SCHEMA_VERSION,
        "python": {
            "implementation": platform.python_implementation(),
            "version": platform.python_version(),
        },
        "packages": {
            name: _package_version(name)
            for name in SOLVER_RUNTIME_PACKAGES
        },
    }


def known_answer_environment(
    runtime: Mapping[str, Any] | None = None,
) -> dict[str, str | None]:
    """Project the proof runtime onto the frozen known-answer schema."""

    runtime = proof_runtime_fingerprint() if runtime is None else runtime
    python = runtime.get("python")
    packages = runtime.get("packages")
    if (
        runtime.get("schema_version") != PROOF_RUNTIME_SCHEMA_VERSION
        or not isinstance(python, Mapping)
        or not isinstance(python.get("implementation"), str)
        or not python["implementation"]
        or not isinstance(python.get("version"), str)
        or not python["version"]
        or not isinstance(packages, Mapping)
    ):
        raise ValueError("proof runtime fingerprint is malformed")
    environment: dict[str, str | None] = {
        "python": python["version"],
    }
    for name in KNOWN_ANSWER_RUNTIME_PACKAGES:
        value = packages.get(name)
        if value is not None and not isinstance(value, str):
            raise ValueError(
                f"proof runtime package version for {name} is malformed",
            )
        environment[name] = value
    return environment


__all__ = [
    "KNOWN_ANSWER_RUNTIME_PACKAGES",
    "PROOF_RUNTIME_SCHEMA_VERSION",
    "SOLVER_RUNTIME_PACKAGES",
    "known_answer_environment",
    "proof_runtime_fingerprint",
]
