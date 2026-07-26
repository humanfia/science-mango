"""Versioned known-code registry for CSS and non-CSS stabilizer codes."""

from __future__ import annotations

import hashlib
import json
from functools import lru_cache
from pathlib import Path
from typing import Any

from evaluation.structural_dedup import canonical_digest
from evaluation.tanner_equivalence import canonical_hash_noncss


DEFAULT_REGISTRY = (
    Path(__file__).resolve().parent.parent / "results" / "known_code_registry.json"
)


def canonical_digest_noncss(code) -> str:
    digest = hashlib.sha256()
    for left, right in canonical_hash_noncss(code):
        digest.update(int(left).to_bytes(4, "little"))
        digest.update(int(right).to_bytes(4, "little"))
    return digest.hexdigest()


def canonical_json_sha256(value: Any, *, omit: str | None = None) -> str:
    if isinstance(value, dict) and omit:
        value = {key: item for key, item in value.items() if key != omit}
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


@lru_cache(maxsize=4)
def load_registry(path: str | Path = DEFAULT_REGISTRY) -> dict[str, Any]:
    registry = json.loads(Path(path).read_text())
    expected = canonical_json_sha256(registry, omit="registry_sha256")
    if registry.get("registry_sha256") != expected:
        raise ValueError("known-code registry SHA-256 mismatch")
    if registry.get("schema_version") != 1:
        raise ValueError("unsupported known-code registry schema")
    return registry


def check_code_novelty(
    code,
    *,
    code_type: str,
    registry_path: str | Path = DEFAULT_REGISTRY,
) -> dict[str, Any]:
    if code_type not in {"css", "noncss"}:
        raise ValueError("code_type must be css or noncss")
    digest = (
        canonical_digest(code)
        if code_type == "css"
        else canonical_digest_noncss(code)
    )
    n, k = int(code.num_qudits), int(code.dimension)
    registry = load_registry(registry_path)
    matches = [
        entry for entry in registry["entries"]
        if entry["code_type"] == code_type
        and int(entry["n"]) == n
        and int(entry["k"]) == k
        and entry["canonical_digest"] == digest
    ]
    return {
        "checked": True,
        "novel": not matches,
        "code_type": code_type,
        "canonical_digest": digest,
        "registry_version": registry["registry_version"],
        "registry_sha256": registry["registry_sha256"],
        "matched_entries": [
            {
                "id": entry["id"],
                "family": entry["family"],
                "provenance": entry["provenance"],
            }
            for entry in matches
        ],
    }
