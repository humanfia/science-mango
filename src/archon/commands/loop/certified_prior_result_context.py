"""A6-only consumer adapter for the controller-certified A4/A5 receipt.

All parsing, ownership, immutability, size, canonical-shape, and receipt-hash
checks live in :mod:`prior_result_dependency`.  This adapter only makes the
A6 receipt mandatory, binds it to the current consumer source projection, and
projects the small wrapper used by existing Review source contracts.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
import json
from pathlib import Path
from typing import Any

from .prior_result_dependency import (
    canonical_prior_result_value_sha256,
    load_prior_result_dependency_context_checked,
    prior_result_dependency_relative_path,
    render_prior_result_dependency_prompt,
)


REQUIRED_CERTIFIED_PRIOR_RESULT_CONSUMERS = frozenset({
    "icho_2026_t1_a6",
})


class CertifiedPriorResultContextError(ValueError):
    """Raised before model dispatch for a missing or stale A6 receipt."""


def canonical_value_sha256(value: Any) -> str:
    """Compatibility alias for the core receipt canonical hash."""

    return canonical_prior_result_value_sha256(value)


def uses_full_theory_inline_prior(project_path: Path, record_ids: Sequence[str]) -> bool:
    """An explicit fresh full68 campaign rederives priors instead of importing receipts."""
    config_path = project_path / ".archon/config.json"
    if config_path.is_symlink() or config_path.parent.is_symlink():
        raise CertifiedPriorResultContextError("inline-prior config must not be a symlink")
    if not config_path.exists():
        return False
    try:
        config = json.loads(config_path.read_text())
        enabled = config.get("loop", {}).get("rootless_full_theory") is True
    except (OSError, ValueError, AttributeError) as exc:
        raise CertifiedPriorResultContextError("invalid inline-prior config") from exc
    if not enabled:
        return False
    full_ids = {f"icho_2026_t{paper}_a{part}"
                for paper, count in enumerate((6, 7, 7, 9, 6, 7, 7, 10, 9), 1)
                for part in range(1, count + 1)}
    if len(record_ids) != 68 or set(record_ids) != full_ids:
        raise CertifiedPriorResultContextError("inline prior derivation requires the complete full68 scope")
    return True


def load_certified_prior_result_context(
    *,
    project_path: Path,
    consumer_record_id: str,
    consumer_target_rel: str,
    source_bundle_sha256: str,
    source_record_sha256: str,
    previous_parts: Sequence[Mapping[str, Any]],
    trusted_controller_uid: int,
) -> dict[str, Any]:
    """Load and bind the single A4/A5-to-A6 receipt.

    Other targets intentionally receive no receipt and keep their existing
    answer-blind derive-inline policy.
    """

    if consumer_record_id not in REQUIRED_CERTIFIED_PRIOR_RESULT_CONSUMERS:
        return {}
    if not previous_parts:
        raise CertifiedPriorResultContextError(
            "A6 certified prior-result receipt has no previous_parts binding"
        )

    receipt, reason = load_prior_result_dependency_context_checked(
        project_path,
        consumer_record_id,
        controller_uid=trusted_controller_uid,
    )
    if reason:
        if reason == "missing_receipt":
            message = "required certified prior-result context is missing"
        else:
            message = (
                "certified prior-result context failed controller trust check: "
                + reason
            )
        raise CertifiedPriorResultContextError(message)

    consumer = receipt.get("consumer")
    if not isinstance(consumer, Mapping):
        raise CertifiedPriorResultContextError(
            "certified prior-result receipt has no A6 consumer binding"
        )
    expected = {
        "source_id": consumer_record_id,
        "target": consumer_target_rel,
        "source_record_sha256": source_record_sha256,
        "previous_parts_sha256": canonical_value_sha256(list(previous_parts)),
        "source_bundle_sha256": source_bundle_sha256,
        "official_answer_seen": False,
    }
    for key, value in expected.items():
        if consumer.get(key) != value:
            raise CertifiedPriorResultContextError(
                f"certified prior-result A6 binding is stale: {key} changed"
            )

    receipt_sha256 = receipt.get("receipt_sha256")
    if not isinstance(receipt_sha256, str):
        raise CertifiedPriorResultContextError(
            "certified prior-result receipt hash is missing"
        )
    return {
        "path": prior_result_dependency_relative_path(
            consumer_record_id
        ).as_posix(),
        "sha256": receipt_sha256,
        "context_receipt_sha256": receipt_sha256,
        "context": receipt,
    }


def render_certified_prior_result_prompt(
    binding: Mapping[str, Any] | None,
) -> str:
    if not isinstance(binding, Mapping) or not binding:
        return ""
    receipt = binding.get("context")
    if not isinstance(receipt, Mapping):
        raise CertifiedPriorResultContextError(
            "certified prior-result binding has no receipt"
        )
    rendered = render_prior_result_dependency_prompt(receipt)
    if not rendered:
        raise CertifiedPriorResultContextError(
            "certified prior-result receipt could not be rendered"
        )
    return rendered


__all__ = [
    "CertifiedPriorResultContextError",
    "REQUIRED_CERTIFIED_PRIOR_RESULT_CONSUMERS",
    "canonical_value_sha256",
    "load_certified_prior_result_context",
    "render_certified_prior_result_prompt",
]
