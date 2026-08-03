"""Public challenge-gate API.

The current final verifier supports CSS BB claims.  PBB/non-CSS records are
rejected explicitly instead of being accidentally evaluated as their CSS
``A,B`` projection.

This API validates stored proof structure.  Formal release code must also run
``evaluation.certificate_dispatch.verify_certificate``; self-hashed SAT
``UNSAT`` evidence is not a standalone proof-carrying certificate.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any

from evaluation.final_gate import evaluate_final_gate


def evaluate_challenge_gate(
    row: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
) -> dict[str, Any]:
    if row.get("C_terms") or row.get("D_terms"):
        return {
            "schema_version": 1,
            "gate": "qldpc-challenge-final",
            "accepted": False,
            "checks": {"css_bb_candidate": False},
            "failures": [
                "PBB/non-CSS final claims are not supported by the CSS gate"
            ],
        }
    result = evaluate_final_gate(
        row,
        known_answer_artifact=known_answer_artifact,
    )
    result["checks"]["css_bb_candidate"] = True
    return result
