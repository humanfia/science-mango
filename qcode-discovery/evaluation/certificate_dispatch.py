"""Single dispatch point for every supported qLDPC certificate schema."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Callable, Mapping

from evaluation.certificate import build_css_certificate, verify_css_certificate
from evaluation.matrix_certificate import (
    CERTIFICATE_TYPE as MATRIX_CSS_TYPE,
)
from evaluation.matrix_certificate import (
    build_matrix_css_certificate,
    verify_matrix_css_certificate,
)
from evaluation.noncss_certificate import (
    MATRIX_TYPE as NONCSS_MATRIX_TYPE,
)
from evaluation.noncss_certificate import (
    PBB_TYPE,
    build_noncss_certificate,
    verify_noncss_certificate,
)
from evaluation.sector_certificate import (
    CERTIFICATE_TYPE as SECTOR_SAT_CSS_TYPE,
    REQUEST_FIELD as SECTOR_SAT_REQUEST_FIELD,
    build_sector_sat_certificate,
    verify_sector_sat_certificate,
)
from evaluation.twobga_certificate import (
    CERTIFICATE_TYPE as TWOBGA_CSS_TYPE,
    build_twobga_certificate,
    verify_twobga_certificate,
)
from scripts.screen_frontier_twobga import TWOBGA_REQUEST_FIELD

BB_CSS_TYPE = "qldpc-css-bb-exact"
SUPPORTED_CERTIFICATE_TYPES = (
    BB_CSS_TYPE,
    MATRIX_CSS_TYPE,
    PBB_TYPE,
    NONCSS_MATRIX_TYPE,
    SECTOR_SAT_CSS_TYPE,
    TWOBGA_CSS_TYPE,
)
CHECKPOINT_CERTIFICATE_TYPES = frozenset({
    BB_CSS_TYPE,
    MATRIX_CSS_TYPE,
    SECTOR_SAT_CSS_TYPE,
    TWOBGA_CSS_TYPE,
})

Builder = Callable[..., dict[str, Any]]
Verifier = Callable[..., dict[str, Any]]

VERIFIERS: dict[str, Verifier] = {
    BB_CSS_TYPE: verify_css_certificate,
    MATRIX_CSS_TYPE: verify_matrix_css_certificate,
    PBB_TYPE: verify_noncss_certificate,
    NONCSS_MATRIX_TYPE: verify_noncss_certificate,
    SECTOR_SAT_CSS_TYPE: verify_sector_sat_certificate,
    TWOBGA_CSS_TYPE: verify_twobga_certificate,
}


def builder_for_claim(claim: dict[str, Any]) -> Builder:
    if claim.get(TWOBGA_REQUEST_FIELD) is not None:
        return build_twobga_certificate
    # Compact constructions are always independently rebuilt into the generic
    # matrix certificate.  A Stage 3 SAT request is useful screening evidence,
    # but is not allowed to switch them back into the BB-only sector builder.
    if isinstance(claim.get("construction"), Mapping):
        return build_matrix_css_certificate
    if claim.get(SECTOR_SAT_REQUEST_FIELD) is not None:
        return build_sector_sat_certificate
    if claim.get("H_X") is not None or claim.get("hx") is not None:
        return build_matrix_css_certificate
    if (
        claim.get("symplectic_stabilizer") is not None
        or claim.get("C_terms")
        or claim.get("D_terms")
    ):
        return build_noncss_certificate
    return build_css_certificate


def build_certificate(
    claim: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    timeout_per_logical: float = 300,
    total_timeout: float = 7200,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    solver_workers: int = 1,
) -> dict[str, Any]:
    builder = builder_for_claim(claim)
    kwargs: dict[str, Any] = {
        "known_answer_artifact": known_answer_artifact,
        "timeout_per_logical": timeout_per_logical,
        "total_timeout": total_timeout,
    }
    # Select capabilities from the claim schema, not callable identity.  The
    # latter is brittle under instrumentation/monkeypatching and can silently
    # drop resume controls from an otherwise supported builder.
    noncss_claim = bool(
        claim.get("symplectic_stabilizer") is not None
        or claim.get("C_terms")
        or claim.get("D_terms")
    )
    if not noncss_claim:
        kwargs.update(
            {
                "checkpoint_path": checkpoint_path,
                "resume": resume,
                "solver_workers": solver_workers,
            }
        )
    return builder(
        claim,
        **kwargs,
    )


def verifier_for_certificate(certificate: dict[str, Any]) -> Verifier:
    certificate_type = certificate.get("certificate_type")
    verifier = VERIFIERS.get(str(certificate_type))
    if verifier is None:
        raise ValueError(f"unsupported certificate_type: {certificate_type!r}")
    return verifier


def verify_certificate(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path | str,
    rerun_milp: bool = True,
    timeout_per_logical: float | None = None,
    checkpoint_path: Path | str | None = None,
    resume: bool = False,
    total_timeout: float | None = None,
    solver_workers: int = 1,
) -> dict[str, Any]:
    verifier = verifier_for_certificate(certificate)
    certificate_type = str(certificate.get("certificate_type"))
    kwargs: dict[str, Any] = {
        "known_answer_artifact": known_answer_artifact,
        "rerun_milp": rerun_milp,
        "timeout_per_logical": timeout_per_logical,
        "total_timeout": total_timeout,
        "solver_workers": solver_workers,
    }
    if certificate_type in CHECKPOINT_CERTIFICATE_TYPES:
        kwargs.update(
            {
                "checkpoint_path": checkpoint_path,
                "resume": resume,
            }
        )
    return verifier(
        certificate,
        **kwargs,
    )
