"""Single dispatch point for every supported qLDPC certificate schema."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Callable

from evaluation.certificate import build_css_certificate, verify_css_certificate
from evaluation.matrix_certificate import (
    CERTIFICATE_TYPE as MATRIX_CSS_TYPE,
    build_matrix_css_certificate,
    verify_matrix_css_certificate,
)
from evaluation.noncss_certificate import (
    MATRIX_TYPE as NONCSS_MATRIX_TYPE,
    PBB_TYPE,
    build_noncss_certificate,
    verify_noncss_certificate,
)


BB_CSS_TYPE = "qldpc-css-bb-exact"
SUPPORTED_CERTIFICATE_TYPES = (
    BB_CSS_TYPE,
    MATRIX_CSS_TYPE,
    PBB_TYPE,
    NONCSS_MATRIX_TYPE,
)

Builder = Callable[..., dict[str, Any]]
Verifier = Callable[..., dict[str, Any]]

VERIFIERS: dict[str, Verifier] = {
    BB_CSS_TYPE: verify_css_certificate,
    MATRIX_CSS_TYPE: verify_matrix_css_certificate,
    PBB_TYPE: verify_noncss_certificate,
    NONCSS_MATRIX_TYPE: verify_noncss_certificate,
}


def builder_for_claim(claim: dict[str, Any]) -> Builder:
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
    if builder is build_css_certificate:
        kwargs.update({
            "checkpoint_path": checkpoint_path,
            "resume": resume,
            "solver_workers": solver_workers,
        })
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
    kwargs: dict[str, Any] = {
        "known_answer_artifact": known_answer_artifact,
        "rerun_milp": rerun_milp,
        "timeout_per_logical": timeout_per_logical,
    }
    if verifier is verify_css_certificate:
        kwargs.update({
            "checkpoint_path": checkpoint_path,
            "resume": resume,
            "total_timeout": total_timeout,
            "solver_workers": solver_workers,
        })
    return verifier(
        certificate,
        **kwargs,
    )
