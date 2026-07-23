import pytest

from evaluation.certificate import build_css_certificate
from evaluation.certificate_dispatch import (
    BB_CSS_TYPE,
    SUPPORTED_CERTIFICATE_TYPES,
    builder_for_claim,
    verifier_for_certificate,
)
from evaluation.matrix_certificate import build_matrix_css_certificate
from evaluation.noncss_certificate import build_noncss_certificate


def test_builder_dispatches_every_claim_shape():
    assert builder_for_claim({"ell": 6, "m": 6}) is build_css_certificate
    assert builder_for_claim({"H_X": [[1]], "H_Z": [[0]]}) is build_matrix_css_certificate
    assert builder_for_claim({"C_terms": [[0, 0]]}) is build_noncss_certificate
    assert builder_for_claim({"symplectic_stabilizer": [[1, 0]]}) is build_noncss_certificate


def test_verifier_dispatch_is_fail_closed():
    assert len(SUPPORTED_CERTIFICATE_TYPES) == 4
    assert verifier_for_certificate({"certificate_type": BB_CSS_TYPE})
    with pytest.raises(ValueError, match="unsupported certificate_type"):
        verifier_for_certificate({"certificate_type": "untrusted"})
