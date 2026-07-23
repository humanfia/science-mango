from evaluation.matrix_certificate import CERTIFICATE_TYPE as MATRIX_CSS_TYPE
from evaluation.noncss_certificate import MATRIX_TYPE, PBB_TYPE
from scripts.finalize_challenge import VERIFIERS


def test_final_gate_dispatches_all_supported_certificate_types():
    assert set(VERIFIERS) == {
        "qldpc-css-bb-exact",
        MATRIX_CSS_TYPE,
        MATRIX_TYPE,
        PBB_TYPE,
    }
