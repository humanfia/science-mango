from evaluation.certificate_dispatch import SUPPORTED_CERTIFICATE_TYPES


def test_final_gate_dispatches_all_supported_certificate_types():
    assert len(SUPPORTED_CERTIFICATE_TYPES) == 6
