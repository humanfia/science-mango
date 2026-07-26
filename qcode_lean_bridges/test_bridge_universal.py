from bridge_universal import (
    certificate_payload,
    render_module,
)


def packed(bits):
    value = 0
    for index, bit in enumerate(bits):
        value |= bit << index
    raw = value.to_bytes((len(bits) + 7) // 8, "little")
    import hashlib
    return {
        "length": len(bits),
        "weight": sum(bits),
        "packed_hex": raw.hex(),
        "sha256": hashlib.sha256(f"{len(bits)}:".encode() + raw).hexdigest(),
    }


def matrix(rows):
    return {"rows": len(rows), "cols": len(rows[0]), "data": [packed(row) for row in rows]}


def test_generic_symplectic_certificate_renders_exact_theorem():
    certificate = {
        "certificate_type": "qldpc-noncss-matrix-exact",
        "certificate_sha256": "a" * 64,
        "passed": True,
        "claim": {
            "n": 2, "k": 1, "d": 1,
            "symplectic_stabilizer": matrix([[1, 1, 0, 0]]),
        },
        "milp": {"directions": [
            {"target_logical": packed([1, 0, 0, 0])},
            {"target_logical": packed([0, 0, 1, 1])},
        ]},
        "upper_witness": {"operator": packed([1, 0, 0, 0])},
    }
    payload = certificate_payload(certificate)
    source = render_module(payload, "Smoke", sat_timeout=30)
    assert payload["n"] == 2
    assert len(payload["logicals"]) == 2
    assert "theorem distance_lower" in source
    assert "bv_decide" in source
    assert "theorem exact_parameters" in source
