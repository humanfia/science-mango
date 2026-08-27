"""Fail-closed logical-symmetry certificate for the paper Dic5 code.

This is the production successor to the exploratory logical-symmetry audit.
It validates all source hashes, shapes, CSS logical duality, Tanner generator
identities, and the identity logical action before any orbit enumeration.
Every finite closure has an explicit size cap and every orbit loop has a
progress guard.
"""

from __future__ import annotations

import copy
import hashlib
import json
from collections import Counter
from typing import Any, Sequence

import numpy as np

from evaluation import paper400_dic5_xz_isometry as dic5


METHOD = "paper400-dic5-full-sector-logical-normalization-final-v1"
SCHEMA_VERSION = 1
PHYSICAL_GROUP_ORDER = 200
LOGICAL_ACTION_ORDER = 100
EXPECTED_LOGICAL_BASIS_SHA256 = {
    "L_X": "ae5dbf5b0e50f80ff9f09a845f0eb2cbac6f98979eeb44b71d05a27433bfcd49",
    "L_Z": "4f2e07b817ec93436d98ff3ceac96359d4221c4774a71c3c6fe19dd1fe7e3f2e",
}
EXPECTED_GENERATOR_SHA256 = {
    "T": {
        "qubits": "8382054bafa5c5accddfcc4d5d19379307e6ec770eb69d8915d4dd021dba17d6",
        "x_rows": "a7d1c35be921bbbe762ac3d65c9bf62ff25500b118389ef23f1610119146f2c5",
        "z_rows": "a7d1c35be921bbbe762ac3d65c9bf62ff25500b118389ef23f1610119146f2c5",
    },
    "U": {
        "qubits": "caff505643b4639d8076fdd4ef53d34ae1f66e42d62b46113c2d83c1e5a9ec1e",
        "x_rows": "a6f49f4e7746cae540aaffa91fa9f23174e66d9da8ae87aeebec25165eafea16",
        "z_rows": "f7e517ee9fd2c8510c5947565ef524aaa7f217dd6d6601bb53cf2099c486a0b0",
    },
    "V": {
        "qubits": "68bae94f7fa36419b21910dfb15eeb4f30258b2e152a6c389e56ef1fb79dc966",
        "x_rows": "a961f652f5f3c3f3999efc174d4721716484992797a4e33e465480b509452bb6",
        "z_rows": "f6c4cc075d9585e2982622b5913eaeaed599ab69e08617e3c67d966d7a3826e3",
    },
    "W": {
        "qubits": "3ebc61402b47331bd5f4aba9e1f2a6badc7308d81734ce6b250a97775488b979",
        "x_rows": "8bf8537a355b38f62e811043cb66c55e9ac179045040374af9301132de7c48da",
        "z_rows": "9fc7882c07eab305610779f7820aaf4365c5865df38b47e5d711ab874da3792a",
    },
}
EXPECTED_QUBIT_ORBIT_SHA256 = (
    "bd614c0bc7b65d7b50c6f2a2435b9fa1e0121102bcd4f915bd6781c568e5500a"
)
JOINT_TARGETS = {
    0: (0, 40, 18, 29, 199, 35, 12, 181),
    1: (1, 41, 19, 38, 7, 47, 5, 32),
    200: (200, 240, 202, 301, 284, 324, 286, 239),
    201: (201, 241, 203, 310, 287, 327, 289, 394),
}

_VALID_REPORT_CACHE: dict[tuple[str, ...], dict[str, Any]] = {}


def _sha(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode()
    ).hexdigest()


def _safe_matrix_hash(value: np.ndarray) -> str:
    array = np.ascontiguousarray(np.asarray(value, dtype=np.uint8) & 1)
    if array.ndim == 2:
        return dic5._matrix_sha256(array)
    digest = hashlib.sha256()
    digest.update(json.dumps(list(array.shape), separators=(",", ":")).encode())
    digest.update(b"\0")
    digest.update(np.packbits(array, bitorder="little").tobytes())
    return digest.hexdigest()


def _failure(
    phase: str,
    matrix_hashes: dict[str, str],
    logical_hashes: dict[str, str],
    detail: str,
) -> dict[str, Any]:
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "method": METHOD,
        "verified": False,
        "failed_phase": phase,
        "failure": detail,
        "matrix_sha256": matrix_hashes,
        "logical_basis_sha256": logical_hashes,
        "orbit_enumeration_started": False,
    }
    report["report_sha256"] = _sha(report)
    return report


def _inverse(value: dic5.GroupElement) -> dic5.GroupElement:
    for trial in dic5.RAW_GROUP:
        if (
            dic5._mul(value, trial) == dic5.IDENTITY
            and dic5._mul(trial, value) == dic5.IDENTITY
        ):
            return trial
    raise RuntimeError("finite group inversion failed")


def _left(value: dic5.GroupElement) -> np.ndarray:
    return np.asarray(
        [
            dic5.QUOTIENT_INDEX[dic5._canonical_coset(dic5._mul(value, item))]
            for item in dic5.QUOTIENT_REPS
        ],
        dtype=np.int64,
    )


def _right(value: dic5.GroupElement) -> np.ndarray:
    return np.asarray(
        [
            dic5.QUOTIENT_INDEX[dic5._canonical_coset(dic5._mul(item, value))]
            for item in dic5.QUOTIENT_REPS
        ],
        dtype=np.int64,
    )


def _blocks(first: np.ndarray, second: np.ndarray) -> np.ndarray:
    return np.concatenate((first, second + 200))


def _hom(
    images: Sequence[dic5.GroupElement],
    value: dic5.GroupElement,
) -> dic5.GroupElement:
    result = dic5.IDENTITY
    for image, exponent in zip(images, value, strict=True):
        result = dic5._word(result, dic5._power(image, exponent))
    return result


def _w() -> tuple[np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    psi3 = (
        dic5._word(dic5._power(dic5.R1, 4), dic5._power(dic5.R2, 5)),
        dic5.S1,
        dic5._word(dic5._power(dic5.R2, 9)),
        dic5._word(dic5._power(dic5.R2, 3), dic5.S2),
    )
    psi1 = (
        dic5._word(dic5._power(dic5.R1, 4), dic5._power(dic5.R2, 5)),
        dic5.S1,
        dic5._word(dic5._power(dic5.R2, 9)),
        dic5._word(dic5.R2, dic5.S2),
    )
    qubits = np.empty(400, dtype=np.int64)
    x_rows = np.empty(200, dtype=np.int64)
    z_rows = np.empty(200, dtype=np.int64)
    for index, value in enumerate(dic5.QUOTIENT_REPS):
        image3, image1 = _hom(psi3, value), _hom(psi1, value)
        qubits[index] = dic5.QUOTIENT_INDEX[image3]
        qubits[200 + index] = 200 + dic5.QUOTIENT_INDEX[
            dic5._word((2, 0, 2, 0), image1)
        ]
        x_rows[index] = dic5.QUOTIENT_INDEX[
            dic5._word((2, 0, 1, 0), image3)
        ]
        z_rows[index] = dic5.QUOTIENT_INDEX[
            dic5._word((0, 0, 1, 0), image1)
        ]
    formula: dict[str, Any] = {
        "psi3_R1_S1_R2_S2": [list(item) for item in psi3],
        "psi1_R1_S1_R2_S2": [list(item) for item in psi1],
        "qubit_block0": "psi3(g)",
        "qubit_block1": "(2,0,2,0)*psi1(g)",
        "x_rows": "(2,0,1,0)*psi3(g)",
        "z_rows": "(0,0,1,0)*psi1(g)",
    }
    formula["formula_sha256"] = _sha(formula)
    return qubits, x_rows, z_rows, formula


def sector_generators() -> dict[str, tuple[np.ndarray, np.ndarray, np.ndarray]]:
    r2_inverse = _inverse(dic5.R2)
    h = dic5._word(dic5._power(dic5.R1, 2), dic5.S1, dic5.S2)
    c0 = dic5._word(dic5.S1, dic5._power(dic5.R2, 4), dic5.S2)
    wq, wx, wz, _ = _w()
    return {
        "T": (
            _blocks(_right(dic5.R1), _right(dic5.R1)),
            _right(dic5.R1),
            _right(dic5.R1),
        ),
        "U": (
            _blocks(_left(r2_inverse), _left(dic5.R2)),
            _left(dic5.R2),
            _left(r2_inverse),
        ),
        "V": (
            _blocks(_left(c0), _left(h)),
            _left(h),
            _left(c0),
        ),
        "W": (wq, wx, wz),
    }


def _compose(after: tuple[int, ...], before: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(after[before[index]] for index in range(len(after)))


def _closure(generators: Sequence[np.ndarray]) -> list[tuple[int, ...]]:
    identity = tuple(range(400))
    encoded = [tuple(int(item) for item in generator) for generator in generators]
    closure = {identity}
    frontier = [identity]
    while frontier:
        current = frontier.pop()
        for generator in encoded:
            image = _compose(generator, current)
            if image not in closure:
                closure.add(image)
                frontier.append(image)
                if len(closure) > PHYSICAL_GROUP_ORDER:
                    raise RuntimeError("physical closure exceeded its hard cap")
    if len(closure) != PHYSICAL_GROUP_ORDER:
        raise RuntimeError("physical closure order mismatch")
    return sorted(closure)


def _encode_action(matrix: np.ndarray) -> tuple[int, ...]:
    return tuple(
        sum(int(matrix[row, column]) << row for row in range(16))
        for column in range(16)
    )


def _apply(action: Sequence[int], value: int) -> int:
    result, remaining = 0, int(value)
    while remaining:
        bit = remaining & -remaining
        result ^= int(action[bit.bit_length() - 1])
        remaining ^= bit
    return result


def _action(
    permutation: Sequence[int],
    detector: np.ndarray,
    representatives: np.ndarray,
) -> tuple[int, ...]:
    pushed = dic5.push_forward_rows(representatives, permutation)
    return _encode_action((detector @ pushed.T) & 1)


def _rank(covectors: Sequence[int]) -> int:
    pivots: dict[int, int] = {}
    for raw in covectors:
        value = int(raw)
        while value:
            pivot = value.bit_length() - 1
            if pivot in pivots:
                value ^= pivots[pivot]
            else:
                pivots[pivot] = value
                break
    return len(pivots)


def _point_orbits(closure: Sequence[Sequence[int]]) -> list[list[int]]:
    unseen, result = set(range(400)), []
    for _ in range(400):
        if not unseen:
            return result
        representative = min(unseen)
        orbit = sorted({int(item[representative]) for item in closure})
        if representative not in orbit:
            raise RuntimeError("point orbit made no progress")
        unseen -= set(orbit)
        result.append(orbit)
    raise RuntimeError("point orbit loop exceeded its hard cap")


def _logical_report(actions: Sequence[tuple[int, ...]], sector: str) -> dict[str, Any]:
    group = sorted(set(actions))
    identity = tuple(1 << index for index in range(16))
    if len(group) != LOGICAL_ACTION_ORDER or identity not in group:
        raise RuntimeError("logical action identity/order failed before orbit replay")
    unseen, orbits = set(range(1, 1 << 16)), []
    for _ in range((1 << 16) - 1):
        if not unseen:
            break
        representative = min(unseen)
        orbit = sorted({_apply(action, representative) for action in group})
        if representative not in orbit:
            raise RuntimeError("logical orbit made no progress")
        unseen -= set(orbit)
        orbits.append(orbit)
    if unseen:
        raise RuntimeError("logical orbit loop exceeded its hard cap")
    missed = [
        sum(all(not ((value >> bit) & 1) for value in orbit) for orbit in orbits)
        for bit in range(16)
    ]
    hits = [
        next(index for index, action in enumerate(group) if _apply(action, orbit[0]) & 1)
        for orbit in orbits
    ] if missed[0] == 0 else []
    orbit_digest = hashlib.sha256()
    for orbit in orbits:
        orbit_digest.update(len(orbit).to_bytes(4, "little"))
        orbit_digest.update(np.asarray(orbit, dtype="<u2").tobytes())
    report: dict[str, Any] = {
        "sector": sector,
        "logical_action_group_order": len(group),
        "logical_action_closure_sha256": hashlib.sha256(
            b"".join(np.asarray(item, dtype="<u2").tobytes() for item in group)
        ).hexdigest(),
        "nonzero_syndrome_count": 65535,
        "nonzero_orbit_count": len(orbits),
        "orbit_size_distribution": {
            str(size): count for size, count in sorted(Counter(map(len, orbits)).items())
        },
        "orbit_partition_sha256": orbit_digest.hexdigest(),
        "orbits_missed_by_output_bit": missed,
        "normalizing_output_bit": 0,
        "normalizing_bit_complete": missed[0] == 0,
        "orbit_hit_selector_sha256": hashlib.sha256(
            np.asarray(hits, dtype="<u2").tobytes()
        ).hexdigest(),
    }
    report["report_sha256"] = _sha(report)
    return report


def _joint(
    closure: Sequence[tuple[int, ...]],
    z_actions: Sequence[tuple[int, ...]],
    point_orbits: Sequence[Sequence[int]],
) -> dict[str, Any]:
    records, all_targets = {}, []
    for representative, selected in JOINT_TARGETS.items():
        fibers: dict[int, set[int]] = {}
        for permutation, action in zip(closure, z_actions, strict=True):
            target = int(permutation[representative])
            functional = sum(
                ((int(action[column]) & 1) != 0) << column for column in range(16)
            )
            fibers.setdefault(target, set()).add(functional)
        if len(fibers) != 100:
            raise RuntimeError("joint transporter orbit size mismatch")
        fiber_sizes = sorted({len(value) for value in fibers.values()})
        maximum_fiber = max(fiber_sizes)
        lower_bound = (16 + maximum_fiber - 1) // maximum_fiber
        covectors = [item for target in selected for item in sorted(fibers[target])]
        rank = _rank(covectors)
        records[str(representative)] = {
            "transporter_distinct_functionals_per_target": fiber_sizes,
            "selected_targets": list(selected),
            "selected_functionals_hex": {
                str(target): [f"{item:04x}" for item in sorted(fibers[target])]
                for target in selected
            },
            "selected_functional_rank": rank,
            "rank_lower_bound_on_target_count": lower_bound,
            "target_count_optimal": len(selected) == lower_bound and rank == 16,
        }
        all_targets.extend(selected)
    layers = [
        [JOINT_TARGETS[representative][index] for representative in (0, 1, 200, 201)]
        for index in range(8)
    ]
    report: dict[str, Any] = {
        "criterion": "transporter output-bit covectors span GF(2)^16 dual",
        "point_orbit_representatives": [int(orbit[0]) for orbit in point_orbits],
        "per_orbit": records,
        "all_selected_targets": sorted(all_targets),
        "all_selected_target_count": len(set(all_targets)),
        "parallel_four_anchor_layers": layers,
        "complete": bool(
            len(set(all_targets)) == 32
            and all(item["target_count_optimal"] for item in records.values())
        ),
    }
    report["report_sha256"] = _sha(report)
    return report


def verify_paper400_dic5_logical_symmetry(
    hx: np.ndarray,
    hz: np.ndarray,
    lx: np.ndarray,
    lz: np.ndarray,
) -> dict[str, Any]:
    """Replay the source-bound finite-group certificate, failing before orbits."""

    values = tuple(np.asarray(item, dtype=np.uint8) & 1 for item in (hx, hz, lx, lz))
    matrix_x, matrix_z, logical_x, logical_z = values
    matrix_hashes = {"H_X": _safe_matrix_hash(matrix_x), "H_Z": _safe_matrix_hash(matrix_z)}
    logical_hashes = {"L_X": _safe_matrix_hash(logical_x), "L_Z": _safe_matrix_hash(logical_z)}
    shape_valid = bool(
        matrix_x.shape == matrix_z.shape == (200, 400)
        and logical_x.shape == logical_z.shape == (16, 400)
    )
    if not shape_valid:
        return _failure("shape", matrix_hashes, logical_hashes, "shape mismatch")
    if matrix_hashes != dic5.EXPECTED_MATRIX_SHA256:
        return _failure("matrix_hash", matrix_hashes, logical_hashes, "matrix hash mismatch")
    if logical_hashes != EXPECTED_LOGICAL_BASIS_SHA256:
        return _failure("logical_hash", matrix_hashes, logical_hashes, "logical hash mismatch")
    identity16 = np.eye(16, dtype=np.uint8)
    if not np.array_equal((logical_x @ logical_z.T) & 1, identity16):
        return _failure("logical_duality", matrix_hashes, logical_hashes, "L_X L_Z^T != I")
    cache_key = tuple(matrix_hashes.values()) + tuple(logical_hashes.values())
    if cache_key in _VALID_REPORT_CACHE:
        return copy.deepcopy(_VALID_REPORT_CACHE[cache_key])

    generators = sector_generators()
    generator_records, generator_valid = {}, True
    for name, (qubits, x_rows, z_rows) in generators.items():
        hashes = {
            "qubits": dic5._permutation_sha256(qubits),
            "x_rows": dic5._permutation_sha256(x_rows),
            "z_rows": dic5._permutation_sha256(z_rows),
        }
        hx_ok = np.array_equal(matrix_x[np.ix_(x_rows, qubits)], matrix_x)
        hz_ok = np.array_equal(matrix_z[np.ix_(z_rows, qubits)], matrix_z)
        valid = bool(hashes == EXPECTED_GENERATOR_SHA256[name] and hx_ok and hz_ok)
        generator_valid &= valid
        generator_records[name] = {**hashes, "Hx_replay": hx_ok, "Hz_replay": hz_ok, "verified": valid}
    generator_records["W"]["formula"] = _w()[3]
    if not generator_valid:
        return _failure("generator", matrix_hashes, logical_hashes, "Tanner generator replay failed")

    closure = _closure([item[0] for item in generators.values()])
    identity_permutation = tuple(range(400))
    x_identity = _action(identity_permutation, logical_z, logical_x)
    z_identity = _action(identity_permutation, logical_x, logical_z)
    expected_identity = tuple(1 << index for index in range(16))
    if x_identity != expected_identity or z_identity != expected_identity:
        return _failure("logical_identity", matrix_hashes, logical_hashes, "identity action mismatch")

    point_orbits = _point_orbits(closure)
    orbit_hash = hashlib.sha256(
        b"".join(np.asarray(orbit, dtype="<u4").tobytes() for orbit in point_orbits)
    ).hexdigest()
    if (
        [(orbit[0], len(orbit)) for orbit in point_orbits]
        != [(0, 100), (1, 100), (200, 100), (201, 100)]
        or orbit_hash != EXPECTED_QUBIT_ORBIT_SHA256
    ):
        return _failure("point_orbits", matrix_hashes, logical_hashes, "point orbit mismatch")
    x_actions = [_action(item, logical_z, logical_x) for item in closure]
    z_actions = [_action(item, logical_x, logical_z) for item in closure]
    x_report, z_report = _logical_report(x_actions, "X"), _logical_report(z_actions, "Z")
    joint = _joint(closure, z_actions, point_orbits)
    verified = bool(
        x_report["normalizing_bit_complete"]
        and z_report["normalizing_bit_complete"]
        and joint["complete"]
    )
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "method": METHOD,
        "verified": verified,
        "matrix_sha256": matrix_hashes,
        "logical_basis_sha256": logical_hashes,
        "orbit_enumeration_started": True,
        "generators": generator_records,
        "physical_group_order": len(closure),
        "physical_group_closure_sha256": hashlib.sha256(
            b"".join(np.asarray(item, dtype="<u4").tobytes() for item in closure)
        ).hexdigest(),
        "qubit_orbits": [{"representative": item[0], "size": len(item)} for item in point_orbits],
        "qubit_orbit_partition_sha256": orbit_hash,
        "X_logical_action": x_report,
        "Z_logical_action": z_report,
        "canonical_Z_partition": {
            "partition_index": 0,
            "anchor_indices": [],
            "complete_up_to_symmetry": z_report["normalizing_bit_complete"],
        },
        "joint_normalization": joint,
    }
    report["report_sha256"] = _sha(report)
    _VALID_REPORT_CACHE[cache_key] = copy.deepcopy(report)
    return report


__all__ = [
    "EXPECTED_GENERATOR_SHA256",
    "EXPECTED_LOGICAL_BASIS_SHA256",
    "JOINT_TARGETS",
    "METHOD",
    "SCHEMA_VERSION",
    "sector_generators",
    "verify_paper400_dic5_logical_symmetry",
]
