from __future__ import annotations

import copy
import fcntl
import hashlib
import io
import json
import os
from functools import lru_cache
from pathlib import Path

import numpy as np
import pytest
from qldpc.codes import CSSCode

import evaluation.certificate_dispatch as dispatch
from evaluation import exact_anchor_certificate as module
from evaluation.css_logical_detector import CSS_LOGICAL_DETECTOR_METHOD
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import (
    SAT_FORMULATION,
    _FORMULATION_REVISION,
    _array_sha256,
    build_css_threshold_cnf,
    css_sector_matrices,
)
from evaluation.matrix_io import pack_matrix
from evaluation.matrix_certificate import _rebuild_claim
from scripts.screen_frontier_sat import build_anchor_cover_cubes

FIXTURE_CHECKER_TIMEOUT_S = 5.0
FIXTURE_MAX_PROOF_BYTES = 1 << 35


def _write(path: Path, data: bytes) -> dict[str, object]:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return {
        "path": path.name,
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def _overwrite_same_inode(path: Path, data: bytes) -> None:
    """Rewrite content without replacing the directory entry or inode."""

    before = path.stat()
    with path.open("r+b") as stream:
        stream.seek(0)
        stream.write(data)
        stream.truncate()
        stream.flush()
        os.fsync(stream.fileno())
    after = path.stat()
    assert (after.st_dev, after.st_ino) == (before.st_dev, before.st_ino)


@lru_cache(maxsize=1)
def _hgp_distance_16_material():
    """[[481,1,16]] HGP(repetition-16,repetition-16), no solver needed."""

    length = 16
    classical = np.zeros((length - 1, length), dtype=np.uint8)
    for index in range(length - 1):
        classical[index, index:index + 2] = 1
    rows, columns = classical.shape
    hx = np.hstack((
        np.kron(classical, np.eye(columns, dtype=np.uint8)),
        np.kron(np.eye(rows, dtype=np.uint8), classical.T),
    )).astype(np.uint8)
    hz = np.hstack((
        np.kron(np.eye(columns, dtype=np.uint8), classical),
        np.kron(classical.T, np.eye(rows, dtype=np.uint8)),
    )).astype(np.uint8)
    _hx, _hz, lx, lz = get_code_matrices(CSSCode(hx, hz, field=2))
    hx, hz, lx, lz = (
        np.asarray(value, dtype=np.uint8) & 1 for value in (hx, hz, lx, lz)
    )
    assert lx.shape == lz.shape == (1, 481)
    assert int(lx[0].sum()) == int(lz[0].sum()) == 16
    bundle = {
        "schema_version": 1,
        "kind": module.MATRIX_BUNDLE_KIND,
        "logical_basis_method": CSS_LOGICAL_DETECTOR_METHOD,
        "H_X": pack_matrix(hx),
        "H_Z": pack_matrix(hz),
        "L_X": pack_matrix(lx),
        "L_Z": pack_matrix(lz),
    }
    bundle["bundle_sha256"] = module.canonical_sha256(bundle)
    bundle_bytes = (
        json.dumps(bundle, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    )
    cnfs = {}
    for sector in ("X", "Z"):
        checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
        cnf = build_css_threshold_cnf(
            checks,
            logicals,
            max_weight=15,
            sector=sector,
            cardinality_encoding="seqcounter",
        )
        cnfs[sector] = (checks, logicals, cnf, module.render_dimacs(cnf))
    return hx, hz, lx, lz, bundle_bytes, cnfs


@lru_cache(maxsize=1)
def _hgp_distance_16_isometric_material():
    """The same HGP code with H_Z row-labelled for an involutive isometry."""

    hx, original_hz, lx, lz, _bundle, _cnfs = _hgp_distance_16_material()
    classical_rows, classical_columns = 15, 16
    first_block = np.asarray(
        [
            (index % classical_columns) * classical_columns
            + index // classical_columns
            for index in range(classical_columns * classical_columns)
        ],
        dtype=np.int64,
    )
    second_block = np.asarray(
        [
            classical_columns * classical_columns
            + (index % classical_rows) * classical_rows
            + index // classical_rows
            for index in range(classical_rows * classical_rows)
        ],
        dtype=np.int64,
    )
    qubit_permutation = np.concatenate((first_block, second_block))
    assert np.array_equal(
        qubit_permutation[qubit_permutation], np.arange(hx.shape[1])
    )
    hz = hx[:, qubit_permutation]
    assert not np.any((hx @ hz.T) & 1)
    # This relabels only the H_Z generators; its row space is the original one.
    original_row_order = np.asarray(
        [
            (index % classical_rows) * classical_columns
            + index // classical_rows
            for index in range(classical_rows * classical_columns)
        ],
        dtype=np.int64,
    )
    assert sorted(original_row_order.tolist()) == list(range(hx.shape[0]))
    assert np.array_equal(hz[original_row_order], original_hz)
    detector = module.verify_css_logical_detectors(hx, hz, lx, lz)
    assert detector["verified"] is True
    bundle = {
        "schema_version": 1,
        "kind": module.MATRIX_BUNDLE_KIND,
        "logical_basis_method": CSS_LOGICAL_DETECTOR_METHOD,
        "H_X": pack_matrix(hx),
        "H_Z": pack_matrix(hz),
        "L_X": pack_matrix(lx),
        "L_Z": pack_matrix(lz),
    }
    bundle["bundle_sha256"] = module.canonical_sha256(bundle)
    bundle_bytes = (
        json.dumps(bundle, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    )
    cnfs = {}
    for sector in ("X", "Z"):
        checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
        cnf = build_css_threshold_cnf(
            checks,
            logicals,
            max_weight=15,
            sector=sector,
            cardinality_encoding="seqcounter",
        )
        cnfs[sector] = (checks, logicals, cnf, module.render_dimacs(cnf))
    return hx, hz, lx, lz, bundle_bytes, cnfs, qubit_permutation


def _fixture(tmp_path: Path, *, isometric: bool = False):
    if isometric:
        hx, hz, lx, lz, bundle_bytes, cnfs, qubit_permutation = (
            _hgp_distance_16_isometric_material()
        )
    else:
        hx, hz, lx, lz, bundle_bytes, cnfs = _hgp_distance_16_material()
        qubit_permutation = None
    matrix_descriptor = _write(tmp_path / "matrices.json", bundle_bytes)
    checker_records = {}
    trusted_checkers = {}
    checker_specs = {
        "drat": (module.DRAT_CHECKER_ROLE, "fixture-drat-trim-v1", "1" * 40),
        "lrat": (module.LRAT_CHECKER_ROLE, "fixture-lrat-check-v1", "2" * 40),
    }
    for proof_format, (checker_role, checker_id, source_commit) in checker_specs.items():
        marker = f"VALID-{proof_format.upper()}-FIXTURE\n"
        stdout = (
            b"s VERIFIED\n" if proof_format == "drat" else b"c VERIFIED\n"
        )
        checker_bytes = f"""#!/usr/bin/env python3
import pathlib, sys
with pathlib.Path(sys.argv[1]).open('rb') as stream:
    header = stream.read(6)
proof = pathlib.Path(sys.argv[2]).read_bytes()
if header == b'p cnf ' and proof == {marker.encode()!r}:
    sys.stdout.write({stdout.decode()!r})
    raise SystemExit(0)
sys.stderr.write('{proof_format.upper()} NOT VERIFIED\\n')
raise SystemExit(1)
""".encode()
        checker_descriptor = _write(
            tmp_path / f"fixture-{proof_format}-checker",
            checker_bytes,
        )
        os.chmod(tmp_path / f"fixture-{proof_format}-checker", 0o755)
        source_repository = (
            f"https://invalid.example/reviewed-fixture-{proof_format}-checker"
        )
        source_descriptor = _write(
            tmp_path / f"fixture-{proof_format}-checker-source.txt",
            f"reviewed fixture {proof_format} checker source v1\n".encode(),
        )
        run = {
            "argv_roles": ["binary", "dimacs", "proof"],
            "exit_code": 0,
            "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
            "stderr_sha256": hashlib.sha256(b"").hexdigest(),
            "semantic_stdout_sha256": module.checker_semantic_stdout_sha256(
                proof_format
            ),
        }
        checker_records[proof_format] = {
            "checker_role": checker_role,
            "checker_id": checker_id,
            "proof_format": proof_format,
            "binary": checker_descriptor,
            "source": {
                "repository": source_repository,
                "commit": source_commit,
                "artifact": source_descriptor,
            },
            "run": run,
        }
        trusted_checkers[checker_id] = {
            "checker_role": checker_role,
            "proof_format": proof_format,
            "binary_sha256": checker_descriptor["sha256"],
            "source_repository": source_repository,
            "source_commit": source_commit,
            "source_sha256": source_descriptor["sha256"],
            "argv_roles": ["binary", "dimacs", "proof"],
            "semantic_stdout_sha256": module.checker_semantic_stdout_sha256(
                proof_format
            ),
            "timeout_s": FIXTURE_CHECKER_TIMEOUT_S,
            "max_proof_bytes": FIXTURE_MAX_PROOF_BYTES,
        }
    sectors = []
    for sector in ("X", "Z"):
        checks, logicals, cnf, dimacs_bytes = cnfs[sector]
        dimacs = _write(tmp_path / f"{sector.lower()}.cnf", dimacs_bytes)
        proof_checks = {}
        for proof_format in ("drat", "lrat"):
            proof_artifact = _write(
                tmp_path / f"{sector.lower()}.{proof_format}",
                f"VALID-{proof_format.upper()}-FIXTURE\n".encode(),
            )
            proof_checks[proof_format] = {
                "proof": {"format": proof_format, "artifact": proof_artifact},
                "checker": copy.deepcopy(checker_records[proof_format]),
            }
        unit = {
            "sector": sector,
            "partition_index": None,
            "anchor_cube": None,
            "formulation": SAT_FORMULATION,
            "formulation_revision": _FORMULATION_REVISION,
            "cardinality_encoding": "seqcounter",
            "check_matrix_sha256": _array_sha256("checks", checks),
            "target_logicals_sha256": _array_sha256("logicals", logicals),
            "cnf_sha256": cnf["cnf_sha256"],
            "num_variables": cnf["num_variables"],
            "num_clauses": cnf["num_clauses"],
            "dimacs": dimacs,
            "proof_checks": proof_checks,
        }
        sectors.append({
            "sector": sector,
            "cover": module.GLOBAL_COVER,
            "units": [unit],
        })

    vector = lx[0]
    syndrome = ((lz @ vector) & 1).astype(int).tolist()
    witness = {
        "sector": "X",
        "weight": 16,
        "bits": vector.astype(int).tolist(),
        "support": [int(index) for index in np.flatnonzero(vector)],
        "logical_syndrome": syndrome,
    }
    witness["witness_sha256"] = module.canonical_sha256(witness)
    target = {
        "schema_version": 1,
        "mode": "fixture-distance-at-least-v1",
        "n": 481,
        "k": 1,
        "required_distance": 16,
        "rejection_cutoff": 15,
    }
    target["binding_sha256"] = module.canonical_sha256(target)
    policy = {
        "anchor": {
            "candidate_sha256": "a" * 64,
            "candidate": {"fixture": "hgp-repetition-16"},
            "action_catalog": {"catalog_id": "fixture", "schema_version": 1, "sha256": "b" * 64},
            "paper": {
                "identifier": "fixture:distance-16",
                "upstream_repository": "https://invalid.example/fixture",
                "upstream_commit": "c" * 40,
                "source_record": {"path": "fixture.json", "sha256": "d" * 64, "source_id": "fixture"},
            },
            "published_support": {"reported_n": 481, "reported_k": 1, "reported_distance": 16, "reported_distance_exact": True},
        },
        "construction": {"kind": "fixture-hgp-repetition-16"},
        "n": 481,
        "k": 1,
        "distance": 16,
        "target": target,
    }
    disposition = {
        "classification": "published-calibration",
        "novelty": "known-published-non-novel",
        "calibration_only": True,
        "target_threshold_satisfied": True,
        "selected_win_eligible": False,
        "trusted_win_eligible": False,
        "formal_win_eligible": False,
        "win_awarded": False,
    }
    lower_bound = {
        "max_weight": 15,
        "symmetry": None,
        "sectors": sectors,
    }
    if isometric:
        assert qubit_permutation is not None
        isometry = module.build_xz_isometry_artifact(
            hx=hx,
            hz=hz,
            row_permutation=list(range(hx.shape[0])),
            qubit_permutation=qubit_permutation.tolist(),
            proof_sector="X",
        )
        isometry_payload = (
            json.dumps(isometry, sort_keys=True, separators=(",", ":")).encode()
            + b"\n"
        )
        lower_bound["xz_isometry"] = _write(
            tmp_path / "xz-isometry.json",
            isometry_payload,
        )
        lower_bound["sectors"] = sectors[:1]
    certificate = module.seal_certificate({
        "schema_version": module.SCHEMA_VERSION,
        "certificate_type": module.CERTIFICATE_TYPE,
        "certificate_role": module.CERTIFICATE_ROLE,
        "anchor": copy.deepcopy(policy["anchor"]),
        "construction": copy.deepcopy(policy["construction"]),
        "parameters": {"n": 481, "k": 1, "d": 16},
        "matrix_bundle": matrix_descriptor,
        "distance_proof": {
            "claimed_distance": 16,
            "lower_bound": lower_bound,
            "upper_bound": {"witness": witness},
        },
        "target": copy.deepcopy(target),
        "disposition": disposition,
    })

    def authoritative(_construction):
        return hx, hz

    return certificate, policy, trusted_checkers, authoritative


def _validate(tmp_path: Path, certificate, policy, checkers, authoritative):
    return module._validate_certificate(
        certificate,
        artifact_root=tmp_path,
        trusted_checkers=checkers,
        checker_timeout_s=FIXTURE_CHECKER_TIMEOUT_S,
        policy=policy,
        authoritative_matrix_builder=authoritative,
    )


def _first_unit(certificate):
    return certificate["distance_proof"]["lower_bound"]["sectors"][0]["units"][0]


def _proof_check(certificate, proof_format):
    return _first_unit(certificate)["proof_checks"][proof_format]


def _replace_checker_binary(
    tmp_path,
    certificate,
    checkers,
    proof_format,
    data,
):
    first = _proof_check(certificate, proof_format)["checker"]
    path = tmp_path / first["binary"]["path"]
    descriptor = _write(path, data)
    os.chmod(path, 0o755)
    for sector in certificate["distance_proof"]["lower_bound"]["sectors"]:
        sector["units"][0]["proof_checks"][proof_format]["checker"][
            "binary"
        ] = copy.deepcopy(descriptor)
    checkers[first["checker_id"]]["binary_sha256"] = descriptor["sha256"]


def _rewrite_matrix_bundle(tmp_path: Path, certificate, bundle):
    bundle["bundle_sha256"] = module.canonical_sha256(
        bundle,
        omit="bundle_sha256",
    )
    payload = (
        json.dumps(bundle, sort_keys=True, separators=(",", ":")).encode()
        + b"\n"
    )
    certificate["matrix_bundle"] = _write(tmp_path / "matrices.json", payload)
    return module.seal_certificate(certificate)


def _rewrite_isometry_artifact(tmp_path: Path, certificate, artifact):
    artifact["artifact_sha256"] = module.canonical_sha256(
        artifact,
        omit="artifact_sha256",
    )
    payload = (
        json.dumps(artifact, sort_keys=True, separators=(",", ":")).encode()
        + b"\n"
    )
    descriptor = _write(tmp_path / "xz-isometry.json", payload)
    certificate["distance_proof"]["lower_bound"]["xz_isometry"] = descriptor
    return module.seal_certificate(certificate)


def _install_fixture_policy(monkeypatch, policy, authoritative):
    monkeypatch.setattr(module, "installed_anchor_policy", lambda: policy)
    monkeypatch.setattr(module, "_default_authoritative_matrices", authoritative)


def test_dispatch_selects_anchor_builder_only_for_explicit_type():
    assert dispatch.builder_for_claim({
        "certificate_type": module.CERTIFICATE_TYPE,
        "construction": {"kind": "fixture"},
    }) is module.build_exact_anchor_certificate
    assert dispatch.builder_for_claim({
        "construction": {"kind": "fixture"},
    }) is dispatch.build_matrix_css_certificate
    assert dispatch.builder_for_claim({
        "H_X": [[1]],
        "H_Z": [[0]],
    }) is dispatch.build_matrix_css_certificate
    assert dispatch.builder_for_claim({
        "certificate_type": dispatch.BB_CSS_TYPE,
        "H_X": [[1]],
        "H_Z": [[0]],
    }) is dispatch.build_matrix_css_certificate


def test_claim_certificate_type_typo_fails_closed_without_breaking_null_legacy():
    with pytest.raises(ValueError, match="unsupported claim certificate_type"):
        dispatch.builder_for_claim({
            "certificate_type": "qcode-css-exact-anchor-proof-carrying-vl",
            "H_X": [[1]],
            "H_Z": [[0]],
        })
    assert dispatch.builder_for_claim({
        "certificate_type": None,
        "H_X": [[1]],
        "H_Z": [[0]],
    }) is dispatch.build_matrix_css_certificate


def test_dispatch_build_is_packaging_only_and_requires_explicit_type(tmp_path):
    certificate, _policy, _checkers, _authoritative = _fixture(tmp_path)
    rebuilt = dispatch.build_certificate(
        certificate,
        known_answer_artifact=tmp_path / "unused-known-answer.json",
    )
    assert rebuilt == certificate
    untyped = dict(certificate)
    untyped.pop("certificate_type")
    with pytest.raises(ValueError, match="fields are not exact"):
        module.build_exact_anchor_certificate(untyped)


def test_valid_fixture_reaches_exact_anchor_verifier_via_dispatch(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    _install_fixture_policy(monkeypatch, policy, authoritative)
    result = dispatch.verify_certificate(
        certificate,
        known_answer_artifact=tmp_path / "unused-known-answer.json",
        artifact_root=tmp_path,
        trusted_checkers=checkers,
        checker_timeout_s=FIXTURE_CHECKER_TIMEOUT_S,
    )
    assert result == {
        "valid": True,
        "proof_valid": True,
        "calibration_valid": True,
        "passed": False,
        "win_awarded": False,
        "selected_win": False,
        "trusted_win": False,
        "formal_win": False,
        "failures": [],
    }


@pytest.mark.parametrize(
    "missing",
    ["artifact_root", "trusted_checkers", "checker_timeout_s"],
)
def test_dispatch_fails_closed_without_anchor_trust_inputs(
    tmp_path,
    missing,
):
    certificate, _policy, checkers, _authoritative = _fixture(tmp_path)
    kwargs = {
        "known_answer_artifact": tmp_path / "unused-known-answer.json",
        "artifact_root": tmp_path,
        "trusted_checkers": checkers,
        "checker_timeout_s": FIXTURE_CHECKER_TIMEOUT_S,
    }
    kwargs.pop(missing)
    with pytest.raises(ValueError, match=f"requires {missing}"):
        dispatch.verify_certificate(certificate, **kwargs)


@pytest.mark.parametrize(
    "invalid_timeout",
    [True, False, 0, -1, float("nan"), float("inf"), "5"],
)
def test_checker_timeout_rejects_invalid_bool_number_or_type(
    tmp_path,
    invalid_timeout,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    with pytest.raises(ValueError, match="positive finite"):
        module._validate_certificate(
            certificate,
            artifact_root=tmp_path,
            trusted_checkers=checkers,
            checker_timeout_s=invalid_timeout,
            policy=policy,
            authoritative_matrix_builder=authoritative,
        )


def test_checker_timeout_rejects_value_above_hard_cap(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    with pytest.raises(ValueError, match="positive finite"):
        module._validate_certificate(
            certificate,
            artifact_root=tmp_path,
            trusted_checkers=checkers,
            checker_timeout_s=module.MAX_CHECKER_TIMEOUT_S + 1,
            policy=policy,
            authoritative_matrix_builder=authoritative,
        )


def test_checker_timeout_is_pinned_by_trusted_policy(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    checkers["fixture-drat-trim-v1"]["timeout_s"] = (
        FIXTURE_CHECKER_TIMEOUT_S + 1
    )
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"] is False
    assert any("one exact timeout" in item for item in result["failures"])


def test_checker_process_timeout_fails_closed(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    proof_check = _proof_check(certificate, "drat")
    checker = proof_check["checker"]
    binary_path = tmp_path / checker["binary"]["path"]
    replacement = b"""#!/usr/bin/env python3
import time
time.sleep(1)
print('s VERIFIED')
"""
    checker["binary"] = _write(binary_path, replacement)
    os.chmod(binary_path, 0o755)
    checkers[checker["checker_id"]]["binary_sha256"] = checker["binary"]["sha256"]
    timeout_s = 0.01
    for trusted in checkers.values():
        trusted["timeout_s"] = timeout_s
    certificate = module.seal_certificate(certificate)
    result = module._validate_certificate(
        certificate,
        artifact_root=tmp_path,
        trusted_checkers=checkers,
        checker_timeout_s=timeout_s,
        policy=policy,
        authoritative_matrix_builder=authoritative,
    )
    assert result["valid"] is False
    assert any("timed out" in item for item in result["failures"])


def test_trusted_proof_cap_can_explicitly_exceed_sixteen_gib(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    assert FIXTURE_MAX_PROOF_BYTES > 16 * (1 << 30)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"], result["failures"]


@pytest.mark.parametrize(
    "invalid_cap",
    [True, 0, -1, module.MAX_TRUSTED_PROOF_BYTES + 1],
)
def test_trusted_proof_cap_is_strict_and_fail_closed(tmp_path, invalid_cap):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    checkers["fixture-lrat-check-v1"]["max_proof_bytes"] = invalid_cap
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"] is False
    assert any("max_proof_bytes" in item for item in result["failures"])


def _write_checker_policy(path: Path, checkers):
    policy = {
        "schema_version": 1,
        "kind": module.CHECKER_POLICY_KIND,
        "checkers": copy.deepcopy(checkers),
    }
    policy["policy_sha256"] = module.canonical_sha256(policy)
    path.write_text(
        json.dumps(policy, sort_keys=True, separators=(",", ":")) + "\n"
    )
    return policy


def test_strict_checker_policy_loader_accepts_only_sealed_dual_policy(tmp_path):
    _certificate, _policy, checkers, _authoritative = _fixture(tmp_path)
    path = tmp_path / "checker-policy.json"
    _write_checker_policy(path, checkers)
    assert module.load_trusted_checker_policy(path) == checkers


@pytest.mark.parametrize(
    "payload",
    [
        b'{"schema_version":1,"schema_version":1}\n',
        b'{"value":NaN}\n',
        b'{"value":Infinity}\n',
        b'{"value":-Infinity}\n',
    ],
)
def test_shared_strict_json_loader_rejects_duplicates_and_nonfinite_numbers(
    tmp_path,
    payload,
):
    with pytest.raises(ValueError):
        module._load_strict_json(io.BytesIO(payload))

    path = tmp_path / "checker-policy.json"
    path.write_bytes(payload)
    with pytest.raises(ValueError, match="not strict JSON"):
        module.load_trusted_checker_policy(path)


def test_checker_policy_path_swap_cannot_redirect_pinned_json(
    tmp_path,
    monkeypatch,
):
    _certificate, _policy, checkers, _authoritative = _fixture(tmp_path)
    path = tmp_path / "checker-policy.json"
    replacement = tmp_path / "replacement-policy.json"
    expected = _write_checker_policy(path, checkers)
    altered_checkers = copy.deepcopy(checkers)
    altered_checkers["fixture-drat-trim-v1"]["source_repository"] = (
        "https://invalid.example/swapped-policy"
    )
    _write_checker_policy(replacement, altered_checkers)
    real_loads = module.json.loads
    swapped = False

    def swap_path_before_parse(payload, *args, **kwargs):
        nonlocal swapped
        if not swapped:
            swapped = True
            replacement.replace(path)
        return real_loads(payload, *args, **kwargs)

    monkeypatch.setattr(module.json, "loads", swap_path_before_parse)
    loaded = module.load_trusted_checker_policy(path)

    assert swapped is True
    assert loaded == expected["checkers"]
    assert loaded != altered_checkers


def test_checker_policy_same_inode_overwrite_cannot_repair_snapshotted_json(
    tmp_path,
    monkeypatch,
):
    _certificate, _policy, checkers, _authoritative = _fixture(tmp_path)
    path = tmp_path / "checker-policy.json"
    _write_checker_policy(path, checkers)
    valid_bytes = path.read_bytes()
    invalid = json.loads(valid_bytes)
    invalid["policy_sha256"] = "0" * 64
    invalid_bytes = (
        json.dumps(invalid, sort_keys=True, separators=(",", ":")).encode()
        + b"\n"
    )
    _overwrite_same_inode(path, invalid_bytes)
    inode = path.stat().st_ino
    real_loads = module.json.loads
    attacked = False

    def overwrite_source_before_parse(payload, *args, **kwargs):
        nonlocal attacked
        if not attacked:
            attacked = True
            _overwrite_same_inode(path, valid_bytes)
            try:
                return real_loads(payload, *args, **kwargs)
            finally:
                _overwrite_same_inode(path, invalid_bytes)
        return real_loads(payload, *args, **kwargs)

    monkeypatch.setattr(module.json, "loads", overwrite_source_before_parse)
    with pytest.raises(ValueError, match="identity/self hash"):
        module.load_trusted_checker_policy(path)

    assert attacked is True
    assert path.stat().st_ino == inode


@pytest.mark.parametrize("mutation", ["self_hash", "unknown_field", "same_binary"])
def test_checker_policy_loader_tamper_fails_closed(tmp_path, mutation):
    _certificate, _policy, checkers, _authoritative = _fixture(tmp_path)
    path = tmp_path / "checker-policy.json"
    policy = _write_checker_policy(path, checkers)
    if mutation == "self_hash":
        policy["policy_sha256"] = "0" * 64
    elif mutation == "unknown_field":
        policy["unknown"] = True
        policy["policy_sha256"] = module.canonical_sha256(
            policy,
            omit="policy_sha256",
        )
    elif mutation == "same_binary":
        policy["checkers"]["fixture-lrat-check-v1"]["binary_sha256"] = (
            policy["checkers"]["fixture-drat-trim-v1"]["binary_sha256"]
        )
        policy["policy_sha256"] = module.canonical_sha256(
            policy,
            omit="policy_sha256",
        )
    else:  # pragma: no cover
        raise AssertionError(mutation)
    path.write_text(json.dumps(policy) + "\n")
    with pytest.raises(ValueError):
        module.load_trusted_checker_policy(path)


def test_artifact_hash_and_dimacs_compare_do_not_use_read_bytes(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)

    def forbidden_read_bytes(_path):
        raise AssertionError("unbounded Path.read_bytes is forbidden in validation")

    monkeypatch.setattr(Path, "read_bytes", forbidden_read_bytes)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"], result["failures"]


def test_proof_path_swap_after_prehash_cannot_redirect_checker(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    proof_check = _proof_check(certificate, "drat")
    proof_path = tmp_path / proof_check["proof"]["artifact"]["path"]
    proof_check["proof"]["artifact"] = _write(
        proof_path,
        b"INVALID-DRAT-FIXTURE\n",
    )
    swap_path = tmp_path / "swap-valid.drat"
    swap_path.write_bytes(b"VALID-DRAT-FIXTURE\n")
    certificate = module.seal_certificate(certificate)
    real_run = module.subprocess.run
    swapped = False

    def swapping_run(argv, **kwargs):
        nonlocal swapped
        assert argv[1].startswith("/proc/self/fd/")
        assert argv[2].startswith("/proc/self/fd/")
        assert set(kwargs["pass_fds"]) == {
            int(argv[0].rsplit("/", 1)[1]),
            int(argv[1].rsplit("/", 1)[1]),
            int(argv[2].rsplit("/", 1)[1]),
        }
        if not swapped:
            os.replace(swap_path, proof_path)
            swapped = True
        return real_run(argv, **kwargs)

    monkeypatch.setattr(module.subprocess, "run", swapping_run)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert swapped is True
    assert result["valid"] is False
    assert any("checker exit mismatch" in item for item in result["failures"])


def test_proof_same_inode_overwrite_after_hash_cannot_redirect_checker(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    proof_check = _proof_check(certificate, "drat")
    proof_path = tmp_path / proof_check["proof"]["artifact"]["path"]
    invalid = b"INVALID-DRAT-FIXTURE\n"
    valid = b"VALID-DRAT-FIXTURE\n"
    proof_check["proof"]["artifact"] = _write(proof_path, invalid)
    certificate = module.seal_certificate(certificate)
    inode = proof_path.stat().st_ino
    real_run = module.subprocess.run
    attacked = False

    def overwriting_run(argv, **kwargs):
        nonlocal attacked
        if not attacked:
            attacked = True
            _overwrite_same_inode(proof_path, valid)
            try:
                return real_run(argv, **kwargs)
            finally:
                _overwrite_same_inode(proof_path, invalid)
        return real_run(argv, **kwargs)

    monkeypatch.setattr(module.subprocess, "run", overwriting_run)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert attacked is True
    assert proof_path.stat().st_ino == inode
    assert result["valid"] is False
    assert any("checker exit mismatch" in item for item in result["failures"])


def test_dimacs_path_swap_after_canonical_compare_cannot_redirect_checkers(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    unit = _first_unit(certificate)
    dimacs_path = tmp_path / unit["dimacs"]["path"]
    swapped_dimacs = tmp_path / "swap.cnf"
    swapped_dimacs.write_bytes(dimacs_path.read_bytes() + b"c SWAPPED\n")
    checker = b"""#!/usr/bin/env python3
import pathlib, sys
cnf = pathlib.Path(sys.argv[1]).read_bytes()
proof = pathlib.Path(sys.argv[2]).read_bytes()
if b'c SWAPPED\\n' in cnf and proof == b'VALID-DRAT-FIXTURE\\n':
    print('s VERIFIED')
    raise SystemExit(0)
raise SystemExit(1)
"""
    _replace_checker_binary(
        tmp_path,
        certificate,
        checkers,
        "drat",
        checker,
    )
    certificate = module.seal_certificate(certificate)
    real_run = module.subprocess.run
    swapped = False

    def swapping_run(argv, **kwargs):
        nonlocal swapped
        assert argv[1].startswith("/proc/self/fd/")
        assert argv[2].startswith("/proc/self/fd/")
        if not swapped:
            os.replace(swapped_dimacs, dimacs_path)
            swapped = True
        return real_run(argv, **kwargs)

    monkeypatch.setattr(module.subprocess, "run", swapping_run)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert swapped is True
    assert result["valid"] is False
    assert any("checker exit mismatch" in item for item in result["failures"])


def test_dimacs_same_inode_overwrite_cannot_bypass_canonical_compare(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    unit = _first_unit(certificate)
    dimacs_path = tmp_path / unit["dimacs"]["path"]
    valid = dimacs_path.read_bytes()
    invalid = valid + b"c NONCANONICAL\n"
    unit["dimacs"] = _write(dimacs_path, invalid)
    certificate = module.seal_certificate(certificate)
    inode = dimacs_path.stat().st_ino
    real_match = module._dimacs_matches
    attacked = False

    def overwrite_source_during_compare(stream, cnf):
        nonlocal attacked
        if not attacked:
            attacked = True
            _overwrite_same_inode(dimacs_path, valid)
            try:
                return real_match(stream, cnf)
            finally:
                _overwrite_same_inode(dimacs_path, invalid)
        return real_match(stream, cnf)

    monkeypatch.setattr(module, "_dimacs_matches", overwrite_source_during_compare)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert attacked is True
    assert dimacs_path.stat().st_ino == inode
    assert result["valid"] is False
    assert any("DIMACS does not reproduce" in item for item in result["failures"])


def test_checker_binary_path_swap_cannot_execute_unhashed_replacement(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    rejecting = b"#!/usr/bin/env python3\nraise SystemExit(1)\n"
    _replace_checker_binary(
        tmp_path,
        certificate,
        checkers,
        "drat",
        rejecting,
    )
    binary_path = tmp_path / _proof_check(certificate, "drat")["checker"][
        "binary"
    ]["path"]
    replacement = tmp_path / "unhashed-checker"
    replacement.write_bytes(
        b"#!/usr/bin/env python3\nprint('s VERIFIED')\n"
    )
    os.chmod(replacement, 0o755)
    certificate = module.seal_certificate(certificate)
    real_run = module.subprocess.run
    swapped = False

    def swapping_run(argv, **kwargs):
        nonlocal swapped
        assert argv[0].startswith("/proc/self/fd/")
        if not swapped:
            os.replace(replacement, binary_path)
            swapped = True
        return real_run(argv, **kwargs)

    monkeypatch.setattr(module.subprocess, "run", swapping_run)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert swapped is True
    assert result["valid"] is False
    assert any("checker exit mismatch" in item for item in result["failures"])


def test_checker_binary_same_inode_overwrite_cannot_execute_replacement(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    rejecting = b"#!/usr/bin/env python3\nraise SystemExit(1)\n"
    accepting = b"#!/usr/bin/env python3\nprint('s VERIFIED')\n"
    _replace_checker_binary(
        tmp_path,
        certificate,
        checkers,
        "drat",
        rejecting,
    )
    binary_path = tmp_path / _proof_check(certificate, "drat")["checker"][
        "binary"
    ]["path"]
    certificate = module.seal_certificate(certificate)
    inode = binary_path.stat().st_ino
    real_run = module.subprocess.run
    attacked = False

    def overwriting_run(argv, **kwargs):
        nonlocal attacked
        if not attacked:
            attacked = True
            snapshot_fd = int(argv[0].rsplit("/", 1)[1])
            snapshot_metadata = os.fstat(snapshot_fd)
            source_metadata = binary_path.stat()
            assert (snapshot_metadata.st_dev, snapshot_metadata.st_ino) != (
                source_metadata.st_dev,
                source_metadata.st_ino,
            )
            required_seals = (
                fcntl.F_SEAL_SEAL
                | fcntl.F_SEAL_SHRINK
                | fcntl.F_SEAL_GROW
                | fcntl.F_SEAL_WRITE
            )
            assert fcntl.fcntl(snapshot_fd, fcntl.F_GET_SEALS) == required_seals
            assert fcntl.fcntl(snapshot_fd, fcntl.F_GETFL) & os.O_NONBLOCK == 0
            _overwrite_same_inode(binary_path, accepting)
            try:
                return real_run(argv, **kwargs)
            finally:
                _overwrite_same_inode(binary_path, rejecting)
        return real_run(argv, **kwargs)

    monkeypatch.setattr(module.subprocess, "run", overwriting_run)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert attacked is True
    assert binary_path.stat().st_ino == inode
    assert result["valid"] is False
    assert any("checker exit mismatch" in item for item in result["failures"])


def test_matrix_bundle_path_swap_cannot_redirect_parsed_json(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    descriptor = certificate["matrix_bundle"]
    matrix_path = tmp_path / descriptor["path"]
    original = matrix_path.read_bytes()
    invalid_bundle = json.loads(original)
    invalid_bundle["logical_basis_method"] = "tampered-method"
    invalid_bundle["bundle_sha256"] = module.canonical_sha256(
        invalid_bundle,
        omit="bundle_sha256",
    )
    invalid_bytes = (
        json.dumps(invalid_bundle, sort_keys=True, separators=(",", ":")).encode()
        + b"\n"
    )
    certificate["matrix_bundle"] = _write(matrix_path, invalid_bytes)
    replacement = tmp_path / "valid-matrices.json"
    replacement.write_bytes(original)
    certificate = module.seal_certificate(certificate)
    real_load = module.json.load
    swapped = False

    def swapping_load(stream, *args, **kwargs):
        nonlocal swapped
        if not swapped:
            os.replace(replacement, matrix_path)
            swapped = True
        return real_load(stream, *args, **kwargs)

    monkeypatch.setattr(module.json, "load", swapping_load)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert swapped is True
    assert result["valid"] is False
    assert any("matrix bundle identity" in item for item in result["failures"])


def test_matrix_bundle_same_inode_overwrite_cannot_redirect_parsed_json(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    descriptor = certificate["matrix_bundle"]
    matrix_path = tmp_path / descriptor["path"]
    valid = matrix_path.read_bytes()
    invalid_bundle = json.loads(valid)
    invalid_bundle["logical_basis_method"] = "tampered-method"
    invalid_bundle["bundle_sha256"] = module.canonical_sha256(
        invalid_bundle,
        omit="bundle_sha256",
    )
    invalid = (
        json.dumps(invalid_bundle, sort_keys=True, separators=(",", ":")).encode()
        + b"\n"
    )
    certificate["matrix_bundle"] = _write(matrix_path, invalid)
    certificate = module.seal_certificate(certificate)
    inode = matrix_path.stat().st_ino
    real_load = module.json.load
    attacked = False

    def overwrite_source_during_parse(stream, *args, **kwargs):
        nonlocal attacked
        if not attacked:
            attacked = True
            _overwrite_same_inode(matrix_path, valid)
            try:
                return real_load(stream, *args, **kwargs)
            finally:
                _overwrite_same_inode(matrix_path, invalid)
        return real_load(stream, *args, **kwargs)

    monkeypatch.setattr(module.json, "load", overwrite_source_during_parse)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert attacked is True
    assert matrix_path.stat().st_ino == inode
    assert result["valid"] is False
    assert any("matrix bundle identity" in item for item in result["failures"])


def test_isometry_path_swap_cannot_redirect_parsed_json(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(
        tmp_path,
        isometric=True,
    )
    descriptor = certificate["distance_proof"]["lower_bound"]["xz_isometry"]
    isometry_path = tmp_path / descriptor["path"]
    original = isometry_path.read_bytes()
    invalid = json.loads(original)
    invalid["matrix_sha256"]["H_X"] = "0" * 64
    invalid["artifact_sha256"] = module.canonical_sha256(
        invalid,
        omit="artifact_sha256",
    )
    invalid_bytes = (
        json.dumps(invalid, sort_keys=True, separators=(",", ":")).encode()
        + b"\n"
    )
    certificate["distance_proof"]["lower_bound"]["xz_isometry"] = _write(
        isometry_path,
        invalid_bytes,
    )
    replacement = tmp_path / "valid-isometry.json"
    replacement.write_bytes(original)
    certificate = module.seal_certificate(certificate)
    real_load = module.json.load
    loads = 0

    def swapping_second_load(stream, *args, **kwargs):
        nonlocal loads
        loads += 1
        if loads == 2:
            os.replace(replacement, isometry_path)
        return real_load(stream, *args, **kwargs)

    monkeypatch.setattr(module.json, "load", swapping_second_load)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert loads == 2
    assert result["valid"] is False
    assert any("matrix hash binding" in item for item in result["failures"])


def test_isometry_same_inode_overwrite_cannot_redirect_parsed_json(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(
        tmp_path,
        isometric=True,
    )
    descriptor = certificate["distance_proof"]["lower_bound"]["xz_isometry"]
    isometry_path = tmp_path / descriptor["path"]
    valid = isometry_path.read_bytes()
    invalid_artifact = json.loads(valid)
    invalid_artifact["matrix_sha256"]["H_X"] = "0" * 64
    certificate = _rewrite_isometry_artifact(
        tmp_path,
        certificate,
        invalid_artifact,
    )
    invalid = isometry_path.read_bytes()
    inode = isometry_path.stat().st_ino
    real_load = module.json.load
    loads = 0

    def overwrite_source_during_second_parse(stream, *args, **kwargs):
        nonlocal loads
        loads += 1
        if loads == 2:
            _overwrite_same_inode(isometry_path, valid)
            try:
                return real_load(stream, *args, **kwargs)
            finally:
                _overwrite_same_inode(isometry_path, invalid)
        return real_load(stream, *args, **kwargs)

    monkeypatch.setattr(module.json, "load", overwrite_source_during_second_parse)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert loads == 2
    assert isometry_path.stat().st_ino == inode
    assert result["valid"] is False
    assert any("matrix hash binding" in item for item in result["failures"])


def test_dispatch_tamper_stays_invalid_and_can_never_promote_calibration(
    tmp_path,
    monkeypatch,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    _install_fixture_policy(monkeypatch, policy, authoritative)
    certificate["disposition"]["win_awarded"] = True
    certificate["disposition"]["formal_win_eligible"] = True
    certificate = module.seal_certificate(certificate)
    result = dispatch.verify_certificate(
        certificate,
        known_answer_artifact=tmp_path / "unused-known-answer.json",
        artifact_root=tmp_path,
        trusted_checkers=checkers,
        checker_timeout_s=FIXTURE_CHECKER_TIMEOUT_S,
    )
    assert result["valid"] is False
    assert result["passed"] is False
    assert result["win_awarded"] is False
    assert result["selected_win"] is False
    assert result["trusted_win"] is False
    assert result["formal_win"] is False


def test_dispatch_rejects_unsupported_certificate_type():
    with pytest.raises(ValueError, match="unsupported certificate_type"):
        dispatch.verifier_for_certificate({"certificate_type": "unsupported-v1"})


def test_installed_policy_is_exact_published_anchor_and_non_novel_by_role():
    policy = module.installed_anchor_policy()
    assert policy["anchor"]["candidate_sha256"].startswith("2ebf783f")
    assert policy["anchor"]["paper"]["identifier"] == "arXiv:2606.17268"
    assert policy["anchor"]["paper"]["upstream_commit"] == "a828dc43c55982e0212febea634775d36bf6e968"
    assert policy["anchor"]["paper"]["source_record"]["sha256"] == "1797447d6bea96ffda61b4ce6a91b560b6d52fe2784983c01df6166c5ed69734"
    assert (policy["n"], policy["k"], policy["distance"]) == (224, 12, 16)
    assert policy["target"]["required_distance"] == 15


def test_valid_proof_is_calibration_only_and_never_awards_win(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result == {
        "valid": True,
        "proof_valid": True,
        "calibration_valid": True,
        "passed": False,
        "win_awarded": False,
        "selected_win": False,
        "trusted_win": False,
        "formal_win": False,
        "failures": [],
    }


def test_valid_single_sector_proof_requires_carried_isometry(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(
        tmp_path,
        isometric=True,
    )
    lower = certificate["distance_proof"]["lower_bound"]
    assert [item["sector"] for item in lower["sectors"]] == ["X"]
    assert "xz_isometry" in lower
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"], result["failures"]


def test_certificate_self_hash_tamper_fails(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    certificate["certificate_sha256"] = "0" * 64
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and "certificate self hash mismatch" in result["failures"]


@pytest.mark.parametrize("schema_version", [True, 1.0])
def test_certificate_schema_version_requires_exact_integer_one(
    tmp_path,
    schema_version,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    certificate["schema_version"] = schema_version
    certificate = module.seal_certificate(certificate)

    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert result["valid"] is False
    assert any("schema/type mismatch" in failure for failure in result["failures"])


@pytest.mark.parametrize("schema_version", [True, 1.0])
def test_matrix_bundle_schema_version_requires_exact_integer_one(
    tmp_path,
    schema_version,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    path = tmp_path / certificate["matrix_bundle"]["path"]
    bundle = json.loads(path.read_bytes())
    bundle["schema_version"] = schema_version
    certificate = _rewrite_matrix_bundle(tmp_path, certificate, bundle)

    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert result["valid"] is False
    assert any("matrix bundle identity" in failure for failure in result["failures"])


@pytest.mark.parametrize("schema_version", [True, 1.0])
def test_isometry_schema_version_requires_exact_integer_one(
    tmp_path,
    schema_version,
):
    certificate, policy, checkers, authoritative = _fixture(
        tmp_path,
        isometric=True,
    )
    descriptor = certificate["distance_proof"]["lower_bound"]["xz_isometry"]
    path = tmp_path / descriptor["path"]
    artifact = json.loads(path.read_bytes())
    artifact["schema_version"] = schema_version
    certificate = _rewrite_isometry_artifact(tmp_path, certificate, artifact)

    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert result["valid"] is False
    assert any("isometry artifact identity" in failure for failure in result["failures"])


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("calibration_only", 1),
        ("target_threshold_satisfied", 1),
        ("selected_win_eligible", 0),
        ("trusted_win_eligible", 0),
        ("formal_win_eligible", 0),
        ("win_awarded", 0),
    ],
)
def test_disposition_boolean_fields_reject_equal_integer_aliases(
    tmp_path,
    field,
    value,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    certificate["disposition"][field] = value
    certificate = module.seal_certificate(certificate)

    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert result["valid"] is False
    assert any("no-win disposition" in failure for failure in result["failures"])


@pytest.mark.parametrize(
    ("location", "failure_fragment"),
    [
        ("parameters.k", "published parameters"),
        ("parameters.n", "published parameters"),
        ("claimed_distance", "exact-distance claim"),
        ("max_weight", "lower-bound threshold"),
        ("num_variables", "CNF instance binding"),
        ("num_clauses", "CNF instance binding"),
        ("witness.weight", "upper witness is not exact claimed weight"),
        ("witness.logical_syndrome", "upper witness logical syndrome mismatch"),
        ("target.k", "target binding mismatch"),
        ("anchor.schema_version", "anchor/catalog/paper"),
    ],
)
def test_json_numeric_bindings_reject_python_equal_type_aliases(
    tmp_path,
    location,
    failure_fragment,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    witness = certificate["distance_proof"]["upper_bound"]["witness"]
    if location == "parameters.k":
        certificate["parameters"]["k"] = True
    elif location == "parameters.n":
        certificate["parameters"]["n"] = 481.0
    elif location == "claimed_distance":
        certificate["distance_proof"]["claimed_distance"] = 16.0
    elif location == "max_weight":
        certificate["distance_proof"]["lower_bound"]["max_weight"] = 15.0
    elif location in {"num_variables", "num_clauses"}:
        unit = _first_unit(certificate)
        unit[location] = float(unit[location])
    elif location == "witness.weight":
        witness["weight"] = 16.0
        witness["witness_sha256"] = module.canonical_sha256(
            witness,
            omit="witness_sha256",
        )
    elif location == "witness.logical_syndrome":
        witness["logical_syndrome"] = [True]
        witness["witness_sha256"] = module.canonical_sha256(
            witness,
            omit="witness_sha256",
        )
    elif location == "target.k":
        certificate["target"]["k"] = True
        certificate["target"]["binding_sha256"] = module.canonical_sha256(
            certificate["target"],
            omit="binding_sha256",
        )
    elif location == "anchor.schema_version":
        certificate["anchor"]["action_catalog"]["schema_version"] = True
    else:  # pragma: no cover - parameter list is closed above
        raise AssertionError(location)
    certificate = module.seal_certificate(certificate)

    result = _validate(tmp_path, certificate, policy, checkers, authoritative)

    assert result["valid"] is False
    assert any(failure_fragment in failure for failure in result["failures"]), result


def test_anchor_paper_commit_tamper_fails_even_when_resealed(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    certificate["anchor"]["paper"]["upstream_commit"] = "0" * 40
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and any("anchor/catalog/paper" in item for item in result["failures"])


def test_matrix_artifact_byte_tamper_fails(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    path = tmp_path / certificate["matrix_bundle"]["path"]
    path.write_bytes(path.read_bytes() + b" ")
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and any("matrix_bundle" in item for item in result["failures"])


def test_dimacs_reencoding_tamper_fails_even_with_new_artifact_hash(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    record = _first_unit(certificate)
    path = tmp_path / record["dimacs"]["path"]
    altered = b"c harmless-looking but noncanonical comment\n" + path.read_bytes()
    record["dimacs"] = _write(path, altered)
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and any("DIMACS does not reproduce" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
def test_each_proof_tamper_is_rejected_by_its_replayed_checker(
    tmp_path,
    proof_format,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    record = _proof_check(certificate, proof_format)
    path = tmp_path / record["proof"]["artifact"]["path"]
    record["proof"]["artifact"] = _write(
        path,
        f"INVALID-{proof_format.upper()}-FIXTURE\n".encode(),
    )
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"]
    assert any("checker exit mismatch" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
def test_each_checker_binary_tamper_fails_trusted_policy(tmp_path, proof_format):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    record = _proof_check(certificate, proof_format)
    path = tmp_path / record["checker"]["binary"]["path"]
    altered = path.read_bytes() + b"# altered\n"
    record["checker"]["binary"] = _write(path, altered)
    os.chmod(path, 0o755)
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and any("trusted verifier policy" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
def test_each_checker_source_tamper_fails_trusted_policy(tmp_path, proof_format):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    record = _proof_check(certificate, proof_format)
    source = record["checker"]["source"]
    path = tmp_path / source["artifact"]["path"]
    source["artifact"] = _write(path, b"different source\n")
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and any("trusted verifier policy" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
@pytest.mark.parametrize("field", ["exit_code", "semantic_stdout_sha256"])
def test_each_checker_exit_and_semantic_binding_tamper_fails(
    tmp_path,
    field,
    proof_format,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    run = _proof_check(certificate, proof_format)["checker"]["run"]
    run[field] = 1 if field == "exit_code" else "0" * 64
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and any("checker" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
def test_recorded_raw_stream_hash_is_provenance_not_fresh_timing_equality(
    tmp_path,
    proof_format,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    run = _proof_check(certificate, proof_format)["checker"]["run"]
    run["stdout_sha256"] = "0" * 64
    run["stderr_sha256"] = "f" * 64
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"], result["failures"]


@pytest.mark.parametrize("field", ["stdout_sha256", "stderr_sha256"])
def test_recorded_raw_stream_hash_still_requires_strict_sha256_syntax(
    tmp_path,
    field,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    _proof_check(certificate, "drat")["checker"]["run"][field] = "not-a-sha"
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"] is False
    assert any("stream hash" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
@pytest.mark.parametrize("stdout", [b"NOT VERIFIED\n", b""])
def test_exit_zero_without_tool_specific_success_line_is_rejected(
    tmp_path,
    proof_format,
    stdout,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    proof_check = _proof_check(certificate, proof_format)
    checker = proof_check["checker"]
    binary_path = tmp_path / checker["binary"]["path"]
    replacement = (
        b"#!/usr/bin/env python3\n"
        b"import sys\n"
        + f"sys.stdout.buffer.write({stdout!r})\n".encode()
        + b"raise SystemExit(0)\n"
    )
    checker["binary"] = _write(binary_path, replacement)
    os.chmod(binary_path, 0o755)
    checker["run"]["stdout_sha256"] = hashlib.sha256(stdout).hexdigest()
    checker_id = checker["checker_id"]
    checkers[checker_id]["binary_sha256"] = checker["binary"]["sha256"]
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"] is False
    assert any("semantic success marker" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
def test_fresh_checker_timing_drift_does_not_require_raw_stdout_hash_equality(
    tmp_path,
    proof_format,
):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    success = "s VERIFIED" if proof_format == "drat" else "c VERIFIED"
    replacement = f"""#!/usr/bin/env python3
import time
print({success!r})
print('c verification time', time.monotonic_ns())
""".encode()
    _replace_checker_binary(
        tmp_path,
        certificate,
        checkers,
        proof_format,
        replacement,
    )
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"], result["failures"]


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
def test_fresh_checker_stderr_must_remain_empty(tmp_path, proof_format):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    success = "s VERIFIED" if proof_format == "drat" else "c VERIFIED"
    replacement = f"""#!/usr/bin/env python3
import sys
print({success!r})
sys.stderr.write('unexpected warning\\n')
""".encode()
    _replace_checker_binary(
        tmp_path,
        certificate,
        checkers,
        proof_format,
        replacement,
    )
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"] is False
    assert any("fresh stderr" in item for item in result["failures"])


@pytest.mark.parametrize("proof_format", ["drat", "lrat"])
def test_each_checker_role_tamper_fails(tmp_path, proof_format):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    _proof_check(certificate, proof_format)["checker"]["checker_role"] = "wrong-role"
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"] is False
    assert any("checker role" in item for item in result["failures"])


@pytest.mark.parametrize("missing_format", ["drat", "lrat"])
def test_each_unit_requires_both_proof_formats(tmp_path, missing_format):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    _first_unit(certificate)["proof_checks"].pop(missing_format)
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"] is False
    assert any("proof_checks" in item for item in result["failures"])


def test_w16_algebraic_tamper_fails_after_metadata_is_resealed(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    witness = certificate["distance_proof"]["upper_bound"]["witness"]
    one = witness["bits"].index(1)
    zero = witness["bits"].index(0)
    witness["bits"][one], witness["bits"][zero] = 0, 1
    witness["support"] = [index for index, bit in enumerate(witness["bits"]) if bit]
    witness["logical_syndrome"] = [1]
    witness["witness_sha256"] = module.canonical_sha256(witness, omit="witness_sha256")
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and any("stabilizer syndrome" in item for item in result["failures"])


def test_target_tamper_fails_even_with_fresh_target_and_certificate_hashes(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    certificate["target"]["required_distance"] = 15
    certificate["target"]["binding_sha256"] = module.canonical_sha256(
        certificate["target"], omit="binding_sha256"
    )
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"] and "target binding mismatch" in result["failures"]


def test_calibration_cannot_be_promoted_to_any_win_by_resealing(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    disposition = certificate["disposition"]
    disposition["calibration_only"] = False
    disposition["selected_win_eligible"] = True
    disposition["trusted_win_eligible"] = True
    disposition["formal_win_eligible"] = True
    disposition["win_awarded"] = True
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"]
    assert result["passed"] is False
    assert result["win_awarded"] is False
    assert result["selected_win"] is False
    assert result["trusted_win"] is False
    assert result["formal_win"] is False
    assert any("no-win disposition" in item for item in result["failures"])


def test_first_nonzero_partition_cover_rebuilds_each_unit(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(tmp_path)
    hx, hz, lx, lz, _bundle, _cnfs = _hgp_distance_16_material()
    for group in certificate["distance_proof"]["lower_bound"]["sectors"]:
        sector = group["sector"]
        group["cover"] = module.PARTITION_COVER
        unit = group["units"][0]
        unit["partition_index"] = 0
        checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
        cnf = build_css_threshold_cnf(
            checks,
            logicals,
            max_weight=15,
            sector=sector,
            cardinality_encoding="seqcounter",
            partition_index=0,
        )
        unit.update({
            "cnf_sha256": cnf["cnf_sha256"],
            "num_variables": cnf["num_variables"],
            "num_clauses": cnf["num_clauses"],
            "dimacs": _write(
                tmp_path / f"{sector.lower()}-p0.cnf",
                module.render_dimacs(cnf),
            ),
        })
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert result["valid"], result["failures"]


def test_partition_cover_rejects_missing_duplicate_or_out_of_order_indices():
    valid = [{"partition_index": index} for index in range(12)]
    assert module._expected_partition_indices(
        cover=module.PARTITION_COVER,
        k=12,
        units=valid,
    ) == list(range(12))
    invalid_covers = (
        valid[:-1],
        valid + [{"partition_index": 11}],
        [*valid[:5], valid[6], valid[5], *valid[7:]],
        [{"partition_index": None}],
    )
    for invalid in invalid_covers:
        with pytest.raises(ValueError, match="exactly 0..k-1"):
            module._expected_partition_indices(
                cover=module.PARTITION_COVER,
                k=12,
                units=invalid,
            )


@pytest.mark.parametrize("partition_index", [False, 0.0])
def test_partition_cover_rejects_bool_and_float_indices(partition_index):
    with pytest.raises(ValueError, match="exact integers"):
        module._expected_partition_indices(
            cover=module.PARTITION_COVER,
            k=1,
            units=[{"partition_index": partition_index}],
        )


def test_installed_symmetry_anchor_cover_replays_exact_eight_orbits():
    policy = module.installed_anchor_policy()
    _code, hx, hz, *_rest = _rebuild_claim({"construction": policy["construction"]})
    report = module._construction_symmetry_report(
        policy["construction"],
        np.asarray(hx, dtype=np.uint8) & 1,
        np.asarray(hz, dtype=np.uint8) & 1,
    )
    representatives = [0, 1, 2, 16, 112, 113, 114, 128]
    assert report["verified"] is True
    assert report["orbits_cover_all_qubits"] is True
    assert report["orbit_representatives"] == representatives
    assert [len(orbit) for orbit in report["orbits"]] == [28] * 8
    assert report["report_sha256"] == "1110c4a653a7ef6a06f5322700d33c48006d652de5eaca685640b5c3a636e161"
    cubes = build_anchor_cover_cubes(tuple(representatives))
    units = [
        {"partition_index": None, "anchor_cube": copy.deepcopy(cube)}
        for cube in cubes
    ]
    assert module._symmetry_unit_cover(units, cubes) == [None] * 8
    assert cubes[0]["zero_anchor_indices"] == []
    assert cubes[0]["one_anchor_index"] == 0
    assert cubes[-1]["zero_anchor_indices"] == representatives[:-1]
    assert cubes[-1]["one_anchor_index"] == 128
    for invalid in (
        units[:-1],
        [*units[:1], units[0], *units[2:]],
        [{**units[0], "partition_index": 0}, *units[1:]],
    ):
        with pytest.raises(ValueError, match="symmetry anchor|every symmetry"):
            module._symmetry_unit_cover(invalid, cubes)


def test_canonical_installed_xz_isometry_artifact_replays_both_directions():
    root = Path(module.__file__).resolve().parent
    path = root / "anchor-xz-isometry-v1.json"
    payload = path.read_bytes()
    descriptor = {
        "path": path.name,
        "bytes": len(payload),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }
    policy = module.installed_anchor_policy()
    hx, hz = module._default_authoritative_matrices(policy["construction"])
    artifact = module._validate_xz_isometry_artifact(
        descriptor,
        root=root,
        hx=hx,
        hz=hz,
        supplied_proof_sector="X",
    )
    assert artifact["matrix_sha256"] == {
        "H_X": "a449fa1905d45becbc32a77544bc73b60acfdd4e598aba6dde10ff19098b7eea",
        "H_Z": "39267ddb41b624e7791fecf4008b8c3367222a4e2dd28d632ad5474f02e6efc5",
    }
    assert artifact["row_permutation_sha256"] == (
        "4f985b2f6a2c966845476e8a77d167737b67d8d27a06ce9f89805a38cf18906c"
    )
    assert artifact["qubit_permutation_sha256"] == (
        "e7147776a16d3df9ed15ab4a33dea18f6f479422e232593bc1fbb0086f80b195"
    )


@pytest.mark.parametrize(
    ("mutation", "failure_fragment"),
    [
        ("missing", "exactly"),
        ("duplicate", "bijection"),
        ("out_of_order", "forward matrix identity"),
        ("noninvolution", "involution"),
        ("one_way_only", "fields are not exact"),
        ("matrix_hash", "matrix hash binding"),
        ("sector_direction", "sector direction"),
    ],
)
def test_xz_isometry_tamper_fails_closed_after_resealing(
    tmp_path, mutation, failure_fragment
):
    certificate, policy, checkers, authoritative = _fixture(
        tmp_path, isometric=True
    )
    path = tmp_path / certificate["distance_proof"]["lower_bound"]["xz_isometry"]["path"]
    artifact = json.loads(path.read_text())
    if mutation == "missing":
        artifact["row_permutation"].pop()
        artifact["row_permutation_sha256"] = module.permutation_sha256(
            artifact["row_permutation"]
        )
    elif mutation == "duplicate":
        artifact["row_permutation"][1] = artifact["row_permutation"][0]
        artifact["row_permutation_sha256"] = module.permutation_sha256(
            artifact["row_permutation"]
        )
    elif mutation == "out_of_order":
        artifact["row_permutation"][1], artifact["row_permutation"][2] = (
            artifact["row_permutation"][2],
            artifact["row_permutation"][1],
        )
        artifact["row_permutation_sha256"] = module.permutation_sha256(
            artifact["row_permutation"]
        )
    elif mutation == "noninvolution":
        values = artifact["qubit_permutation"]
        values[0], values[1], values[2] = values[1], values[2], values[0]
        artifact["qubit_permutation_sha256"] = module.permutation_sha256(values)
    elif mutation == "one_way_only":
        artifact.pop("reverse_identity")
    elif mutation == "matrix_hash":
        artifact["matrix_sha256"]["H_X"] = "0" * 64
    elif mutation == "sector_direction":
        artifact["proof_sector"] = "Z"
        artifact["derived_sector"] = "X"
    else:  # pragma: no cover - parameter list is closed above
        raise AssertionError(mutation)
    certificate = _rewrite_isometry_artifact(tmp_path, certificate, artifact)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"]
    assert any(failure_fragment in failure for failure in result["failures"]), result


def test_isometric_single_sector_cover_rejects_missing_checker_verified_unit(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(
        tmp_path, isometric=True
    )
    certificate["distance_proof"]["lower_bound"]["sectors"][0]["units"] = []
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"]
    assert any("nonempty list" in failure for failure in result["failures"])


def test_single_sector_without_isometry_cannot_use_legacy_schema(tmp_path):
    certificate, policy, checkers, authoritative = _fixture(
        tmp_path, isometric=True
    )
    certificate["distance_proof"]["lower_bound"].pop("xz_isometry")
    certificate = module.seal_certificate(certificate)
    result = _validate(tmp_path, certificate, policy, checkers, authoritative)
    assert not result["valid"]
    assert any("exactly X and Z" in failure for failure in result["failures"])
