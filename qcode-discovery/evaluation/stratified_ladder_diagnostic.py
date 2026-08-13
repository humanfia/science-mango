"""Stratified, proof-safe low-weight ladder diagnostic for sealed CSS runs.

This module is intentionally separate from the five-stage pipeline.  It reads
an immutable Stage-2 ranked snapshot, excludes every candidate already audited
at either Stage 1 or Stage 2, independently replays the stored ``d >= 5``
evidence, and selects a deterministic, stratified sample.  The diagnostic then
runs both logical sectors at thresholds 6, 8, and (for survivors)
``required_distance - 1``.

The scientific asymmetry is strict:

* a replayed SAT operator is a trusted negative witness;
* a lower bound advances only when *both* sectors are UNSAT;
* UNKNOWN is fail-open and is counted as a survivor.

The command is resumable through one self-hashed result file per candidate.
It never mutates the source run and never promotes a candidate into a release.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import importlib.metadata
import json
import math
import os
import stat
import subprocess
import sys
import tempfile
import time
from collections import Counter
from collections.abc import Callable, Iterable, Mapping, Sequence
from pathlib import Path
from typing import Any

from evaluation.construction import build_css_code_from_claim
from evaluation.distance_milp import get_code_matrices
from evaluation.distance_sat import css_sector_matrices
from evaluation.low_weight_oracle import (
    evaluate_low_weight_sector,
    verify_css_low_weight_oracle,
    verify_low_weight_sector_evidence,
)
from evaluation.process_hard_wall import run_isolated_call
from evaluation.registry import DEFAULT_REGISTRY, load_registry
from evaluation.selection_ledger import validate_selection_ledger
from evaluation.selection_ledger import snapshot_identity_sha256
from evaluation.solver_budget import acquire_solver_budget
from evaluation.target_policy import TARGET_MODE_SCALAR, target_binding
from evolve.openevolve_evaluator import _normalized_stage2_lower_bound_row
from humanize.audit_state import authoritative_candidate_digest
from humanize.negative_evidence import (
    replay_structural_logical_basis_rejection,
)
from humanize.state import code_key
from scripts.audit_candidate_pool import (
    _is_trusted_terminal_rejection,
    _ranked_selection_key,
    canonicalize_for_audit,
)


DIAGNOSTIC_SCHEMA_VERSION = 1
DIAGNOSTIC_KIND = "qcode-stratified-target-aware-ladder-v1"
SELECTION_POLICY = "published-volume-lattice-q-mechanism-maximin-v1"
DECISION_POLICY = "ansatz-or-deep-proof-gate-v1"
DEFAULT_SAMPLE_SIZE = 64
MIN_SAMPLE_SIZE = 48
MAX_SAMPLE_SIZE = 96
DEFAULT_WORKERS = 4
DEFAULT_TIMEOUTS = {6: 120.0, 8: 300.0, "target": 900.0}
RUNG_THRESHOLDS = (6, 8)


class DiagnosticError(RuntimeError):
    """Raised when immutable inputs or diagnostic evidence fail closed."""


def _canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _file_identity(path: Path) -> dict[str, Any]:
    stat = path.stat()
    return {
        "path": str(path.resolve()),
        "bytes": stat.st_size,
        "sha256": _file_sha256(path),
    }


def _stat_identity(metadata: os.stat_result) -> dict[str, int]:
    return {
        "device": int(metadata.st_dev),
        "inode": int(metadata.st_ino),
        "bytes": int(metadata.st_size),
        "mtime_ns": int(metadata.st_mtime_ns),
    }


def _validate_historical_file_identity(
    expected: Mapping[str, Any],
    *,
    label: str,
) -> Path:
    """Replay an immutable historical file identity without rotating it.

    A ranked snapshot is evidence produced by the sealed run.  Its historical
    source fingerprint is provenance, not a cache key that should rotate when
    this independent diagnostic is added.  The original input and registry
    bytes, however, must still match exactly.
    """

    path_text = expected.get("path")
    expected_stat = expected.get("stat")
    expected_sha256 = expected.get("sha256")
    if (
        not isinstance(path_text, str)
        or not isinstance(expected_stat, Mapping)
        or not isinstance(expected_sha256, str)
    ):
        raise DiagnosticError(f"{label} identity is malformed")
    path = Path(path_text)
    try:
        before = path.lstat()
    except OSError as exc:
        raise DiagnosticError(f"{label} is unavailable") from exc
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        raise DiagnosticError(f"{label} is not a regular non-symlink file")
    if _stat_identity(before) != dict(expected_stat):
        raise DiagnosticError(f"{label} stat identity changed")
    actual_sha256 = _file_sha256(path)
    after = path.lstat()
    if (
        _stat_identity(after) != dict(expected_stat)
        or actual_sha256 != expected_sha256
    ):
        raise DiagnosticError(f"{label} bytes changed")
    return path


def _read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise DiagnosticError(f"cannot read JSON object {path.name}: {exc}") from exc
    if not isinstance(value, dict):
        raise DiagnosticError(f"{path.name} is not a JSON object")
    return value


def _read_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, 1):
            try:
                value = json.loads(line)
            except json.JSONDecodeError as exc:
                raise DiagnosticError(
                    f"{path.name} line {line_number} is invalid JSON"
                ) from exc
            if not isinstance(value, dict):
                raise DiagnosticError(
                    f"{path.name} line {line_number} is not an object"
                )
            yield value


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def _seal(value: Mapping[str, Any], field: str) -> dict[str, Any]:
    sealed = dict(value)
    sealed.pop(field, None)
    sealed[field] = _canonical_sha256(sealed)
    return sealed


def _atomic_json(path: Path, value: Mapping[str, Any]) -> None:
    _atomic_write(path, _canonical_bytes(dict(value)) + b"\n")


def _atomic_jsonl(path: Path, rows: Sequence[Mapping[str, Any]]) -> None:
    payload = b"".join(_canonical_bytes(dict(row)) + b"\n" for row in rows)
    _atomic_write(path, payload)


def _validate_self_hash(value: Mapping[str, Any], field: str) -> None:
    unsigned = dict(value)
    stored = unsigned.pop(field, None)
    if not isinstance(stored, str) or stored != _canonical_sha256(unsigned):
        raise DiagnosticError(f"{field} does not replay")


def _source_bindings() -> list[dict[str, Any]]:
    root = Path(__file__).resolve().parents[1]
    paths = (
        Path(__file__).resolve(),
        root / "evaluation" / "construction.py",
        root / "evaluation" / "bb_code.py",
        root / "evaluation" / "distance_milp.py",
        root / "evaluation" / "distance_sat.py",
        root / "evaluation" / "geometry.py",
        root / "evaluation" / "low_weight_oracle.py",
        root / "evaluation" / "process_hard_wall.py",
        root / "evaluation" / "registry.py",
        root / "evaluation" / "selection_ledger.py",
        root / "evaluation" / "solver_budget.py",
        root / "evaluation" / "structural_dedup.py",
        root / "evaluation" / "tanner_equivalence.py",
        root / "evaluation" / "target_policy.py",
        root / "evolve" / "openevolve_evaluator.py",
        root / "humanize" / "audit_state.py",
        root / "humanize" / "negative_evidence.py",
        root / "humanize" / "state.py",
        root / "scripts" / "audit_candidate_pool.py",
        Path(DEFAULT_REGISTRY).resolve(),
    )
    return [_file_identity(path) for path in paths]


def _runtime_binding() -> dict[str, Any]:
    packages: dict[str, str | None] = {}
    for distribution in ("numpy", "python-sat", "qldpc"):
        try:
            packages[distribution] = importlib.metadata.version(distribution)
        except importlib.metadata.PackageNotFoundError:
            packages[distribution] = None
    return {
        "python": list(sys.version_info[:3]),
        "implementation": sys.implementation.name,
        "packages": packages,
    }


def _twist(row: Mapping[str, Any]) -> int:
    geometry = row.get("geometry")
    if isinstance(geometry, Mapping):
        value = geometry.get("twist", 0)
        if isinstance(value, int) and not isinstance(value, bool):
            return value
    return 0


def _mechanism(row: Mapping[str, Any]) -> str:
    value = row.get("relation_type")
    return value.strip() if isinstance(value, str) and value.strip() else "unclassified"


def _strata(row: Mapping[str, Any]) -> dict[str, Any]:
    ell = int(row["ell"])
    m = int(row["m"])
    return {
        "published_volume": ell * m,
        "lattice": [ell, m],
        "twist": _twist(row),
        "lattice_q": [ell, m, _twist(row)],
        "algebraic_mechanism": _mechanism(row),
        "support_split": f"{len(row['A_terms'])}+{len(row['B_terms'])}",
    }


def _stable_identity(row: Mapping[str, Any]) -> tuple[str, str, str]:
    triage = row.get("triage_identity")
    novelty = row.get("structural_novelty")
    triage_digest = (
        triage.get("canonical_digest") if isinstance(triage, Mapping) else None
    )
    structural_digest = (
        novelty.get("canonical_digest") if isinstance(novelty, Mapping) else None
    )
    if not isinstance(triage_digest, str) or not triage_digest:
        raise DiagnosticError("candidate has no Stage-2 triage digest")
    if not isinstance(structural_digest, str) or not structural_digest:
        raise DiagnosticError("candidate has no structural digest")
    return code_key(dict(row)), structural_digest, triage_digest


def _candidate_score(
    row: Mapping[str, Any],
    *,
    selected: Sequence[Mapping[str, Any]],
) -> tuple[Any, ...]:
    strata = _strata(row)
    selected_strata = [_strata(value) for value in selected]
    volumes = Counter(value["published_volume"] for value in selected_strata)
    lattices = Counter(tuple(value["lattice"]) for value in selected_strata)
    lattice_q = Counter(tuple(value["lattice_q"]) for value in selected_strata)
    mechanisms = Counter(value["algebraic_mechanism"] for value in selected_strata)
    volume = strata["published_volume"]
    lattice = tuple(strata["lattice"])
    q_cell = tuple(strata["lattice_q"])
    mechanism = strata["algebraic_mechanism"]
    required = int(row["required_distance"])
    lower_bound = int(row["distance_lower_bound"])
    key, structural_digest, triage_digest = _stable_identity(row)
    # Lower values sort first.  Coverage and maximin balance precede target
    # proximity.  No BP/OSD distance or FOM field appears in this ordering.
    return (
        int(volume in volumes),
        volumes[volume],
        int(lattice in lattices),
        lattices[lattice],
        int(mechanism in mechanisms),
        mechanisms[mechanism],
        int(q_cell in lattice_q),
        lattice_q[q_cell],
        required - lower_bound,
        key,
        structural_digest,
        triage_digest,
    )


def stratified_candidate_order(
    rows: Sequence[Mapping[str, Any]],
    sample_size: int,
) -> list[dict[str, Any]]:
    """Return a deterministic maximin order over immutable strata.

    This pure helper does not grant proof credit.  ``prepare_diagnostic``
    independently rebuilds and replays each proposed row before accepting it.
    """

    if not MIN_SAMPLE_SIZE <= sample_size <= MAX_SAMPLE_SIZE:
        raise ValueError(
            f"sample_size must be in [{MIN_SAMPLE_SIZE}, {MAX_SAMPLE_SIZE}]"
        )
    remaining = [dict(row) for row in rows]
    ordered: list[dict[str, Any]] = []
    while remaining and len(ordered) < sample_size:
        remaining.sort(key=lambda row: _candidate_score(row, selected=ordered))
        ordered.append(remaining.pop(0))
    return ordered


def _candidate_claim(row: Mapping[str, Any]) -> dict[str, Any]:
    claim = {
        "ell": int(row["ell"]),
        "m": int(row["m"]),
        "A_terms": row["A_terms"],
        "B_terms": row["B_terms"],
    }
    if isinstance(row.get("geometry"), Mapping):
        claim["geometry"] = dict(row["geometry"])
    return claim


def _verify_initial_lower_bound(row: Mapping[str, Any]) -> dict[str, Any]:
    if not (
        row.get("distance_lower_bound") == 5
        and row.get("distance_lower_bound_proven") is True
        and row.get("distance_lower_bound_status") == "search_oracle_proven"
    ):
        raise DiagnosticError("candidate is not a claimed d>=5 row")
    normalized = _normalized_stage2_lower_bound_row(dict(row))
    if normalized is None or normalized.get("distance_lower_bound") != 5:
        raise DiagnosticError("authoritative d>=5 projection does not replay")
    canonical = canonicalize_for_audit(
        row,
        target_mode=TARGET_MODE_SCALAR,
    )
    novelty = canonical.get("novelty")
    if not isinstance(novelty, Mapping) or novelty.get("novel") is not True:
        raise DiagnosticError("candidate is not novel under fresh registry replay")
    code = build_css_code_from_claim(_candidate_claim(row))
    if int(code.num_qudits) != row.get("n") or int(code.dimension) != row.get("k"):
        raise DiagnosticError("candidate n/k do not replay")
    hx, hz, lx, lz = get_code_matrices(code)
    evidence = row.get("low_weight_oracle")
    if not isinstance(evidence, Mapping):
        raise DiagnosticError("candidate has no low-weight evidence")
    failures = verify_css_low_weight_oracle(evidence, hx, hz, lx, lz)
    if failures or evidence.get("outcome") != "UNSAT" or evidence.get("max_weight") != 4:
        raise DiagnosticError("d>=5 evidence does not replay: " + "; ".join(failures))
    recomputed_digest = authoritative_candidate_digest(row)
    _key, stored_digest, _triage = _stable_identity(row)
    if recomputed_digest != stored_digest:
        raise DiagnosticError("structural digest does not replay")
    return {
        "n": int(code.num_qudits),
        "k": int(code.dimension),
        "structural_digest": recomputed_digest,
        "initial_evidence_sha256": evidence.get("evidence_sha256"),
    }


def _manifest_replays(
    manifest: Mapping[str, Any],
    *,
    snapshot_path: Path,
    ledger_path: Path,
) -> dict[str, Any]:
    """Validate the sealed snapshot without treating it as a live cache.

    The upstream cache loader intentionally requires its *current* broad
    source fingerprint.  That is correct before reusing a cache inside the
    source run, but it is wrong for a later independent verifier: adding this
    verifier itself changes that broad fingerprint.  Here we instead bind and
    hash every original input, the registry, snapshot, offset index, chunks,
    and historical source/runtime metadata.  Selected proof rows are then
    reconstructed with the current verifier before receiving any credit.
    """

    unsigned = dict(manifest)
    stored = unsigned.pop("manifest_sha256", None)
    if stored != _canonical_sha256(unsigned):
        raise DiagnosticError("ranked snapshot manifest hash does not replay")
    if manifest.get("schema_version") != 1 or manifest.get("gate") != (
        "qldpc-stage2-ranked-snapshot"
    ):
        raise DiagnosticError("ranked snapshot manifest schema is unsupported")
    binding = manifest.get("binding")
    if not isinstance(binding, Mapping):
        raise DiagnosticError("ranked snapshot binding is absent")
    unsigned_binding = dict(binding)
    embedded_binding_sha256 = unsigned_binding.pop("binding_sha256", None)
    if (
        embedded_binding_sha256 != _canonical_sha256(unsigned_binding)
        or manifest.get("binding_sha256") != embedded_binding_sha256
        or binding.get("target_mode") != TARGET_MODE_SCALAR
        or binding.get("schema_version") != 1
        or binding.get("gate") != "qldpc-stage2-ranked-snapshot"
    ):
        raise DiagnosticError("ranked snapshot binding does not replay")
    inputs = binding.get("inputs")
    if not isinstance(inputs, list) or not inputs:
        raise DiagnosticError("ranked snapshot input binding is absent")
    for index, expected in enumerate(inputs):
        if not isinstance(expected, Mapping):
            raise DiagnosticError("ranked snapshot input identity is malformed")
        _validate_historical_file_identity(
            expected,
            label=f"ranked snapshot input {index}",
        )
    registry_identity = binding.get("known_code_registry")
    if not isinstance(registry_identity, Mapping):
        raise DiagnosticError("ranked snapshot registry identity is absent")
    _validate_historical_file_identity(
        registry_identity,
        label="ranked snapshot known-code registry",
    )

    identity = manifest.get("identity")
    if not isinstance(identity, Mapping):
        raise DiagnosticError("ranked snapshot identity is absent")
    snapshot_stat = manifest.get("snapshot_stat")
    offsets_stat = manifest.get("offsets_stat")
    offsets_path = Path(str(ledger_path) + ".ranked-snapshot.offsets")
    if (
        not isinstance(snapshot_stat, Mapping)
        or not isinstance(offsets_stat, Mapping)
        or _stat_identity(snapshot_path.lstat()) != dict(snapshot_stat)
        or _stat_identity(offsets_path.lstat()) != dict(offsets_stat)
    ):
        raise DiagnosticError("ranked snapshot or offset stat identity changed")
    if identity.get("snapshot_sha256") != _file_sha256(snapshot_path):
        raise DiagnosticError("ranked snapshot payload hash changed")
    if identity.get("offsets_sha256") != _file_sha256(offsets_path):
        raise DiagnosticError("ranked snapshot offset index hash changed")
    counts = manifest.get("counts")
    rows = manifest.get("snapshot_rows")
    eligible_rows = (
        counts.get("eligible_candidates") if isinstance(counts, Mapping) else None
    )
    if (
        not isinstance(rows, int)
        or isinstance(rows, bool)
        or not isinstance(eligible_rows, int)
        or isinstance(eligible_rows, bool)
        or not 0 <= eligible_rows <= rows
        or identity.get("rows") != rows
        or identity.get("eligible_rows") != eligible_rows
        or identity.get("binding_sha256") != embedded_binding_sha256
        or identity.get("counts_sha256") != _canonical_sha256(counts)
        or int(offsets_stat.get("bytes", -1)) != (rows + 1) * 8
    ):
        raise DiagnosticError("ranked snapshot identity/count binding is inconsistent")
    if (
        counts.get("unique_candidates") != rows
        or counts.get("eligible_candidates") != eligible_rows
        or counts.get("rejected_candidates") != rows - eligible_rows
    ):
        raise DiagnosticError("ranked snapshot counts are inconsistent")
    chunks = manifest.get("chunks")
    if (
        manifest.get("chunk_rows") != 128
        or identity.get("chunk_rows") != 128
        or not isinstance(chunks, list)
        or len(chunks) != math.ceil(rows / 128)
        or identity.get("chunk_index_sha256") != _canonical_sha256(chunks)
    ):
        raise DiagnosticError("ranked snapshot chunk index is inconsistent")

    seen: set[str] = set()
    previous_key: tuple[Any, ...] | None = None
    observed_rows = 0
    for index, row in enumerate(_read_jsonl(snapshot_path)):
        observed_rows += 1
        triage = row.get("triage_identity")
        digest = triage.get("canonical_digest") if isinstance(triage, Mapping) else None
        if not isinstance(digest, str) or not digest or digest in seen:
            raise DiagnosticError("ranked snapshot has a duplicate/invalid identity")
        terminal = _is_trusted_terminal_rejection(row)
        if (index < eligible_rows and terminal) or (index >= eligible_rows and not terminal):
            raise DiagnosticError("ranked snapshot eligible boundary does not replay")
        rank_key = _ranked_selection_key(row)
        if previous_key is not None and rank_key < previous_key:
            raise DiagnosticError("ranked snapshot rank order does not replay")
        seen.add(digest)
        previous_key = rank_key
    if observed_rows != rows:
        raise DiagnosticError("ranked snapshot row count binding is inconsistent")
    return {
        "historical_source_fingerprint": binding.get("source_fingerprint"),
        "historical_solver_runtime_sha256": _canonical_sha256(
            binding.get("solver_runtime")
        ),
        "input_count": len(inputs),
        "known_code_registry": dict(registry_identity),
    }


def _validate_twelve_round_boundary(run_root: Path) -> dict[str, Any]:
    state_path = run_root / "state.json"
    state = _read_json(state_path)
    if state.get("status") != "search-complete" or state.get("current_round") != 12:
        raise DiagnosticError("source run has not sealed exactly 12 rounds")
    rounds = state.get("rounds")
    if not isinstance(rounds, list) or len(rounds) != 12:
        raise DiagnosticError("source state does not bind 12 completed rounds")
    round_dirs = sorted((run_root / "rounds").glob("round-*"))
    if len(round_dirs) != 12 or any(path.name == "round-013" for path in round_dirs):
        raise DiagnosticError("source run directory is not an exact 12-round boundary")
    identities: list[dict[str, Any]] = []
    for number, directory in enumerate(round_dirs, 1):
        if directory.name != f"round-{number:03d}":
            raise DiagnosticError("round directory sequence is not contiguous")
        transaction_path = directory / "evolution-transaction.json"
        transaction = _read_json(transaction_path)
        if transaction.get("status") != "committed":
            raise DiagnosticError(f"{directory.name} transaction is not committed")
        for required_name in (
            "candidate-batch.jsonl",
            "selected.jsonl",
            "milp.jsonl",
            "review.json",
            "summary.md",
        ):
            if not (directory / required_name).is_file():
                raise DiagnosticError(f"{directory.name}/{required_name} is absent")
        identities.append(_file_identity(transaction_path))
    return {"state": _file_identity(state_path), "round_transactions": identities}


def _eligible_rows(
    *,
    run_root: Path,
    pipeline_root: Path,
    output_dir: Path,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    boundary = _validate_twelve_round_boundary(run_root)
    state = _read_json(run_root / "state.json")
    solver_state = pipeline_root / "solver-state"
    ledger_path = solver_state / "stage2-selection-ledger.json"
    snapshot_path = Path(str(ledger_path) + ".ranked-snapshot.jsonl")
    manifest_path = Path(str(ledger_path) + ".ranked-snapshot.manifest.json")
    ledger_bytes = ledger_path.read_bytes()
    try:
        ledger = json.loads(ledger_bytes)
    except json.JSONDecodeError as exc:
        raise DiagnosticError("selection ledger is invalid JSON") from exc
    if not isinstance(ledger, dict):
        raise DiagnosticError("selection ledger is not an object")
    manifest = _read_json(manifest_path)
    historical_snapshot_validation = _manifest_replays(
        manifest,
        snapshot_path=snapshot_path,
        ledger_path=ledger_path,
    )
    identity = manifest["identity"]
    validated_ledger = validate_selection_ledger(
        ledger,
        binding_sha256=ledger["binding_sha256"],
        snapshot_identity_sha256_value=ledger["snapshot_identity_sha256"],
        snapshot_rows=ledger["snapshot_rows"],
        eligible_rows=ledger["eligible_rows"],
    )
    if identity.get("rows") != validated_ledger["snapshot_rows"] or identity.get(
        "eligible_rows"
    ) != validated_ledger["eligible_rows"]:
        raise DiagnosticError("selection ledger and ranked snapshot disagree")
    if snapshot_identity_sha256(identity) != validated_ledger[
        "snapshot_identity_sha256"
    ]:
        raise DiagnosticError("selection ledger does not bind ranked snapshot identity")

    audited_structural = set(state.get("audited_structural_digests") or [])
    excluded_stage2 = set(validated_ledger["committed_digests"])
    pending = validated_ledger.get("pending")
    if isinstance(pending, Mapping):
        excluded_stage2.update(pending.get("selected_digests") or [])
    for deferred in validated_ledger.get("deferred_pages") or []:
        if isinstance(deferred, Mapping):
            excluded_stage2.update(deferred.get("selected_digests") or [])

    registry = load_registry(DEFAULT_REGISTRY)
    known_index = {
        (entry.get("n"), entry.get("k"), entry.get("canonical_digest"))
        for entry in registry["entries"]
        if entry.get("code_type") == "css"
    }

    rows: list[dict[str, Any]] = []
    counts = Counter()
    for index, row in enumerate(_read_jsonl(snapshot_path)):
        if index >= int(validated_ledger["eligible_rows"]):
            break
        counts["eligible_prefix"] += 1
        if not (
            row.get("distance_lower_bound") == 5
            and row.get("distance_lower_bound_proven") is True
            and row.get("distance_lower_bound_status") == "search_oracle_proven"
        ):
            continue
        counts["claimed_d_ge_5"] += 1
        novelty = row.get("structural_novelty")
        static = row.get("static_eligibility")
        if not (
            isinstance(novelty, Mapping)
            and isinstance(static, Mapping)
            and static.get("eligible") is True
        ):
            counts["missing_identity_or_ineligible"] += 1
            continue
        key, structural_digest, triage_digest = _stable_identity(row)
        if (
            structural_digest in audited_structural
            or structural_digest in excluded_stage2
            or triage_digest in excluded_stage2
        ):
            counts["already_audited"] += 1
            continue
        target = target_binding(int(row["n"]), int(row["k"]), TARGET_MODE_SCALAR)
        if row.get("required_distance") != target["required_distance"]:
            counts["target_binding_mismatch"] += 1
            continue
        if (row.get("n"), row.get("k"), structural_digest) in known_index:
            canonical = canonicalize_for_audit(
                row,
                target_mode=TARGET_MODE_SCALAR,
            )
            novelty_replay = canonical.get("novelty")
            if (
                isinstance(novelty_replay, Mapping)
                and novelty_replay.get("novel") is False
            ):
                counts["fresh_registry_known"] += 1
                continue
            counts["registry_index_replay_disagreement"] += 1
        normalized = dict(row)
        normalized["candidate_key"] = key
        normalized["required_distance"] = target["required_distance"]
        rows.append(normalized)

    # A live pipeline may advance the ledger while this read-only selection is
    # replaying candidates.  The contract must bind one exact atomic ledger,
    # never a later path state paired with earlier exclusions.
    frozen_ledger_path = output_dir / "source-selection-ledger-at-freeze.json"
    _atomic_write(frozen_ledger_path, ledger_bytes)
    freeze = {
        "boundary": boundary,
        "ranked_snapshot": _file_identity(snapshot_path),
        "ranked_snapshot_manifest": _file_identity(manifest_path),
        "historical_snapshot_validation": historical_snapshot_validation,
        "selection_ledger_at_freeze": _file_identity(frozen_ledger_path),
        "selection_ledger_progress_sha256": validated_ledger["progress_sha256"],
        "selection_ledger_validation": {
            "binding_sha256": validated_ledger["binding_sha256"],
            "snapshot_identity_sha256": validated_ledger[
                "snapshot_identity_sha256"
            ],
            "snapshot_rows": validated_ledger["snapshot_rows"],
            "eligible_rows": validated_ledger["eligible_rows"],
        },
        "excluded_stage1_structural_digests": len(audited_structural),
        "excluded_stage2_structural_digests": len(excluded_stage2),
        "pool_counts": dict(sorted(counts.items())),
        "pre_replay_unaudited_lb5_pool": (
            counts["claimed_d_ge_5"]
            - counts["missing_identity_or_ineligible"]
            - counts["already_audited"]
            - counts["target_binding_mismatch"]
        ),
        "fresh_registry_novel_unaudited_lb5_pool": len(rows),
    }
    return rows, freeze


def _public_row(row: Mapping[str, Any], replay: Mapping[str, Any]) -> dict[str, Any]:
    key, structural_digest, triage_digest = _stable_identity(row)
    target = target_binding(int(row["n"]), int(row["k"]), TARGET_MODE_SCALAR)
    return {
        "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
        "candidate_key": key,
        "structural_digest": structural_digest,
        "triage_digest": triage_digest,
        "claim": _candidate_claim(row),
        "n": int(row["n"]),
        "k": int(row["k"]),
        "target": target,
        "initial_distance_lower_bound": 5,
        "initial_low_weight_oracle": row["low_weight_oracle"],
        "strata": _strata(row),
        "source_identities": list(
            (row.get("triage_identity") or {}).get("source_identities") or []
        ),
        "replay": dict(replay),
    }


def prepare_diagnostic(
    *,
    run_root: Path,
    pipeline_root: Path,
    output_dir: Path,
    sample_size: int = DEFAULT_SAMPLE_SIZE,
) -> dict[str, Any]:
    """Freeze and independently replay a stratified diagnostic sample."""

    if output_dir.exists() and any(output_dir.iterdir()):
        raise DiagnosticError("output directory is not empty")
    rows, freeze = _eligible_rows(
        run_root=run_root,
        pipeline_root=pipeline_root,
        output_dir=output_dir,
    )
    if len(rows) < sample_size:
        raise DiagnosticError(
            f"only {len(rows)} unaudited d>=5 candidates remain; need {sample_size}"
        )

    # Produce a complete deterministic order, then accept only independently
    # replayed rows.  A failed claim never changes the balancing counters.
    remaining = list(rows)
    accepted_raw: list[dict[str, Any]] = []
    accepted: list[dict[str, Any]] = []
    replay_failures: list[dict[str, str]] = []
    preterminal_exclusions: list[dict[str, Any]] = []
    while remaining and len(accepted) < sample_size:
        remaining.sort(key=lambda row: _candidate_score(row, selected=accepted_raw))
        row = remaining.pop(0)
        try:
            replay = _verify_initial_lower_bound(row)
        except Exception as exc:
            replay_failures.append({
                "candidate_key": str(row.get("candidate_key", "unknown")),
                "error": type(exc).__name__,
            })
            continue
        accepted_raw.append(row)
        structural_rejection = replay_structural_logical_basis_rejection(
            row,
            target_mode=TARGET_MODE_SCALAR,
        )
        if structural_rejection is not None:
            accepted_raw.pop()
            preterminal_exclusions.append(
                {
                    "candidate_key": str(row["candidate_key"]),
                    "upper_bound": structural_rejection.upper_bound,
                    "required_distance": structural_rejection.required_distance,
                }
            )
            continue
        replay["preexisting_structural_rejection"] = None
        accepted.append(_public_row(row, replay))
    if len(accepted) != sample_size:
        raise DiagnosticError(
            f"only {len(accepted)} candidates independently replayed; need {sample_size}"
        )

    output_dir.mkdir(parents=True, exist_ok=True)
    selected_path = output_dir / "selected.jsonl"
    _atomic_jsonl(selected_path, accepted)
    selected_identity = _file_identity(selected_path)
    contract = _seal({
        "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
        "kind": DIAGNOSTIC_KIND,
        "selection_policy": SELECTION_POLICY,
        "decision_policy": DECISION_POLICY,
        "source_run_id": _read_json(run_root / "state.json")["run_id"],
        "run_root": str(run_root.resolve()),
        "pipeline_root": str(pipeline_root.resolve()),
        "sample_size": sample_size,
        "target_mode": TARGET_MODE_SCALAR,
        "rungs": [6, 8, "required_distance_minus_1"],
        "both_sectors_required_for_lower_bound": True,
        "both_sectors_attempted_per_rung": True,
        "unknown_semantics": "fail_open_survivor",
        "timeouts_s": {"6": 120.0, "8": 300.0, "target": 900.0},
        "decision_thresholds": {
            "switch_ansatz_rejected_by_w8_fraction": 0.8,
            "retain_family_survived_w8_fraction": 0.2,
            "meaningful_lower_bound": 9,
            "near_target_gap": 3,
            "overlap_resolution": "retain_family_signal_precedes_switch_signal",
        },
        "bp_osd_positive_credit": False,
        "freeze": freeze,
        "selected": selected_identity,
        "selection_replay_failures": replay_failures,
        "selection_preterminal_exclusions": preterminal_exclusions,
        "source_bindings": _source_bindings(),
        "runtime_binding": _runtime_binding(),
    }, "contract_sha256")
    _atomic_json(output_dir / "contract.json", contract)
    return contract


def _load_contract(output_dir: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    contract = _read_json(output_dir / "contract.json")
    _validate_self_hash(contract, "contract_sha256")
    if contract.get("kind") != DIAGNOSTIC_KIND:
        raise DiagnosticError("diagnostic contract kind is wrong")
    for identity in contract.get("source_bindings") or []:
        path = Path(identity["path"])
        if _file_identity(path) != identity:
            raise DiagnosticError(f"bound source changed: {path.name}")
    if contract.get("runtime_binding") != _runtime_binding():
        raise DiagnosticError("diagnostic runtime binding changed")
    selected_path = output_dir / "selected.jsonl"
    if _file_identity(selected_path) != contract.get("selected"):
        raise DiagnosticError("selected sample changed")
    selected = list(_read_jsonl(selected_path))
    if len(selected) != contract.get("sample_size"):
        raise DiagnosticError("selected sample size changed")
    keys = [row.get("candidate_key") for row in selected]
    digests = [row.get("structural_digest") for row in selected]
    if len(set(keys)) != len(keys) or len(set(digests)) != len(digests):
        raise DiagnosticError("selected sample is not definition/digest distinct")
    return contract, selected


def _load_or_freeze_launch_eligibility(
    output_dir: Path,
    contract: Mapping[str, Any],
    selected: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Bind the first launch to a ledger where every sample is unaudited.

    The main pipeline is read-only from this diagnostic's perspective and has
    no external reservation API.  We therefore prove the exact condition at
    first launch and preserve it for resumptions.  A later main-pipeline audit
    may duplicate computation, but cannot retroactively change this sample's
    frozen-time status or evidence.
    """

    eligibility_path = output_dir / "launch-eligibility.json"
    if eligibility_path.is_file():
        eligibility = _read_json(eligibility_path)
        _validate_self_hash(eligibility, "launch_eligibility_sha256")
        if eligibility.get("contract_sha256") != contract.get("contract_sha256"):
            raise DiagnosticError("launch eligibility belongs to another contract")
        ledger_identity = eligibility.get("selection_ledger_at_launch")
        if not isinstance(ledger_identity, Mapping) or _file_identity(
            Path(ledger_identity["path"])
        ) != ledger_identity:
            raise DiagnosticError("launch ledger evidence changed")
        return eligibility

    pipeline_root = Path(str(contract["pipeline_root"]))
    ledger_path = pipeline_root / "solver-state" / "stage2-selection-ledger.json"
    ledger_bytes = ledger_path.read_bytes()
    try:
        ledger = json.loads(ledger_bytes)
    except json.JSONDecodeError as exc:
        raise DiagnosticError("launch selection ledger is invalid JSON") from exc
    validation = contract["freeze"]["selection_ledger_validation"]
    validated = validate_selection_ledger(
        ledger,
        binding_sha256=validation["binding_sha256"],
        snapshot_identity_sha256_value=validation["snapshot_identity_sha256"],
        snapshot_rows=validation["snapshot_rows"],
        eligible_rows=validation["eligible_rows"],
    )
    excluded = set(validated["committed_digests"])
    pending = validated.get("pending")
    if isinstance(pending, Mapping):
        excluded.update(pending.get("selected_digests") or [])
    for deferred in validated.get("deferred_pages") or []:
        if isinstance(deferred, Mapping):
            excluded.update(deferred.get("selected_digests") or [])
    selected_digests = {str(row["structural_digest"]) for row in selected}
    overlap = sorted(selected_digests & excluded)
    if overlap:
        raise DiagnosticError(
            f"{len(overlap)} selected candidates were audited before launch; "
            "prepare a fresh sample"
        )
    frozen_path = output_dir / "source-selection-ledger-at-launch.json"
    _atomic_write(frozen_path, ledger_bytes)
    eligibility = _seal(
        {
            "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
            "kind": DIAGNOSTIC_KIND,
            "contract_sha256": contract["contract_sha256"],
            "selection_ledger_at_launch": _file_identity(frozen_path),
            "selection_ledger_progress_sha256": validated["progress_sha256"],
            "selected_candidates": len(selected),
            "selected_overlap_with_audited": 0,
            "reservation_semantics": (
                "unaudited_at_first_launch; source pipeline has no external "
                "candidate reservation API"
            ),
        },
        "launch_eligibility_sha256",
    )
    _atomic_json(eligibility_path, eligibility)
    return eligibility


def run_candidate_ladder(
    selected: Mapping[str, Any],
    *,
    timeouts: Mapping[int | str, float],
    sector_evaluator: Callable[..., dict[str, Any]] = evaluate_low_weight_sector,
    isolate_sector_calls: bool = True,
    contract_sha256: str | None = None,
    selected_sha256: str | None = None,
) -> dict[str, Any]:
    """Run the two-sector ladder for one independently bound candidate."""

    started = time.monotonic()
    claim = selected["claim"]
    code = build_css_code_from_claim(claim)
    if int(code.num_qudits) != selected["n"] or int(code.dimension) != selected["k"]:
        raise DiagnosticError("selected candidate n/k changed")
    hx, hz, lx, lz = get_code_matrices(code)
    initial = selected.get("initial_low_weight_oracle")
    failures = verify_css_low_weight_oracle(initial, hx, hz, lx, lz)
    if failures or initial.get("outcome") != "UNSAT" or initial.get("max_weight") != 4:
        raise DiagnosticError("selected d>=5 evidence no longer replays")
    if authoritative_candidate_digest(claim) != selected["structural_digest"]:
        raise DiagnosticError("selected structural identity changed")

    required = int(selected["target"]["required_distance"])
    thresholds = [*RUNG_THRESHOLDS]
    if required - 1 > thresholds[-1]:
        thresholds.append(required - 1)
    lower_bound = 5
    upper_bound: int | None = None
    rungs: list[dict[str, Any]] = []
    stopped_reason = "ladder_complete"
    for threshold in thresholds:
        timeout_key: int | str = threshold if threshold in RUNG_THRESHOLDS else "target"
        timeout = float(timeouts[timeout_key])
        sectors: dict[str, dict[str, Any]] = {}
        for sector in ("X", "Z"):
            checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
            try:
                call_kwargs = {
                    "max_weight": threshold,
                    "sector": sector,
                    "hard_timeout_s": timeout,
                }
                hard_wall = None
                if isolate_sector_calls:
                    isolated = run_isolated_call(
                        sector_evaluator,
                        args=(checks, logicals),
                        kwargs=call_kwargs,
                        timeout_s=timeout + 15.0,
                    )
                    hard_wall = isolated.hard_wall
                    if isolated.status != "completed":
                        raise TimeoutError(isolated.error or isolated.status)
                    evidence = isolated.value
                else:
                    evidence = sector_evaluator(checks, logicals, **call_kwargs)
                replay_failures = verify_low_weight_sector_evidence(
                    evidence,
                    checks,
                    logicals,
                    max_weight=threshold,
                    sector=sector,
                )
            except Exception as exc:
                evidence = {
                    "outcome": "UNKNOWN",
                    "decision_complete": False,
                    "retryable": True,
                    "max_weight": threshold,
                    "message": f"{type(exc).__name__}: sector evaluation failed",
                }
                replay_failures = []
            if replay_failures:
                evidence = {
                    "outcome": "UNKNOWN",
                    "decision_complete": False,
                    "retryable": True,
                    "max_weight": threshold,
                    "message": "sector evidence replay failed",
                    "replay_failures": replay_failures,
                }
            sectors[sector] = {
                "evidence": evidence,
                "hard_wall": hard_wall,
            }
        outcomes = {
            sector: sectors[sector]["evidence"].get("outcome")
            for sector in ("X", "Z")
        }
        witnesses = [
            sectors[sector]["evidence"].get("witness")
            for sector in ("X", "Z")
            if outcomes[sector] == "SAT"
        ]
        if witnesses:
            weights = [value.get("weight") for value in witnesses if isinstance(value, Mapping)]
            valid_weights = [int(value) for value in weights if isinstance(value, int)]
            upper_bound = min(valid_weights) if valid_weights else threshold
            rung_outcome = "SAT"
        elif outcomes == {"X": "UNSAT", "Z": "UNSAT"}:
            lower_bound = threshold + 1
            rung_outcome = "UNSAT"
        else:
            rung_outcome = "UNKNOWN"
        rungs.append({
            "threshold": threshold,
            "outcome": rung_outcome,
            "sectors": sectors,
            "distance_lower_bound_after_rung": lower_bound,
            "distance_upper_bound_after_rung": upper_bound,
        })
        if rung_outcome == "SAT":
            stopped_reason = f"trusted_negative_at_w{threshold}"
            break
        if rung_outcome == "UNKNOWN":
            stopped_reason = f"fail_open_unknown_at_w{threshold}"
            break

    by_w8 = any(
        rung["outcome"] == "SAT" and int(rung["threshold"]) <= 8
        for rung in rungs
    )
    survived_w8 = not by_w8
    result = _seal({
        "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
        "kind": DIAGNOSTIC_KIND,
        "candidate_key": selected["candidate_key"],
        "contract_sha256": contract_sha256,
        "selected_sha256": selected_sha256,
        "structural_digest": selected["structural_digest"],
        "n": selected["n"],
        "k": selected["k"],
        "target": selected["target"],
        "strata": selected["strata"],
        "initial_distance_lower_bound": 5,
        "final_distance_lower_bound": lower_bound,
        "trusted_distance_upper_bound": upper_bound,
        "target_gap": max(0, required - lower_bound),
        "rejected_by_w8": by_w8,
        "survived_w8": survived_w8,
        "unknown_fail_open": any(rung["outcome"] == "UNKNOWN" for rung in rungs),
        "stopped_reason": stopped_reason,
        "rungs": rungs,
        "elapsed_s": time.monotonic() - started,
    }, "result_sha256")
    return result


def _worker(output_dir: Path, index: int) -> None:
    contract, selected = _load_contract(output_dir)
    if not 0 <= index < len(selected):
        raise DiagnosticError("worker index is outside the selected sample")
    result_path = (
        output_dir
        / "candidate-results"
        / f"{index:03d}-{selected[index]['candidate_key']}.json"
    )
    if result_path.is_file():
        result = _read_json(result_path)
        _validate_self_hash(result, "result_sha256")
        return
    raw_timeouts = contract["timeouts_s"]
    timeouts: dict[int | str, float] = {
        6: float(raw_timeouts["6"]),
        8: float(raw_timeouts["8"]),
        "target": float(raw_timeouts["target"]),
    }
    try:
        result = run_candidate_ladder(
            selected[index],
            timeouts=timeouts,
            contract_sha256=contract["contract_sha256"],
            selected_sha256=_canonical_sha256(selected[index]),
        )
    except Exception as exc:
        # Operational failure is a scientific survivor, never a rejection.
        result = _seal({
            "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
            "kind": DIAGNOSTIC_KIND,
            "candidate_key": selected[index]["candidate_key"],
            "contract_sha256": contract["contract_sha256"],
            "selected_sha256": _canonical_sha256(selected[index]),
            "structural_digest": selected[index]["structural_digest"],
            "n": selected[index]["n"],
            "k": selected[index]["k"],
            "target": selected[index]["target"],
            "strata": selected[index]["strata"],
            "initial_distance_lower_bound": 5,
            "final_distance_lower_bound": 5,
            "trusted_distance_upper_bound": None,
            "target_gap": int(selected[index]["target"]["required_distance"]) - 5,
            "rejected_by_w8": False,
            "survived_w8": True,
            "unknown_fail_open": True,
            "stopped_reason": "fail_open_worker_error",
            "error_type": type(exc).__name__,
            "rungs": [],
            "elapsed_s": 0.0,
        }, "result_sha256")
    _atomic_json(result_path, result)


def decide(results: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    """Apply the preregistered ansatz/deep-proof decision rule."""

    if not results:
        raise ValueError("results must not be empty")
    total = len(results)
    rejected = sum(value.get("rejected_by_w8") is True for value in results)
    survived = sum(value.get("survived_w8") is True for value in results)
    unknown = sum(value.get("unknown_fail_open") is True for value in results)
    meaningful = [
        value["candidate_key"]
        for value in results
        if int(value.get("final_distance_lower_bound", 0)) >= 9
    ]
    near_target = [
        value["candidate_key"]
        for value in results
        if int(value.get("target_gap", 10**9)) <= 3
    ]
    rejected_fraction = rejected / total
    survived_fraction = survived / total
    if survived_fraction >= 0.2 or meaningful or near_target:
        action = "retain_generalized_toric_family_and_targeted_deep_proof"
        reason = "survivor_or_lower_bound_signal"
    elif rejected_fraction >= 0.8:
        action = "change_ansatz_within_generalized_toric_family"
        reason = "low_weight_rejection_concentration"
    else:
        action = "inconclusive_collect_more_diagnostic_evidence"
        reason = "decision_thresholds_not_met"
    return _seal({
        "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
        "kind": DIAGNOSTIC_KIND,
        "decision_policy": DECISION_POLICY,
        "sample_size": total,
        "rejected_by_w8": rejected,
        "rejected_by_w8_fraction": rejected_fraction,
        "survived_w8": survived,
        "survived_w8_fraction": survived_fraction,
        "unknown_fail_open": unknown,
        "meaningful_lb_ge_9": meaningful,
        "near_target_gap_le_3": near_target,
        "action": action,
        "reason": reason,
        "whole_family_abandonment_authorized": False,
        "bp_osd_positive_credit": False,
    }, "decision_sha256")


def _replay_result(
    result: Mapping[str, Any],
    candidate: Mapping[str, Any],
    contract_sha256: str,
) -> dict[str, Any]:
    """Replay proof rows and recompute every field consumed by the decision."""

    if (
        result.get("kind") != DIAGNOSTIC_KIND
        or result.get("candidate_key") != candidate.get("candidate_key")
        or result.get("structural_digest") != candidate.get("structural_digest")
        or result.get("contract_sha256") != contract_sha256
        or result.get("selected_sha256") != _canonical_sha256(candidate)
        or result.get("n") != candidate.get("n")
        or result.get("k") != candidate.get("k")
        or result.get("target") != candidate.get("target")
        or result.get("strata") != candidate.get("strata")
    ):
        raise DiagnosticError("candidate result binding is inconsistent")
    if result.get("stopped_reason") == "fail_open_worker_error":
        expected = {
            "final_distance_lower_bound": 5,
            "trusted_distance_upper_bound": None,
            "target_gap": int(candidate["target"]["required_distance"]) - 5,
            "rejected_by_w8": False,
            "survived_w8": True,
            "unknown_fail_open": True,
        }
        if any(result.get(key) != value for key, value in expected.items()):
            raise DiagnosticError("fail-open worker result is inconsistent")
        return dict(result)

    code = build_css_code_from_claim(candidate["claim"])
    hx, hz, lx, lz = get_code_matrices(code)
    if (
        int(code.num_qudits) != candidate.get("n")
        or int(code.dimension) != candidate.get("k")
        or authoritative_candidate_digest(candidate["claim"])
        != candidate.get("structural_digest")
    ):
        raise DiagnosticError("candidate reconstruction changed during result replay")
    initial = candidate.get("initial_low_weight_oracle")
    initial_failures = verify_css_low_weight_oracle(initial, hx, hz, lx, lz)
    if (
        initial_failures
        or not isinstance(initial, Mapping)
        or initial.get("outcome") != "UNSAT"
        or initial.get("max_weight") != 4
    ):
        raise DiagnosticError("candidate initial d>=5 proof no longer replays")
    lower_bound = 5
    upper_bound: int | None = None
    rejected_by_w8 = False
    unknown = False
    rungs = result.get("rungs")
    if not isinstance(rungs, list) or not rungs:
        raise DiagnosticError("candidate result has no replayable rungs")
    expected_thresholds = [6, 8]
    required = int(candidate["target"]["required_distance"])
    if required - 1 > 8:
        expected_thresholds.append(required - 1)
    for rung_index, rung in enumerate(rungs):
        if not isinstance(rung, Mapping):
            raise DiagnosticError("candidate rung is not an object")
        threshold = rung.get("threshold")
        if rung_index >= len(expected_thresholds) or threshold != expected_thresholds[rung_index]:
            raise DiagnosticError("candidate rung order is inconsistent")
        sectors = rung.get("sectors")
        if not isinstance(sectors, Mapping) or set(sectors) != {"X", "Z"}:
            raise DiagnosticError("candidate rung lacks two sectors")
        outcomes: dict[str, Any] = {}
        witnesses: list[int] = []
        for sector in ("X", "Z"):
            envelope = sectors[sector]
            if not isinstance(envelope, Mapping):
                raise DiagnosticError("candidate sector envelope is malformed")
            evidence = envelope.get("evidence")
            if not isinstance(evidence, Mapping):
                raise DiagnosticError("candidate sector evidence is absent")
            outcome = evidence.get("outcome")
            outcomes[sector] = outcome
            if outcome in {"SAT", "UNSAT"}:
                checks, logicals = css_sector_matrices(hx, hz, lx, lz, sector)
                failures = verify_low_weight_sector_evidence(
                    evidence,
                    checks,
                    logicals,
                    max_weight=int(threshold),
                    sector=sector,
                )
                if failures:
                    raise DiagnosticError("candidate sector proof does not replay")
            elif outcome != "UNKNOWN":
                raise DiagnosticError("candidate sector outcome is invalid")
            if outcome == "SAT":
                witness = evidence.get("witness")
                if not isinstance(witness, Mapping) or not isinstance(witness.get("weight"), int):
                    raise DiagnosticError("candidate SAT witness is malformed")
                witnesses.append(int(witness["weight"]))
        if witnesses:
            rung_outcome = "SAT"
            upper_bound = min(witnesses)
            rejected_by_w8 = int(threshold) <= 8
        elif outcomes == {"X": "UNSAT", "Z": "UNSAT"}:
            rung_outcome = "UNSAT"
            lower_bound = int(threshold) + 1
        else:
            rung_outcome = "UNKNOWN"
            unknown = True
        if (
            rung.get("outcome") != rung_outcome
            or rung.get("distance_lower_bound_after_rung") != lower_bound
            or rung.get("distance_upper_bound_after_rung") != upper_bound
        ):
            raise DiagnosticError("candidate rung derived fields are inconsistent")
        if rung_outcome in {"SAT", "UNKNOWN"} and rung_index != len(rungs) - 1:
            raise DiagnosticError("candidate continued after a terminal diagnostic rung")
    if (
        rungs[-1].get("outcome") == "UNSAT"
        and len(rungs) != len(expected_thresholds)
    ):
        raise DiagnosticError("candidate ladder stopped before its next required rung")
    derived = {
        "final_distance_lower_bound": lower_bound,
        "trusted_distance_upper_bound": upper_bound,
        "target_gap": max(0, required - lower_bound),
        "rejected_by_w8": rejected_by_w8,
        "survived_w8": not rejected_by_w8,
        "unknown_fail_open": unknown,
    }
    if any(result.get(key) != value for key, value in derived.items()):
        raise DiagnosticError("candidate result derived fields do not replay")
    return dict(result)


def summarize(output_dir: Path) -> dict[str, Any]:
    contract, selected = _load_contract(output_dir)
    results: list[dict[str, Any]] = []
    for index, candidate in enumerate(selected):
        path = output_dir / "candidate-results" / f"{index:03d}-{candidate['candidate_key']}.json"
        if not path.is_file():
            raise DiagnosticError(f"candidate result {index} is absent")
        result = _read_json(path)
        _validate_self_hash(result, "result_sha256")
        results.append(
            _replay_result(result, candidate, contract["contract_sha256"])
        )
    _atomic_jsonl(output_dir / "results.jsonl", results)
    decision = decide(results)
    decision["contract_sha256"] = contract["contract_sha256"]
    decision["results"] = _file_identity(output_dir / "results.jsonl")
    decision = _seal(decision, "decision_sha256")
    _atomic_json(output_dir / "decision.json", decision)
    return decision


def run_all(output_dir: Path, workers: int) -> dict[str, Any]:
    contract, selected = _load_contract(output_dir)
    if isinstance(workers, bool) or not isinstance(workers, int) or not 1 <= workers <= 12:
        raise DiagnosticError("workers must be in [1, 12]")
    with acquire_solver_budget(workers) as lease:
        # Admission must precede the durable first-launch eligibility seal.  A
        # failed admission is not a launch and must not freeze a ledger that a
        # later retry would otherwise trust after the source pipeline moved.
        launch_eligibility = _load_or_freeze_launch_eligibility(
            output_dir,
            contract,
            selected,
        )
        _atomic_json(output_dir / "admission.json", _seal({
            "schema_version": DIAGNOSTIC_SCHEMA_VERSION,
            "kind": DIAGNOSTIC_KIND,
            "contract_sha256": contract["contract_sha256"],
            "launch_eligibility_sha256": launch_eligibility[
                "launch_eligibility_sha256"
            ],
            "solver_budget": lease.as_dict(),
        }, "admission_sha256"))

        def launch(index: int) -> None:
            repo_root = Path(__file__).resolve().parents[1]
            command = [
                sys.executable,
                "-B",
                "-m",
                "evaluation.stratified_ladder_diagnostic",
                "worker",
                "--output-dir",
                str(output_dir),
                "--index",
                str(index),
            ]
            environment = dict(os.environ)
            environment.update({
                "PYTHONDONTWRITEBYTECODE": "1",
                "OMP_NUM_THREADS": "1",
                "OPENBLAS_NUM_THREADS": "1",
                "MKL_NUM_THREADS": "1",
                "NUMEXPR_NUM_THREADS": "1",
            })
            existing_pythonpath = environment.get("PYTHONPATH")
            environment["PYTHONPATH"] = str(repo_root) + (
                os.pathsep + existing_pythonpath if existing_pythonpath else ""
            )
            completed = subprocess.run(
                command,
                cwd=repo_root,
                env=environment,
                check=False,
            )
            if completed.returncode != 0:
                raise DiagnosticError(
                    f"candidate worker {index} exited {completed.returncode}"
                )

        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            futures = [executor.submit(launch, index) for index in range(len(selected))]
            for future in concurrent.futures.as_completed(futures):
                future.result()
    return summarize(output_dir)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    prepare = subparsers.add_parser("prepare")
    prepare.add_argument("--run-root", type=Path, required=True)
    prepare.add_argument("--pipeline-root", type=Path, required=True)
    prepare.add_argument("--output-dir", type=Path, required=True)
    prepare.add_argument("--sample-size", type=int, default=DEFAULT_SAMPLE_SIZE)
    run = subparsers.add_parser("run")
    run.add_argument("--output-dir", type=Path, required=True)
    run.add_argument("--workers", type=int, default=DEFAULT_WORKERS)
    summary = subparsers.add_parser("summarize")
    summary.add_argument("--output-dir", type=Path, required=True)
    worker = subparsers.add_parser("worker")
    worker.add_argument("--output-dir", type=Path, required=True)
    worker.add_argument("--index", type=int, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.command == "prepare":
        result = prepare_diagnostic(
            run_root=args.run_root,
            pipeline_root=args.pipeline_root,
            output_dir=args.output_dir,
            sample_size=args.sample_size,
        )
    elif args.command == "run":
        result = run_all(args.output_dir, args.workers)
    elif args.command == "summarize":
        result = summarize(args.output_dir)
    else:
        _worker(args.output_dir, args.index)
        return 0
    print(json.dumps(result, sort_keys=True, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "DIAGNOSTIC_KIND",
    "DiagnosticError",
    "decide",
    "prepare_diagnostic",
    "run_candidate_ladder",
    "stratified_candidate_order",
    "summarize",
]
