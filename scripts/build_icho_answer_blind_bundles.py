#!/usr/bin/env python3
"""Split IChO records into a problem-only solver bundle and a sealed grader key.

This is a trusted-controller utility.  It must never be copied into a solver
workspace because it necessarily reads the official answers.  The solver
bundle is an explicit allowlist projection; unknown input fields are ignored,
while every retained asset is hash-bound.  The grader bundle is written to a
separate path and binds each answer to the exact problem-only record that was
shown to the solver.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path
from typing import Any, Iterable, Sequence


SCHEMA_VERSION = 1
PROTOCOL = "icho-answer-blind-v1"

# No key in a solver record may have one of these semantic roles.  The check is
# recursive and deliberately broader than the projection below so a future
# schema extension fails closed rather than silently exposing a key.
FORBIDDEN_SOLVER_KEY_FRAGMENTS = (
    "answer",
    "solution",
    "marking",
    "rubric",
    "explanation",
    "reasoning",
    "reusable_conclusion",
    "grader",
)


def _numeric_output(
    output_id: str,
    source_requirement: str,
    unit: str,
    *,
    decimal_places: int | None = None,
) -> dict[str, Any]:
    precision = (
        {
            "kind": "decimal_places",
            "digits": decimal_places,
            "source": "explicit_problem_instruction",
        }
        if decimal_places is not None
        else {
            "kind": "significant_figures",
            "digits": 3,
            "source": "uniform_blind_evaluation_default",
        }
    )
    return {
        "id": output_id,
        "source_requirement": source_requirement,
        "kind": "numeric",
        "unit": unit,
        "reporting_policy": precision,
    }


def _exact_output(
    output_id: str,
    source_requirement: str,
    kind: str,
    unit: str = "",
    *,
    audit_requirements: tuple[str, ...] = (),
) -> dict[str, Any]:
    output = {
        "id": output_id,
        "source_requirement": source_requirement,
        "kind": kind,
        "unit": unit,
        "reporting_policy": {
            "kind": "exact_integer" if kind == "integer" else "exact_symbolic",
            "source": "problem_output_type",
        },
    }
    if audit_requirements:
        output["audit_requirements"] = list(audit_requirements)
    return output


# The output identities and counts below are a transcription of the official
# problem statements, not of their answers.  Reporting policies marked
# ``explicit_problem_instruction`` are likewise source-derived; policies
# marked ``uniform_blind_evaluation_default`` are a protocol choice fixed
# before either solver runs when the problem itself gives no display rule.
# Keeping those provenances distinct prevents an evaluation convention from
# masquerading as a fact supplied by the problem.
REQUESTED_OUTPUTS: dict[str, tuple[dict[str, Any], ...]] = {
    "icho_2026_t1_a3": (
        _exact_output("carbon_atom_count", "number of carbon atoms n", "integer"),
        _exact_output("compound_identity", "identity of W", "classification"),
    ),
    "icho_2026_t1_a6": (
        _exact_output("stone_formula", "chemical formula of the stone", "formula"),
        _exact_output("compound_h_formula", "chemical formula of compound H", "formula"),
    ),
    "icho_2026_t2_a2": (
        _numeric_output("hbro2_process_a", "stationary [HBrO2] in Process A", "mol dm^-3"),
        _numeric_output("hbro2_process_b", "stationary [HBrO2] in Process B", "mol dm^-3"),
    ),
    "icho_2026_t2_a3": (
        _numeric_output("bromide_critical", "critical bromide concentration", "mol dm^-3"),
    ),
    "icho_2026_t2_a5": (
        _numeric_output("oscillation_period", "period of oscillations tau", "s"),
    ),
    "icho_2026_t3_a1": (
        _exact_output("cof1_empirical_formula", "empirical formula of COF-1", "formula"),
        _numeric_output("cof1_carbon_mass_percent", "carbon mass percentage in COF-1", "%", decimal_places=2),
    ),
    "icho_2026_t3_a2": (
        _numeric_output("cof2_internal_diameter", "internal honeycomb diameter d of COF-2", "angstrom"),
    ),
    "icho_2026_t3_a6": (
        _numeric_output("stacking_energy_aa", "pi-pi stacking energy for AA between two layers of one repeat unit", "kJ mol^-1"),
        _numeric_output("stacking_energy_ab", "pi-pi stacking energy for AB between two layers of one repeat unit", "kJ mol^-1"),
        _numeric_output("stacking_energy_ab_prime", "pi-pi stacking energy for AB' between two layers of one repeat unit", "kJ mol^-1"),
    ),
    "icho_2026_t3_a7": (
        _numeric_output("equilibrium_absorption_capacity", "equilibrium absorption capacity qe", "mg g^-1"),
        _numeric_output("uranyl_ions_per_pore", "number of uranyl ions absorbed per pore", "ions pore^-1"),
    ),
    "icho_2026_t4_a1": (
        _numeric_output("uranium235_abundance", "atomic abundance of uranium-235", "%"),
    ),
    "icho_2026_t4_a4": (
        _numeric_output("fission_energy", "energy released in the fission reaction", "MeV"),
    ),
    "icho_2026_t4_a5": (
        _numeric_output("average_collision_count", "average number of neutron collisions", "collisions"),
    ),
    "icho_2026_t4_a6": (
        _numeric_output("combustion_enthalpy_298", "methane combustion enthalpy at 298 K", "kJ mol^-1"),
    ),
    "icho_2026_t4_a7": (
        _numeric_output("combustion_enthalpy_2000", "methane combustion enthalpy at 2000 K", "kJ mol^-1"),
    ),
    "icho_2026_t4_a8": (
        _numeric_output("daily_energy", "total energy released per day", "J day^-1"),
    ),
    "icho_2026_t4_a9": (
        _numeric_output("total_fissions", "total number of fissions TN", "fissions"),
        _numeric_output("enriched_uranium_mass", "mass of enriched uranium used", "kg"),
    ),
    "icho_2026_t5_a1": (
        _exact_output("fragment_parity_statement", "correct parity statement for n", "classification"),
    ),
    "icho_2026_t5_a3": (
        _exact_output("fatty_acid_formula", "molecular formula of the fatty acid", "formula"),
    ),
    "icho_2026_t5_a4": (
        _exact_output("compound_x_formula", "molecular formula of X", "formula"),
    ),
    "icho_2026_t6_a3": (
        _exact_output("possible_halogens", "possible halogen or halogens in the reagent", "finite_set"),
    ),
    "icho_2026_t6_a4": (
        _exact_output("ion_783", "identity of the ion at m/z 783", "formula"),
        _exact_output("ion_879", "identity of the ion at m/z 879", "formula"),
        _exact_output("ion_1174", "identity of the ion at m/z 1174", "formula"),
    ),
    "icho_2026_t6_a7": (
        _exact_output("minimum_electrons_removed", "minimum number of electrons removed", "integer"),
        _exact_output("global_pi_electron_count", "total number of pi electrons in the global system", "integer"),
    ),
    "icho_2026_t7_a2": (
        _numeric_output("annual_methane_mass", "annual methane mass required", "tons"),
    ),
    "icho_2026_t7_a3": (
        _numeric_output("nitrogen_after_58_cycles", "nitrogen amount after the 58th cycle", "mol", decimal_places=4),
        _exact_output("cycles_for_97_percent", "number of cycles needed to reach 97.0 percent overall yield", "integer"),
    ),
    "icho_2026_t8_a5": (
        _numeric_output("catalyst_surface_density", "catalytic molecules per square nanometre", "molecules nm^-2"),
    ),
    "icho_2026_t8_a6": (
        _numeric_output("co_quantum_yield", "quantum yield for CO formation", "%"),
    ),
    "icho_2026_t8_a9": (
        _numeric_output("s1_quenching", "percentage quenching of the S1 state", "%"),
        _numeric_output("t1_quenching", "percentage quenching of the T1 state", "%"),
    ),
    "icho_2026_t9_a1": (
        _numeric_output("beta_cd_molar_mass", "molar mass of beta-CD", "g mol^-1"),
    ),
    "icho_2026_t9_a3": (
        _exact_output("macrocycle_ring_size", "ring size of macrocycle X", "integer"),
        _exact_output("macrocycle_stereocentres", "number of stereocentres in X", "integer"),
    ),
    "icho_2026_t9_a6": (
        _exact_output("dimer_isomer_count", "number of beta-CD dimer isomers", "integer"),
    ),
    "icho_2026_t9_a7": (
        _exact_output(
            "first_fragment_mz",
            "m/z of the first degradation-product sodium adduct",
            "integer",
            "m/z",
            audit_requirements=("image_component_accounting",),
        ),
        _exact_output(
            "second_fragment_mz",
            "m/z of the second degradation-product sodium adduct",
            "integer",
            "m/z",
            audit_requirements=("image_component_accounting",),
        ),
    ),
    "icho_2026_t9_a9": (
        _exact_output("arrangement_count", "number of functional-group arrangements", "integer"),
    ),
}

# These two rows are controller-selected dependency producers, not members of
# the scored 32-target inventory above. Keeping their contracts separate
# prevents a validation run from silently changing the committed full-scope
# target set while still allowing A6 to consume hard-green, typed results.
DEPENDENCY_REQUESTED_OUTPUTS: dict[str, tuple[dict[str, Any], ...]] = {
    "icho_2026_t1_a4": (
        _exact_output("metal_q_identity", "identity of metal Q", "classification"),
        _exact_output("hydrated_c_formula", "chemical formula of C · xH2O", "formula"),
        _exact_output("compound_d_formula", "chemical formula of compound D", "formula"),
    ),
    "icho_2026_t1_a5": (
        _exact_output("compound_e_structure", "structure of compound E", "classification"),
        _exact_output("compound_f_structure", "structure of acid F", "classification"),
        _exact_output("compound_g_structure", "structure of compound G", "classification"),
    ),
}


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_tmp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    tmp = Path(raw_tmp)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        value = json.loads(line)
        if not isinstance(value, dict):
            raise ValueError(f"{path}:{line_no}: row must be a JSON object")
        rows.append(value)
    return rows


def _problem_question(row: dict[str, Any]) -> str:
    shared = str(row.get("shared_context") or row.get("context") or "").strip()
    current = str(row.get("current_question") or "").strip()
    if not current:
        raise ValueError(f"{row.get('id') or row.get('index')}: missing current_question")
    sections: list[str] = []
    if shared:
        sections.extend(["## Shared official problem context", shared, ""])
    sections.extend(
        [
            f"## Current subquestion {str(row.get('part_id') or '').strip()}".rstrip(),
            current,
        ]
    )
    return "\n".join(sections).strip() + "\n"


def _sanitized_previous_parts(row: dict[str, Any]) -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    raw_parts = row.get("previous_parts") or []
    if not isinstance(raw_parts, list):
        raise ValueError(f"{row.get('id')}: previous_parts must be a list")
    for raw in raw_parts:
        if not isinstance(raw, dict):
            raise ValueError(f"{row.get('id')}: previous part must be an object")
        result.append(
            {
                "source_id": str(raw.get("source_id") or "").strip(),
                "part_id": str(raw.get("part_id") or "").strip(),
                "question": str(raw.get("question") or "").strip(),
                "dependency_policy": (
                    "derive_in_answer_blind_run_or_use_problem_stated_fallback"
                ),
            }
        )
    return result


def _asset_records(
    row: dict[str, Any], *, image_root: Path, problem_pdf: Path
) -> tuple[list[str], list[dict[str, Any]]]:
    names = row.get("images") or []
    if not isinstance(names, list) or not names:
        raise ValueError(f"{row.get('id')}: at least one problem image is required")
    normalized: list[str] = []
    assets: list[dict[str, Any]] = []
    seen: set[str] = set()
    for raw_name in names:
        name = str(raw_name).strip()
        if not name or name in seen:
            continue
        if "_answer_" in name.lower():
            raise ValueError(f"{row.get('id')}: answer-sheet/solution image is forbidden: {name}")
        path = (image_root / name).resolve()
        try:
            path.relative_to(image_root.resolve())
        except ValueError as exc:
            raise ValueError(f"{row.get('id')}: image escapes image_root: {name}") from exc
        if not path.is_file():
            raise ValueError(f"{row.get('id')}: missing problem image: {path}")
        seen.add(name)
        normalized.append(name)
        assets.append(
            {
                "kind": "problem_page",
                "path": name,
                "sha256": _sha256_file(path),
                "source_page": int(row.get("source_page") or 0),
                "printed_page": int(row.get("printed_page") or 0),
            }
        )
    if not normalized:
        raise ValueError(f"{row.get('id')}: no usable problem images")
    assets.append(
        {
            "kind": "problem_pdf",
            "path": problem_pdf.name,
            "sha256": _sha256_file(problem_pdf),
            "source_page": int(row.get("source_page") or 0),
        }
    )
    return normalized, assets


def _blind_row(
    row: dict[str, Any], *, image_root: Path, problem_pdf: Path
) -> dict[str, Any]:
    identifier = str(row.get("id") or row.get("index") or "").strip()
    if not identifier:
        raise ValueError("row is missing id/index")
    images, assets = _asset_records(
        row, image_root=image_root, problem_pdf=problem_pdf
    )
    current_question = str(row.get("current_question") or "").strip()
    shared_context = str(row.get("shared_context") or row.get("context") or "").strip()
    requested_template = (
        REQUESTED_OUTPUTS.get(identifier)
        or DEPENDENCY_REQUESTED_OUTPUTS.get(identifier)
    )
    if not requested_template:
        raise ValueError(f"{identifier}: no pre-solve requested-output contract")
    # Round-trip through JSON to avoid sharing mutable nested policy objects
    # between rows or later controller phases.
    requested_outputs = json.loads(json.dumps(requested_template))
    if len(requested_outputs) == 1 and requested_outputs[0]["kind"] == "numeric":
        final_precision = dict(requested_outputs[0]["reporting_policy"])
    else:
        final_precision = {
            "kind": "per_requested_output",
            "source": "requested_outputs",
        }
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "phase": "solve",
        "id": identifier,
        "index": str(row.get("index") or identifier),
        "source_index": str(row.get("source_index") or row.get("part_id") or ""),
        "problem_id": str(row.get("problem_id") or ""),
        "part_id": str(row.get("part_id") or ""),
        "question": _problem_question(row),
        "current_question": current_question,
        "shared_context": shared_context,
        "category": str(row.get("category") or "IChO 2026 Theory"),
        "dataset": "IChO 2026 official English problem materials",
        "dataset_format": "native",
        "points": row.get("points"),
        "paper": str(row.get("paper") or ""),
        "kind": str(row.get("kind") or "theory"),
        "formalization_ready": (
            identifier in DEPENDENCY_REQUESTED_OUTPUTS
            or bool(row.get("formalization_ready", True))
        ),
        "image": images[0],
        "images": images,
        "previous_parts": _sanitized_previous_parts(row),
        "source_pdf": problem_pdf.name,
        "source_page": int(row.get("source_page") or 0),
        "printed_page": int(row.get("printed_page") or 0),
        "problem_assets": assets,
        "requested_outputs": requested_outputs,
        "reporting_policy": {
            "intermediate_rounding": "forbidden",
            "explicit_precision": "use_only_precision_requested_in_problem",
            "default_final_display": "three_significant_figures",
            "final_precision": final_precision,
            "tie_rule": "half_away_from_zero",
            "raw_result_required": True,
        },
        "measurement_policy": {
            "stipulated_constants": "exact_as_printed_unless_problem_calls_them_measured",
            "measured_display_half_width": "one_half_of_last_displayed_quantum",
            "derived_tolerances": "must_be_proved_from_source_measurement_intervals",
        },
        "candidate_domain_policy": {
            "allowed_sources": [
                "problem_text",
                "problem_image",
                "problem_stated_fallback",
                "trusted_general_law",
                "derived_theorem",
            ],
            "previous_part_results": (
                "derive_inline_from_problem_only_material_or_use_problem_stated_fallback"
            ),
            "unjustified_search_bounds": "forbidden",
            "underdetermined_result": "must_be_reported",
        },
    }


def _assert_solver_safe(value: Any, *, path: str = "$") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            lowered = str(key).lower()
            if lowered == "official_answer_seen":
                if child is not False:
                    raise ValueError(
                        f"answer-blind integrity flag must be false at {path}.{key}"
                    )
                continue
            if any(fragment in lowered for fragment in FORBIDDEN_SOLVER_KEY_FRAGMENTS):
                raise ValueError(f"forbidden solver key at {path}.{key}")
            _assert_solver_safe(child, path=f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _assert_solver_safe(child, path=f"{path}[{index}]")
    elif isinstance(value, str):
        normalized = value.lower().replace("\\", "/")
        if (
            "theory_solution" in normalized
            or "_answer_page-" in normalized
            or normalized.endswith("/solution.pdf")
        ):
            raise ValueError(f"forbidden solution asset reference at {path}")


def _grader_row(
    source: dict[str, Any], blind: dict[str, Any], *, solution_pdf: Path
) -> dict[str, Any]:
    answer = source.get("answer")
    if not isinstance(answer, str) or not answer.strip():
        raise ValueError(f"{blind['id']}: missing official answer for grader")
    return {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "phase": "post_freeze_grade",
        "id": blind["id"],
        "part_id": blind["part_id"],
        "blind_record_sha256": _sha256_bytes(_json_bytes(blind)),
        "official_answer": answer,
        "official_points": source.get("points"),
        "solution_pdf": solution_pdf.name,
        "solution_pdf_sha256": _sha256_file(solution_pdf),
        "solution_url": str(source.get("solution_url") or ""),
    }


def build_bundles(
    *,
    input_jsonl: Path,
    blind_output: Path,
    grader_output: Path,
    image_root: Path,
    problem_pdf: Path,
    solution_pdf: Path,
    expected_count: int = 32,
    target_ids: Sequence[str] | None = None,
) -> dict[str, Any]:
    rows = _read_jsonl(input_jsonl)
    dependency_selection_is_explicit = target_ids is not None
    if target_ids is not None:
        requested = [str(identifier).strip() for identifier in target_ids]
        if not requested or any(not identifier for identifier in requested):
            raise ValueError("target_ids must be a non-empty list of non-empty IDs")
        if len(set(requested)) != len(requested):
            raise ValueError("target_ids contains duplicates")
        by_id: dict[str, dict[str, Any]] = {}
        for row in rows:
            identifier = str(row.get("id") or row.get("index") or "").strip()
            if not identifier:
                raise ValueError("input row is missing id/index")
            if identifier in by_id:
                raise ValueError(f"duplicate input id: {identifier}")
            by_id[identifier] = row
        missing = sorted(set(requested) - set(by_id))
        if missing:
            raise ValueError(f"requested target IDs are absent from input: {missing}")
        # The controller-provided order is part of the pilot/full-scope
        # commitment.  Do not inherit an accidental source-file ordering.
        rows = [by_id[identifier] for identifier in requested]
    if expected_count > 0 and len(rows) != expected_count:
        raise ValueError(f"expected {expected_count} rows, found {len(rows)}")
    selected_ids = [
        str(row.get("id") or row.get("index") or "").strip() for row in rows
    ]
    selected_dependency_ids = sorted(
        set(selected_ids) & set(DEPENDENCY_REQUESTED_OUTPUTS)
    )
    if selected_dependency_ids and not dependency_selection_is_explicit:
        raise ValueError(
            "dependency producer IDs require explicit target_ids: "
            f"{selected_dependency_ids}"
        )
    if expected_count == len(REQUESTED_OUTPUTS) and (
        len(selected_ids) != len(REQUESTED_OUTPUTS)
        or set(selected_ids) != set(REQUESTED_OUTPUTS)
    ):
        raise ValueError(
            "32-target scored inventory must exactly match REQUESTED_OUTPUTS"
        )
    blind_rows: list[dict[str, Any]] = []
    grader_rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for source in rows:
        blind = _blind_row(source, image_root=image_root, problem_pdf=problem_pdf)
        if blind["id"] in seen:
            raise ValueError(f"duplicate id: {blind['id']}")
        seen.add(blind["id"])
        _assert_solver_safe(blind)
        blind_rows.append(blind)
        grader_rows.append(_grader_row(source, blind, solution_pdf=solution_pdf))

    blind_payload = b"".join(_json_bytes(row) for row in blind_rows)
    grader_payload = b"".join(_json_bytes(row) for row in grader_rows)
    _atomic_write(blind_output, blind_payload)
    _atomic_write(grader_output, grader_payload)
    blind_manifest = {
        "schema_version": SCHEMA_VERSION,
        "protocol": PROTOCOL,
        "row_count": len(blind_rows),
        "ids": sorted(seen),
        "blind_output": blind_output.name,
        "blind_sha256": _sha256_bytes(blind_payload),
        "problem_pdf_sha256": _sha256_file(problem_pdf),
        "evaluation_mode": "answer_blind",
        "official_answer_seen": False,
        "phase": "solve",
    }
    grader_manifest = {
        **blind_manifest,
        "phase": "post_freeze_grade",
        "grader_output": grader_output.name,
        "grader_sha256": _sha256_bytes(grader_payload),
        "solution_pdf_sha256": _sha256_file(solution_pdf),
    }
    _atomic_write(
        blind_output.with_suffix(blind_output.suffix + ".manifest.json"),
        _json_bytes(blind_manifest),
    )
    _atomic_write(
        grader_output.with_suffix(grader_output.suffix + ".manifest.json"),
        _json_bytes(grader_manifest),
    )
    return grader_manifest


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-jsonl", type=Path, required=True)
    parser.add_argument("--blind-output", type=Path, required=True)
    parser.add_argument("--grader-output", type=Path, required=True)
    parser.add_argument("--image-root", type=Path, required=True)
    parser.add_argument("--problem-pdf", type=Path, required=True)
    parser.add_argument("--solution-pdf", type=Path, required=True)
    parser.add_argument("--expected-count", type=int, default=32)
    parser.add_argument(
        "--target-id",
        action="append",
        dest="target_ids",
        help=(
            "Controller-selected target ID. Repeat to build an exact pilot "
            "scope; order is preserved and missing/duplicate IDs fail closed."
        ),
    )
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    manifest = build_bundles(
        input_jsonl=args.input_jsonl.resolve(),
        blind_output=args.blind_output.resolve(),
        grader_output=args.grader_output.resolve(),
        image_root=args.image_root.resolve(),
        problem_pdf=args.problem_pdf.resolve(),
        solution_pdf=args.solution_pdf.resolve(),
        expected_count=args.expected_count,
        target_ids=args.target_ids,
    )
    print(json.dumps(manifest, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
