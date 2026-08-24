"""Version-pinned, offline chemistry reference queries.

This module is deliberately a closed-world data service.  It accepts only a
small structured query vocabulary, reads only its sealed packaged registry
resource (never user/workspace files or environment variables), and has no
network/process API.  The returned data version and digest make a solver's
dependency on general chemistry constants auditable.

Atomic weights are the CIAAW 2024 abridged standard atomic weights.  Isotope
masses are a small, explicit AME2020 subset; an absent nuclide fails closed.
The reaction-template registry contains generic schemas, never problem
instances or candidate answers.  The contest-interpretation registry contains
explicitly labelled language policies, not empirical chemistry laws; every
policy requires independent problem-text cues before it may instantiate a
generic schema.
"""

from __future__ import annotations

from collections import Counter
from decimal import Decimal
from enum import Enum
import hashlib
from importlib import resources
import json
import re
from typing import Mapping, NoReturn

import typer


SCHEMA_VERSION = 1
BASE_DATASET_VERSION = (
    "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1"
    "+contest-interpretation-v1"
)
DATASET_VERSION = BASE_DATASET_VERSION + "+trusted-empirical-rules-v1"
MAX_ARGUMENT_CHARS = 128
MAX_GROUP_DEPTH = 4
MAX_ATOM_COUNT = 1_000_000
MAX_MULTIPLIER = 10_000

_CIAAW_SOURCE = {
    "id": "CIAAW_Abridged_Standard_Atomic_Weights_2024",
    "edition": "2024",
    "url": "https://ciaaw.org/abridged-atomic-weights.htm",
}
_AME_SOURCE = {
    "id": "AME2020_mass_1.mas20_selected_nuclides",
    "edition": "2020",
    "url": "https://amdc.impcas.ac.cn/masstables/Ame2020/mass_1.mas20",
}
_TEMPLATE_SOURCE = {
    "id": "Archon_Generic_Chemistry_Reaction_Templates_v1",
    "edition": "1",
}
_CONTEST_INTERPRETATION_SOURCE = {
    "id": "Archon_Chemistry_Contest_Interpretations_v1",
    "edition": "1",
    "authority_kind": "contest_semantics_policy",
    "empirical_claim": False,
}

# symbol -> (atomic number, abridged standard atomic weight, uncertainty)
# Elements without a standard atomic weight are intentionally absent.  Values
# and uncertainties are decimal strings so no binary floating point enters a
# calculation or receipt.
_ATOMIC_WEIGHTS: dict[str, tuple[int, str, str]] = {
    "H": (1, "1.0080", "0.0002"),
    "He": (2, "4.0026", "0.0001"),
    "Li": (3, "6.94", "0.06"),
    "Be": (4, "9.0122", "0.0001"),
    "B": (5, "10.81", "0.02"),
    "C": (6, "12.011", "0.002"),
    "N": (7, "14.007", "0.001"),
    "O": (8, "15.999", "0.001"),
    "F": (9, "18.998", "0.001"),
    "Ne": (10, "20.180", "0.001"),
    "Na": (11, "22.990", "0.001"),
    "Mg": (12, "24.305", "0.002"),
    "Al": (13, "26.982", "0.001"),
    "Si": (14, "28.085", "0.001"),
    "P": (15, "30.974", "0.001"),
    "S": (16, "32.06", "0.02"),
    "Cl": (17, "35.45", "0.01"),
    "Ar": (18, "39.95", "0.16"),
    "K": (19, "39.098", "0.001"),
    "Ca": (20, "40.078", "0.004"),
    "Sc": (21, "44.956", "0.001"),
    "Ti": (22, "47.867", "0.001"),
    "V": (23, "50.942", "0.001"),
    "Cr": (24, "51.996", "0.001"),
    "Mn": (25, "54.938", "0.001"),
    "Fe": (26, "55.845", "0.002"),
    "Co": (27, "58.933", "0.001"),
    "Ni": (28, "58.693", "0.001"),
    "Cu": (29, "63.546", "0.003"),
    "Zn": (30, "65.38", "0.02"),
    "Ga": (31, "69.723", "0.001"),
    "Ge": (32, "72.630", "0.008"),
    "As": (33, "74.922", "0.001"),
    "Se": (34, "78.971", "0.008"),
    "Br": (35, "79.904", "0.003"),
    "Kr": (36, "83.798", "0.002"),
    "Rb": (37, "85.468", "0.001"),
    "Sr": (38, "87.62", "0.01"),
    "Y": (39, "88.906", "0.001"),
    "Zr": (40, "91.222", "0.003"),
    "Nb": (41, "92.906", "0.001"),
    "Mo": (42, "95.95", "0.01"),
    "Ru": (44, "101.07", "0.02"),
    "Rh": (45, "102.91", "0.01"),
    "Pd": (46, "106.42", "0.01"),
    "Ag": (47, "107.87", "0.01"),
    "Cd": (48, "112.41", "0.01"),
    "In": (49, "114.82", "0.01"),
    "Sn": (50, "118.71", "0.01"),
    "Sb": (51, "121.76", "0.01"),
    "Te": (52, "127.60", "0.03"),
    "I": (53, "126.90", "0.01"),
    "Xe": (54, "131.29", "0.01"),
    "Cs": (55, "132.91", "0.01"),
    "Ba": (56, "137.33", "0.01"),
    "La": (57, "138.91", "0.01"),
    "Ce": (58, "140.12", "0.01"),
    "Pr": (59, "140.91", "0.01"),
    "Nd": (60, "144.24", "0.01"),
    "Sm": (62, "150.36", "0.02"),
    "Eu": (63, "151.96", "0.01"),
    "Gd": (64, "157.25", "0.01"),
    "Tb": (65, "158.93", "0.01"),
    "Dy": (66, "162.50", "0.01"),
    "Ho": (67, "164.93", "0.01"),
    "Er": (68, "167.26", "0.01"),
    "Tm": (69, "168.93", "0.01"),
    "Yb": (70, "173.05", "0.02"),
    "Lu": (71, "174.97", "0.01"),
    "Hf": (72, "178.49", "0.01"),
    "Ta": (73, "180.95", "0.01"),
    "W": (74, "183.84", "0.01"),
    "Re": (75, "186.21", "0.01"),
    "Os": (76, "190.23", "0.03"),
    "Ir": (77, "192.22", "0.01"),
    "Pt": (78, "195.08", "0.02"),
    "Au": (79, "196.97", "0.01"),
    "Hg": (80, "200.59", "0.01"),
    "Tl": (81, "204.38", "0.01"),
    "Pb": (82, "207.2", "1.1"),
    "Bi": (83, "208.98", "0.01"),
    "Th": (90, "232.04", "0.01"),
    "Pa": (91, "231.04", "0.01"),
    "U": (92, "238.03", "0.01"),
}

# canonical symbol-mass -> (atomic number, mass in Da, uncertainty in Da)
_ISOTOPE_MASSES: dict[str, tuple[int, str, str]] = {
    "H-1": (1, "1.007825031898", "0.000000000014"),
    "H-2": (1, "2.014101777844", "0.000000000015"),
    "C-12": (6, "12.000000000000", "0"),
    "C-13": (6, "13.00335483534", "0.00000000025"),
    "N-14": (7, "14.00307400425", "0.00000000024"),
    "O-16": (8, "15.99491461926", "0.00000000032"),
    "F-19": (9, "18.99840316207", "0.00000000088"),
    "Na-23": (11, "22.98976928195", "0.00000000194"),
    "Al-27": (13, "26.981538408", "0.000000050"),
    "Cl-35": (17, "34.968852694", "0.000000038"),
    "Cl-37": (17, "36.965902573", "0.000000055"),
    "Br-79": (35, "78.918337574", "0.000001074"),
    "Br-81": (35, "80.916288197", "0.000001049"),
    "I-127": (53, "126.904472592", "0.000003887"),
    "U-235": (92, "235.043928117", "0.000001198"),
    "U-238": (92, "238.050786936", "0.000001601"),
}

_REACTION_TEMPLATES: dict[str, dict[str, object]] = {
    "binary_two_fragment_electrophilic_addition": {
        "template_version": 1,
        "reaction_class": "electrophilic_addition",
        "site": {
            "kind": "two_center_unsaturated_site",
            "sites_consumed_per_event": 1,
        },
        "reagent": {
            "kind": "binary_two_fragment_reagent",
            "fragments_per_reagent": 2,
            "fragment_kind": "single_atom_addend",
            "distinct_fragments_required": False,
        },
        "stoichiometry": {
            "reagent_molecules_per_site": 1,
            "addends_delivered_per_site": 2,
        },
        "retention": {
            "all_reagent_addends_retained_in_product": True,
        },
        "instantiation_policy": {
            "automatic_problem_instantiation": False,
            "requires_source_or_trusted_classification_evidence": True,
            "does_not_identify_elements": True,
        },
    },
}


# These records state a bounded contest-language convention.  They are not
# empirical inverse-classification theorems: use requires all printed cues and
# a source locator, and the policy never determines a particular reagent.
_CONTEST_INTERPRETATIONS: dict[str, dict[str, object]] = {
    "analogous_halogen_addition": {
        "policy_version": 1,
        "authority_kind": "contest_semantics_policy",
        "empirical_claim": False,
        "scope": {
            "domain": "olympiad_chemistry",
            "task_kind": "molecular_reagent_identification",
        },
        "source_cues": {
            "benchmark_reagent_reference": (
                "molecular_formula_or_elemental_halogen_name_in_addition_context"
            ),
            "same_unsaturated_substrate": True,
            "comparison_wording_any_of": ["same_way", "similar_way", "analogous_way"],
            "quantitative_addition_or_adduct_context": True,
            "molecular_formula_of_unknown_requested": True,
        },
        "interpretation": {
            "reaction_template_id": "binary_two_fragment_electrophilic_addition",
            "site_kind": "two_center_unsaturated_site",
            "same_site_as_benchmark": True,
            "sites_consumed_per_event": 1,
            "unknown_reagent_kind": "neutral_diatomic_halogen_or_interhalogen",
            "ordinary_olympiad_element_domain": ["F", "Cl", "Br", "I"],
            "atoms_per_reagent_molecule": 2,
            "charge": 0,
            "same_element_allowed": True,
            "different_elements_allowed": True,
            "reagent_molecules_per_site": 1,
            "addends_delivered_per_site": 2,
            "all_reagent_addends_retained_in_product": True,
        },
        "admission_policy": {
            "automatic_problem_instantiation": False,
            "requires_exact_problem_text_locator": True,
            "requires_all_source_cues": True,
            "requires_no_contrary_problem_statement": True,
            "problem_wording_overrides_policy": True,
            "missing_or_ambiguous_cue": "fail_closed",
            "does_not_identify_specific_reagent": True,
            "not_a_universal_inverse_chemistry_claim": True,
        },
    },
}

REACTION_TEMPLATE_IDS = tuple(sorted(_REACTION_TEMPLATES))
CONTEST_INTERPRETATION_IDS = tuple(sorted(_CONTEST_INTERPRETATIONS))


class ChemistryConstantError(ValueError):
    """A query is outside the closed, structured reference vocabulary."""


class ChemistryConstantOperation(str, Enum):
    atomic_weight = "atomic_weight"
    isotope_mass = "isotope_mass"
    molar_mass = "molar_mass"
    reaction_template = "reaction_template"
    contest_interpretation = "contest_interpretation"
    empirical_rule = "empirical_rule"


def _canonical_json(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


_BASE_DATASET_PAYLOAD = {
    "schema_version": SCHEMA_VERSION,
    "dataset_version": BASE_DATASET_VERSION,
    "sources": [
        _CIAAW_SOURCE,
        _AME_SOURCE,
        _TEMPLATE_SOURCE,
        _CONTEST_INTERPRETATION_SOURCE,
    ],
    "atomic_weights": _ATOMIC_WEIGHTS,
    "isotope_masses": _ISOTOPE_MASSES,
    "reaction_templates": _REACTION_TEMPLATES,
    "contest_interpretations": _CONTEST_INTERPRETATIONS,
}
BASE_DATASET_SHA256 = hashlib.sha256(
    _canonical_json(_BASE_DATASET_PAYLOAD)
).hexdigest()


def _strict_json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise RuntimeError(f"duplicate empirical-registry field: {key}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> NoReturn:
    raise ValueError(f"non-finite JSON constant: {value}")


def _load_empirical_registry() -> dict[str, object]:
    """Load and verify the sealed, packaged empirical-rule snapshot."""

    resource = resources.files("archon").joinpath(
        ".archon-src", "chemistry-registry", "empirical-rules-v1.json"
    )
    try:
        payload = json.loads(
            resource.read_text(encoding="utf-8"),
            object_pairs_hook=_strict_json_object,
            parse_constant=_reject_json_constant,
        )
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError("invalid packaged empirical chemistry registry") from exc
    if not isinstance(payload, dict) or set(payload) != {"manifest", "records"}:
        raise RuntimeError("empirical registry must contain manifest and records")
    manifest = payload["manifest"]
    records = payload["records"]
    if not isinstance(manifest, dict) or set(manifest) != {
        "base_dataset_sha256",
        "manifest_sha256",
        "manifest_type",
        "record_count",
        "records",
        "schema_version",
    }:
        raise RuntimeError("invalid empirical registry manifest")
    unsigned_manifest = dict(manifest)
    manifest_sha256 = unsigned_manifest.pop("manifest_sha256")
    if (
        manifest.get("schema_version") != 1
        or manifest.get("manifest_type") != "trusted_chemistry_registry"
        or manifest.get("base_dataset_sha256") != BASE_DATASET_SHA256
        or not isinstance(manifest_sha256, str)
        or hashlib.sha256(_canonical_json(unsigned_manifest)).hexdigest()
        != manifest_sha256
        or not isinstance(records, list)
        or manifest.get("record_count") != len(records)
    ):
        raise RuntimeError("empirical registry manifest verification failed")

    entries: list[dict[str, object]] = []
    seen: set[str] = set()
    rule_id_pattern = re.compile(r"^[a-z][a-z0-9_]{2,95}$", flags=re.ASCII)
    digest_pattern = re.compile(r"^[0-9a-f]{64}$", flags=re.ASCII)
    for record in records:
        if not isinstance(record, dict) or set(record) != {
            "base_dataset_sha256",
            "record_sha256",
            "record_type",
            "review",
            "rule",
            "runtime_network_access",
            "schema_version",
            "source",
        }:
            raise RuntimeError("invalid empirical rule record")
        unsigned_record = dict(record)
        record_sha256 = unsigned_record.pop("record_sha256")
        rule = record.get("rule")
        source = record.get("source")
        review = record.get("review")
        if (
            record.get("schema_version") != 1
            or record.get("record_type") != "trusted_chemistry_rule"
            or record.get("base_dataset_sha256") != BASE_DATASET_SHA256
            or record.get("runtime_network_access") is not False
            or not isinstance(record_sha256, str)
            or digest_pattern.fullmatch(record_sha256) is None
            or hashlib.sha256(_canonical_json(unsigned_record)).hexdigest()
            != record_sha256
            or not isinstance(rule, dict)
            or set(rule) != {
                "applicability_conditions",
                "authority_kind",
                "automatic_problem_instantiation",
                "claim",
                "exclusions",
                "rule_id",
                "rule_version",
            }
            or rule.get("automatic_problem_instantiation") is not False
            or not isinstance(source, dict)
            or set(source) != {"content_sha256", "doi", "locator", "url"}
            or not isinstance(source.get("content_sha256"), str)
            or digest_pattern.fullmatch(source["content_sha256"]) is None
            or not isinstance(review, dict)
            or review.get("status") != "approved"
            or review.get("approval_scope") != "rule_and_source"
        ):
            raise RuntimeError("empirical rule verification failed")
        rule_id = rule.get("rule_id")
        rule_version = rule.get("rule_version")
        if (
            not isinstance(rule_id, str)
            or rule_id_pattern.fullmatch(rule_id) is None
            or rule_id in seen
            or type(rule_version) is not int
        ):
            raise RuntimeError("invalid or duplicate empirical rule id")
        seen.add(rule_id)
        entries.append(
            {
                "record_sha256": record_sha256,
                "rule_id": rule_id,
                "rule_version": rule_version,
            }
        )
    if entries != manifest.get("records") or [
        entry["rule_id"] for entry in entries
    ] != sorted(seen):
        raise RuntimeError("empirical registry index does not match records")
    return payload


_EMPIRICAL_REGISTRY = _load_empirical_registry()
_EMPIRICAL_RULES = {
    record["rule"]["rule_id"]: record
    for record in _EMPIRICAL_REGISTRY["records"]
}
EMPIRICAL_RULE_IDS = tuple(sorted(_EMPIRICAL_RULES))
DORMANT_RUNTIME_BRIDGE_IDS = (
    "closed_domain_mellite_terminal_residue_candidate_filter",
    "mellitic_acid_p2o5_heating_forms_some_trianhydride",
)
BASELINE_EMPIRICAL_RULE_IDS = tuple(
    rule_id
    for rule_id in EMPIRICAL_RULE_IDS
    if rule_id not in DORMANT_RUNTIME_BRIDGE_IDS
)

_DATASET_PAYLOAD = {
    **_BASE_DATASET_PAYLOAD,
    "dataset_version": DATASET_VERSION,
    "empirical_registry": _EMPIRICAL_REGISTRY,
}
DATASET_SHA256 = hashlib.sha256(_canonical_json(_DATASET_PAYLOAD)).hexdigest()

_ELEMENT = re.compile(r"^[A-Z][a-z]?$", flags=re.ASCII)
_ISOTOPE = re.compile(r"^([A-Z][a-z]?)-([1-9][0-9]{0,2})$", flags=re.ASCII)
_TEMPLATE_ID = re.compile(r"^[a-z][a-z0-9_]{0,63}$", flags=re.ASCII)


def _fail(message: str) -> NoReturn:
    raise ChemistryConstantError(message)


def _validate_argument(value: object, *, label: str) -> str:
    if not isinstance(value, str):
        _fail(f"{label} must be a string")
    if not value or len(value) > MAX_ARGUMENT_CHARS:
        _fail(f"{label} must contain 1..{MAX_ARGUMENT_CHARS} characters")
    if value != value.strip() or any(character.isspace() for character in value):
        _fail(f"{label} must not contain whitespace")
    return value


def _base_result(operation: ChemistryConstantOperation) -> dict[str, object]:
    return {
        "schema_version": SCHEMA_VERSION,
        "service": "archon_offline_chemistry_reference",
        "dataset_version": DATASET_VERSION,
        "dataset_sha256": DATASET_SHA256,
        "operation": operation.value,
        "runtime_network_access": False,
    }


def _with_record_receipt(payload: dict[str, object]) -> dict[str, object]:
    """Bind one exact lookup result without changing the pinned dataset hash."""

    result = dict(payload)
    result["record_sha256"] = hashlib.sha256(_canonical_json(payload)).hexdigest()
    return result


def atomic_weight(element: str) -> dict[str, object]:
    """Return one CIAAW abridged standard atomic weight by element symbol."""

    symbol = _validate_argument(element, label="element")
    if _ELEMENT.fullmatch(symbol) is None:
        _fail("element must be one canonical element symbol, for example C or Al")
    record = _ATOMIC_WEIGHTS.get(symbol)
    if record is None:
        _fail("element has no standard atomic weight in the pinned dataset")
    atomic_number, value, uncertainty = record
    return _with_record_receipt({
        **_base_result(ChemistryConstantOperation.atomic_weight),
        "query": {"element": symbol},
        "result": {
            "quantity": "abridged_standard_atomic_weight",
            "atomic_number": atomic_number,
            "element": symbol,
            "value": value,
            "uncertainty": uncertainty,
            "unit": "1",
        },
        "source": dict(_CIAAW_SOURCE),
    })


def isotope_mass(isotope: str) -> dict[str, object]:
    """Return one AME2020 isotope mass from the explicit pinned subset."""

    nuclide = _validate_argument(isotope, label="isotope")
    match = _ISOTOPE.fullmatch(nuclide)
    if match is None:
        _fail("isotope must use canonical Symbol-MassNumber form, for example U-235")
    record = _ISOTOPE_MASSES.get(nuclide)
    if record is None:
        _fail("isotope is not present in the pinned isotope allowlist")
    atomic_number, value, uncertainty = record
    return _with_record_receipt({
        **_base_result(ChemistryConstantOperation.isotope_mass),
        "query": {"isotope": nuclide},
        "result": {
            "quantity": "atomic_mass",
            "atomic_number": atomic_number,
            "element": match.group(1),
            "mass_number": int(match.group(2)),
            "value": value,
            "uncertainty": uncertainty,
            "unit": "Da",
        },
        "source": dict(_AME_SOURCE),
    })


class _FormulaParser:
    def __init__(self, text: str) -> None:
        self.text = text
        self.position = 0

    def parse(self, *, depth: int = 0, closing: str | None = None) -> Counter[str]:
        if depth > MAX_GROUP_DEPTH:
            _fail(f"formula nesting exceeds {MAX_GROUP_DEPTH}")
        result: Counter[str] = Counter()
        consumed = False
        while self.position < len(self.text):
            character = self.text[self.position]
            if character == ")":
                if closing != ")":
                    _fail("formula contains an unmatched closing parenthesis")
                break
            if character == "(":
                self.position += 1
                group = self.parse(depth=depth + 1, closing=")")
                if self.position >= len(self.text) or self.text[self.position] != ")":
                    _fail("formula contains an unmatched opening parenthesis")
                self.position += 1
                multiplier = self._parse_count()
                self._merge(result, group, multiplier)
                consumed = True
                continue
            if not ("A" <= character <= "Z"):
                _fail("formula accepts only element symbols, integer counts, and parentheses")
            start = self.position
            self.position += 1
            if self.position < len(self.text) and "a" <= self.text[self.position] <= "z":
                self.position += 1
            symbol = self.text[start:self.position]
            if symbol not in _ATOMIC_WEIGHTS:
                _fail("formula contains an element without a pinned standard atomic weight")
            result[symbol] += self._parse_count()
            self._check_total(result)
            consumed = True
        if not consumed:
            _fail("formula contains an empty component or group")
        return result

    def _parse_count(self) -> int:
        start = self.position
        while self.position < len(self.text) and self.text[self.position].isdigit():
            self.position += 1
        if start == self.position:
            return 1
        token = self.text[start:self.position]
        if token.startswith("0"):
            _fail("formula counts must be positive integers without leading zeroes")
        value = int(token)
        if value > MAX_MULTIPLIER:
            _fail(f"formula count exceeds {MAX_MULTIPLIER}")
        return value

    @staticmethod
    def _check_total(composition: Counter[str]) -> None:
        if sum(composition.values()) > MAX_ATOM_COUNT:
            _fail(f"formula expands beyond {MAX_ATOM_COUNT} atoms")

    def _merge(
        self, destination: Counter[str], source: Counter[str], multiplier: int
    ) -> None:
        for symbol, count in source.items():
            destination[symbol] += count * multiplier
        self._check_total(destination)


def _parse_formula(formula: object) -> tuple[str, Counter[str]]:
    text = _validate_argument(formula, label="formula")
    components = re.split(r"[.·]", text)
    if not components or any(not component for component in components):
        _fail("formula contains an empty hydrate/adduct component")
    composition: Counter[str] = Counter()
    for component in components:
        coefficient = 1
        match = re.match(r"([1-9][0-9]*)(?=[A-Z(])", component, flags=re.ASCII)
        if match is not None:
            coefficient = int(match.group(1))
            if coefficient > MAX_MULTIPLIER:
                _fail(f"formula coefficient exceeds {MAX_MULTIPLIER}")
            component = component[match.end():]
        parser = _FormulaParser(component)
        parsed = parser.parse()
        if parser.position != len(component):
            _fail("formula contains an unmatched closing parenthesis")
        parser._merge(composition, parsed, coefficient)
    return text, composition


def _decimal_text(value: Decimal) -> str:
    text = format(value, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text or "0"


def molar_mass(formula: str) -> dict[str, object]:
    """Compute a formula molar mass from the pinned abridged atomic weights."""

    text, composition = _parse_formula(formula)
    value = Decimal(0)
    uncertainty = Decimal(0)
    for symbol, count in composition.items():
        _, weight, weight_uncertainty = _ATOMIC_WEIGHTS[symbol]
        value += Decimal(weight) * count
        # A conservative linear bound; correlations are not asserted.
        uncertainty += Decimal(weight_uncertainty) * count
    ordered = dict(
        sorted(composition.items(), key=lambda item: _ATOMIC_WEIGHTS[item[0]][0])
    )
    return _with_record_receipt({
        **_base_result(ChemistryConstantOperation.molar_mass),
        "query": {"formula": text},
        "result": {
            "quantity": "molar_mass_from_abridged_standard_atomic_weights",
            "formula": text,
            "composition": ordered,
            "value": _decimal_text(value),
            "uncertainty_bound": _decimal_text(uncertainty),
            "uncertainty_combination": "linear_sum",
            "unit": "g mol^-1",
        },
        "source": dict(_CIAAW_SOURCE),
    })


def reaction_template(template: str) -> dict[str, object]:
    """Return one generic reaction schema without instantiating a problem."""

    template_id = _validate_argument(template, label="template")
    if _TEMPLATE_ID.fullmatch(template_id) is None:
        _fail("template must be one lowercase registry identifier")
    record = _REACTION_TEMPLATES.get(template_id)
    if record is None:
        _fail("reaction template is not present in the pinned registry")
    # JSON round-tripping provides a detached object without admitting an
    # arbitrary deep-copy/data-loader dependency into this pure module.
    detached = json.loads(_canonical_json(record))
    return _with_record_receipt({
        **_base_result(ChemistryConstantOperation.reaction_template),
        "query": {"template": template_id},
        "result": {"id": template_id, **detached},
        "source": dict(_TEMPLATE_SOURCE),
    })


def contest_interpretation(policy: str) -> dict[str, object]:
    """Return one bounded contest-language policy without choosing an answer."""

    policy_id = _validate_argument(policy, label="policy")
    if _TEMPLATE_ID.fullmatch(policy_id) is None:
        _fail("policy must be one lowercase registry identifier")
    record = _CONTEST_INTERPRETATIONS.get(policy_id)
    if record is None:
        _fail("contest interpretation is not present in the pinned registry")
    detached = json.loads(_canonical_json(record))
    return _with_record_receipt({
        **_base_result(ChemistryConstantOperation.contest_interpretation),
        "query": {"policy": policy_id},
        "result": {"id": policy_id, **detached},
        "source": dict(_CONTEST_INTERPRETATION_SOURCE),
    })


def empirical_rule(rule: str) -> dict[str, object]:
    """Return one reviewed literature rule or bounded policy without instantiation."""

    rule_id = _validate_argument(rule, label="rule")
    if _TEMPLATE_ID.fullmatch(rule_id) is None:
        _fail("rule must be one lowercase registry identifier")
    record = _EMPIRICAL_RULES.get(rule_id)
    if record is None:
        _fail("empirical rule is not present in the pinned registry")
    detached = json.loads(_canonical_json(record))
    pinned_record_sha256 = detached.pop("record_sha256")
    return _with_record_receipt({
        **_base_result(ChemistryConstantOperation.empirical_rule),
        "query": {"rule": rule_id},
        "result": detached["rule"],
        "source": detached["source"],
        "approval": detached["review"],
        "pinned_rule_record_sha256": pinned_record_sha256,
        "empirical_registry_manifest_sha256": _EMPIRICAL_REGISTRY["manifest"][
            "manifest_sha256"
        ],
        "base_dataset_sha256": BASE_DATASET_SHA256,
    })


def query_chemistry_constant(request: Mapping[str, object]) -> dict[str, object]:
    """Dispatch one strict ``{operation, argument}`` request.

    Exact field equality is intentional: there is no field in which a problem
    id, question, URL, search phrase, or other free text can be smuggled.
    """

    if not isinstance(request, Mapping):
        _fail("request must be an object")
    if set(request) != {"operation", "argument"}:
        _fail("request must contain exactly operation and argument")
    raw_operation = request["operation"]
    if not isinstance(raw_operation, str):
        _fail("operation must be a string enum")
    try:
        operation = ChemistryConstantOperation(raw_operation)
    except ValueError:
        _fail("unsupported chemistry constant operation")
    argument = request["argument"]
    if not isinstance(argument, str):
        _fail("argument must be a string")
    dispatch = {
        ChemistryConstantOperation.atomic_weight: atomic_weight,
        ChemistryConstantOperation.isotope_mass: isotope_mass,
        ChemistryConstantOperation.molar_mass: molar_mass,
        ChemistryConstantOperation.reaction_template: reaction_template,
        ChemistryConstantOperation.contest_interpretation: contest_interpretation,
        ChemistryConstantOperation.empirical_rule: empirical_rule,
    }
    return dispatch[operation](argument)


def chemistry_constant(
    operation: ChemistryConstantOperation = typer.Argument(
        ...,
        help=(
            "atomic_weight | isotope_mass | molar_mass | reaction_template | "
            "contest_interpretation | empirical_rule"
        ),
    ),
    argument: str = typer.Argument(
        ...,
        help=(
            "One element symbol, isotope, formula, registered template id, or "
            "registered contest-policy/empirical-rule id."
        ),
    ),
) -> None:
    """Emit one version-pinned offline chemistry reference result as JSON."""

    try:
        result = query_chemistry_constant(
            {"operation": operation.value, "argument": argument}
        )
    except ChemistryConstantError as exc:
        raise typer.BadParameter(str(exc)) from exc
    print(_canonical_json(result).decode("utf-8"))
