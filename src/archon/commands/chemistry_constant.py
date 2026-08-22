"""Version-pinned, offline chemistry reference queries.

This module is deliberately a closed-world data service.  It accepts only a
small structured query vocabulary, reads no files or environment variables,
and has no network/process API.  The returned data version and digest make a
solver's dependency on general chemistry constants auditable.

Atomic weights are the CIAAW 2024 abridged standard atomic weights.  Isotope
masses are a small, explicit AME2020 subset; an absent nuclide fails closed.
The reaction-template registry contains generic schemas, never problem
instances or candidate answers.
"""

from __future__ import annotations

from collections import Counter
from decimal import Decimal
from enum import Enum
import hashlib
import json
import re
from typing import Mapping, NoReturn

import typer


SCHEMA_VERSION = 1
DATASET_VERSION = "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1"
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


class ChemistryConstantError(ValueError):
    """A query is outside the closed, structured reference vocabulary."""


class ChemistryConstantOperation(str, Enum):
    atomic_weight = "atomic_weight"
    isotope_mass = "isotope_mass"
    molar_mass = "molar_mass"
    reaction_template = "reaction_template"


def _canonical_json(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


_DATASET_PAYLOAD = {
    "schema_version": SCHEMA_VERSION,
    "dataset_version": DATASET_VERSION,
    "sources": [_CIAAW_SOURCE, _AME_SOURCE, _TEMPLATE_SOURCE],
    "atomic_weights": _ATOMIC_WEIGHTS,
    "isotope_masses": _ISOTOPE_MASSES,
    "reaction_templates": _REACTION_TEMPLATES,
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
    }
    return dispatch[operation](argument)


def chemistry_constant(
    operation: ChemistryConstantOperation = typer.Argument(
        ...,
        help="atomic_weight | isotope_mass | molar_mass | reaction_template",
    ),
    argument: str = typer.Argument(
        ...,
        help="One element symbol, isotope, formula, or registered template id.",
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
