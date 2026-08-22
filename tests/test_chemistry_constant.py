from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

import pytest
from typer.testing import CliRunner

from archon.cli import app
from archon.commands import chemistry_constant as chemistry


ROOT = Path(__file__).resolve().parents[1]
FORMALIZER_MODE = (
    ROOT
    / "src/archon/.archon-src/prover-modes/chemistry-formalize.md"
)


def test_dataset_digest_and_atomic_weight_are_version_pinned() -> None:
    assert chemistry.DATASET_VERSION == (
        "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1"
    )
    assert chemistry.DATASET_SHA256 == (
        "2b3ff5a2c617ac4eb86bcd72f40c09f78bb46565828f6b333a1778dc99396eba"
    )
    result = chemistry.atomic_weight("C")
    assert result["runtime_network_access"] is False
    assert result["dataset_sha256"] == chemistry.DATASET_SHA256
    assert result["query"] == {"element": "C"}
    assert result["result"] == {
        "quantity": "abridged_standard_atomic_weight",
        "atomic_number": 6,
        "element": "C",
        "value": "12.011",
        "uncertainty": "0.002",
        "unit": "1",
    }


def test_isotope_mass_uses_canonical_allowlisted_nuclide() -> None:
    result = chemistry.isotope_mass("U-235")
    assert result["query"] == {"isotope": "U-235"}
    assert result["result"] == {
        "quantity": "atomic_mass",
        "atomic_number": 92,
        "element": "U",
        "mass_number": 235,
        "value": "235.043928117",
        "uncertainty": "0.000001198",
        "unit": "Da",
    }
    assert chemistry.isotope_mass("C-12")["result"]["value"] == (
        "12.000000000000"
    )


def test_each_lookup_has_a_stable_exact_record_receipt() -> None:
    lookups = (
        chemistry.atomic_weight("Br"),
        chemistry.isotope_mass("Br-79"),
        chemistry.molar_mass("H2O"),
        chemistry.reaction_template("binary_two_fragment_electrophilic_addition"),
    )
    receipts: set[str] = set()
    for lookup in lookups:
        receipt = lookup["record_sha256"]
        unsigned = dict(lookup)
        del unsigned["record_sha256"]
        expected = hashlib.sha256(
            json.dumps(
                unsigned,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
            ).encode("utf-8")
        ).hexdigest()
        assert receipt == expected
        receipts.add(receipt)
    assert len(receipts) == len(lookups)


def test_molar_mass_parses_formula_groups_and_hydrates_without_float() -> None:
    glucose = chemistry.molar_mass("C6H12O6")
    assert glucose["result"] == {
        "quantity": "molar_mass_from_abridged_standard_atomic_weights",
        "formula": "C6H12O6",
        "composition": {"H": 12, "C": 6, "O": 6},
        "value": "180.156",
        "uncertainty_bound": "0.0204",
        "uncertainty_combination": "linear_sum",
        "unit": "g mol^-1",
    }

    hydrate = chemistry.molar_mass("Al2(C6(COO)6)·16H2O")
    assert hydrate["result"]["composition"] == {
        "H": 32,
        "C": 12,
        "O": 28,
        "Al": 2,
    }
    assert hydrate["result"]["value"] == "678.324"


def test_generic_reaction_template_does_not_instantiate_or_encode_an_answer() -> None:
    result = chemistry.reaction_template(
        "binary_two_fragment_electrophilic_addition"
    )
    contract = result["result"]
    assert contract["stoichiometry"] == {
        "addends_delivered_per_site": 2,
        "reagent_molecules_per_site": 1,
    }
    assert contract["reagent"]["fragment_kind"] == "single_atom_addend"
    assert contract["retention"]["all_reagent_addends_retained_in_product"] is True
    assert contract["instantiation_policy"] == {
        "automatic_problem_instantiation": False,
        "does_not_identify_elements": True,
        "requires_source_or_trusted_classification_evidence": True,
    }
    serialized = json.dumps(result, ensure_ascii=False).lower()
    for forbidden in ("ibr", "t5-a4", "icho_", "official_answer"):
        assert forbidden not in serialized


@pytest.mark.parametrize(
    ("function", "argument"),
    [
        (chemistry.atomic_weight, "carbon"),
        (chemistry.atomic_weight, "T5-A4"),
        (chemistry.atomic_weight, "C;search"),
        (chemistry.atomic_weight, "Xx"),
        (chemistry.isotope_mass, "235U"),
        (chemistry.isotope_mass, "U 235"),
        (chemistry.isotope_mass, "icho_2026_t3_a1"),
        (chemistry.molar_mass, "mass of water"),
        (chemistry.molar_mass, "T3-A1"),
        (chemistry.molar_mass, "H2O;search"),
        (chemistry.molar_mass, "NaCl+"),
        (chemistry.molar_mass, "H0"),
        (chemistry.molar_mass, "H2O..NaCl"),
        (chemistry.molar_mass, "(((((H)))))"),
        (chemistry.reaction_template, "T5-A4"),
        (chemistry.reaction_template, "I-Br"),
    ],
)
def test_query_arguments_fail_closed_on_names_questions_and_free_text(
    function: object, argument: str
) -> None:
    with pytest.raises(chemistry.ChemistryConstantError):
        function(argument)  # type: ignore[operator]


@pytest.mark.parametrize(
    "query",
    [
        {"operation": "atomic_weight", "argument": "C", "question": "..."},
        {"operation": "atomic_weight", "element": "C"},
        {"operation": "web_search", "argument": "C"},
        {"operation": "atomic_weight", "argument": "C", "id": "T3-A1"},
    ],
)
def test_structured_request_rejects_extra_or_unknown_fields(
    query: dict[str, object]
) -> None:
    with pytest.raises(chemistry.ChemistryConstantError):
        chemistry.query_chemistry_constant(query)


def test_module_has_no_file_process_environment_or_network_imports() -> None:
    source = Path(chemistry.__file__).read_text(encoding="utf-8")
    imported_roots: set[str] = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Import):
            imported_roots.update(alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported_roots.add(node.module.split(".", 1)[0])
    assert imported_roots.isdisjoint(
        {
            "http",
            "os",
            "pathlib",
            "requests",
            "shutil",
            "socket",
            "subprocess",
            "urllib",
        }
    )


def test_cli_emits_one_json_result_and_rejects_extra_input() -> None:
    runner = CliRunner()
    success = runner.invoke(
        app, ["chemistry-constant", "atomic_weight", "Br"]
    )
    assert success.exit_code == 0, success.output
    payload = json.loads(success.stdout)
    assert payload["query"] == {"element": "Br"}
    assert payload["result"]["value"] == "79.904"
    assert payload["runtime_network_access"] is False

    for arguments in (
        ["chemistry-constant", "atomic_weight", "T5-A4"],
        ["chemistry-constant", "atomic_weight", "C", "question text"],
        ["chemistry-constant", "web_search", "C"],
    ):
        rejected = runner.invoke(app, arguments)
        assert rejected.exit_code != 0
        assert rejected.stdout == ""


def test_chemistry_formalizer_sees_strict_offline_query_contract() -> None:
    mode = " ".join(FORMALIZER_MODE.read_text(encoding="utf-8").split())
    for phrase in (
        "Trusted offline chemistry reference",
        '"$ARCHON_CLI_BIN" chemistry-constant atomic_weight <ELEMENT>',
        '"$ARCHON_CLI_BIN" chemistry-constant isotope_mass <ISOTOPE>',
        '"$ARCHON_CLI_BIN" chemistry-constant molar_mass <FORMULA>',
        "reaction_template <TEMPLATE_ID>",
        "grammar placeholders, not literal tokens",
        "illustrative, not an allowlist",
        "record_sha256",
        "candidate-local `axiom`",
        "name alone is not provenance",
        "configured sealed pinned library",
        "Reviewer must verify every used lookup",
        "source uncertainty could change",
        "Problem-stipulated values override",
        chemistry.DATASET_VERSION,
        "Never send a",
        "problem id, question text",
        "performs no network access",
        "never establishes that the current reaction",
        "an instance.",
    ):
        assert phrase in mode

    assert "archon chemistry-constant" not in mode
