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
        "+contest-interpretation-v1"
    )
    assert chemistry.DATASET_SHA256 == (
        "3f9ac23f3515cf263275c244772de895c5402fb59a12061aa81c65ede91c094f"
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
        chemistry.contest_interpretation("analogous_halogen_addition"),
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


def test_contest_interpretation_is_bounded_policy_not_empirical_answer() -> None:
    lookup = chemistry.contest_interpretation("analogous_halogen_addition")
    policy = lookup["result"]
    assert lookup["record_sha256"] == (
        "0eae4e05cd841f16d00ca474eab8eb9158e1c208be357eddfc1320f8f203ac82"
    )
    assert lookup["operation"] == "contest_interpretation"
    assert lookup["runtime_network_access"] is False
    assert lookup["source"]["empirical_claim"] is False
    assert lookup["source"]["authority_kind"] == "contest_semantics_policy"
    assert policy["authority_kind"] == "contest_semantics_policy"
    assert policy["empirical_claim"] is False
    assert policy["source_cues"] == {
        "benchmark_reagent_reference": (
            "molecular_formula_or_elemental_halogen_name_in_addition_context"
        ),
        "same_unsaturated_substrate": True,
        "comparison_wording_any_of": ["same_way", "similar_way", "analogous_way"],
        "quantitative_addition_or_adduct_context": True,
        "molecular_formula_of_unknown_requested": True,
    }
    assert policy["interpretation"] == {
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
    }
    admission = policy["admission_policy"]
    assert admission["automatic_problem_instantiation"] is False
    assert admission["requires_exact_problem_text_locator"] is True
    assert admission["requires_no_contrary_problem_statement"] is True
    assert admission["problem_wording_overrides_policy"] is True
    assert admission["requires_all_source_cues"] is True
    assert admission["missing_or_ambiguous_cue"] == "fail_closed"
    assert admission["does_not_identify_specific_reagent"] is True
    assert admission["not_a_universal_inverse_chemistry_claim"] is True
    assert set(chemistry._CONTEST_INTERPRETATIONS) == {
        "analogous_halogen_addition"
    }
    serialized = json.dumps(lookup, ensure_ascii=False).lower()
    for forbidden in ("ibr", "t5-a4", "icho_", "181.0", "36.57", "official_answer"):
        assert forbidden not in serialized
    template = chemistry.reaction_template(
        policy["interpretation"]["reaction_template_id"]
    )["result"]
    interpretation = policy["interpretation"]
    assert interpretation["site_kind"] == template["site"]["kind"]
    assert (
        interpretation["sites_consumed_per_event"]
        == template["site"]["sites_consumed_per_event"]
    )
    assert (
        interpretation["reagent_molecules_per_site"]
        == template["stoichiometry"]["reagent_molecules_per_site"]
    )
    assert (
        interpretation["addends_delivered_per_site"]
        == template["stoichiometry"]["addends_delivered_per_site"]
    )
    assert (
        interpretation["all_reagent_addends_retained_in_product"]
        == template["retention"]["all_reagent_addends_retained_in_product"]
    )


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
        (chemistry.contest_interpretation, "T5-A4"),
        (chemistry.contest_interpretation, "IBr"),
        (chemistry.contest_interpretation, "similar way"),
        (chemistry.contest_interpretation, "unregistered_policy"),
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

    policy_success = runner.invoke(
        app,
        [
            "chemistry-constant",
            "contest_interpretation",
            "analogous_halogen_addition",
        ],
    )
    assert policy_success.exit_code == 0, policy_success.output
    policy_payload = json.loads(policy_success.stdout)
    assert policy_payload["query"] == {"policy": "analogous_halogen_addition"}
    assert policy_payload["result"]["empirical_claim"] is False

    for arguments in (
        ["chemistry-constant", "atomic_weight", "T5-A4"],
        ["chemistry-constant", "atomic_weight", "C", "question text"],
        ["chemistry-constant", "web_search", "C"],
        ["chemistry-constant", "contest_interpretation", "IBr"],
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
        "contest_interpretation <POLICY_ID>",
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
        "contest-language policy, not a paper, empirical chemistry fact",
        "exact problem-text locator",
        "Problem wording always overrides the policy",
        "missing, ambiguous, on a different substrate",
        "does not identify the specific reagent",
    ):
        assert phrase in mode

    assert "archon chemistry-constant" not in mode
