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

EXPECTED_EMPIRICAL_RULE_IDS = (
    "aqueous_feiii_phenol_colored_complex",
    "closed_candidate_feiii_phenol_filter",
    "closed_domain_mellite_terminal_residue_candidate_filter",
    "directed_reaction_omitted_protocol_candidate_filter",
    "hexamethylbenzene_cold_kmno4_to_mellitic_acid",
    "mellite_ideal_stoichiometry",
    "mellitic_acid_benzoyl_chloride_to_c12o9",
    "mellitic_acid_p2o5_heating_forms_some_trianhydride",
)


def test_dataset_digest_and_atomic_weight_are_version_pinned() -> None:
    assert chemistry.BASE_DATASET_VERSION == (
        "ciaaw-abridged-2024+ame2020-subset+archon-templates-v1"
        "+contest-interpretation-v1"
    )
    assert chemistry.BASE_DATASET_SHA256 == (
        "3f9ac23f3515cf263275c244772de895c5402fb59a12061aa81c65ede91c094f"
    )
    assert chemistry.DATASET_VERSION == (
        chemistry.BASE_DATASET_VERSION + "+trusted-empirical-rules-v1"
    )
    assert chemistry.DATASET_SHA256 == (
        "6c5b5693698bb4f871d92889801080ef5b50a4342acd79e1881a578bc228d71d"
    )
    assert chemistry.REACTION_TEMPLATE_IDS == (
        "binary_two_fragment_electrophilic_addition",
    )
    assert chemistry.CONTEST_INTERPRETATION_IDS == (
        "analogous_halogen_addition",
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
        chemistry.empirical_rule("closed_candidate_feiii_phenol_filter"),
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
        "88237b93c886b5101c9d01b4cedecc79a64b19d87f4c8930679002bb80492911"
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


def test_empirical_rule_inventory_is_exact_reviewed_and_source_hash_bound() -> None:
    assert chemistry.EMPIRICAL_RULE_IDS == EXPECTED_EMPIRICAL_RULE_IDS
    authority_kinds: set[str] = set()
    for rule_id in EXPECTED_EMPIRICAL_RULE_IDS:
        lookup = chemistry.empirical_rule(rule_id)
        rule = lookup["result"]
        source = lookup["source"]
        approval = lookup["approval"]
        assert lookup["query"] == {"rule": rule_id}
        assert lookup["operation"] == "empirical_rule"
        assert lookup["runtime_network_access"] is False
        assert lookup["dataset_sha256"] == chemistry.DATASET_SHA256
        assert lookup["base_dataset_sha256"] == chemistry.BASE_DATASET_SHA256
        assert lookup["empirical_registry_manifest_sha256"] == (
            "3e601284303874283cf0b8a08b06db1653fc037b82360b0ef5385c8bec832dc0"
        )
        for digest in (
            lookup["record_sha256"],
            lookup["pinned_rule_record_sha256"],
            lookup["empirical_registry_manifest_sha256"],
            source["content_sha256"],
        ):
            assert len(digest) == 64
            assert set(digest) <= set("0123456789abcdef")
        assert set(source) == {"content_sha256", "doi", "locator", "url"}
        assert type(source["url"]) is str and source["url"].startswith("https://")
        if rule_id == "closed_domain_mellite_terminal_residue_candidate_filter":
            assert source["doi"] is None
        else:
            assert type(source["doi"]) is str and source["doi"].startswith(
                "10."
            )
        assert type(source["locator"]) is str and source["locator"]
        assert set(approval) == {
            "approval_scope",
            "approved_at",
            "reviewer_id",
            "status",
        }
        assert approval["status"] == "approved"
        assert approval["approval_scope"] == "rule_and_source"
        assert rule["rule_id"] == rule_id
        assert rule["automatic_problem_instantiation"] is False
        assert rule["applicability_conditions"]
        assert rule["exclusions"]
        authority_kinds.add(rule["authority_kind"])

    assert authority_kinds == {
        "contest_semantics_policy",
        "peer_reviewed_literature",
    }
    bounded = chemistry.empirical_rule("closed_candidate_feiii_phenol_filter")
    assert bounded["pinned_rule_record_sha256"] == (
        "ec6cff1cee7889c97ad67a0f5c9a33d1462a67ea6f14a01dc1087cd10e67e7be"
    )
    assert bounded["source"]["content_sha256"] == (
        "31b0a37ddab2aba737a30d94dbd514b0a5831ac61451631a2b73dd7164148286"
    )
    assert bounded["result"]["authority_kind"] == "contest_semantics_policy"
    assert bounded["record_sha256"] == (
        "730d52d5dbafadff8fc6bf12a9bbe594ee282b70e76a9015cd4da6b49d2b8cd5"
    )
    assert bounded["result"]["rule_version"] == 2
    assert chemistry.BASELINE_EMPIRICAL_RULE_IDS == (
        "aqueous_feiii_phenol_colored_complex",
        "hexamethylbenzene_cold_kmno4_to_mellitic_acid",
        "mellite_ideal_stoichiometry",
        "mellitic_acid_benzoyl_chloride_to_c12o9",
    )
    assert chemistry.DORMANT_RUNTIME_BRIDGE_IDS == (
        "closed_candidate_feiii_phenol_filter",
        "closed_domain_mellite_terminal_residue_candidate_filter",
        "mellitic_acid_p2o5_heating_forms_some_trianhydride",
    )
    conditions = " ".join(
        bounded["result"]["applicability_conditions"]
    ).casefold()
    for required_condition in (
        "independently source-bound exact-carbon-count",
        "positive aqueous iron(iii)",
        "problem authors explicitly label",
        "complete source-bound structure",
        "unactivated aliphatic alcohol",
        "saturated ether",
        "hydrocarbon",
        "simple non-chelating monoketone",
        "beta-dicarbonyl or enol",
        "hydroxamate",
        "catecholate-like",
        "explicitly iron-binding ligand",
        "unclassified functionality",
        "incompatible ph",
        "strong ligand",
        "precipitation branch",
        "alternative reagent",
        "nonselective branch",
        "does not require or infer unstated test details",
        "solver-created category",
    ):
        assert required_condition in conditions
    exclusions = " ".join(bounded["result"]["exclusions"]).casefold()
    for required_exclusion in (
        "required source-stated cue or required audit is missing",
        "fixed whitelist cannot be expanded",
        "failure to find an interferent",
        "unclassified response-relevant functionality",
        "does not infer unstated ph",
    ):
        assert required_exclusion in exclusions
    assert any(
        "not a universal" in exclusion.casefold()
        for exclusion in bounded["result"]["exclusions"]
    )
    serialized = json.dumps(bounded, ensure_ascii=False).casefold()
    for forbidden in ("t1-a3", "icho_", "official_answer"):
        assert forbidden not in serialized



def test_empirical_rule_partitions_are_exact_disjoint_and_complete() -> None:
    assert chemistry.BASELINE_EMPIRICAL_RULE_IDS == (
        "aqueous_feiii_phenol_colored_complex",
        "closed_candidate_feiii_phenol_filter",
        "hexamethylbenzene_cold_kmno4_to_mellitic_acid",
        "mellite_ideal_stoichiometry",
        "mellitic_acid_benzoyl_chloride_to_c12o9",
    )
    assert chemistry.REFERENCE_ONLY_EMPIRICAL_RULE_IDS == (
        "mellitic_acid_p2o5_heating_forms_some_trianhydride",
    )
    assert chemistry.DORMANT_RUNTIME_BRIDGE_IDS == (
        "closed_domain_mellite_terminal_residue_candidate_filter",
        "directed_reaction_omitted_protocol_candidate_filter",
    )
    partitions = (
        set(chemistry.BASELINE_EMPIRICAL_RULE_IDS),
        set(chemistry.REFERENCE_ONLY_EMPIRICAL_RULE_IDS),
        set(chemistry.DORMANT_RUNTIME_BRIDGE_IDS),
    )
    assert all(
        not left.intersection(right)
        for index, left in enumerate(partitions)
        for right in partitions[index + 1 :]
    )
    assert set().union(*partitions) == set(chemistry.EMPIRICAL_RULE_IDS)


def test_mellitic_acid_p2o5_rule_is_partial_and_cannot_ground_tga_residue() -> None:
    rule_id = "mellitic_acid_p2o5_heating_forms_some_trianhydride"
    lookup = chemistry.empirical_rule(rule_id)

    assert lookup["pinned_rule_record_sha256"] == (
        "3b7cdcf821c3e9a5dd9afa3619055d24128848437b7c52d0af517b61c64c5e1a"
    )
    assert lookup["source"]["content_sha256"] == (
        "1822acf0805229c60a29a539aa0c520b1a54114a32296da405cf6f1632d6ca7c"
    )
    assert lookup["source"]["doi"] == "10.1007/BF01519380"
    assert "printed pp. 512–513" in lookup["source"]["locator"]
    assert (
        "0f4ebc8243842aad7ebb646fe9ac80cadd07515cab6553fc80ae526403b306e6"
        in lookup["source"]["locator"]
    )

    rule = lookup["result"]
    assert rule["claim"] == (
        "When mellitic acid is heated with phosphorus pentoxide under the "
        "reported conditions, some mellitic trianhydride (C12O9) forms."
    )
    assert any(
        "existential and partial" in condition.casefold()
        for condition in rule["applicability_conditions"]
    )
    claim = rule["claim"].casefold()
    for unsupported in (
        "complete", "quantitative", "sole", "principal", "pure", "yield"
    ):
        assert unsupported not in claim
    exclusions = " ".join(rule["exclusions"]).casefold()
    for required_boundary in (
        "complete or quantitative dehydration",
        "sole or principal product",
        "thermal-decomposition rule",
        "open-air thermogravimetric residue",
    ):
        assert required_boundary in exclusions
    assert "al2o3" not in json.dumps(lookup, ensure_ascii=False).casefold()
    assert rule_id in chemistry.REFERENCE_ONLY_EMPIRICAL_RULE_IDS
    assert rule_id not in chemistry.DORMANT_RUNTIME_BRIDGE_IDS
    assert rule_id not in chemistry.BASELINE_EMPIRICAL_RULE_IDS

    assert not any(
        "open_air" in registered or "thermal_residue" in registered
        for registered in chemistry.EMPIRICAL_RULE_IDS
    )
    for unsupported_rule_id in (
        "mellitic_acid_p2o5_complete_dehydration",
        "mellite_open_air_thermal_residue_identity",
    ):
        with pytest.raises(chemistry.ChemistryConstantError):
            chemistry.empirical_rule(unsupported_rule_id)


def test_directed_reaction_omitted_protocol_policy_is_strictly_bounded() -> None:
    rule_id = "directed_reaction_omitted_protocol_candidate_filter"
    lookup = chemistry.empirical_rule(rule_id)

    assert lookup["record_sha256"] == (
        "e26dd359e15994fad029afaa9fe4b9d2fd2099ef387ca7749707a7b17f6286b7"
    )
    assert lookup["pinned_rule_record_sha256"] == (
        "95b269e7749a26345fbc62a57b37412f5c71ff985d4a7929f088024bdef1309d"
    )
    assert lookup["source"]["content_sha256"] == (
        "6076dbf045427d68c6cdda3d5632223a69b5d14fd7304f5cb50ce4519d3aefde"
    )
    assert lookup["source"]["doi"] == "10.1039/9781847557889"
    assert "section 2.12.1" in lookup["source"]["locator"]
    assert lookup["result"]["rule_version"] == 1
    assert lookup["result"]["authority_kind"] == "contest_semantics_policy"
    assert lookup["result"]["automatic_problem_instantiation"] is False

    claim = lookup["result"]["claim"].casefold()
    for required in (
        "explicitly closed source-bounded candidate set",
        "explicit directed statement",
        "non-exclusive positive constraint",
        "protocol details are omitted",
    ):
        assert required in claim

    conditions = " ".join(
        lookup["result"]["applicability_conditions"]
    ).casefold()
    for required in (
        "exact input-source locator",
        "same clause",
        "direction is source-stated",
        "every omitted detail is recorded as unknown",
        "independently established from source-bounded evidence",
        "composition and symmetry",
        "finite, explicitly closed candidate set",
        "derived without this policy",
        "independently satisfies its own exact substrate, reagent, and protocol",
    ):
        assert required in conditions

    exclusions = " ".join(lookup["result"]["exclusions"]).casefold()
    for required in (
        "does not infer heating",
        "temperature, time, pressure, solvent, atmosphere",
        "yield, conversion extent, completeness",
        "sole or principal product",
        "extra conditions may not supply an omitted source condition",
        "neither identifies any reactant, reagent, or product",
        "reverse implication",
        "open-world classification",
        "thermal-decomposition inference",
        "terminal-residue inference",
        "does not establish this bounded contest policy",
    ):
        assert required in exclusions

    serialized = json.dumps(lookup, ensure_ascii=False).casefold()
    for forbidden in (
        "c12o9",
        "al2o3",
        "mellitic",
        "t1-a6",
        "icho_",
        "official_answer",
        "expected_answer",
    ):
        assert forbidden not in serialized


def test_closed_domain_mellite_terminal_residue_policy_is_strictly_bounded() -> None:
    rule_id = "closed_domain_mellite_terminal_residue_candidate_filter"
    lookup = chemistry.empirical_rule(rule_id)

    assert lookup["record_sha256"] == (
        "db55dee7aee6811f4cae4d81b7e944002414828fb8f6124cd47831ba8f693de3"
    )
    assert lookup["pinned_rule_record_sha256"] == (
        "b1720156ef1b5e8e0c169a12cfe0179fe95bcba91841e53a5a8b6fba91b73308"
    )
    assert lookup["empirical_registry_manifest_sha256"] == (
        "3e601284303874283cf0b8a08b06db1653fc037b82360b0ef5385c8bec832dc0"
    )
    assert lookup["source"] == {
        "content_sha256": (
            "e70b86d5caf6a3ddc2de272796dabece6197d5e3f6e396ece643188e680bcb2e"
        ),
        "doi": None,
        "locator": (
            "Piazza, Mellite, Enciclopedia Italiana (1934), sentence "
            "reporting that mellite burns in a blowpipe test and leaves an "
            "infusible alumina residue. Normalized Italian sentence SHA-256: "
            "5b58d1ef840834a81224de8487fde93c4f09ef2ed4643f70f0e530cdc76357a5."
        ),
        "url": (
            "https://www.treccani.it/enciclopedia/"
            "mellite_%28Enciclopedia-Italiana%29/"
        ),
    }

    rule = lookup["result"]
    assert rule["rule_version"] == 2
    assert rule["authority_kind"] == "contest_semantics_policy"
    assert rule["automatic_problem_instantiation"] is False
    assert rule["claim"] == (
        "Within an explicitly closed source-bounded domain satisfying every "
        "listed condition, the source's conjunctive named-final cue may be "
        "used only to retain a primitive neutral terminal-residue formula "
        "candidate that passes the complete atom, charge, and measured-mass "
        "interval audit."
    )
    conditions = " ".join(rule["applicability_conditions"]).casefold()
    for required_cue in (
        "one exact input-source locator",
        "thermogravimetric analysis",
        "unambiguous stated atmosphere",
        "later mass-loss event",
        "names the ensuing mass as final",
        "named single compound",
        "mass remains constant at higher temperatures",
        "bounded terminal-product stipulation",
        "current source bundle",
        "controller-authenticated fallback",
        "transparently rederives",
        "bound prior-part sources",
        "prior-part question or label",
        "every earlier mass-loss stage",
        "source-led mass ledger",
        "identity and completeness are established independently",
        "treccani source is used only as qualitative corroboration",
        "finite closed candidate audit",
        "primitive neutral integer terminal-residue formula",
        "independently established element and oxidation-state domain",
        "atom, charge, and every measured-mass interval",
        "pinned constants and source uncertainties",
        "every possible counterion, dopant, container, reagent",
        "mere failure to mention one is insufficient",
    ):
        assert required_cue in conditions

    exclusions = " ".join(rule["exclusions"]).casefold()
    for required_boundary in (
        "not a paper or universal empirical calcination law",
        "does not identify an open-world residue",
        "bare stable plateau",
        "ambiguous or unstated atmosphere",
        "not expressly called final",
        "not expressly named as a single compound",
        "activation receipt proves catalog integrity",
        "does not prove that any named-final cue",
        "does not establish the identity or completeness of any earlier dehydration",
        "does not establish thermogravimetric conditions",
        "complete conversion",
        "quantitative recovery",
        "temperature-time program",
        "specific temperature",
        "duration, yield, purity, phase, or polymorph",
        "mass agreement alone",
        "missing constituents, oxidation states, candidate closure",
    ):
        assert required_boundary in exclusions

    serialized = json.dumps(lookup, ensure_ascii=False).casefold()
    for forbidden_value in (
        "al2o3",
        "c12o9",
        "szöőr",
        "t1-a6",
        "icho_",
        "official_answer",
        "expected_answer",
    ):
        assert forbidden_value not in serialized

    def all_mapping_keys(value: object) -> set[str]:
        if isinstance(value, dict):
            return set(value) | set().union(
                *(all_mapping_keys(child) for child in value.values())
            )
        if isinstance(value, list):
            return set().union(*(all_mapping_keys(child) for child in value))
        return set()

    assert all_mapping_keys(lookup).isdisjoint(
        {
            "answer_key",
            "candidate_answer",
            "expected_answer",
            "official_answer",
            "problem_id",
            "question_id",
            "target",
            "target_id",
        }
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
        (chemistry.reaction_template, "benzylic_oxidation_permanganate"),
        (chemistry.contest_interpretation, "symmetry_guided_benzylic_oxidation"),
        (chemistry.empirical_rule, "benzylic_oxidation_permanganate"),
        (chemistry.empirical_rule, "T1-A3"),
        (chemistry.empirical_rule, "https://example.test/rule"),
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
    rule_success = runner.invoke(
        app,
        [
            "chemistry-constant",
            "empirical_rule",
            "closed_candidate_feiii_phenol_filter",
        ],
    )
    assert rule_success.exit_code == 0, rule_success.output
    rule_payload = json.loads(rule_success.stdout)
    assert rule_payload["query"] == {
        "rule": "closed_candidate_feiii_phenol_filter"
    }
    assert rule_payload["result"]["authority_kind"] == "contest_semantics_policy"
    assert rule_payload["source"]["content_sha256"] == (
        "31b0a37ddab2aba737a30d94dbd514b0a5831ac61451631a2b73dd7164148286"
    )


    for arguments in (
        ["chemistry-constant", "atomic_weight", "T5-A4"],
        ["chemistry-constant", "atomic_weight", "C", "question text"],
        ["chemistry-constant", "web_search", "C"],
        ["chemistry-constant", "contest_interpretation", "IBr"],
        ["chemistry-constant", "empirical_rule", "benzylic_oxidation_permanganate"],
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
        "empirical_rule <RULE_ID>",
        "exact `TEMPLATE_ID` allowlist",
        "binary_two_fragment_electrophilic_addition",
        "exact `POLICY_ID` allowlist",
        "analogous_halogen_addition",
        "full supported registries",
        "exact allowed `RULE_ID` inventory",
        "four-ID list is an exact allowlist",
        "Reference-only empirical-rule IDs",
        "cannot receive a controller activation receipt",
        "Never borrow a missing protocol condition",
        "if even one lacks exact evidence",
        "Receipt completeness never establishes applicability",
        "non-premise context",
        "Dormant Reviewer-requestable bridge IDs",
        "ordinary lookup",
        "complete controller-built",
        "Never guess, enumerate, or probe other rule ids",
        "unlisted id must fail closed",
        "peer_reviewed_literature",
        "contest_semantics_policy",
        "bounded contest policy—not a paper or universal empirical law",
        "complete source-supplied finite candidate set",
        "automatic_problem_instantiation",
        "bounded policy into an open-world rule",
        "base_dataset_sha256",
        "pinned_rule_record_sha256",
        "empirical_registry_manifest_sha256",
        "source.url",
        "source.doi",
        "source.locator",
        "source.content_sha256",
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
    for rule_id in EXPECTED_EMPIRICAL_RULE_IDS:
        assert mode.count(rule_id) == 1
    assert "benzylic_oxidation_permanganate" not in mode
    assert mode.count("binary_two_fragment_electrophilic_addition") == 1
    assert mode.count("analogous_halogen_addition") == 1
    assert "symmetry_guided_benzylic_oxidation" not in mode
