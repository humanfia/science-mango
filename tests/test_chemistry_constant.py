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
        "c78d4b2d859195f692874a2a6547216d3748fa4659c190531a73acc15cfabf1a"
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
        "f50956bdd17a984bbc103df8686f705ae791fa155235c39390137c0dd31d3473"
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
            "9a8243a90ece51b7f9f22851aa0ea8b41db2ce7c4585c38399d407c0322541cb"
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
        "a557ad414f8d8e902c5ba2909db4dba67ffc8aaa6982448170fd27d8218e3ace"
    )
    assert bounded["source"]["content_sha256"] == (
        "31b0a37ddab2aba737a30d94dbd514b0a5831ac61451631a2b73dd7164148286"
    )
    assert bounded["result"]["authority_kind"] == "contest_semantics_policy"
    assert any(
        "not a universal" in exclusion.casefold()
        for exclusion in bounded["result"]["exclusions"]
    )
    serialized = json.dumps(bounded, ensure_ascii=False).casefold()
    for forbidden in ("t1-a3", "icho_", "official_answer"):
        assert forbidden not in serialized


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


def test_closed_domain_mellite_terminal_residue_policy_is_strictly_bounded() -> None:
    rule_id = "closed_domain_mellite_terminal_residue_candidate_filter"
    lookup = chemistry.empirical_rule(rule_id)

    assert lookup["record_sha256"] == (
        "c536a858931b0ef83671140ebb9ed87e8f8c3f791c9f743dba526872fc1fa61f"
    )
    assert lookup["pinned_rule_record_sha256"] == (
        "cdb1daf3b0e543ce4e17e399324a2fb3d05c13a2cb896fd692b0d74f9db940f6"
    )
    assert lookup["empirical_registry_manifest_sha256"] == (
        "9a8243a90ece51b7f9f22851aa0ea8b41db2ce7c4585c38399d407c0322541cb"
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
    assert rule["authority_kind"] == "contest_semantics_policy"
    assert rule["automatic_problem_instantiation"] is False
    assert rule["claim"] == (
        "Within an explicitly closed problem domain satisfying every listed "
        "condition, a neutral integer formula candidate composed only of "
        "trivalent aluminium and divalent oxygen may be retained as a "
        "terminal-residue candidate when it passes the complete atom, charge, "
        "and measured-mass interval audit."
    )
    conditions = " ".join(rule["applicability_conditions"]).casefold()
    for required_cue in (
        "independently established as ideal stoichiometric mellite",
        "mellite_ideal_stoichiometry receipt",
        "problem source explicitly states thermogravimetric heating in open air",
        "final residue mass that remains stable at higher temperatures",
        "affirmatively establishes complete conversion to a terminal phase",
        "only nonvolatile elements available to the terminal residue",
        "every possible counterion, dopant, container, or atmosphere contribution",
        "every charge-neutral integer formula",
        "trivalent aluminium and divalent oxygen",
        "atom, charge, and measured-mass intervals",
        "pinned constants and source uncertainties",
        "treccani mellite source is used only as qualitative corroboration",
        "infusible alumina residue in a blowpipe test",
    ):
        assert required_cue in conditions

    exclusions = " ".join(rule["exclusions"]).casefold()
    for required_boundary in (
        "not a paper or a universal empirical calcination law",
        "does not identify an open-world residue",
        "missing or ambiguous",
        "does not itself establish open-air thermogravimetric conditions",
        "complete conversion",
        "quantitative recovery",
        "temperature-time program",
        "specific calcination or thermogravimetric temperature",
        "duration, yield, purity, phase, or polymorph",
        "mass agreement alone",
        "ambiguous-atmosphere trace",
    ):
        assert required_boundary in exclusions

    serialized = json.dumps(lookup, ensure_ascii=False).casefold()
    for forbidden_value in (
        "al2o3",
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
        "five-ID list is an exact allowlist",
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
