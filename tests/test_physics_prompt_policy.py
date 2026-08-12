from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PHYSICS_FORMALIZE_MODE = (
    ROOT / "src" / "archon" / ".archon-src" / "prover-modes" / "physics-formalize.md"
)
PHYSICS_PROVER_MODE = (
    ROOT / "src" / "archon" / ".archon-src" / "prover-modes" / "physics.md"
)
PHYSICS_REVIEWER = (
    ROOT / "src" / "archon" / ".archon-src" / "subagents" / "physics-reviewer.md"
)
CHEMISTRY_FORMALIZE_MODE = (
    ROOT / "src" / "archon" / ".archon-src" / "prover-modes" / "chemistry-formalize.md"
)
CHEMISTRY_PROVER_MODE = (
    ROOT / "src" / "archon" / ".archon-src" / "prover-modes" / "chemistry.md"
)
CHEMISTRY_REVIEWER = (
    ROOT / "src" / "archon" / ".archon-src" / "subagents" / "chemistry-reviewer.md"
)
PYPROJECT = ROOT / "pyproject.toml"


def test_physics_formalize_mode_is_loop_native_and_uses_leanexplore_physlib_scope():
    mode = PHYSICS_FORMALIZE_MODE.read_text(encoding="utf-8")

    assert "compatible_stages:\n  - autoformalize" in mode
    assert "create a Lean file" in mode
    assert "sorry bodies" in mode
    assert "Use LeanExplore before inventing APIs" in mode
    assert 'packages: ["Mathlib", "Physlib"]' in mode
    assert 'packages: ["Mathlib", "PhysLean"]' not in mode


def test_physics_formalize_mode_preserves_physical_modeling_not_scalar_placeholders():
    mode = PHYSICS_FORMALIZE_MODE.read_text(encoding="utf-8")

    required_contracts = [
        "Assumption/target split",
        "governing laws",
        "previous-part results",
        "figure/data readouts",
        "current target conclusions",
        "must not appear as hypotheses",
        "Goal-faithfulness audit",
        "named quantities and their roles",
        "units or dimensional meaning",
        "geometry/figure labels",
        "physical laws used as assumptions",
        "final relation to be proved",
        "Do not replace a physics statement with `True`",
        "Do not collapse basic physical primitives to transparent scalar aliases",
        "one-field wrappers",
        "smallest abstract type, structure, or hypothesis interface",
        "Capture problem/figure parameters",
        "Prefer assumptions that state the physical law",
        "derivability/bridge-obligation inventory",
        "Every abstract `Prop`-valued relation",
        "countermodel sanity check",
        "Preserve uncertainty and error information",
        "Preserve branch and orientation information",
        "Derivability and bridge obligations",
        "Abstraction sufficiency and countermodel audit",
        "Uncertainty and branch coverage",
        "Grounding gaps",
    ]
    for contract in required_contracts:
        assert contract in mode


def test_physics_prover_mode_keeps_statement_frozen_and_reports_redraft_needs():
    mode = PHYSICS_PROVER_MODE.read_text(encoding="utf-8")

    required_contracts = [
        "Fill `sorry` placeholders",
        "keep that contract fixed",
        "Do not rename declarations, change hypotheses, weaken conclusions",
        "If the statement is not provable",
        "keep the signature unchanged",
        "Redraft needed",
        "The declaration header is frozen",
        "You may edit only the proof body after `:= by`",
    ]
    for contract in required_contracts:
        assert contract in mode


def test_physics_reviewer_blocks_fake_statement_structures_and_missing_grounding():
    reviewer = PHYSICS_REVIEWER.read_text(encoding="utf-8")

    required_contracts = [
        "Goal-faithfulness / answer-as-assumption",
        "Assumption-target split",
        "Current target smuggled into hypotheses",
        "Official outputs covered",
        "Valid...Physics",
        "Satisfies...",
        "current target conclusion",
        "LeanExplore grounding evidence",
        "missing or incomplete LeanExplore grounding evidence",
        "Missing physical hypotheses",
        "arbitrary field",
        "governing-law premise",
        "local approximation",
        "global exact equality",
        "HasDerivAt",
        "HasFDerivAt",
        "IsLittleO",
        "IsBigO",
        "`∃ _, True`",
        "disconnected calculus claim",
        "derivability and abstraction sufficiency",
        "countermodel sanity check",
        "Uncertainty propagation",
        "Branch/orientation coverage",
        "Bridge obligations",
        "BLOCKED ON MODELING",
        "BLOCKED ON GROUNDING",
    ]
    for contract in required_contracts:
        assert contract in reviewer


def test_package_data_does_not_ship_copied_auto_formalizer():
    pyproject = PYPROJECT.read_text(encoding="utf-8")

    assert '"formalizer/**/*"' not in pyproject


def test_chemistry_answer_blind_policy_requires_raw_derivation_and_provenance():
    formalize = CHEMISTRY_FORMALIZE_MODE.read_text(encoding="utf-8")
    prover = CHEMISTRY_PROVER_MODE.read_text(encoding="utf-8")
    reviewer = CHEMISTRY_REVIEWER.read_text(encoding="utf-8")

    assert "The recorded answer may guide validation" not in formalize
    for phrase in [
        "evaluation_mode: answer_blind",
        "official answer",
        "without intermediate rounding",
        "width is mechanically",
        "candidate set",
        "underdetermination",
        "frozen proof",
        "blind_candidates/<entry.id>.json",
        "lean_blind_result_contract",
        "Do not try to calculate SHA-256",
    ]:
        assert phrase in formalize
    for phrase in [
        "evaluation_mode: answer_blind",
        "raw end-to-end calculation",
            "or add a finite",
            "underdetermination",
            "blind_candidates/<entry.id>.json",
    ]:
        assert phrase in prover
    for phrase in [
        "evaluation_mode: answer_blind",
        "raw, unrounded end-to-end derivation",
        "reporting/rounding rule",
        "candidate domain",
        "post-hoc tolerances",
    ]:
        assert phrase in reviewer
