import Mathlib
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0517

open Dimension

/-!
# Highest-frequency spectral line of a three-level atom

The supplied energy-level diagram has levels at `0 eV`, `1 eV`, and `3 eV`.
It shows three downward emission arrows, with energy gaps `1 eV`, `2 eV`, and
`3 eV`, as well as two upward absorption arrows.

Energies, photon frequencies, and Planck's constant are represented as
dimensionful physical quantities.  Real numbers are used only for calibrated
unit readouts and displayed answer values.  In particular, an emitted
frequency is an independent observable related to a level gap by the
Planck--Einstein law; it is not defined to be the recorded answer.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- The physical dimension of action, equivalently energy times time. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical value of action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- A nonnegative, unit-independent ordinary frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Coherent-SI readout of an energy, in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Energy readout in electron volts, grounded by `DimEnergy.electronVolt`. -/
def energyInElectronVolts (energy : DimEnergy) : ℝ :=
  energyInJoules energy / energyInJoules DimEnergy.electronVolt

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of an ordinary frequency, in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-! ## Energy-level and transition labels from the primary figure -/

/-- The three horizontal atomic energy levels in the diagram. -/
inductive AtomicEnergyLevel where
  | ground
  | oneElectronVolt
  | threeElectronVolts
  deriving DecidableEq, Fintype, Repr

/-- The three downward arrows in the emission part of the diagram. -/
inductive EmissionTransition where
  | threeToOne
  | threeToGround
  | oneToGround
  deriving DecidableEq, Fintype, Repr

/-- Initial level of each labeled emission transition. -/
def EmissionTransition.initialLevel : EmissionTransition → AtomicEnergyLevel
  | .threeToOne => .threeElectronVolts
  | .threeToGround => .threeElectronVolts
  | .oneToGround => .oneElectronVolt

/-- Final level of each labeled emission transition. -/
def EmissionTransition.finalLevel : EmissionTransition → AtomicEnergyLevel
  | .threeToOne => .oneElectronVolt
  | .threeToGround => .ground
  | .oneToGround => .ground

/-- The two upward arrows in the absorption part of the diagram. -/
inductive AbsorptionTransition where
  | groundToOne
  | groundToThree
  deriving DecidableEq, Fintype, Repr

/-- Initial level of each labeled absorption transition. -/
def AbsorptionTransition.initialLevel :
    AbsorptionTransition → AtomicEnergyLevel
  | .groundToOne => .ground
  | .groundToThree => .ground

/-- Final level of each labeled absorption transition. -/
def AbsorptionTransition.finalLevel :
    AbsorptionTransition → AtomicEnergyLevel
  | .groundToOne => .oneElectronVolt
  | .groundToThree => .threeElectronVolts

/-- Vertical orientation of a transition arrow in the supplied diagram. -/
inductive ArrowDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The two arrow colors which distinguish absorption from emission. -/
inductive ArrowColor where
  | blue
  | pink
  deriving DecidableEq, Repr

/-!
Raster-visible diagram data.  Its scalar labels are electron-volt readouts,
not replacement types for the physical level energies stored in the setup.
-/
structure AtomicEnergyLevelDiagram where
  levelIsShown : AtomicEnergyLevel → Bool
  levelIsHorizontal : AtomicEnergyLevel → Bool
  levelLabelElectronVolts : AtomicEnergyLevel → ℝ
  emissionArrowIsShown : EmissionTransition → Bool
  emissionArrowDirection : EmissionTransition → ArrowDirection
  emissionArrowColor : EmissionTransition → ArrowColor
  emissionGapLabelElectronVolts : EmissionTransition → ℝ
  absorptionArrowIsShown : AbsorptionTransition → Bool
  absorptionArrowDirection : AbsorptionTransition → ArrowDirection
  absorptionArrowColor : AbsorptionTransition → ArrowColor
  absorptionGapLabelElectronVolts : AbsorptionTransition → ℝ
  emissionSectionLabelPresent : Bool
  absorptionSectionLabelPresent : Bool

/-! ## Atom setup, source data, and governing physics -/

/-- The preparation state specified by the words "when excited". -/
inductive AtomPreparation where
  | groundState
  | excited
  deriving DecidableEq, Repr

/-!
The physical atom and its emitted spectral lines.  Each line frequency is a
dimensionful observable.  The governing-law premise below, rather than a
definition here, relates it to the appropriate energy-level difference.
-/
structure ThreeLevelAtomSetup where
  levelEnergy : AtomicEnergyLevel → DimEnergy
  emittedPhotonFrequency : EmissionTransition → FrequencyQuantity
  planckConstant : ActionQuantity
  preparation : AtomPreparation
  diagram : AtomicEnergyLevelDiagram

/-- The atom is in the excited preparation contemplated by the question. -/
structure MatchesExcitedAtomScenario (setup : ThreeLevelAtomSetup) : Prop where
  atomIsExcited : setup.preparation = .excited

/-!
Numerical energy-level data and every visible feature of image 517.  These are
source/figure readouts only: no emitted frequency, maximum line, or answer
choice occurs in this premise.
-/
structure MatchesSuppliedEnergyLevelDiagram
    (setup : ThreeLevelAtomSetup) : Prop where
  groundEnergyElectronVolts :
    energyInElectronVolts (setup.levelEnergy .ground) = 0
  oneLevelEnergyElectronVolts :
    energyInElectronVolts (setup.levelEnergy .oneElectronVolt) = 1
  threeLevelEnergyElectronVolts :
    energyInElectronVolts (setup.levelEnergy .threeElectronVolts) = 3
  everyLevelShown : ∀ level, setup.diagram.levelIsShown level = true
  everyLevelHorizontal :
    ∀ level, setup.diagram.levelIsHorizontal level = true
  groundLevelLabel : setup.diagram.levelLabelElectronVolts .ground = 0
  oneLevelLabel :
    setup.diagram.levelLabelElectronVolts .oneElectronVolt = 1
  threeLevelLabel :
    setup.diagram.levelLabelElectronVolts .threeElectronVolts = 3
  everyEmissionArrowShown :
    ∀ transition, setup.diagram.emissionArrowIsShown transition = true
  emissionArrowsPointDownward :
    ∀ transition,
      setup.diagram.emissionArrowDirection transition = .downward
  emissionArrowsArePink :
    ∀ transition, setup.diagram.emissionArrowColor transition = .pink
  threeToOneGapLabel :
    setup.diagram.emissionGapLabelElectronVolts .threeToOne = 2
  threeToGroundGapLabel :
    setup.diagram.emissionGapLabelElectronVolts .threeToGround = 3
  oneToGroundGapLabel :
    setup.diagram.emissionGapLabelElectronVolts .oneToGround = 1
  everyAbsorptionArrowShown :
    ∀ transition, setup.diagram.absorptionArrowIsShown transition = true
  absorptionArrowsPointUpward :
    ∀ transition,
      setup.diagram.absorptionArrowDirection transition = .upward
  absorptionArrowsAreBlue :
    ∀ transition, setup.diagram.absorptionArrowColor transition = .blue
  groundToOneGapLabel :
    setup.diagram.absorptionGapLabelElectronVolts .groundToOne = 1
  groundToThreeGapLabel :
    setup.diagram.absorptionGapLabelElectronVolts .groundToThree = 3
  emissionSectionLabel : setup.diagram.emissionSectionLabelPresent = true
  absorptionSectionLabel : setup.diagram.absorptionSectionLabelPresent = true

/-- Positivity and strict level ordering for the physical branch of the model. -/
structure HasPhysicalSpectralParameters (setup : ThreeLevelAtomSetup) : Prop where
  planckConstantPositive : 0 < actionInJouleSeconds setup.planckConstant
  emittedFrequenciesPositive :
    ∀ transition, 0 < frequencyInHertz (setup.emittedPhotonFrequency transition)
  groundBelowOne :
    energyInJoules (setup.levelEnergy .ground) <
      energyInJoules (setup.levelEnergy .oneElectronVolt)
  oneBelowThree :
    energyInJoules (setup.levelEnergy .oneElectronVolt) <
      energyInJoules (setup.levelEnergy .threeElectronVolts)

/-!
Physlib supplies the reduced Planck constant `Constants.ℏ` in SI
joule-seconds.  Ordinary Planck's constant is `2πℏ`.  This reference datum
contains no line frequency or answer-choice value.
-/
structure UsesStandardPlanckConstant (setup : ThreeLevelAtomSetup) : Prop where
  planckConstantJouleSeconds :
    actionInJouleSeconds setup.planckConstant =
      2 * Real.pi * (Constants.ℏ : ℝ)

/-!
Planck--Einstein emission law `E_initial - E_final = h ν` for every arrow.
It is a general relation between the independent physical quantities and does
not specialize any frequency to the requested maximum or displayed answer.
-/
structure SatisfiesPlanckEinsteinEmissionLaw
    (setup : ThreeLevelAtomSetup) : Prop where
  photonEnergyFromLevelGap : ∀ transition : EmissionTransition,
    energyInJoules (setup.levelEnergy transition.initialLevel) -
        energyInJoules (setup.levelEnergy transition.finalLevel) =
      actionInJouleSeconds setup.planckConstant *
        frequencyInHertz (setup.emittedPhotonFrequency transition)

/-! ## Derived relations and answer semantics -/

/-- Energy released by an emission transition, read in joules. -/
def emissionEnergyGapInJoules
    (setup : ThreeLevelAtomSetup) (transition : EmissionTransition) : ℝ :=
  energyInJoules (setup.levelEnergy transition.initialLevel) -
    energyInJoules (setup.levelEnergy transition.finalLevel)

/-- The direct `3 eV → 0 eV` arrow has the unique largest energy gap. -/
lemma threeToGround_has_unique_largest_energyGap
    (setup : ThreeLevelAtomSetup)
    (_data : MatchesSuppliedEnergyLevelDiagram setup) :
    ∀ other, other ≠ EmissionTransition.threeToGround →
      emissionEnergyGapInJoules setup other <
        emissionEnergyGapInJoules setup .threeToGround := by
  have heV_pos : 0 < energyInJoules DimEnergy.electronVolt := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, NNReal.coe_ofScientific]
  have hground := _data.groundEnergyElectronVolts
  have hone := _data.oneLevelEnergyElectronVolts
  have hthree := _data.threeLevelEnergyElectronVolts
  simp only [energyInElectronVolts] at hground hone hthree
  field_simp [ne_of_gt heV_pos] at hground hone hthree
  intro other hother
  cases other with
  | threeToOne =>
      simp only [emissionEnergyGapInJoules, EmissionTransition.initialLevel,
        EmissionTransition.finalLevel]
      linarith
  | threeToGround =>
      exact (hother rfl).elim
  | oneToGround =>
      simp only [emissionEnergyGapInJoules, EmissionTransition.initialLevel,
        EmissionTransition.finalLevel]
      linarith

/-- A labeled line has strictly greater frequency than every other line. -/
def IsUniqueHighestEmissionTransition
    (setup : ThreeLevelAtomSetup) (transition : EmissionTransition) : Prop :=
  ∀ other, other ≠ transition →
    frequencyInHertz (setup.emittedPhotonFrequency other) <
      frequencyInHertz (setup.emittedPhotonFrequency transition)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Frequency printed beside an answer choice, in hertz. -/
def AnswerChoice.frequencyHertz : AnswerChoice → ℝ
  | .A => 9.16 * 10 ^ (14 : ℕ)
  | .B => 2.42 * 10 ^ (14 : ℕ)
  | .C => 5.50 * 10 ^ (14 : ℕ)
  | .D => 7.25 * 10 ^ (14 : ℕ)

/-- Dataset metadata recording answer D; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Absolute error between an emitted line and a displayed answer, in hertz. -/
def answerChoiceErrorHertz
    (setup : ThreeLevelAtomSetup)
    (transition : EmissionTransition)
    (choice : AnswerChoice) : ℝ :=
  |frequencyInHertz (setup.emittedPhotonFrequency transition) -
    choice.frequencyHertz|

/-!
Agreement after rounding the coefficient to the displayed hundredth in units
of `10^14 Hz`; half of one display unit is `5 × 10^11 Hz`.
-/
def AgreesWithDisplayedFrequency
    (setup : ThreeLevelAtomSetup)
    (transition : EmissionTransition)
    (choice : AnswerChoice) : Prop :=
  answerChoiceErrorHertz setup transition choice < 5 * 10 ^ (11 : ℕ)

/-- The named answer is strictly closer than every other displayed frequency. -/
def IsUniqueClosestAnswerChoice
    (setup : ThreeLevelAtomSetup)
    (transition : EmissionTransition)
    (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorHertz setup transition choice <
      answerChoiceErrorHertz setup transition other

/-!
For the three depicted levels, the largest drop is the direct `3 eV → 0 eV`
transition.  The Planck--Einstein law gives approximately
`7.25 × 10^14 Hz`, so the highest spectral line agrees with and uniquely
selects choice D.

Blueprint: `thm:physics:phyx_mini_0517:target`.
-/
theorem highestEmittedSpectralLine_is_choiceD
    (setup : ThreeLevelAtomSetup)
    (_scenario : MatchesExcitedAtomScenario setup)
    (_data : MatchesSuppliedEnergyLevelDiagram setup)
    (_physical : HasPhysicalSpectralParameters setup)
    (_planck : UsesStandardPlanckConstant setup)
    (_law : SatisfiesPlanckEinsteinEmissionLaw setup) :
    IsUniqueHighestEmissionTransition setup .threeToGround ∧
      AgreesWithDisplayedFrequency setup .threeToGround .D ∧
      IsUniqueClosestAnswerChoice setup .threeToGround .D := by
  have heV_pos : 0 < energyInJoules DimEnergy.electronVolt := by
    norm_num [energyInJoules, DimEnergy.electronVolt,
      CarriesDimension.toDimensionful_apply_apply, NNReal.coe_ofScientific]
  have hground := _data.groundEnergyElectronVolts
  have hthree := _data.threeLevelEnergyElectronVolts
  simp only [energyInElectronVolts] at hground hthree
  field_simp [ne_of_gt heV_pos] at hground hthree
  have hfrequencyEquation :=
    _law.photonEnergyFromLevelGap EmissionTransition.threeToGround
  simp only [EmissionTransition.initialLevel, EmissionTransition.finalLevel] at hfrequencyEquation
  rw [hthree, hground, _planck.planckConstantJouleSeconds] at hfrequencyEquation
  norm_num [energyInJoules, DimEnergy.electronVolt,
    CarriesDimension.toDimensionful_apply_apply, NNReal.coe_ofScientific,
    Constants.ℏ] at hfrequencyEquation
  have hfrequencyPositive :=
    _physical.emittedFrequenciesPositive EmissionTransition.threeToGround
  have hfrequencyLower :
      7.25 * 10 ^ (14 : ℕ) - 5 * 10 ^ (11 : ℕ) <
        frequencyInHertz
          (setup.emittedPhotonFrequency EmissionTransition.threeToGround) := by
    by_contra h
    have hfrequencyLe :
        frequencyInHertz
            (setup.emittedPhotonFrequency EmissionTransition.threeToGround) ≤
          7.25 * 10 ^ (14 : ℕ) - 5 * 10 ^ (11 : ℕ) :=
      le_of_not_gt h
    have hproductUpper :
        Real.pi *
            frequencyInHertz
              (setup.emittedPhotonFrequency EmissionTransition.threeToGround) <
          3.1416 *
            (7.25 * 10 ^ (14 : ℕ) - 5 * 10 ^ (11 : ℕ)) := by
      calc
        Real.pi *
              frequencyInHertz
                (setup.emittedPhotonFrequency EmissionTransition.threeToGround) <
            3.1416 *
              frequencyInHertz
                (setup.emittedPhotonFrequency EmissionTransition.threeToGround) :=
          mul_lt_mul_of_pos_right Real.pi_lt_d4 hfrequencyPositive
        _ ≤ 3.1416 *
              (7.25 * 10 ^ (14 : ℕ) - 5 * 10 ^ (11 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hfrequencyLe (by norm_num)
    nlinarith
  have hfrequencyUpper :
      frequencyInHertz
          (setup.emittedPhotonFrequency EmissionTransition.threeToGround) <
        7.25 * 10 ^ (14 : ℕ) + 5 * 10 ^ (11 : ℕ) := by
    by_contra h
    have hfrequencyGe :
        7.25 * 10 ^ (14 : ℕ) + 5 * 10 ^ (11 : ℕ) ≤
          frequencyInHertz
            (setup.emittedPhotonFrequency EmissionTransition.threeToGround) :=
      le_of_not_gt h
    have hproductLower :
        3.1415 *
            (7.25 * 10 ^ (14 : ℕ) + 5 * 10 ^ (11 : ℕ)) <
          Real.pi *
            frequencyInHertz
              (setup.emittedPhotonFrequency EmissionTransition.threeToGround) := by
      calc
        3.1415 *
              (7.25 * 10 ^ (14 : ℕ) + 5 * 10 ^ (11 : ℕ)) <
            Real.pi *
              (7.25 * 10 ^ (14 : ℕ) + 5 * 10 ^ (11 : ℕ)) :=
          mul_lt_mul_of_pos_right Real.pi_gt_d4 (by norm_num)
        _ ≤ Real.pi *
              frequencyInHertz
                (setup.emittedPhotonFrequency EmissionTransition.threeToGround) := by
          exact mul_le_mul_of_nonneg_left hfrequencyGe Real.pi_pos.le
    nlinarith
  have hchoiceDError :
      answerChoiceErrorHertz setup EmissionTransition.threeToGround .D <
        5 * 10 ^ (11 : ℕ) := by
    simp only [answerChoiceErrorHertz, AnswerChoice.frequencyHertz]
    rw [abs_lt]
    constructor <;> nlinarith
  constructor
  · intro other hother
    have hgap :=
      threeToGround_has_unique_largest_energyGap setup _data other hother
    have hotherLaw := _law.photonEnergyFromLevelGap other
    have hmaxLaw :=
      _law.photonEnergyFromLevelGap EmissionTransition.threeToGround
    simp only [emissionEnergyGapInJoules] at hgap
    rw [hotherLaw, hmaxLaw] at hgap
    nlinarith [_physical.planckConstantPositive]
  · constructor
    · exact hchoiceDError
    · intro other hother
      cases other with
      | A =>
          calc
            answerChoiceErrorHertz setup .threeToGround .D <
                5 * 10 ^ (11 : ℕ) := hchoiceDError
            _ < answerChoiceErrorHertz setup .threeToGround .A := by
              simp only [answerChoiceErrorHertz, AnswerChoice.frequencyHertz]
              rw [abs_of_nonpos]
              · nlinarith
              · nlinarith
      | B =>
          calc
            answerChoiceErrorHertz setup .threeToGround .D <
                5 * 10 ^ (11 : ℕ) := hchoiceDError
            _ < answerChoiceErrorHertz setup .threeToGround .B := by
              simp only [answerChoiceErrorHertz, AnswerChoice.frequencyHertz]
              rw [abs_of_nonneg]
              · nlinarith
              · nlinarith
      | C =>
          calc
            answerChoiceErrorHertz setup .threeToGround .D <
                5 * 10 ^ (11 : ℕ) := hchoiceDError
            _ < answerChoiceErrorHertz setup .threeToGround .C := by
              simp only [answerChoiceErrorHertz, AnswerChoice.frequencyHertz]
              rw [abs_of_nonneg]
              · nlinarith
              · nlinarith
      | D =>
          exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0517
