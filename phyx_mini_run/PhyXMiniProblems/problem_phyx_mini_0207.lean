import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0207

open Dimension

/-!
# Spring constant of a carbon--oxygen bond from a symmetric CO₂ vibration

The supplied image shows a linear O--C--O molecule in two phases of its
symmetric stretching mode.  The two oxygen atoms move inward and outward in
opposite horizontal directions, while the central carbon atom has no motion
arrow.  Each C--O bond is modeled as a spring and each oxygen as a classical
simple harmonic oscillator.

Mass, ordinary frequency, and spring constant are unit-independent Physlib
quantities.  Real numbers occur below only as readouts in a coherent unit
system, including kilograms, hertz, and newtons per metre in SI.
-/

/-! ## Dimensionful physical quantities and their readouts -/

/-- A physical mass, such as the mass of one oxygen atom. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- An ordinary (cycles-per-time) frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-!
A spring constant has dimension force per length, equivalently mass per time
squared.  Its SI readout is therefore measured in newtons per metre.
-/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Scalar readout of a physical mass in a coherent choice of units. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  (mass units).val

/-- Scalar readout of an ordinary frequency in a coherent choice of units. -/
def frequencyReadout
    (units : UnitChoices) (frequency : FrequencyQuantity) : ℝ :=
  (frequency units).val

/-- Scalar readout of a spring constant in a coherent choice of units. -/
def springConstantReadout
    (units : UnitChoices) (springConstant : SpringConstantQuantity) : ℝ :=
  (springConstant units).val

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout UnitChoices.SI mass

/-- SI hertz readout of an ordinary frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout UnitChoices.SI frequency

/-- SI newton-per-metre readout of a spring constant. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  springConstantReadout UnitChoices.SI springConstant

/-! ## Labels and qualitative information read from the supplied image -/

/-- The three atom labels in their left-to-right order in the image. -/
inductive AtomLabel where
  | leftOxygen
  | carbon
  | rightOxygen
  deriving DecidableEq, Repr

/-- Chemical element represented by an atom label. -/
inductive AtomKind where
  | oxygen
  | carbon
  deriving DecidableEq, Repr

/-- The two carbon--oxygen bonds in the linear molecule. -/
inductive COBond where
  | left
  | right
  deriving DecidableEq, Repr

/-- The two depicted phases of the symmetric stretching oscillation. -/
inductive VibrationFrame where
  | inward
  | outward
  deriving DecidableEq, Repr

/-- Horizontal motion indicated by an arrow, or absence of translational motion. -/
inductive HorizontalMotion where
  | leftward
  | stationary
  | rightward
  deriving DecidableEq, Repr

/-- Qualitative molecular geometry shown by the diagram. -/
inductive MolecularArrangement where
  | linear
  | bent
  deriving DecidableEq, Repr

/-- The spring-like drawing used for each carbon--oxygen bond. -/
inductive BondDepiction where
  | coilSpring
  | rigidLink
  deriving DecidableEq, Repr

/-!
Raw labels, connectivity, and motion-arrow readouts from the supplied image.
No numerical mass, frequency, or spring constant is stored here.
-/
structure SymmetricStretchFigure where
  atomKind : AtomLabel → AtomKind
  arrangement : MolecularArrangement
  bondEndpoints : COBond → AtomLabel × AtomLabel
  bondDepiction : COBond → BondDepiction
  horizontalMotion : VibrationFrame → AtomLabel → HorizontalMotion

/-!
Primary-image evidence: a linear O--C--O molecule, two spring-like C--O
bonds, oxygen arrows directed inward in one frame and outward in the other,
and a stationary carbon in both frames.
-/
def MatchesSuppliedFigure (figure : SymmetricStretchFigure) : Prop :=
  figure.atomKind .leftOxygen = .oxygen ∧
    figure.atomKind .carbon = .carbon ∧
    figure.atomKind .rightOxygen = .oxygen ∧
    figure.arrangement = .linear ∧
    figure.bondEndpoints .left = (.leftOxygen, .carbon) ∧
    figure.bondEndpoints .right = (.carbon, .rightOxygen) ∧
    figure.bondDepiction .left = .coilSpring ∧
    figure.bondDepiction .right = .coilSpring ∧
    figure.horizontalMotion .inward .leftOxygen = .rightward ∧
    figure.horizontalMotion .inward .carbon = .stationary ∧
    figure.horizontalMotion .inward .rightOxygen = .leftward ∧
    figure.horizontalMotion .outward .leftOxygen = .leftward ∧
    figure.horizontalMotion .outward .carbon = .stationary ∧
    figure.horizontalMotion .outward .rightOxygen = .rightward

/-- The oxygen atom attached to each of the two C--O bonds. -/
def oxygenAtomForBond : COBond → AtomLabel
  | .left => .leftOxygen
  | .right => .rightOxygen

/-! ## Physical setup, measured data, and governing laws -/

/-!
The physical quantities for the symmetric-stretch experiment.  The spring
constants remain unknown.  `oscillatorSIReadout` uses Physlib's classical
harmonic-oscillator structure to package the positive SI mass and spring
constant readouts for each oxygen--bond pair.
-/
structure CO2SymmetricStretchSetup where
  figure : SymmetricStretchFigure
  atomicMassUnit : MassQuantity
  oxygenMass : COBond → MassQuantity
  observedFrequency : FrequencyQuantity
  bondSpringConstant : COBond → SpringConstantQuantity
  oscillatorSIReadout : COBond → ClassicalMechanics.HarmonicOscillator

/-!
The frequency stated in the problem.  It is the common ordinary frequency of
the symmetric mode, measured in hertz.  The diagram and oscillator laws are
kept in separate predicates.
-/
def MatchesProblemStatement (setup : CO2SymmetricStretchSetup) : Prop :=
  frequencyInHertz setup.observedFrequency = 2.83 * 10 ^ 13

/-!
Standard atomic-mass data needed for the numerical calculation: one atomic
mass unit is approximated as `1.66 × 10⁻²⁷ kg`, and an oxygen atom has mass
`16 u`.  The latter equality is required in every coherent unit system.
-/
structure MatchesOxygenAtomicMassData
    (setup : CO2SymmetricStretchSetup) : Prop where
  atomicMassUnitInKilograms :
    massInKilograms setup.atomicMassUnit = 1.66 / 10 ^ 27
  oxygenMassIsSixteenAtomicMassUnits :
    ∀ bond units,
      massReadout units (setup.oxygenMass bond) =
        16 * massReadout units setup.atomicMassUnit

/-- Positivity conditions for the measured physical quantities. -/
structure HasPhysicalParameters
    (setup : CO2SymmetricStretchSetup) : Prop where
  atomicMassUnitPositive : 0 < massInKilograms setup.atomicMassUnit
  oxygenMassPositive :
    ∀ bond, 0 < massInKilograms (setup.oxygenMass bond)
  observedFrequencyPositive : 0 < frequencyInHertz setup.observedFrequency
  bondSpringConstantPositive :
    ∀ bond,
      0 < springConstantInNewtonsPerMeter (setup.bondSpringConstant bond)

/-!
The governing simple-harmonic-oscillator model.  For each bond, the mass and
spring constant in Physlib's `HarmonicOscillator` are precisely the SI
readouts of the dimensionful quantities.  The angular frequency `ω` of that
oscillator is related to the observed ordinary frequency by `ω = 2πf`.

These are general physical laws and readout bridges.  They do not mention a
numerical spring-constant answer or an answer-choice label.
-/
structure SatisfiesIndependentOxygenOscillatorModel
    (setup : CO2SymmetricStretchSetup) : Prop where
  oscillatorMassIsOxygenMass :
    ∀ bond,
      (setup.oscillatorSIReadout bond).m =
        massInKilograms (setup.oxygenMass bond)
  oscillatorSpringConstantIsBondReadout :
    ∀ bond,
      (setup.oscillatorSIReadout bond).k =
        springConstantInNewtonsPerMeter (setup.bondSpringConstant bond)
  angularFrequencyFromOrdinaryFrequency :
    ∀ bond,
      (setup.oscillatorSIReadout bond).ω =
        2 * Real.pi * frequencyInHertz setup.observedFrequency

/-!
Physlib's theorem `ClassicalMechanics.HarmonicOscillator.ω_sq` implies the
usual readout relation `k = m (2πf)²` after applying the three bridges above.
This is a generic consequence of the governing model, before any numerical
oxygen-mass or frequency data are substituted.
-/
lemma bondSpringConstant_eq_mass_mul_angularFrequency_sq
    (setup : CO2SymmetricStretchSetup)
    (hModel : SatisfiesIndependentOxygenOscillatorModel setup)
    (bond : COBond) :
    springConstantInNewtonsPerMeter (setup.bondSpringConstant bond) =
      massInKilograms (setup.oxygenMass bond) *
        (2 * Real.pi * frequencyInHertz setup.observedFrequency) ^ 2 := by
  rw [← hModel.oscillatorSpringConstantIsBondReadout bond,
    ← hModel.oscillatorMassIsOxygenMass bond,
    ← hModel.angularFrequencyFromOrdinaryFrequency bond]
  have hω := (setup.oscillatorSIReadout bond).ω_sq
  field_simp [(setup.oscillatorSIReadout bond).m_ne_zero] at hω
  nlinarith [hω]

/-! ## Displayed answer choices and final target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Spring-constant value displayed by each choice, in newtons per metre. -/
def displayedSpringConstantInNewtonsPerMeter : AnswerChoice → ℝ
  | .A => 760
  | .B => 800
  | .C => 880
  | .D => 840

/-!
The computed spring constant rounds to a displayed whole-newton-per-metre
answer.  The half-unit tolerance is independent of which choice is supplied.
-/
def MatchesAnswerToNearestNewtonPerMeter
    (setup : CO2SymmetricStretchSetup)
    (bond : COBond)
    (choice : AnswerChoice) : Prop :=
  |springConstantInNewtonsPerMeter (setup.bondSpringConstant bond) -
      displayedSpringConstantInNewtonsPerMeter choice| ≤ (1 / 2 : ℝ)

/-- The selected displayed value is strictly closer than every other choice. -/
def IsUniqueClosestDisplayedChoice
    (setup : CO2SymmetricStretchSetup)
    (bond : COBond)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |springConstantInNewtonsPerMeter (setup.bondSpringConstant bond) -
        displayedSpringConstantInNewtonsPerMeter choice| <
      |springConstantInNewtonsPerMeter (setup.bondSpringConstant bond) -
        displayedSpringConstantInNewtonsPerMeter other|

/-!
For the symmetric CO₂ stretch, the SHO relation with `m_O = 16 u`,
`u = 1.66 × 10⁻²⁷ kg`, and `f = 2.83 × 10¹³ Hz` gives approximately
`839.77 N/m`.  Thus each identical C--O bond rounds to `840 N/m`, and answer D
is uniquely closest among the four displayed choices.

This formalizes blueprint label `thm:physics:phyx_mini_0207:target`.  Neither
`840 N/m`, answer D, nor a problem-specific spring-constant interval appears
in any premise, setup field, or governing-law field.
-/
theorem problem_phyx_mini_0207
    (setup : CO2SymmetricStretchSetup)
    (hStatement : MatchesProblemStatement setup)
    (hFigure : MatchesSuppliedFigure setup.figure)
    (hMassData : MatchesOxygenAtomicMassData setup)
    (hPhysical : HasPhysicalParameters setup)
    (hModel : SatisfiesIndependentOxygenOscillatorModel setup) :
    ∀ bond : COBond,
      MatchesAnswerToNearestNewtonPerMeter setup bond .D ∧
        IsUniqueClosestDisplayedChoice setup bond .D := by
  intro bond
  have hOxygenMass :
      massInKilograms (setup.oxygenMass bond) = 16 * (1.66 / 10 ^ 27) := by
    calc
      _ = 16 * massInKilograms setup.atomicMassUnit :=
        hMassData.oxygenMassIsSixteenAtomicMassUnits bond UnitChoices.SI
      _ = 16 * (1.66 / 10 ^ 27) := by
        rw [hMassData.atomicMassUnitInKilograms]
  have hSpring :=
    bondSpringConstant_eq_mass_mul_angularFrequency_sq setup hModel bond
  rw [hOxygenMass, hStatement] at hSpring
  ring_nf at hSpring
  have hPiSqLower : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr Real.pi_gt_d4)
      (by nlinarith [Real.pi_gt_d4] : 0 < Real.pi + 3.1415)]
  have hPiSqUpper : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr Real.pi_lt_d4)
      (by nlinarith [Real.pi_pos] : 0 < 3.1416 + Real.pi)]
  have hLower : (839.5 : ℝ) < springConstantInNewtonsPerMeter
      (setup.bondSpringConstant bond) := by
    rw [hSpring]
    nlinarith
  have hUpper : springConstantInNewtonsPerMeter
      (setup.bondSpringConstant bond) < (840.5 : ℝ) := by
    rw [hSpring]
    nlinarith
  have hNearest : MatchesAnswerToNearestNewtonPerMeter setup bond .D := by
    unfold MatchesAnswerToNearestNewtonPerMeter
    change |springConstantInNewtonsPerMeter
      (setup.bondSpringConstant bond) - 840| ≤ (1 / 2 : ℝ)
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨hNearest, ?_⟩
  unfold IsUniqueClosestDisplayedChoice
  intro other hOther
  have hSelectedDistance :
      |springConstantInNewtonsPerMeter
        (setup.bondSpringConstant bond) - 840| ≤ (1 / 2 : ℝ) := by
    simpa [MatchesAnswerToNearestNewtonPerMeter,
      displayedSpringConstantInNewtonsPerMeter] using hNearest
  cases other with
  | A =>
      change |springConstantInNewtonsPerMeter
        (setup.bondSpringConstant bond) - 840| <
        |springConstantInNewtonsPerMeter
          (setup.bondSpringConstant bond) - 760|
      rw [abs_of_nonneg (show 0 ≤ springConstantInNewtonsPerMeter
        (setup.bondSpringConstant bond) - 760 by linarith)]
      linarith
  | B =>
      change |springConstantInNewtonsPerMeter
        (setup.bondSpringConstant bond) - 840| <
        |springConstantInNewtonsPerMeter
          (setup.bondSpringConstant bond) - 800|
      rw [abs_of_nonneg (show 0 ≤ springConstantInNewtonsPerMeter
        (setup.bondSpringConstant bond) - 800 by linarith)]
      linarith
  | C =>
      change |springConstantInNewtonsPerMeter
        (setup.bondSpringConstant bond) - 840| <
        |springConstantInNewtonsPerMeter
          (setup.bondSpringConstant bond) - 880|
      rw [abs_of_nonpos (show springConstantInNewtonsPerMeter
        (setup.bondSpringConstant bond) - 880 ≤ 0 by linarith)]
      linarith
  | D =>
      exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0207
