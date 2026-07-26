import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/-!
# Oscillation frequency of a block attached to two springs

A block of mass `m` moves horizontally on a frictionless floor between two
wall-mounted springs.  With the left spring removed (so only the right spring
acts), its frequency is `30 Hz`; with the right spring removed, its frequency
is `45 Hz`.  The requested quantity is its frequency with both springs acting.

Mass, spring stiffness, and cyclic frequency are represented by Physlib
dimensionful quantities.  Physlib's scalar `HarmonicOscillator` models are
linked explicitly to their coherent SI readouts by the governing-law
interface below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0252

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/--
A nonnegative linear spring stiffness, with SI unit newtons per metre and
dimension mass per time squared.
-/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative cyclic frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical mass in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a spring stiffness in SI newtons per metre. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-- Read a cyclic frequency in hertz, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-! ## Apparatus and primary-figure labels -/

/-- The two sides of the block distinguished in the supplied figure. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The sole mathematical label printed on the block in the figure. -/
inductive FigureLabel where
  | blockMass_m
  deriving DecidableEq, Repr

/-- The horizontal direction of the block's allowed displacement. -/
inductive MotionAxis where
  | horizontal
  deriving DecidableEq, Repr

/-- The idealized contact condition specified by the problem statement. -/
inductive FloorCondition where
  | frictionless
  deriving DecidableEq, Repr

/--
Qualitative geometry read from the primary image.  `springGlyphsMatchInStyle`
records only the springs' matching schematic appearance; it does not assert
that their physical stiffnesses are equal, which would conflict with the two
different one-spring frequencies.
-/
structure TwoSpringFigure where
  displayedBlockLabel : FigureLabel
  springShownAt : FigureSide → Bool
  springWallAnchoredAt : FigureSide → Bool
  blockDrawnBetweenSprings : Bool
  springsAppearRelaxed : Bool
  springGlyphsMatchInStyle : Bool

/-!
The dimensionful apparatus data and the three oscillator configurations.

The `bothSpringsFrequency` is an independent unknown rather than a definition
of the requested answer.  The scalar Physlib oscillator fields are likewise
independent here and are connected to the dimensionful apparatus only by the
general laws below.
-/
structure TwoSpringBlockSetup where
  blockMass : MassQuantity
  leftSpringStiffness : SpringStiffnessQuantity
  rightSpringStiffness : SpringStiffnessQuantity
  rightOnlyFrequency : FrequencyQuantity
  leftOnlyFrequency : FrequencyQuantity
  bothSpringsFrequency : FrequencyQuantity
  rightOnlyOscillator : ClassicalMechanics.HarmonicOscillator
  leftOnlyOscillator : ClassicalMechanics.HarmonicOscillator
  bothSpringsOscillator : ClassicalMechanics.HarmonicOscillator
  motionAxis : MotionAxis
  floorCondition : FloorCondition
  figure : TwoSpringFigure

/-!
Problem-text calibrations and qualitative evidence from the supplied image.
Removing the left spring leaves the right-only configuration at `30 Hz`, and
removing the right spring leaves the left-only configuration at `45 Hz`.
Nothing here specifies the frequency with both springs attached.
-/
structure MatchesProblemAndFigure (setup : TwoSpringBlockSetup) : Prop where
  leftSpringRemovedFrequency :
    frequencyInHertz setup.rightOnlyFrequency = 30
  rightSpringRemovedFrequency :
    frequencyInHertz setup.leftOnlyFrequency = 45
  horizontalMotion : setup.motionAxis = .horizontal
  floorIsFrictionless : setup.floorCondition = .frictionless
  figureBlockLabel : setup.figure.displayedBlockLabel = .blockMass_m
  figureShowsBothSprings :
    ∀ side : FigureSide, setup.figure.springShownAt side = true
  figureShowsBothWallAnchors :
    ∀ side : FigureSide, setup.figure.springWallAnchoredAt side = true
  figurePlacesBlockBetweenSprings :
    setup.figure.blockDrawnBetweenSprings = true
  figureShowsRelaxedSprings : setup.figure.springsAppearRelaxed = true
  figureUsesMatchingSpringGlyphs :
    setup.figure.springGlyphsMatchInStyle = true

/-- Positivity of the physical mass and the two spring stiffnesses. -/
structure HasPhysicalParameters (setup : TwoSpringBlockSetup) : Prop where
  blockMassPositive : 0 < massInKilograms setup.blockMass
  leftSpringStiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.leftSpringStiffness
  rightSpringStiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.rightSpringStiffness

/-!
## Governing small-oscillation laws

All three configurations contain the same block.  A one-spring configuration
has the stiffness of its remaining spring, while a horizontal displacement
with both springs attached produces restoring forces in the same direction,
so the effective stiffness is `k_left + k_right`.  Physlib supplies
`HarmonicOscillator.ω = sqrt (k / m)`; the final three fields relate that
angular frequency to the physical cyclic frequency by `ω = 2 π f`.

These are general governing relations.  They include no numerical value or
answer-choice assertion for the both-springs frequency.
-/
structure SatisfiesLinearTwoSpringOscillatorModel
    (setup : TwoSpringBlockSetup) : Prop where
  rightOnlyUsesSameBlock :
    setup.rightOnlyOscillator.m = massInKilograms setup.blockMass
  leftOnlyUsesSameBlock :
    setup.leftOnlyOscillator.m = massInKilograms setup.blockMass
  bothSpringsUsesSameBlock :
    setup.bothSpringsOscillator.m = massInKilograms setup.blockMass
  rightOnlyEffectiveStiffness :
    setup.rightOnlyOscillator.k =
      stiffnessInNewtonsPerMeter setup.rightSpringStiffness
  leftOnlyEffectiveStiffness :
    setup.leftOnlyOscillator.k =
      stiffnessInNewtonsPerMeter setup.leftSpringStiffness
  bothSpringsEffectiveStiffness :
    setup.bothSpringsOscillator.k =
      stiffnessInNewtonsPerMeter setup.leftSpringStiffness +
        stiffnessInNewtonsPerMeter setup.rightSpringStiffness
  rightOnlyCyclicToAngularFrequency :
    2 * Real.pi * frequencyInHertz setup.rightOnlyFrequency =
      setup.rightOnlyOscillator.ω
  leftOnlyCyclicToAngularFrequency :
    2 * Real.pi * frequencyInHertz setup.leftOnlyFrequency =
      setup.leftOnlyOscillator.ω
  bothSpringsCyclicToAngularFrequency :
    2 * Real.pi * frequencyInHertz setup.bothSpringsFrequency =
      setup.bothSpringsOscillator.ω

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each answer label. -/
def AnswerChoice.hertz : AnswerChoice → ℝ
  | .A => 48
  | .B => 51
  | .C => 54
  | .D => 57

/--
A whole-hertz answer agrees with the physical frequency when it is within
half a hertz, corresponding to rounding to the nearest displayed integer.
-/
def MatchesAnswerChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ (1 : ℝ) / 2

/-!
The frequency contributions add in quadrature:

`f_both = sqrt (30^2 + 45^2) = 15 sqrt 13 Hz`.

This is approximately `54.08 Hz`, so the nearest displayed whole-hertz answer
is C, `54 Hz`.  This formalizes
`thm:physics:phyx_mini_0252:target`.
-/
theorem bothSpringsFrequency_exact_and_matches_choiceC
    (setup : TwoSpringBlockSetup)
    (_problemAndFigure : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_model : SatisfiesLinearTwoSpringOscillatorModel setup) :
    frequencyInHertz setup.bothSpringsFrequency =
        Real.sqrt ((30 : ℝ) ^ 2 + (45 : ℝ) ^ 2) ∧
      MatchesAnswerChoice setup.bothSpringsFrequency .C := by
  have h_omega_sq_add :
      setup.bothSpringsOscillator.ω ^ 2 =
        setup.leftOnlyOscillator.ω ^ 2 +
          setup.rightOnlyOscillator.ω ^ 2 := by
    rw [setup.bothSpringsOscillator.ω_sq,
      setup.leftOnlyOscillator.ω_sq,
      setup.rightOnlyOscillator.ω_sq]
    rw [_model.bothSpringsEffectiveStiffness,
      _model.leftOnlyEffectiveStiffness,
      _model.rightOnlyEffectiveStiffness,
      _model.bothSpringsUsesSameBlock,
      _model.leftOnlyUsesSameBlock,
      _model.rightOnlyUsesSameBlock]
    ring
  have h_scaled_frequency_sq :
      (2 * Real.pi * frequencyInHertz setup.bothSpringsFrequency) ^ 2 =
        (2 * Real.pi * frequencyInHertz setup.leftOnlyFrequency) ^ 2 +
          (2 * Real.pi * frequencyInHertz setup.rightOnlyFrequency) ^ 2 := by
    calc
      (2 * Real.pi * frequencyInHertz setup.bothSpringsFrequency) ^ 2 =
          setup.bothSpringsOscillator.ω ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2)
          _model.bothSpringsCyclicToAngularFrequency
      _ = setup.leftOnlyOscillator.ω ^ 2 +
          setup.rightOnlyOscillator.ω ^ 2 := h_omega_sq_add
      _ = (2 * Real.pi * frequencyInHertz setup.leftOnlyFrequency) ^ 2 +
          (2 * Real.pi * frequencyInHertz setup.rightOnlyFrequency) ^ 2 := by
        rw [← _model.leftOnlyCyclicToAngularFrequency,
          ← _model.rightOnlyCyclicToAngularFrequency]
  rw [_problemAndFigure.leftSpringRemovedFrequency,
    _problemAndFigure.rightSpringRemovedFrequency] at h_scaled_frequency_sq
  have h_scale_sq_ne : (2 * Real.pi) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have h_factored_frequency_sq :
      (2 * Real.pi) ^ 2 *
          frequencyInHertz setup.bothSpringsFrequency ^ 2 =
        (2 * Real.pi) ^ 2 * ((30 : ℝ) ^ 2 + (45 : ℝ) ^ 2) := by
    calc
      (2 * Real.pi) ^ 2 *
          frequencyInHertz setup.bothSpringsFrequency ^ 2 =
          (2 * Real.pi * frequencyInHertz setup.bothSpringsFrequency) ^ 2 := by
        ring
      _ = (2 * Real.pi * 45) ^ 2 + (2 * Real.pi * 30) ^ 2 :=
        h_scaled_frequency_sq
      _ = (2 * Real.pi) ^ 2 * ((30 : ℝ) ^ 2 + (45 : ℝ) ^ 2) := by
        ring
  have h_frequency_sq :
      frequencyInHertz setup.bothSpringsFrequency ^ 2 =
        (30 : ℝ) ^ 2 + (45 : ℝ) ^ 2 :=
    mul_left_cancel₀ h_scale_sq_ne h_factored_frequency_sq
  have h_frequency_nonneg :
      0 ≤ frequencyInHertz setup.bothSpringsFrequency := by
    unfold frequencyInHertz
    positivity
  have h_radicand_nonneg :
      (0 : ℝ) ≤ (30 : ℝ) ^ 2 + (45 : ℝ) ^ 2 := by
    norm_num
  have h_frequency_exact :
      frequencyInHertz setup.bothSpringsFrequency =
        Real.sqrt ((30 : ℝ) ^ 2 + (45 : ℝ) ^ 2) := by
    nlinarith [Real.sq_sqrt h_radicand_nonneg,
      Real.sqrt_nonneg ((30 : ℝ) ^ 2 + (45 : ℝ) ^ 2)]
  constructor
  · exact h_frequency_exact
  · have h_lower :
        (107 : ℝ) / 2 ≤ Real.sqrt ((30 : ℝ) ^ 2 + (45 : ℝ) ^ 2) :=
      (Real.le_sqrt (by norm_num) h_radicand_nonneg).2 (by norm_num)
    have h_upper :
        Real.sqrt ((30 : ℝ) ^ 2 + (45 : ℝ) ^ 2) ≤ (109 : ℝ) / 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    simp only [MatchesAnswerChoice, AnswerChoice.hertz, h_frequency_exact]
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0252
