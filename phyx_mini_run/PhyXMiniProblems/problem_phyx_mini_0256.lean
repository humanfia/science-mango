import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Oscillation frequency for two identical springs in series

A block of mass `0.245 kg` moves horizontally on a frictionless floor.  The
primary figure places two springs, each labeled `k`, in a single chain from the
block to a wall.  Each spring has stiffness `6430 N/m`.

Mass, spring stiffness, and cyclic frequency are represented by Physlib
dimensionful quantities.  Physlib's scalar `HarmonicOscillator` is connected
to their coherent SI readouts by the governing-law interface below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0256

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/--
A nonnegative linear spring stiffness, whose SI unit is newtons per metre and
whose physical dimension is mass per time squared.
-/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative cyclic frequency, with inverse-time dimension. -/
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

/-- The two springs, distinguished by their positions along the series chain. -/
inductive SpringLabel where
  | blockAdjacent
  | wallAdjacent
  deriving DecidableEq, Repr

/-- Endpoints visible in the block-to-wall spring chain. -/
inductive ChainEndpoint where
  | block
  | springJunction
  | wall
  deriving DecidableEq, Repr

/-- Labels printed on the block and springs in the supplied figure. -/
inductive FigureLabel where
  | mass_m
  | stiffness_k
  deriving DecidableEq, Repr

/-- The horizontal direction of the block's allowed displacement. -/
inductive MotionAxis where
  | horizontal
  deriving DecidableEq, Repr

/-- The idealized contact condition specified in the problem. -/
inductive FloorCondition where
  | frictionless
  deriving DecidableEq, Repr

/--
Qualitative data transcribed from the primary image.  The endpoint maps retain
the order block--first spring--junction--second spring--wall, rather than
collapsing the two drawn springs into a single glyph.
-/
structure TwoSeriesSpringFigure where
  displayedBlockLabel : FigureLabel
  displayedSpringLabel : SpringLabel → FigureLabel
  springShown : SpringLabel → Bool
  springLeftEndpoint : SpringLabel → ChainEndpoint
  springRightEndpoint : SpringLabel → ChainEndpoint
  blockAndSpringsAlignedHorizontally : Bool
  wallShownAtRight : Bool
  floorShown : Bool

/-!
The independent physical quantities and observables of the apparatus.

`oscillationFrequency` and `effectiveSeriesStiffness` are unknown physical
quantities.  The scalar Physlib oscillator is linked to them only by the
general laws below; none of these fields defines the requested answer.
-/
structure SeriesSpringBlockSetup where
  blockMass : MassQuantity
  springStiffness : SpringLabel → SpringStiffnessQuantity
  effectiveSeriesStiffness : SpringStiffnessQuantity
  oscillationFrequency : FrequencyQuantity
  equivalentOscillator : ClassicalMechanics.HarmonicOscillator
  motionAxis : MotionAxis
  floorCondition : FloorCondition
  figure : TwoSeriesSpringFigure

/-! ## Assumption/target split -/

/-!
Problem-text calibrations and qualitative evidence from the supplied image.
This fixes the two component stiffnesses, but neither the effective stiffness
nor the requested oscillation frequency.
-/
structure MatchesProblemAndFigure (setup : SeriesSpringBlockSetup) : Prop where
  massReadout : massInKilograms setup.blockMass = (245 : ℝ) / 1000
  eachSpringStiffnessReadout : ∀ spring : SpringLabel,
    stiffnessInNewtonsPerMeter (setup.springStiffness spring) = 6430
  horizontalMotion : setup.motionAxis = .horizontal
  floorIsFrictionless : setup.floorCondition = .frictionless
  figureBlockLabel : setup.figure.displayedBlockLabel = .mass_m
  figureSpringLabels : ∀ spring : SpringLabel,
    setup.figure.displayedSpringLabel spring = .stiffness_k
  figureShowsBothSprings : ∀ spring : SpringLabel,
    setup.figure.springShown spring = true
  blockAdjacentSpringStartsAtBlock :
    setup.figure.springLeftEndpoint .blockAdjacent = .block
  blockAdjacentSpringEndsAtJunction :
    setup.figure.springRightEndpoint .blockAdjacent = .springJunction
  wallAdjacentSpringStartsAtJunction :
    setup.figure.springLeftEndpoint .wallAdjacent = .springJunction
  wallAdjacentSpringEndsAtWall :
    setup.figure.springRightEndpoint .wallAdjacent = .wall
  horizontalFigureAlignment :
    setup.figure.blockAndSpringsAlignedHorizontally = true
  rightWallShown : setup.figure.wallShownAtRight = true
  floorShown : setup.figure.floorShown = true

/-- Positivity of the mass, component stiffnesses, and effective stiffness. -/
structure HasPhysicalParameters (setup : SeriesSpringBlockSetup) : Prop where
  blockMassPositive : 0 < massInKilograms setup.blockMass
  springStiffnessPositive : ∀ spring : SpringLabel,
    0 < stiffnessInNewtonsPerMeter (setup.springStiffness spring)
  effectiveStiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.effectiveSeriesStiffness

/-!
## Governing small-oscillation laws

For two linear springs in series, equal force and additive extension give
`k_eff * (k₁ + k₂) = k₁ * k₂`.  The equivalent Physlib oscillator has the
same block mass and effective stiffness.  Physlib supplies
`HarmonicOscillator.ω = sqrt (k / m)`; cyclic frequency is related to angular
frequency by `ω = 2 π f`.

These are general modeling laws and contain no numerical frequency or answer
choice for this problem.
-/
structure SatisfiesSeriesSpringOscillatorModel
    (setup : SeriesSpringBlockSetup) : Prop where
  seriesStiffnessLaw :
    stiffnessInNewtonsPerMeter setup.effectiveSeriesStiffness *
        (stiffnessInNewtonsPerMeter
            (setup.springStiffness .blockAdjacent) +
          stiffnessInNewtonsPerMeter
            (setup.springStiffness .wallAdjacent)) =
      stiffnessInNewtonsPerMeter
          (setup.springStiffness .blockAdjacent) *
        stiffnessInNewtonsPerMeter
          (setup.springStiffness .wallAdjacent)
  oscillatorUsesBlockMass :
    setup.equivalentOscillator.m = massInKilograms setup.blockMass
  oscillatorUsesEffectiveStiffness :
    setup.equivalentOscillator.k =
      stiffnessInNewtonsPerMeter setup.effectiveSeriesStiffness
  cyclicToAngularFrequency :
    2 * Real.pi * frequencyInHertz setup.oscillationFrequency =
      setup.equivalentOscillator.ω

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
  | .A => 168 / 10
  | .B => 176 / 10
  | .C => 182 / 10
  | .D => 194 / 10

/--
Agreement with a displayed one-decimal-place answer, using the usual nearest
tenth interval of one twentieth hertz on either side.
-/
def MatchesAnswerChoice
    (frequency : FrequencyQuantity) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz frequency - choice.hertz| ≤ (1 : ℝ) / 20

/-!
The series pair has effective stiffness `6430 / 2 N/m`.  Hence the cyclic
frequency is

`sqrt ((6430 / 2) / 0.245) / (2 π) Hz`,

which rounds to `18.2 Hz`, answer C.  This formalizes
`thm:physics:phyx_mini_0256:target`.
-/
theorem seriesSpringsFrequency_exact_and_matches_choiceC
    (setup : SeriesSpringBlockSetup)
    (_problemAndFigure : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_model : SatisfiesSeriesSpringOscillatorModel setup) :
    frequencyInHertz setup.oscillationFrequency =
        Real.sqrt (((6430 : ℝ) / 2) / ((245 : ℝ) / 1000)) /
          (2 * Real.pi) ∧
      MatchesAnswerChoice setup.oscillationFrequency .C := by
  have h_effective :
      stiffnessInNewtonsPerMeter setup.effectiveSeriesStiffness =
        (6430 : ℝ) / 2 := by
    have h := _model.seriesStiffnessLaw
    rw [_problemAndFigure.eachSpringStiffnessReadout .blockAdjacent,
      _problemAndFigure.eachSpringStiffnessReadout .wallAdjacent] at h
    norm_num at h ⊢
    linarith
  have h_omega :
      setup.equivalentOscillator.ω =
        Real.sqrt (((6430 : ℝ) / 2) / ((245 : ℝ) / 1000)) := by
    simp only [ClassicalMechanics.HarmonicOscillator.ω,
      _model.oscillatorUsesEffectiveStiffness,
      _model.oscillatorUsesBlockMass, h_effective,
      _problemAndFigure.massReadout]
  have h_frequency :
      frequencyInHertz setup.oscillationFrequency =
        Real.sqrt (((6430 : ℝ) / 2) / ((245 : ℝ) / 1000)) /
          (2 * Real.pi) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
    rw [← h_omega]
    simpa [mul_comm] using _model.cyclicToAngularFrequency
  -- Derive a sufficiently sharp lower bound on `π` from inscribed polygons.
  have h_pi_lower_generic (n : ℕ) :
      2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) <
        Real.pi := by
    have h :
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply Real.sin_lt
        apply div_pos Real.pi_pos
      all_goals
        apply pow_pos
        norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) h
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have h_lower_sqrt1 :
      Real.sqrt (2 : ℝ) ≤ (338 : ℝ) / 239 := by
    rw [Real.sqrt_le_left] <;> norm_num
  have h_lower_sqrt2 :
      Real.sqrt (2 + Real.sqrt (2 : ℝ)) ≤ (704 : ℝ) / 381 := by
    calc
      Real.sqrt (2 + Real.sqrt (2 : ℝ)) ≤
          Real.sqrt (2 + (338 : ℝ) / 239) := by
            gcongr
      _ ≤ (704 : ℝ) / 381 := by
        rw [Real.sqrt_le_left] <;> norm_num
  have h_lower_sqrt3 :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) ≤
        (1940 : ℝ) / 989 := by
    calc
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) ≤
          Real.sqrt (2 + (704 : ℝ) / 381) := by
            gcongr
      _ ≤ (1940 : ℝ) / 989 := by
        rw [Real.sqrt_le_left] <;> norm_num
  have h_lower_sqrt4 :
      Real.sqrt
          (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) ≤
        (1447 : ℝ) / 727 := by
    calc
      Real.sqrt
          (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) ≤
          Real.sqrt (2 + (1940 : ℝ) / 989) := by
            gcongr
      _ ≤ (1447 : ℝ) / 727 := by
        rw [Real.sqrt_le_left] <;> norm_num
  have h_lower_argument :
      ((157 : ℝ) / 1600) ^ 2 ≤
        2 -
          Real.sqrt
            (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) := by
    nlinarith
  have h_lower_outer :
      (157 : ℝ) / 1600 ≤
        Real.sqrt
          (2 -
            Real.sqrt
              (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))))) :=
    Real.le_sqrt_of_sq_le h_lower_argument
  have h_pi_lower : (3.14 : ℝ) < Real.pi := by
    refine lt_of_le_of_lt ?_ (h_pi_lower_generic 4)
    norm_num [Real.sqrtTwoAddSeries]
    linarith
  -- The companion Taylor estimate gives the required upper bound on `π`.
  have h_pi_upper_generic (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have h :
        Real.pi <
          (Real.sqrt (2 - Real.sqrtTwoAddSeries 0 n) / 2 +
              1 / (2 ^ n) ^ 3 / 4) *
            (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by positivity),
        ← Real.sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <|
            Real.sin_gt_sub_cube (by positivity) <|
              div_le_one_of_le₀ (by
                calc
                  Real.pi ≤ 4 := Real.pi_le_four
                  _ = 2 ^ (0 + 2) := by norm_num
                  _ ≤ 2 ^ (n + 2) := by gcongr <;> norm_num)
                (by positivity)
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le h (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      div_div, ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc,
        mul_comm n]
    all_goals norm_num
  have h_upper_sqrt1 :
      (41 : ℝ) / 29 ≤ Real.sqrt (2 : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have h_upper_sqrt2 :
      (109 : ℝ) / 59 ≤ Real.sqrt (2 + Real.sqrt (2 : ℝ)) := by
    calc
      (109 : ℝ) / 59 ≤ Real.sqrt (2 + (41 : ℝ) / 29) := by
        apply Real.le_sqrt_of_sq_le
        norm_num
      _ ≤ Real.sqrt (2 + Real.sqrt (2 : ℝ)) := by
        gcongr
  have h_upper_sqrt3 :
      (865 : ℝ) / 441 ≤
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) := by
    calc
      (865 : ℝ) / 441 ≤ Real.sqrt (2 + (109 : ℝ) / 59) := by
        apply Real.le_sqrt_of_sq_le
        norm_num
      _ ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) := by
        gcongr
  have h_upper_sqrt4 :
      (412 : ℝ) / 207 ≤
        Real.sqrt
          (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) := by
    calc
      (412 : ℝ) / 207 ≤ Real.sqrt (2 + (865 : ℝ) / 441) := by
        apply Real.le_sqrt_of_sq_le
        norm_num
      _ ≤
          Real.sqrt
            (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) := by
        gcongr
  let q : ℝ := ((63 : ℝ) / 20 - 1 / 256) / 32
  have hq : 0 ≤ q := by
    norm_num [q]
  have h_upper_argument :
      2 -
          Real.sqrt
            (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) ≤
        q ^ 2 := by
    dsimp [q]
    nlinarith
  have h_upper_outer :
      Real.sqrt
          (2 -
            Real.sqrt
              (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))))) ≤
        q :=
    (Real.sqrt_le_left hq).2 h_upper_argument
  have h_pi_upper : Real.pi < (3.15 : ℝ) := by
    have h := h_pi_upper_generic 4
    norm_num [Real.sqrtTwoAddSeries] at h ⊢
    dsimp [q] at h_upper_outer
    linarith
  -- Bound the square root in the frequency formula by nearby rationals.
  have h_sqrt_lower :
      (572 : ℝ) / 5 ≤
        Real.sqrt (((6430 : ℝ) / 2) / ((245 : ℝ) / 1000)) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have h_sqrt_upper :
      Real.sqrt (((6430 : ℝ) / 2) / ((245 : ℝ) / 1000)) ≤
        (573 : ℝ) / 5 := by
    rw [Real.sqrt_le_left] <;> norm_num
  have h_denominator_positive : 0 < 2 * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  have h_frequency_lower :
      (18.15 : ℝ) ≤
        Real.sqrt (((6430 : ℝ) / 2) / ((245 : ℝ) / 1000)) /
          (2 * Real.pi) := by
    apply (le_div_iff₀ h_denominator_positive).2
    nlinarith
  have h_frequency_upper :
      Real.sqrt (((6430 : ℝ) / 2) / ((245 : ℝ) / 1000)) /
          (2 * Real.pi) ≤ (18.25 : ℝ) := by
    apply (div_le_iff₀ h_denominator_positive).2
    nlinarith
  -- The exact value lies in the interval `[18.15, 18.25]`.
  constructor
  · exact h_frequency
  · rw [MatchesAnswerChoice, h_frequency, AnswerChoice.hertz, abs_le]
    norm_num at h_frequency_lower h_frequency_upper ⊢
    constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0256
