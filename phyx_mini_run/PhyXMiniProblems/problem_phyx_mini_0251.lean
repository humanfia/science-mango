import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0251

open Dimension

/-!
# Phase constant from a displacement--time graph

The primary figure shows a sinusoidal displacement curve.  Its vertical axis
is `x (cm)`, its horizontal axis is `t` with no printed time unit, and its
marked vertical scale is `x_s = 6.0 cm`.  There are three equal grid intervals
from equilibrium to `x_s`.  At the plotted time origin the curve is one grid
interval below equilibrium and is descending.  Thus the figure supplies
`x(0) = -2 cm` together with a negative velocity at that instant.

The problem states the cosine convention

`x(t) = x_m cos (omega t + phi)`.

Lengths, times, angular frequencies, and velocities below are dimensionful
Physlib quantities.  Real numbers are used only for explicitly named unit
readouts and for the dimensionless phase in radians.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A signed one-dimensional displacement or oscillation amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time coordinate. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- Angular frequency; radians are dimensionless, so this has inverse-time dimension. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A signed one-dimensional velocity. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a physical time in the selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := unit}).val

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  (frequency {UnitChoices.SI with time := unit}).val

/-- Read velocity in the coherent selected length/time unit system. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : VelocityQuantity) : ℝ :=
  (velocity
    {UnitChoices.SI with length := lengthUnit, time := timeUnit}).val

/-! ## Figure labels and oscillator setup -/

/-- The two coordinate axes shown in the graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The physical quantity printed on each graph axis. -/
inductive AxisQuantity where
  | time_t
  | displacement_x
  deriving DecidableEq, Repr

/--
Labels, scale, and rendering data read from the primary figure.

The graph does not print a horizontal-axis unit.  `timeCoordinateUnit` is an
arbitrary coherent unit chosen only to take scalar readouts in the governing
law; `horizontalAxisShowsUnit = false` records what the image actually shows.
-/
structure DisplacementTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  timeCoordinateUnit : TimeUnit
  verticalLengthUnit : LengthUnit
  horizontalAxisShowsUnit : Bool
  verticalAxisShowsUnit : Bool
  verticalScaleXs : LengthQuantity
  gridIntervalsFromZeroToXs : ℕ
  sinusoidalCurveVisible : Bool

/--
The oscillator quantities referred to by the problem and its graph.

`position` and `velocity` are independent dimensionful observables.  They are
connected to `amplitudeXm`, `angularFrequency`, and `phaseConstantRadians`
only by the governing-law premise below; no requested phase value is stored in
this setup.
-/
structure HarmonicOscillatorGraphSetup where
  graph : DisplacementTimeGraph
  amplitudeXm : LengthQuantity
  angularFrequency : AngularFrequencyQuantity
  phaseConstantRadians : ℝ
  position : TimeQuantity → LengthQuantity
  velocity : TimeQuantity → VelocityQuantity
  plottedTimeOrigin : TimeQuantity

/-!
Primary-image evidence.  The extrema touch the marked levels `x_s` and
`-x_s`, so the amplitude readout is `x_s`.  The curve crosses the vertical
axis one of the three grid intervals below equilibrium and is descending.
These are calibrated figure readouts, not assumptions about the requested
phase constant.
-/
structure MatchesOscillatorFigure
    (setup : HarmonicOscillatorGraphSetup) : Prop where
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .displacement_x
  horizontalUnitNotPrinted :
    setup.graph.horizontalAxisShowsUnit = false
  verticalUnitPrinted :
    setup.graph.verticalAxisShowsUnit = true
  verticalUnitIsCentimeters :
    setup.graph.verticalLengthUnit = LengthUnit.centimeters
  sinusoidalCurveShown :
    setup.graph.sinusoidalCurveVisible = true
  axisScaleReadout :
    lengthReadout LengthUnit.centimeters setup.graph.verticalScaleXs = 6
  threeGridIntervalsToScale :
    setup.graph.gridIntervalsFromZeroToXs = 3
  amplitudeTouchesScale :
    lengthReadout LengthUnit.centimeters setup.amplitudeXm =
      lengthReadout LengthUnit.centimeters setup.graph.verticalScaleXs
  plottedOriginReadout :
    timeReadout setup.graph.timeCoordinateUnit setup.plottedTimeOrigin = 0
  initialPointOneGridBelowEquilibrium :
    lengthReadout LengthUnit.centimeters
        (setup.position setup.plottedTimeOrigin) =
      -(lengthReadout LengthUnit.centimeters setup.graph.verticalScaleXs) / 3
  curveDescendingAtOrigin :
    velocityReadout LengthUnit.centimeters setup.graph.timeCoordinateUnit
        (setup.velocity setup.plottedTimeOrigin) < 0

/-!
Nondegeneracy and the conventional positive phase branch.  The full-turn
bound is a phase convention; it does not fix the quadrant or numerical answer.
The figure's negative initial velocity selects the quadrant through the
velocity law below.
-/
structure HasPhysicalHarmonicParameters
    (setup : HarmonicOscillatorGraphSetup) : Prop where
  amplitudePositive :
    0 < lengthReadout LengthUnit.centimeters setup.amplitudeXm
  angularFrequencyPositive :
    0 < angularFrequencyReadout setup.graph.timeCoordinateUnit
      setup.angularFrequency
  phasePositive : 0 < setup.phaseConstantRadians
  phaseBelowFullTurn : setup.phaseConstantRadians < 2 * Real.pi

/-!
The governing simple-harmonic-motion laws in the sign convention printed in
the question.  The velocity equation is the physical time derivative of the
position equation.  Neither field assumes the requested phase or an answer
choice.

Physlib's `HarmonicOscillator.AmplitudePhase` uses the alternative convention
`A cos (omega t - phi)` and scalar coordinates.  This local interface keeps
the problem's plus-sign convention and connects dimensionful observables via
coherent unit readouts.
-/
structure SatisfiesCosineHarmonicMotion
    (setup : HarmonicOscillatorGraphSetup) : Prop where
  harmonicPositionLaw :
    ∀ time : TimeQuantity,
      lengthReadout LengthUnit.centimeters (setup.position time) =
        lengthReadout LengthUnit.centimeters setup.amplitudeXm *
          Real.cos
            (angularFrequencyReadout setup.graph.timeCoordinateUnit
                setup.angularFrequency *
              timeReadout setup.graph.timeCoordinateUnit time +
              setup.phaseConstantRadians)
  harmonicVelocityLaw :
    ∀ time : TimeQuantity,
      velocityReadout LengthUnit.centimeters setup.graph.timeCoordinateUnit
          (setup.velocity time) =
        -(lengthReadout LengthUnit.centimeters setup.amplitudeXm) *
          angularFrequencyReadout setup.graph.timeCoordinateUnit
            setup.angularFrequency *
          Real.sin
            (angularFrequencyReadout setup.graph.timeCoordinateUnit
                setup.angularFrequency *
              timeReadout setup.graph.timeCoordinateUnit time +
              setup.phaseConstantRadians)

/-! ## Displayed answers and target conclusions -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Phase value in radians printed beside each answer choice. -/
def answerChoiceRadians : AnswerChoice → ℝ
  | .A => 1.15
  | .B => 1.47
  | .C => 1.91
  | .D => 2.23

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed phase to the nearest hundredth of a radian. -/
def MatchesAnswerToNearestHundredth
    (phaseRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |phaseRadians - answerChoiceRadians choice| < 0.005

/-- The initial graph ordinate and the cosine law give `cos phi = -1/3`. -/
lemma initial_phase_cosine_eq_neg_one_third
    (setup : HarmonicOscillatorGraphSetup)
    (hFigure : MatchesOscillatorFigure setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    Real.cos setup.phaseConstantRadians = -(1 : ℝ) / 3 := by
  have hAmplitude := hFigure.amplitudeTouchesScale
  have hPosition := hFigure.initialPointOneGridBelowEquilibrium
  have hPositionLaw :=
    hLaws.harmonicPositionLaw setup.plottedTimeOrigin
  rw [hFigure.plottedOriginReadout] at hPositionLaw
  norm_num at hPositionLaw
  nlinarith only [hAmplitude, hPosition, hPositionLaw,
    hPhysical.amplitudePositive]

/-!
The descending curve gives `sin phi > 0`; together with negative cosine and
the positive full-turn convention, this places the phase in quadrant II.
-/
lemma phase_lies_in_second_quadrant
    (setup : HarmonicOscillatorGraphSetup)
    (hFigure : MatchesOscillatorFigure setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    setup.phaseConstantRadians ∈ Set.Ioo (Real.pi / 2) Real.pi := by
  have hVelocityLaw :=
    hLaws.harmonicVelocityLaw setup.plottedTimeOrigin
  rw [hFigure.plottedOriginReadout] at hVelocityLaw
  norm_num at hVelocityLaw
  have hCoefficient :
      0 <
        lengthReadout LengthUnit.centimeters setup.amplitudeXm *
          angularFrequencyReadout setup.graph.timeCoordinateUnit
            setup.angularFrequency :=
    mul_pos hPhysical.amplitudePositive hPhysical.angularFrequencyPositive
  have hSinPositive :
      0 < Real.sin setup.phaseConstantRadians := by
    by_contra hSin
    have hSinNonpositive :
        Real.sin setup.phaseConstantRadians ≤ 0 :=
      le_of_not_gt hSin
    have hNegativeCoefficient :
        -(lengthReadout LengthUnit.centimeters setup.amplitudeXm) *
            angularFrequencyReadout setup.graph.timeCoordinateUnit
              setup.angularFrequency ≤ 0 := by
      nlinarith only [hCoefficient]
    have hVelocityNonnegative :
        0 ≤
          -(lengthReadout LengthUnit.centimeters setup.amplitudeXm) *
              angularFrequencyReadout setup.graph.timeCoordinateUnit
                setup.angularFrequency *
            Real.sin setup.phaseConstantRadians :=
      mul_nonneg_of_nonpos_of_nonpos hNegativeCoefficient hSinNonpositive
    nlinarith only [hFigure.curveDescendingAtOrigin, hVelocityLaw,
      hVelocityNonnegative]
  have hCosine :=
    initial_phase_cosine_eq_neg_one_third setup hFigure hPhysical hLaws
  have hCosineNegative :
      Real.cos setup.phaseConstantRadians < 0 := by
    rw [hCosine]
    norm_num
  have hAboveHalfTurn :
      Real.pi / 2 < setup.phaseConstantRadians := by
    by_contra hPhase
    have hPhaseLe :
        setup.phaseConstantRadians ≤ Real.pi / 2 :=
      le_of_not_gt hPhase
    have hCosineNonnegative :
        0 ≤ Real.cos setup.phaseConstantRadians :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by nlinarith only [Real.pi_pos, hPhysical.phasePositive])
        hPhaseLe
    linarith only [hCosineNegative, hCosineNonnegative]
  have hBelowPi :
      setup.phaseConstantRadians < Real.pi := by
    by_contra hPhase
    have hPiLe :
        Real.pi ≤ setup.phaseConstantRadians :=
      le_of_not_gt hPhase
    have hShiftedSinNonpositive :
        Real.sin (setup.phaseConstantRadians - 2 * Real.pi) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by linarith only [hPhysical.phaseBelowFullTurn])
        (by linarith only [hPiLe])
    rw [Real.sin_sub_two_pi] at hShiftedSinNonpositive
    linarith only [hSinPositive, hShiftedSinNonpositive]
  exact ⟨hAboveHalfTurn, hBelowPi⟩

/-- On the selected quadrant, the exact phase is the principal inverse cosine. -/
lemma phase_constant_eq_arccos_neg_one_third
    (setup : HarmonicOscillatorGraphSetup)
    (hFigure : MatchesOscillatorFigure setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    setup.phaseConstantRadians = Real.arccos (-(1 : ℝ) / 3) := by
  have hQuadrant :=
    phase_lies_in_second_quadrant setup hFigure hPhysical hLaws
  have hCosine :=
    initial_phase_cosine_eq_neg_one_third setup hFigure hPhysical hLaws
  rw [← hCosine]
  exact
    (Real.arccos_cos (le_of_lt hPhysical.phasePositive)
      (le_of_lt hQuadrant.2)).symm

/-- The exact inverse-cosine value rounds to `1.91 rad`, displayed as choice C. -/
lemma arccos_neg_one_third_matches_choice_C :
    MatchesAnswerToNearestHundredth
      (Real.arccos (-(1 : ℝ) / 3)) .C := by
  let xLower : ℝ := 381 / 3200
  have hxLowerAbs : |xLower| ≤ 1 := by
    norm_num [xLower, abs_of_nonneg]
  have hTaylorLower := abs_le.mp (Real.cos_bound hxLowerAbs)
  rw [abs_of_nonneg (by norm_num [xLower])] at hTaylorLower
  have hCosXLower :
      (0.9929 : ℝ) ≤ Real.cos xLower := by
    norm_num [xLower] at hTaylorLower ⊢
    nlinarith only [hTaylorLower.1]
  have hCosTwoLower :
      (0.9717 : ℝ) ≤ Real.cos (2 * xLower) := by
    rw [Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.9929) hCosXLower
    nlinarith only [hSquare]
  have hCosFourLower :
      (0.8884 : ℝ) ≤ Real.cos (4 * xLower) := by
    rw [show 4 * xLower = 2 * (2 * xLower) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.9717)
        hCosTwoLower
    nlinarith only [hSquare]
  have hCosEightLower :
      (0.5785 : ℝ) ≤ Real.cos (8 * xLower) := by
    rw [show 8 * xLower = 2 * (4 * xLower) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.8884)
        hCosFourLower
    nlinarith only [hSquare]
  have hCosSixteenLower :
      -(1 : ℝ) / 3 < Real.cos (16 * xLower) := by
    rw [show 16 * xLower = 2 * (8 * xLower) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.5785)
        hCosEightLower
    nlinarith only [hSquare]
  have hCosLowerEndpoint :
      -(1 : ℝ) / 3 < Real.cos ((381 : ℝ) / 200) := by
    norm_num [xLower] at hCosSixteenLower ⊢
    exact hCosSixteenLower
  let xUpper : ℝ := 383 / 3200
  have hxUpperAbs : |xUpper| ≤ 1 := by
    norm_num [xUpper, abs_of_nonneg]
  have hTaylorUpper := abs_le.mp (Real.cos_bound hxUpperAbs)
  rw [abs_of_nonneg (by norm_num [xUpper])] at hTaylorUpper
  have hCosXUpperNonnegative :
      0 ≤ Real.cos xUpper := by
    norm_num [xUpper] at hTaylorUpper ⊢
    nlinarith only [hTaylorUpper.1]
  have hCosXUpper :
      Real.cos xUpper ≤ (0.99285 : ℝ) := by
    norm_num [xUpper] at hTaylorUpper ⊢
    nlinarith only [hTaylorUpper.2]
  have hCosTwoUpperNonnegative :
      0 ≤ Real.cos (2 * xUpper) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
  have hCosTwoUpper :
      Real.cos (2 * xUpper) ≤ (0.97151 : ℝ) := by
    rw [Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosXUpperNonnegative hCosXUpper
    nlinarith only [hSquare]
  have hCosFourUpperNonnegative :
      0 ≤ Real.cos (4 * xUpper) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
  have hCosFourUpper :
      Real.cos (4 * xUpper) ≤ (0.88767 : ℝ) := by
    rw [show 4 * xUpper = 2 * (2 * xUpper) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosTwoUpperNonnegative hCosTwoUpper
    nlinarith only [hSquare]
  have hCosEightUpperNonnegative :
      0 ≤ Real.cos (8 * xUpper) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
      (by norm_num [xUpper]; linarith only [Real.one_le_pi_div_two])
  have hCosEightUpper :
      Real.cos (8 * xUpper) ≤ (0.57592 : ℝ) := by
    rw [show 8 * xUpper = 2 * (4 * xUpper) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosFourUpperNonnegative hCosFourUpper
    nlinarith only [hSquare]
  have hCosSixteenUpper :
      Real.cos (16 * xUpper) < -(1 : ℝ) / 3 := by
    rw [show 16 * xUpper = 2 * (8 * xUpper) by ring,
      Real.cos_two_mul]
    have hSquare :=
      mul_self_le_mul_self hCosEightUpperNonnegative hCosEightUpper
    nlinarith only [hSquare]
  have hCosUpperEndpoint :
      Real.cos ((383 : ℝ) / 200) < -(1 : ℝ) / 3 := by
    norm_num [xUpper] at hCosSixteenUpper ⊢
    exact hCosSixteenUpper
  have hAngleLower :
      (381 : ℝ) / 200 < Real.arccos (-(1 : ℝ) / 3) := by
    have hComparison :=
      Real.arccos_lt_arccos (x := -(1 : ℝ) / 3)
        (y := Real.cos ((381 : ℝ) / 200))
        (by norm_num) hCosLowerEndpoint
        (Real.cos_le_one _)
    rw [Real.arccos_cos (by norm_num)
      (by nlinarith only [Real.two_le_pi])] at hComparison
    exact hComparison
  have hAngleUpper :
      Real.arccos (-(1 : ℝ) / 3) < (383 : ℝ) / 200 := by
    have hComparison :=
      Real.arccos_lt_arccos
        (x := Real.cos ((383 : ℝ) / 200))
        (y := -(1 : ℝ) / 3)
        (Real.neg_one_le_cos _) hCosUpperEndpoint (by norm_num)
    rw [Real.arccos_cos (by norm_num)
      (by nlinarith only [Real.two_le_pi])] at hComparison
    exact hComparison
  change |Real.arccos (-(1 : ℝ) / 3) - 1.91| < 0.005
  rw [abs_lt]
  constructor <;> norm_num at hAngleLower hAngleUpper ⊢ <;> linarith

/-!
At `t = 0`, the graph has `x/x_m = -2/6 = -1/3` and negative velocity.
Therefore the phase in the problem's positive full-turn convention is

`phi = arccos (-1/3) approximately 1.91063 rad`.

It rounds to `1.91 rad`, choice C, and is at least as close to C as to every
other displayed choice.  The rounding statement is deliberately not the
false exact equality `phi = 1.91`.

This formalizes `thm:physics:phyx_mini_0251:target`.
-/
theorem problem_phyx_mini_0251
    (setup : HarmonicOscillatorGraphSetup)
    (hFigure : MatchesOscillatorFigure setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    Real.cos setup.phaseConstantRadians = -(1 : ℝ) / 3 ∧
      setup.phaseConstantRadians = Real.arccos (-(1 : ℝ) / 3) ∧
      MatchesAnswerToNearestHundredth
        setup.phaseConstantRadians recordedAnswerChoice ∧
      ∀ choice : AnswerChoice,
        |setup.phaseConstantRadians -
            answerChoiceRadians recordedAnswerChoice| ≤
          |setup.phaseConstantRadians - answerChoiceRadians choice| := by
  have hCosine :=
    initial_phase_cosine_eq_neg_one_third setup hFigure hPhysical hLaws
  have hPhase :=
    phase_constant_eq_arccos_neg_one_third setup hFigure hPhysical hLaws
  have hMatch :
      MatchesAnswerToNearestHundredth
        setup.phaseConstantRadians recordedAnswerChoice := by
    rw [hPhase, recordedAnswerChoice]
    exact arccos_neg_one_third_matches_choice_C
  refine ⟨hCosine, hPhase, hMatch, ?_⟩
  intro choice
  have hClose :
      |setup.phaseConstantRadians - 1.91| < 0.005 := by
    simpa [MatchesAnswerToNearestHundredth, recordedAnswerChoice,
      answerChoiceRadians] using hMatch
  have hBounds := abs_lt.mp hClose
  cases choice with
  | A =>
      change
        |setup.phaseConstantRadians - 1.91| ≤
          |setup.phaseConstantRadians - 1.15|
      have hRightNonnegative :
          0 ≤ setup.phaseConstantRadians - 1.15 := by
        linarith only [hBounds.1]
      rw [abs_of_nonneg hRightNonnegative]
      linarith only [hClose, hBounds.1]
  | B =>
      change
        |setup.phaseConstantRadians - 1.91| ≤
          |setup.phaseConstantRadians - 1.47|
      have hRightNonnegative :
          0 ≤ setup.phaseConstantRadians - 1.47 := by
        linarith only [hBounds.1]
      rw [abs_of_nonneg hRightNonnegative]
      linarith only [hClose, hBounds.1]
  | C =>
      exact le_rfl
  | D =>
      change
        |setup.phaseConstantRadians - 1.91| ≤
          |setup.phaseConstantRadians - 2.23|
      have hRightNonpositive :
          setup.phaseConstantRadians - 2.23 ≤ 0 := by
        linarith only [hBounds.2]
      rw [abs_of_nonpos hRightNonpositive]
      linarith only [hClose, hBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0251
