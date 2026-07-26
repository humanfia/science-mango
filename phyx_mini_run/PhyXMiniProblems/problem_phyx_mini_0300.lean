import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0300

open Dimension

/-!
# Positive phase of a sinusoidal string wave

The primary graph shows transverse displacement `y` in millimeters against
time `t` at the string point `x = 0`.  The marked scale is `y_s = 6.0 mm`.
At the graph's time origin the curve is one of the three equal positive-side
grid intervals above equilibrium, hence at `2 mm`, and the curve is rising.

The physical length, time, wave-number, angular-frequency, and velocity
quantities below use Physlib's unit-independent `Dimensionful` type.  Real
numbers are used only for named-unit readouts and dimensionless phases in
radians.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- A nonnegative wave amplitude or graph scale length. -/
abbrev AmplitudeQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial coordinate or transverse displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed time coordinate relative to the graph origin. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative wave number; radians are dimensionless. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed transverse-velocity component of a string point. -/
abbrev TransverseVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a nonnegative length in the selected unit. -/
def amplitudeReadout
    (unit : LengthUnit) (amplitude : AmplitudeQuantity) : ℝ :=
  ((amplitude {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed length coordinate or displacement in the selected unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a signed time coordinate in the selected unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := unit}).val

/-- Read a wave number in radians per selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read transverse velocity in a coherent selected length/time unit system. -/
def transverseVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : TransverseVelocityQuantity) : ℝ :=
  (velocity
    {UnitChoices.SI with length := lengthUnit, time := timeUnit}).val

/-! ## Physical roles and primary-figure labels -/

/-- The kind of disturbance specified in the problem. -/
inductive StringWaveKind where
  | transverseSinusoidal
  deriving DecidableEq, Repr

/-- Propagation direction encoded by the sign of the temporal phase. -/
inductive PropagationDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Sign in `kx ± omega t + phi` for the two propagation directions. -/
def temporalPhaseSign : PropagationDirection → ℝ
  | .negativeX => 1
  | .positiveX => -1

/-- The two coordinate axes drawn in the graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity denoted by each printed axis label. -/
inductive AxisQuantity where
  | time_t
  | transverseDisplacement_y
  deriving DecidableEq, Repr

/-- The upper and lower scale marks printed on the vertical axis. -/
inductive ScaleMarkRole where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Literal mathematical roles of the two scale labels `y_s` and `-y_s`. -/
inductive ScaleMarkLabel where
  | ys
  | negativeYs
  deriving DecidableEq, Repr

/-!
The labels and geometry visible in the supplied displacement--time graph.
The horizontal axis prints `t` without a time unit, while the vertical axis
prints `y (mm)`.  Six equal vertical intervals separate `-y_s` from `y_s`.
-/
structure DisplacementTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  verticalLengthUnit : LengthUnit
  horizontalUnitPrinted : Bool
  verticalUnitPrinted : Bool
  scaleMarkLabel : ScaleMarkRole → ScaleMarkLabel
  verticalScaleYs : AmplitudeQuantity
  verticalIntervalsFromNegativeYsToYs : ℕ
  sinusoidalCurveVisible : Bool
  extremaTouchScaleLines : Bool

/-!
Independent physical quantities and observables for the string wave.
The displacement and transverse velocity fields are kept dimensionful and
are related to the wave parameters only by the governing-law premise below.
-/
structure TravelingStringWaveSetup where
  waveKind : StringWaveKind
  propagationDirection : PropagationDirection
  graph : DisplacementTimeGraph
  amplitudeYm : AmplitudeQuantity
  waveNumber : WaveNumberQuantity
  angularFrequency : AngularFrequencyQuantity
  phaseOffsetRadians : ℝ
  axialOrigin : SignedLengthQuantity
  graphTimeOrigin : TimeQuantity
  transverseDisplacement :
    SignedLengthQuantity → TimeQuantity → SignedLengthQuantity
  transverseVelocity :
    SignedLengthQuantity → TimeQuantity → TransverseVelocityQuantity

/-!
Problem-statement data.  The minus sign in the supplied formula corresponds
to propagation in positive `x`; the graph is explicitly the trace at `x=0`.
No numerical phase value or answer choice occurs in this structure.
-/
structure MatchesStringWaveProblemData
    (setup : TravelingStringWaveSetup) : Prop where
  waveIsTransverseSinusoidal :
    setup.waveKind = .transverseSinusoidal
  formulaHasMinusTemporalPhase :
    setup.propagationDirection = .positiveX
  observedPointIsXZero :
    ∀ unit : LengthUnit,
      signedLengthReadout unit setup.axialOrigin = 0
  graphOriginIsTimeZero :
    ∀ unit : TimeUnit,
      timeReadout unit setup.graphTimeOrigin = 0

/-!
Calibrated evidence read from the primary bitmap.  The vertical scale has
three equal intervals on each side of equilibrium.  The curve crosses the
vertical axis at the first positive grid line (`2 mm`) and is rising there.
These are figure readouts, not assumptions about the requested phase.
-/
structure MatchesPrimaryDisplacementTimeGraph
    (setup : TravelingStringWaveSetup) : Prop where
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .transverseDisplacement_y
  verticalUnitIsMillimeters :
    setup.graph.verticalLengthUnit = LengthUnit.millimeters
  horizontalUnitIsNotPrinted :
    setup.graph.horizontalUnitPrinted = false
  verticalUnitIsPrinted :
    setup.graph.verticalUnitPrinted = true
  upperScaleLabelIsYs :
    setup.graph.scaleMarkLabel .upper = .ys
  lowerScaleLabelIsNegativeYs :
    setup.graph.scaleMarkLabel .lower = .negativeYs
  sixEqualVerticalIntervals :
    setup.graph.verticalIntervalsFromNegativeYsToYs = 6
  sinusoidalCurveShown :
    setup.graph.sinusoidalCurveVisible = true
  extremaReachScaleLines :
    setup.graph.extremaTouchScaleLines = true
  scaleYsMillimeters :
    amplitudeReadout LengthUnit.millimeters setup.graph.verticalScaleYs = 6
  amplitudeTouchesScale :
    amplitudeReadout LengthUnit.millimeters setup.amplitudeYm =
      amplitudeReadout LengthUnit.millimeters setup.graph.verticalScaleYs
  initialDisplacementMillimeters :
    signedLengthReadout LengthUnit.millimeters
        (setup.transverseDisplacement setup.axialOrigin setup.graphTimeOrigin) = 2
  curveRisesAtTimeOrigin :
    0 < transverseVelocityReadout LengthUnit.millimeters TimeUnit.seconds
      (setup.transverseVelocity setup.axialOrigin setup.graphTimeOrigin)

/-!
Nondegeneracy and the requested positive principal phase representative.
The range condition does not determine the answer: the displacement readout,
slope sign, and governing laws select its value.
-/
structure HasPhysicalWaveParameters
    (setup : TravelingStringWaveSetup) : Prop where
  amplitudePositive :
    0 < amplitudeReadout LengthUnit.millimeters setup.amplitudeYm
  waveNumberPositive :
    0 < waveNumberReadout LengthUnit.meters setup.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyReadout TimeUnit.seconds setup.angularFrequency
  phasePositive : 0 < setup.phaseOffsetRadians
  phaseBelowFullTurn : setup.phaseOffsetRadians < 2 * Real.pi

/-!
The governing laws stated or implied by the problem:

* `y(x,t) = y_m sin(kx - omega t + phi)` for a positive-`x` wave;
* transverse particle velocity is the time derivative of displacement.

The cosine formula is the dimensionful observable interface corresponding to
Mathlib's scalar sine chain rule.  Neither law mentions the requested phase
value or any displayed answer choice.
-/
structure SatisfiesSinusoidalStringWaveLaws
    (setup : TravelingStringWaveSetup) : Prop where
  sinusoidalDisplacementLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (position : SignedLengthQuantity) (time : TimeQuantity),
      signedLengthReadout lengthUnit
          (setup.transverseDisplacement position time) =
        amplitudeReadout lengthUnit setup.amplitudeYm *
          Real.sin
            (waveNumberReadout lengthUnit setup.waveNumber *
                signedLengthReadout lengthUnit position +
              temporalPhaseSign setup.propagationDirection *
                angularFrequencyReadout timeUnit setup.angularFrequency *
                timeReadout timeUnit time +
              setup.phaseOffsetRadians)
  transverseVelocityLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (position : SignedLengthQuantity) (time : TimeQuantity),
      transverseVelocityReadout lengthUnit timeUnit
          (setup.transverseVelocity position time) =
        amplitudeReadout lengthUnit setup.amplitudeYm *
          temporalPhaseSign setup.propagationDirection *
          angularFrequencyReadout timeUnit setup.angularFrequency *
          Real.cos
            (waveNumberReadout lengthUnit setup.waveNumber *
                signedLengthReadout lengthUnit position +
              temporalPhaseSign setup.propagationDirection *
                angularFrequencyReadout timeUnit setup.angularFrequency *
                timeReadout timeUnit time +
              setup.phaseOffsetRadians)

/-! ## Derived phase relations and displayed choices -/

/-- Labels printed beside the four candidate phase values. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Phase in radians printed beside each answer label. -/
def AnswerChoice.phaseRadians : AnswerChoice → ℝ
  | .A => 2 / 5
  | .B => 7 / 10
  | .C => 7 / 5
  | .D => 14 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a phase displayed to one decimal place. -/
def MatchesDisplayedPhase (phaseRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |phaseRadians - choice.phaseRadians| < 1 / 20

/-!
The `2 mm` initial displacement and `6 mm` amplitude imply
`sin phi = 1/3`.  This is an intermediate consequence, not a premise.
-/
lemma sine_phaseOffsetRadians_eq_one_third
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_figure : MatchesPrimaryDisplacementTimeGraph setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesSinusoidalStringWaveLaws setup) :
    Real.sin setup.phaseOffsetRadians = 1 / 3 := by
  have hDisplacement :=
    _laws.sinusoidalDisplacementLaw
      LengthUnit.millimeters TimeUnit.seconds
      setup.axialOrigin setup.graphTimeOrigin
  rw [_figure.initialDisplacementMillimeters,
    _figure.amplitudeTouchesScale, _figure.scaleYsMillimeters,
    _data.observedPointIsXZero LengthUnit.millimeters,
    _data.graphOriginIsTimeZero TimeUnit.seconds,
    _data.formulaHasMinusTemporalPhase] at hDisplacement
  norm_num [temporalPhaseSign] at hDisplacement ⊢
  linarith

/-!
Because the trace is rising while the formula contains `-omega t`, the
initial phase has negative cosine and therefore lies in quadrant II.
-/
lemma cosine_phaseOffsetRadians_negative
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_figure : MatchesPrimaryDisplacementTimeGraph setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesSinusoidalStringWaveLaws setup) :
    Real.cos setup.phaseOffsetRadians < 0 := by
  have hVelocity :=
    _laws.transverseVelocityLaw
      LengthUnit.millimeters TimeUnit.seconds
      setup.axialOrigin setup.graphTimeOrigin
  rw [_figure.amplitudeTouchesScale, _figure.scaleYsMillimeters,
    _data.observedPointIsXZero LengthUnit.millimeters,
    _data.graphOriginIsTimeZero TimeUnit.seconds,
    _data.formulaHasMinusTemporalPhase] at hVelocity
  norm_num [temporalPhaseSign] at hVelocity
  by_contra hCosine
  have hCosineNonnegative : 0 ≤ Real.cos setup.phaseOffsetRadians :=
    le_of_not_gt hCosine
  have hProductNonnegative :
      0 ≤ angularFrequencyReadout TimeUnit.seconds setup.angularFrequency *
        Real.cos setup.phaseOffsetRadians :=
    mul_nonneg (le_of_lt _physical.angularFrequencyPositive) hCosineNonnegative
  nlinarith [_figure.curveRisesAtTimeOrigin]

/-!
The positive principal representative selected by the initial displacement
and rising slope is `pi - arcsin (1/3)` radians.
-/
lemma phaseOffsetRadians_eq_pi_sub_arcsin_one_third
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_figure : MatchesPrimaryDisplacementTimeGraph setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesSinusoidalStringWaveLaws setup) :
    setup.phaseOffsetRadians = Real.pi - Real.arcsin (1 / 3) := by
  have hSine :=
    sine_phaseOffsetRadians_eq_one_third
      setup _data _figure _physical _laws
  have hCosine :=
    cosine_phaseOffsetRadians_negative
      setup _data _figure _physical _laws
  have hPhaseBelowPi : setup.phaseOffsetRadians < Real.pi := by
    by_contra hNotBelowPi
    have hDifferenceNonnegative :
        0 ≤ setup.phaseOffsetRadians - Real.pi :=
      sub_nonneg.mpr (le_of_not_gt hNotBelowPi)
    have hDifferenceBelowPi :
        setup.phaseOffsetRadians - Real.pi ≤ Real.pi := by
      linarith [_physical.phaseBelowFullTurn]
    have hSineDifferenceNonnegative :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        hDifferenceNonnegative hDifferenceBelowPi
    rw [Real.sin_sub_pi, hSine] at hSineDifferenceNonnegative
    norm_num at hSineDifferenceNonnegative
  have hPiDivTwoBelowPhase :
      Real.pi / 2 < setup.phaseOffsetRadians := by
    by_contra hNotAbove
    have hCosineNonnegative :=
      Real.cos_nonneg_of_mem_Icc
        (show setup.phaseOffsetRadians ∈
            Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
          constructor
          · linarith [_physical.phasePositive, Real.pi_pos]
          · exact le_of_not_gt hNotAbove)
    linarith
  have hComplementSine :
      Real.sin (Real.pi - setup.phaseOffsetRadians) = 1 / 3 := by
    rw [Real.sin_pi_sub, hSine]
  have hArcsin :
      Real.arcsin (1 / 3) = Real.pi - setup.phaseOffsetRadians :=
    Real.arcsin_eq_of_sin_eq hComplementSine
      (show Real.pi - setup.phaseOffsetRadians ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith)
  linarith

/-!
The exact phase `pi - arcsin (1/3)` is approximately `2.8018 rad`, so the
one-decimal displayed answer is `2.8 rad`, choice D.  The final conjunct also
states that D is at least as close as every displayed alternative.

This formalizes blueprint label `thm:physics:phyx_mini_0300:target`.
-/
theorem problem_phyx_mini_0300
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_figure : MatchesPrimaryDisplacementTimeGraph setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesSinusoidalStringWaveLaws setup) :
    setup.phaseOffsetRadians = Real.pi - Real.arcsin (1 / 3) ∧
      MatchesDisplayedPhase setup.phaseOffsetRadians recordedDatasetAnswer ∧
      ∀ choice : AnswerChoice,
        |setup.phaseOffsetRadians - recordedDatasetAnswer.phaseRadians| ≤
          |setup.phaseOffsetRadians - choice.phaseRadians| := by
  have hPhaseExact :=
    phaseOffsetRadians_eq_pi_sub_arcsin_one_third
      setup _data _figure _physical _laws
  have hPhaseSine :=
    sine_phaseOffsetRadians_eq_one_third
      setup _data _figure _physical _laws
  have hSinFive (x : ℝ) :
      Real.sin (5 * x) =
        16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 +
          5 * Real.sin x := by
    have hCosineSquared :
        Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [show (5 : ℝ) * x = 2 * x + 3 * x by ring, Real.sin_add,
      Real.sin_two_mul, Real.cos_three_mul, Real.cos_two_mul,
      Real.sin_three_mul]
    calc
      2 * Real.sin x * Real.cos x *
            (4 * Real.cos x ^ 3 - 3 * Real.cos x) +
          (2 * Real.cos x ^ 2 - 1) *
            (3 * Real.sin x - 4 * Real.sin x ^ 3) =
        2 * Real.sin x * (Real.cos x ^ 2) *
            (4 * Real.cos x ^ 2 - 3) +
          (2 * Real.cos x ^ 2 - 1) *
            (3 * Real.sin x - 4 * Real.sin x ^ 3) := by
              ring
      _ = 16 * Real.sin x ^ 5 - 20 * Real.sin x ^ 3 +
          5 * Real.sin x := by
            rw [hCosineSquared]
            ring
  have hSineElevenTwentieth :
      207 / 400 < Real.sin (11 / 20 : ℝ) ∧
        Real.sin (11 / 20 : ℝ) < 53 / 100 := by
    have hBound :=
      Real.sin_bound (x := (11 / 20 : ℝ)) (by norm_num)
    rw [abs_le] at hBound
    norm_num [abs_of_nonneg] at hBound ⊢
    constructor <;> linarith
  have hSineFiftySevenHundredths :
      533 / 1000 < Real.sin (57 / 100 : ℝ) ∧
        Real.sin (57 / 100 : ℝ) < 109 / 200 := by
    have hBound :=
      Real.sin_bound (x := (57 / 100 : ℝ)) (by norm_num)
    rw [abs_le] at hBound
    norm_num [abs_of_nonneg] at hBound ⊢
    constructor <;> linarith
  have hSineElevenFourths :
      1 / 3 < Real.sin (11 / 4 : ℝ) := by
    rw [show (11 / 4 : ℝ) = 5 * (11 / 20) by norm_num, hSinFive]
    let s := Real.sin (11 / 20 : ℝ)
    have hLower : 207 / 400 < s :=
      hSineElevenTwentieth.1
    have hUpper : s < 53 / 100 :=
      hSineElevenTwentieth.2
    have hSquareUpper :
        s ^ 2 < (53 / 100 : ℝ) ^ 2 := by
      nlinarith
    have hCoefficient :
        16 * (s ^ 2 + (53 / 100 : ℝ) ^ 2) - 20 < 0 := by
      nlinarith [sq_nonneg s]
    have hFactor :
        16 * (53 / 100 : ℝ) ^ 4 -
            20 * (53 / 100 : ℝ) ^ 2 + 5 <
          16 * s ^ 4 - 20 * s ^ 2 + 5 := by
      have hProduct :=
        mul_pos (sub_pos.mpr hSquareUpper) (neg_pos.mpr hCoefficient)
      nlinarith [sq_nonneg (s ^ 2 - (53 / 100 : ℝ) ^ 2)]
    have hFactorPositive :
        0 < 16 * (53 / 100 : ℝ) ^ 4 -
          20 * (53 / 100 : ℝ) ^ 2 + 5 := by
      norm_num
    have hProductOne :=
      mul_pos (sub_pos.mpr hLower) (lt_trans hFactorPositive hFactor)
    have hProductTwo :=
      mul_pos (by norm_num : (0 : ℝ) < 207 / 400)
        (sub_pos.mpr hFactor)
    norm_num at hProductOne hProductTwo ⊢
    nlinarith
  have hSineFiftySevenTwentieth :
      0 < Real.sin (57 / 20 : ℝ) ∧
        Real.sin (57 / 20 : ℝ) < 1 / 3 := by
    rw [show (57 / 20 : ℝ) = 5 * (57 / 100) by norm_num, hSinFive]
    let s := Real.sin (57 / 100 : ℝ)
    have hLower : 533 / 1000 < s :=
      hSineFiftySevenHundredths.1
    have hUpper : s < 109 / 200 :=
      hSineFiftySevenHundredths.2
    have hSquareLower :
        (533 / 1000 : ℝ) ^ 2 < s ^ 2 := by
      nlinarith
    have hSquareUpper :
        s ^ 2 < (109 / 200 : ℝ) ^ 2 := by
      nlinarith
    have hCoefficientLower :
        16 * (s ^ 2 + (533 / 1000 : ℝ) ^ 2) - 20 < 0 := by
      nlinarith [sq_nonneg s]
    have hFactorUpper :
        16 * s ^ 4 - 20 * s ^ 2 + 5 <
          16 * (533 / 1000 : ℝ) ^ 4 -
            20 * (533 / 1000 : ℝ) ^ 2 + 5 := by
      have hProduct :=
        mul_neg_of_pos_of_neg
          (sub_pos.mpr hSquareLower) hCoefficientLower
      nlinarith [sq_nonneg (s ^ 2 - (533 / 1000 : ℝ) ^ 2)]
    have hCoefficientUpper :
        16 * (s ^ 2 + (109 / 200 : ℝ) ^ 2) - 20 < 0 := by
      nlinarith [sq_nonneg s]
    have hFactorLower :
        16 * (109 / 200 : ℝ) ^ 4 -
            20 * (109 / 200 : ℝ) ^ 2 + 5 <
          16 * s ^ 4 - 20 * s ^ 2 + 5 := by
      have hProduct :=
        mul_pos (sub_pos.mpr hSquareUpper)
          (neg_pos.mpr hCoefficientUpper)
      nlinarith [sq_nonneg (s ^ 2 - (109 / 200 : ℝ) ^ 2)]
    have hFactorPositive :
        0 < 16 * (109 / 200 : ℝ) ^ 4 -
          20 * (109 / 200 : ℝ) ^ 2 + 5 := by
      norm_num
    have hPositiveProduct :=
      mul_pos (by norm_num at hLower ⊢; linarith : 0 < s)
        (lt_trans hFactorPositive hFactorLower)
    have hProductOne :=
      mul_pos (sub_pos.mpr hUpper)
        (lt_trans hFactorPositive hFactorLower)
    have hProductTwo :=
      mul_pos (by norm_num : (0 : ℝ) < 109 / 200)
        (sub_pos.mpr hFactorUpper)
    constructor
    · nlinarith
    · norm_num at hProductOne hProductTwo ⊢
      nlinarith
  have hFiftySevenTwentiethBelowPi :
      (57 / 20 : ℝ) < Real.pi := by
    by_contra hNotBelow
    have hDifferenceNonnegative :
        0 ≤ (57 / 20 : ℝ) - Real.pi :=
      sub_nonneg.mpr (le_of_not_gt hNotBelow)
    have hDifferenceBelowPi :
        (57 / 20 : ℝ) - Real.pi ≤ Real.pi := by
      nlinarith [Real.two_le_pi]
    have hSineDifferenceNonnegative :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        hDifferenceNonnegative hDifferenceBelowPi
    rw [Real.sin_sub_pi] at hSineDifferenceNonnegative
    linarith [hSineFiftySevenTwentieth.1]
  have hPhaseBelowPi :
      setup.phaseOffsetRadians < Real.pi := by
    have hArcsinPositive :
        0 < Real.arcsin (1 / 3 : ℝ) := by
      rw [Real.arcsin_pos]
      norm_num
    linarith
  have hPiDivTwoBelowPhase :
      Real.pi / 2 < setup.phaseOffsetRadians := by
    have hArcsinBelowPiDivTwo :
        Real.arcsin (1 / 3 : ℝ) < Real.pi / 2 := by
      rw [Real.arcsin_lt_pi_div_two]
      norm_num
    linarith
  have hElevenFourthsBelowPhase :
      (11 / 4 : ℝ) < setup.phaseOffsetRadians := by
    by_contra hNotBelow
    have hEndpointComplement :
        Real.pi - (11 / 4 : ℝ) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [Real.pi_pos]
      · nlinarith [Real.pi_le_four]
    have hPhaseComplement :
        Real.pi - setup.phaseOffsetRadians ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hMonotone :=
      Real.strictMonoOn_sin.monotoneOn
        hEndpointComplement hPhaseComplement
        (show Real.pi - (11 / 4 : ℝ) ≤
            Real.pi - setup.phaseOffsetRadians by
          linarith)
    rw [Real.sin_pi_sub, Real.sin_pi_sub, hPhaseSine] at hMonotone
    linarith [hSineElevenFourths]
  have hPhaseBelowFiftySevenTwentieth :
      setup.phaseOffsetRadians < (57 / 20 : ℝ) := by
    by_contra hNotBelow
    have hPhaseComplement :
        Real.pi - setup.phaseOffsetRadians ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hEndpointComplement :
        Real.pi - (57 / 20 : ℝ) ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [Real.pi_pos]
      · nlinarith [Real.pi_le_four]
    have hMonotone :=
      Real.strictMonoOn_sin.monotoneOn
        hPhaseComplement hEndpointComplement
        (show Real.pi - setup.phaseOffsetRadians ≤
            Real.pi - (57 / 20 : ℝ) by
          linarith)
    rw [Real.sin_pi_sub, Real.sin_pi_sub, hPhaseSine] at hMonotone
    linarith [hSineFiftySevenTwentieth.2]
  have hDisplayedDistance :
      |setup.phaseOffsetRadians - (14 / 5 : ℝ)| < 1 / 20 := by
    rw [abs_lt]
    constructor <;> linarith
  have hDisplayed :
      MatchesDisplayedPhase
        setup.phaseOffsetRadians recordedDatasetAnswer := by
    exact hDisplayedDistance
  have hNearest :
      ∀ choice : AnswerChoice,
        |setup.phaseOffsetRadians - recordedDatasetAnswer.phaseRadians| ≤
          |setup.phaseOffsetRadians - choice.phaseRadians| := by
    intro choice
    change |setup.phaseOffsetRadians - (14 / 5 : ℝ)| ≤
      |setup.phaseOffsetRadians - choice.phaseRadians|
    cases choice with
    | A =>
        calc
          |setup.phaseOffsetRadians - (14 / 5 : ℝ)| ≤ 1 / 20 :=
            le_of_lt hDisplayedDistance
          _ ≤ setup.phaseOffsetRadians - 2 / 5 := by
            linarith
          _ = |setup.phaseOffsetRadians - 2 / 5| := by
            rw [abs_of_pos]
            linarith
    | B =>
        calc
          |setup.phaseOffsetRadians - (14 / 5 : ℝ)| ≤ 1 / 20 :=
            le_of_lt hDisplayedDistance
          _ ≤ setup.phaseOffsetRadians - 7 / 10 := by
            linarith
          _ = |setup.phaseOffsetRadians - 7 / 10| := by
            rw [abs_of_pos]
            linarith
    | C =>
        calc
          |setup.phaseOffsetRadians - (14 / 5 : ℝ)| ≤ 1 / 20 :=
            le_of_lt hDisplayedDistance
          _ ≤ setup.phaseOffsetRadians - 7 / 5 := by
            linarith
          _ = |setup.phaseOffsetRadians - 7 / 5| := by
            rw [abs_of_pos]
            linarith
    | D => exact le_rfl
  exact ⟨hPhaseExact, hDisplayed, hNearest⟩

end PhyXMiniProblems.ProblemPhyXMini0300
