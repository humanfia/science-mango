import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0230

open Dimension

/-!
# Maximum acceleration read from a spring-motion graph

The primary figure is a displacement-versus-time graph for an object attached
to a spring.  It has horizontal label `t (s)`, vertical label `x (cm)`, and
marked displacement samples

`(0, 0), (1, 2), (2, 0), (3, -2), (4, 0), (5, 2), (6, 0)`.

In particular, the two consecutive positive peaks occur at `t = 1 s` and
`t = 5 s`, so the period read from the image is `4 s`.  The auxiliary caption's
claim that a cycle runs from `0` to `6` conflicts with the primary image and is
not used.  The answer readouts are interpreted in `cm / s²`, the coherent
acceleration unit determined by the two plotted axis units.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A signed displacement or oscillation amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time or period. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- Angular frequency; radians are dimensionless, so its dimension is inverse time. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A signed one-dimensional acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a physical time in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := unit}).val

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  (frequency {UnitChoices.SI with time := unit}).val

/-- Read acceleration in a coherent selected length/time unit system. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration
    {UnitChoices.SI with length := lengthUnit, time := timeUnit}).val

/-! ## Primary-figure labels and samples -/

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

/-- The seven black sample points explicitly marked in the primary image. -/
inductive FigureSample where
  | t0
  | t1
  | t2
  | t3
  | t4
  | t5
  | t6
  deriving DecidableEq, Repr

/-- Printed time coordinate, in seconds, of each marked point. -/
def figureTimeInSeconds : FigureSample → ℝ
  | .t0 => 0
  | .t1 => 1
  | .t2 => 2
  | .t3 => 3
  | .t4 => 4
  | .t5 => 5
  | .t6 => 6

/-- Printed displacement coordinate, in centimeters, of each marked point. -/
def figureDisplacementInCentimeters : FigureSample → ℝ
  | .t0 => 0
  | .t1 => 2
  | .t2 => 0
  | .t3 => -2
  | .t4 => 0
  | .t5 => 2
  | .t6 => 0

/-- The qualitative restoring element named in the problem statement. -/
inductive RestoringElement where
  | spring
  deriving DecidableEq, Repr

/-- The motion regime asserted by the problem statement. -/
inductive MotionRegime where
  | simpleHarmonic
  deriving DecidableEq, Repr

/-- Axis labels, units, and qualitative rendering features of the graph. -/
structure DisplacementTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  horizontalTimeUnit : TimeUnit
  verticalLengthUnit : LengthUnit
  sampleTime : FigureSample → TimeQuantity
  gridlinesVisible : Bool
  sinusoidalCurveVisible : Bool

/-!
The spring oscillator and its dimensionful kinematic quantities.

The acceleration function is not defined from the requested answer.  It is an
independent physical quantity linked to displacement only by the governing
simple-harmonic-motion laws below.
-/
structure SpringOscillationSetup where
  restoringElement : RestoringElement
  motionRegime : MotionRegime
  graph : DisplacementTimeGraph
  amplitude : LengthQuantity
  period : TimeQuantity
  angularFrequency : AngularFrequencyQuantity
  displacement : TimeQuantity → LengthQuantity
  acceleration : TimeQuantity → AccelerationQuantity

/-!
Scenario and primary-image evidence.  The amplitude and period here are graph
readouts, not conclusions about acceleration.  The period is the separation
of the consecutive positive peaks at samples `t1` and `t5`.
-/
structure MatchesSpringMotionFigure (setup : SpringOscillationSetup) : Prop where
  attachedToSpring : setup.restoringElement = .spring
  statedMotionRegime : setup.motionRegime = .simpleHarmonic
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .displacement_x
  horizontalAxisUnit :
    setup.graph.horizontalTimeUnit = TimeUnit.seconds
  verticalAxisUnit :
    setup.graph.verticalLengthUnit = LengthUnit.centimeters
  gridlinesShown : setup.graph.gridlinesVisible = true
  sinusoidalCurveShown : setup.graph.sinusoidalCurveVisible = true
  markedTimeCoordinates :
    ∀ sample : FigureSample,
      timeReadout TimeUnit.seconds (setup.graph.sampleTime sample) =
        figureTimeInSeconds sample
  markedDisplacementCoordinates :
    ∀ sample : FigureSample,
      lengthReadout LengthUnit.centimeters
          (setup.displacement (setup.graph.sampleTime sample)) =
        figureDisplacementInCentimeters sample
  amplitudeReadout :
    lengthReadout LengthUnit.centimeters setup.amplitude = 2
  peakToPeakPeriodReadout :
    timeReadout TimeUnit.seconds setup.period =
      timeReadout TimeUnit.seconds (setup.graph.sampleTime .t5) -
        timeReadout TimeUnit.seconds (setup.graph.sampleTime .t1)
  periodReadout : timeReadout TimeUnit.seconds setup.period = 4

/-- Positivity conditions for the nondegenerate oscillator shown in the graph. -/
structure HasPhysicalSpringMotionParameters
    (setup : SpringOscillationSetup) : Prop where
  amplitudePositive :
    0 < lengthReadout LengthUnit.centimeters setup.amplitude
  periodPositive : 0 < timeReadout TimeUnit.seconds setup.period
  angularFrequencyPositive :
    0 < angularFrequencyReadout TimeUnit.seconds setup.angularFrequency

/-!
Governing laws for the chosen phase of the simple harmonic motion.

The graph crosses equilibrium at `t = 0` while moving toward its positive
peak, hence the sine phase.  The other fields state `ω = 2π/T` and
`a = -ω²x` in the coherent centimeter/second readouts.  No maximum
acceleration or answer-choice value occurs in this premise structure.
-/
structure SatisfiesSimpleHarmonicMotionLaws
    (setup : SpringOscillationSetup) : Prop where
  angularFrequencyPeriodLaw :
    angularFrequencyReadout TimeUnit.seconds setup.angularFrequency =
      2 * Real.pi / timeReadout TimeUnit.seconds setup.period
  harmonicDisplacementLaw :
    ∀ time : TimeQuantity,
      lengthReadout LengthUnit.centimeters (setup.displacement time) =
        lengthReadout LengthUnit.centimeters setup.amplitude *
          Real.sin
            (angularFrequencyReadout TimeUnit.seconds
                setup.angularFrequency *
              timeReadout TimeUnit.seconds time)
  harmonicAccelerationLaw :
    ∀ time : TimeQuantity,
      accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          (setup.acceleration time) =
        -(angularFrequencyReadout TimeUnit.seconds
            setup.angularFrequency) ^ 2 *
          lengthReadout LengthUnit.centimeters (setup.displacement time)

/-! ## Requested maximum and displayed answers -/

/-- A physical acceleration magnitude that is attained and bounds the motion. -/
def IsMaximumAccelerationMagnitude
    (setup : SpringOscillationSetup)
    (maximumAcceleration : AccelerationQuantity) : Prop :=
  0 ≤ accelerationReadout LengthUnit.centimeters TimeUnit.seconds
      maximumAcceleration ∧
    (∀ time : TimeQuantity,
      |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          (setup.acceleration time)| ≤
        accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          maximumAcceleration) ∧
    ∃ time : TimeQuantity,
      |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          (setup.acceleration time)| =
        accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          maximumAcceleration

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed answer readouts, inferred to be in centimeters per second squared. -/
def answerChoiceInCentimetersPerSecondSquared : AnswerChoice → ℝ
  | .A => 4.39
  | .B => 5.93
  | .C => 3.93
  | .D => 4.93

/-!
The graph has amplitude `2 cm` and period `4 s`.  Simple harmonic motion
therefore has maximum acceleration magnitude

`A ω² = A (2π/T)² = π² / 2 cm/s² ≈ 4.9348 cm/s²`,

which rounds to the displayed choice D (`4.93 cm/s²`) and is no farther from
D than from any other displayed choice.
-/
theorem problem_phyx_mini_0230
    (setup : SpringOscillationSetup)
    (hFigure : MatchesSpringMotionFigure setup)
    (hPhysical : HasPhysicalSpringMotionParameters setup)
    (hLaws : SatisfiesSimpleHarmonicMotionLaws setup) :
    ∃ maximumAcceleration : AccelerationQuantity,
      IsMaximumAccelerationMagnitude setup maximumAcceleration ∧
        accelerationReadout LengthUnit.centimeters TimeUnit.seconds
            maximumAcceleration =
          lengthReadout LengthUnit.centimeters setup.amplitude *
            (angularFrequencyReadout TimeUnit.seconds
              setup.angularFrequency) ^ 2 ∧
        accelerationReadout LengthUnit.centimeters TimeUnit.seconds
            maximumAcceleration =
          lengthReadout LengthUnit.centimeters setup.amplitude *
            (2 * Real.pi /
              timeReadout TimeUnit.seconds setup.period) ^ 2 ∧
        accelerationReadout LengthUnit.centimeters TimeUnit.seconds
            maximumAcceleration = Real.pi ^ 2 / 2 ∧
        |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
              maximumAcceleration -
            answerChoiceInCentimetersPerSecondSquared .D| < 0.005 ∧
        ∀ choice : AnswerChoice,
          |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
                maximumAcceleration -
              answerChoiceInCentimetersPerSecondSquared .D| ≤
            |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
                maximumAcceleration -
              answerChoiceInCentimetersPerSecondSquared choice| := by
  have hAmplitude :
      lengthReadout LengthUnit.centimeters setup.amplitude = 2 :=
    hFigure.amplitudeReadout
  have hPeriod :
      timeReadout TimeUnit.seconds setup.period = 4 :=
    hFigure.periodReadout
  have hOmega :
      angularFrequencyReadout TimeUnit.seconds setup.angularFrequency =
        Real.pi / 2 := by
    rw [hLaws.angularFrequencyPeriodLaw, hPeriod]
    ring
  have hPiPositive : 0 < Real.pi := by
    have hFrequencyPositive := hPhysical.angularFrequencyPositive
    rw [hOmega] at hFrequencyPositive
    linarith
  let accelerationUnit : UnitChoices :=
    {UnitChoices.SI with
      length := LengthUnit.centimeters, time := TimeUnit.seconds}
  let maximumAcceleration : AccelerationQuantity :=
    CarriesDimension.toDimensionful accelerationUnit
      (⟨Real.pi ^ 2 / 2⟩ :
        WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
  have hMaximumReadout :
      accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          maximumAcceleration =
        Real.pi ^ 2 / 2 := by
    simp [maximumAcceleration, accelerationReadout, accelerationUnit,
      CarriesDimension.toDimensionful_apply_apply]
  have hMaximum :
      IsMaximumAccelerationMagnitude setup maximumAcceleration := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hMaximumReadout]
      positivity
    · intro time
      rw [hMaximumReadout, hLaws.harmonicAccelerationLaw,
        hLaws.harmonicDisplacementLaw, hAmplitude, hOmega]
      have hSinBound := Real.abs_sin_le_one
        ((Real.pi / 2) * timeReadout TimeUnit.seconds time)
      rw [abs_mul, abs_neg, abs_mul, abs_pow, abs_div,
        abs_of_pos hPiPositive]
      norm_num
      nlinarith [sq_nonneg Real.pi]
    · refine ⟨setup.graph.sampleTime .t1, ?_⟩
      rw [hLaws.harmonicAccelerationLaw,
        hFigure.markedDisplacementCoordinates .t1,
        figureDisplacementInCentimeters, hOmega, hMaximumReadout]
      rw [abs_of_nonpos]
      · ring
      · nlinarith [sq_nonneg Real.pi]
  have hFormulaFromAmplitudeAndFrequency :
      accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          maximumAcceleration =
        lengthReadout LengthUnit.centimeters setup.amplitude *
          (angularFrequencyReadout TimeUnit.seconds
            setup.angularFrequency) ^ 2 := by
    rw [hMaximumReadout, hAmplitude, hOmega]
    ring
  have hFormulaFromAmplitudeAndPeriod :
      accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          maximumAcceleration =
        lengthReadout LengthUnit.centimeters setup.amplitude *
          (2 * Real.pi /
            timeReadout TimeUnit.seconds setup.period) ^ 2 := by
    rw [hMaximumReadout, hAmplitude, hPeriod]
    ring
  -- The exact half-angle formula at `π / 256`, together with a fourth-order
  -- sine bound, supplies the decimal bounds needed for the recorded rounding.
  let r1 : ℝ := √2
  let r2 : ℝ := √(2 + r1)
  let r3 : ℝ := √(2 + r2)
  let r4 : ℝ := √(2 + r3)
  let r5 : ℝ := √(2 + r4)
  let r6 : ℝ := √(2 + r5)
  have hr1_nonneg : 0 ≤ r1 := by simp [r1]
  have hr2_nonneg : 0 ≤ r2 := by simp [r2]
  have hr3_nonneg : 0 ≤ r3 := by simp [r3]
  have hr4_nonneg : 0 ≤ r4 := by simp [r4]
  have hr5_nonneg : 0 ≤ r5 := by simp [r5]
  have hr6_nonneg : 0 ≤ r6 := by simp [r6]
  have hr1_sq : r1 ^ 2 = 2 := by simp [r1]
  have hr2_sq : r2 ^ 2 = 2 + r1 := by
    change √(2 + r1) ^ 2 = 2 + r1
    rw [Real.sq_sqrt (by positivity)]
  have hr3_sq : r3 ^ 2 = 2 + r2 := by
    change √(2 + r2) ^ 2 = 2 + r2
    rw [Real.sq_sqrt (by positivity)]
  have hr4_sq : r4 ^ 2 = 2 + r3 := by
    change √(2 + r3) ^ 2 = 2 + r3
    rw [Real.sq_sqrt (by positivity)]
  have hr5_sq : r5 ^ 2 = 2 + r4 := by
    change √(2 + r4) ^ 2 = 2 + r4
    rw [Real.sq_sqrt (by positivity)]
  have hr6_sq : r6 ^ 2 = 2 + r5 := by
    change √(2 + r5) ^ 2 = 2 + r5
    rw [Real.sq_sqrt (by positivity)]
  have hr1_lower : (14142135623 : ℝ) / 10000000000 < r1 := by
    nlinarith only [hr1_sq, hr1_nonneg]
  have hr2_lower : (18477590650 : ℝ) / 10000000000 < r2 := by
    nlinarith only [hr2_sq, hr2_nonneg, hr1_lower]
  have hr3_lower : (19615705608 : ℝ) / 10000000000 < r3 := by
    nlinarith only [hr3_sq, hr3_nonneg, hr2_lower]
  have hr4_lower : (19903694533 : ℝ) / 10000000000 < r4 := by
    nlinarith only [hr4_sq, hr4_nonneg, hr3_lower]
  have hr5_lower : (19975909123 : ℝ) / 10000000000 < r5 := by
    nlinarith only [hr5_sq, hr5_nonneg, hr4_lower]
  have hr6_lower : (19993976373 : ℝ) / 10000000000 < r6 := by
    nlinarith only [hr6_sq, hr6_nonneg, hr5_lower]
  have hr1_upper : r1 < (141421357 : ℝ) / 100000000 := by
    nlinarith only [hr1_sq, hr1_nonneg]
  have hr2_upper : r2 < (184775907 : ℝ) / 100000000 := by
    nlinarith only [hr2_sq, hr2_nonneg, hr1_upper]
  have hr3_upper : r3 < (196157057 : ℝ) / 100000000 := by
    nlinarith only [hr3_sq, hr3_nonneg, hr2_upper]
  have hr4_upper : r4 < (199036946 : ℝ) / 100000000 := by
    nlinarith only [hr4_sq, hr4_nonneg, hr3_upper]
  have hr5_upper : r5 < (199759092 : ℝ) / 100000000 := by
    nlinarith only [hr5_sq, hr5_nonneg, hr4_upper]
  have hr6_upper : r6 < (199939764 : ℝ) / 100000000 := by
    nlinarith only [hr6_sq, hr6_nonneg, hr5_upper]
  have hr6_series : Real.sqrtTwoAddSeries 0 6 = r6 := by
    simp [Real.sqrtTwoAddSeries, r1, r2, r3, r4, r5, r6]
  have hRadicalNonneg : 0 ≤ √(2 - r6) := Real.sqrt_nonneg _
  have hRadicalSq : (√(2 - r6)) ^ 2 = 2 - r6 := by
    rw [Real.sq_sqrt]
    nlinarith only [hr6_upper]
  have hSinLower :
      (122715 : ℝ) / 10000000 <
        √(2 - Real.sqrtTwoAddSeries 0 6) / 2 := by
    rw [hr6_series]
    nlinarith only [hr6_upper, hRadicalNonneg, hRadicalSq]
  have hSinUpper :
      √(2 - Real.sqrtTwoAddSeries 0 6) / 2 <
        (1227154 : ℝ) / 100000000 := by
    rw [hr6_series]
    nlinarith only [hr6_lower, hRadicalNonneg, hRadicalSq]
  let x : ℝ := Real.pi / 256
  have hx_def : x = Real.pi / 256 := rfl
  have hx_nonneg : 0 ≤ x := by
    rw [hx_def]
    exact div_nonneg Real.pi_nonneg (by norm_num)
  have hx_le_coarse : x ≤ (1 : ℝ) / 64 := by
    rw [hx_def]
    nlinarith only [Real.pi_le_four]
  have hx_abs_le_one : |x| ≤ 1 := by
    rw [abs_of_nonneg hx_nonneg]
    nlinarith only [hx_le_coarse]
  have hTaylor := Real.sin_bound hx_abs_le_one
  have hSinFormula :
      Real.sin x =
        √(2 - Real.sqrtTwoAddSeries 0 6) / 2 := by
    rw [hx_def]
    convert Real.sin_pi_over_two_pow_succ 6 using 1
    all_goals norm_num
  rw [hSinFormula, abs_le, abs_of_nonneg hx_nonneg] at hTaylor
  have hx3_nonneg : 0 ≤ x ^ 3 := by positivity
  have hx4_le_coarse : x ^ 4 ≤ ((1 : ℝ) / 64) ^ 4 := by
    gcongr
  have hx3_le_coarse : x ^ 3 ≤ ((1 : ℝ) / 64) ^ 3 := by
    gcongr
  have hPiLower : (3.1415 : ℝ) < Real.pi := by
    nlinarith only [hTaylor.2, hSinLower, hx_def, hx3_nonneg,
      hx4_le_coarse]
  have hx_le_first : x < (3.142 : ℝ) / 256 := by
    nlinarith only [hTaylor.1, hSinUpper, hx3_le_coarse,
      hx4_le_coarse]
  have hx3_le_fine : x ^ 3 ≤ ((3.142 : ℝ) / 256) ^ 3 := by
    gcongr
  have hx4_le_fine : x ^ 4 ≤ ((3.142 : ℝ) / 256) ^ 4 := by
    gcongr
  have hPiUpper : Real.pi < (3.1416 : ℝ) := by
    nlinarith only [hTaylor.1, hSinUpper, hx_def, hx3_le_fine,
      hx4_le_fine]
  have hPiSquareLower : (3.1415 : ℝ) ^ 2 < Real.pi ^ 2 :=
    (sq_lt_sq₀ (by norm_num) Real.pi_nonneg).2 hPiLower
  have hPiSquareUpper : Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 :=
    (sq_lt_sq₀ Real.pi_nonneg (by norm_num)).2 hPiUpper
  have hValueLower : (4.9345 : ℝ) < Real.pi ^ 2 / 2 := by
    nlinarith only [hPiSquareLower]
  have hValueUpper : Real.pi ^ 2 / 2 < (4.9349 : ℝ) := by
    nlinarith only [hPiSquareUpper]
  have hNearChoiceD :
      |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
          maximumAcceleration -
        answerChoiceInCentimetersPerSecondSquared .D| < 0.005 := by
    rw [hMaximumReadout, answerChoiceInCentimetersPerSecondSquared,
      abs_lt]
    constructor <;> nlinarith only [hValueLower, hValueUpper]
  have hChoiceDClosest :
      ∀ choice : AnswerChoice,
        |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
              maximumAcceleration -
            answerChoiceInCentimetersPerSecondSquared .D| ≤
          |accelerationReadout LengthUnit.centimeters TimeUnit.seconds
              maximumAcceleration -
            answerChoiceInCentimetersPerSecondSquared choice| := by
    intro choice
    rw [hMaximumReadout]
    cases choice
    case A =>
      simp only [answerChoiceInCentimetersPerSecondSquared]
      rw [abs_of_nonneg (by linarith only [hValueLower]),
        abs_of_nonneg (by linarith only [hValueLower])]
      linarith only [hValueLower, hValueUpper]
    case B =>
      simp only [answerChoiceInCentimetersPerSecondSquared]
      rw [abs_of_nonneg (by linarith only [hValueLower]),
        abs_of_nonpos (by linarith only [hValueUpper])]
      linarith only [hValueLower, hValueUpper]
    case C =>
      simp only [answerChoiceInCentimetersPerSecondSquared]
      rw [abs_of_nonneg (by linarith only [hValueLower]),
        abs_of_nonneg (by linarith only [hValueLower])]
      linarith only [hValueLower, hValueUpper]
    case D =>
      rfl
  exact ⟨maximumAcceleration, hMaximum,
    hFormulaFromAmplitudeAndFrequency,
    hFormulaFromAmplitudeAndPeriod, hMaximumReadout,
    hNearChoiceD, hChoiceDClosest⟩

end PhyXMiniProblems.ProblemPhyXMini0230
