import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0576

open Dimension

/-!
# Activity of an exponentially decaying radioactive sample

The supplied graph plots the expected number `N` of undecayed parent nuclei
against elapsed time `t`. Its symbolic scales are `N_s = 2.00 × 10^6` and
`t_s = 10.0 s`; the ten-by-ten grid places the half-height crossing two
horizontal divisions after the origin, hence at `2 s`. The question asks for
the activity at `27 s`.

Time, decay constants, and activities below are unit-independent Physlib
quantities. Real numbers are used only for named-unit readouts, dimensionless
expected nucleus counts, normalized grid coordinates, and displayed numerical
answers. The continuous parent population is an expectation in the standard
exponential-decay model, rather than an assertion that a literal nucleus count
can be fractional.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical elapsed time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative radioactive decay constant, carrying inverse-time dimension. -/
abbrev DecayConstantQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative radioactive activity, carrying inverse-time dimension. -/
abbrev ActivityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical elapsed time in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  ((time {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a decay constant in inverse units of a selected time unit. -/
def decayConstantReadout
    (unit : TimeUnit) (decayConstant : DecayConstantQuantity) : ℝ :=
  ((decayConstant {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read an activity as decays per selected time unit. -/
def activityReadout
    (unit : TimeUnit) (activity : ActivityQuantity) : ℝ :=
  ((activity {UnitChoices.SI with time := unit}).val : ℝ)

/-- Seconds readout of a physical elapsed time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Per-second readout of a radioactive decay constant. -/
def decayConstantInPerSecond
    (decayConstant : DecayConstantQuantity) : ℝ :=
  decayConstantReadout TimeUnit.seconds decayConstant

/-- Becquerel readout of an activity; one becquerel is one decay per second. -/
def activityInBecquerels (activity : ActivityQuantity) : ℝ :=
  activityReadout TimeUnit.seconds activity

/-! ## Radioactive sample and primary-image geometry -/

/-!
An idealized radioactive sample. Its expected parent population and activity
at a time are independent observables here; the governing laws below relate
them without defining either observable to be the requested answer.
-/
structure RadioactiveSample where
  initialExpectedParentCount : NNReal
  expectedParentCountAt : TimeQuantity → NNReal
  decayConstant : DecayConstantQuantity
  activityAt : TimeQuantity → ActivityQuantity

/-- The color of the curve visible in the supplied bitmap. -/
inductive DecayCurveColor where
  | magenta
  deriving DecidableEq, Repr

/-- Qualitative vertical trend of the plotted parent population. -/
inductive DecayCurveTrend where
  | decreasing
  deriving DecidableEq, Repr

/-- Physical model represented by the shape of the plotted curve. -/
inductive DecayCurveShape where
  | exponential
  deriving DecidableEq, Repr

/-!
Literal labels and grid information read from the primary image. Grid indices
are normalized diagram coordinates, not physical times or parent counts.
-/
structure ParentDecayFigure where
  horizontalAxisLabel : String
  verticalAxisLabel : String
  horizontalScaleLabel : String
  verticalScaleLabel : String
  originLabelShown : Bool
  horizontalGridIntervalCount : ℕ
  verticalGridIntervalCount : ℕ
  curveColor : DecayCurveColor
  curveTrend : DecayCurveTrend
  curveShape : DecayCurveShape
  curveStartsAtTopLeft : Bool
  curveApproachesTimeAxis : Bool
  halfHeightCrossingColumn : ℕ
  halfHeightRowFromBottom : ℕ

/-!
The sample, the two axis scales, the queried time, and the half-life point read
from the graph. Each physical quantity remains independent of its scalar
readout and of the answer choices.
-/
structure RadioactiveDecaySetup where
  sample : RadioactiveSample
  parentCountAxisScale : NNReal
  timeAxisScale : TimeQuantity
  halfLifeReadFromFigure : TimeQuantity
  queryTime : TimeQuantity
  figure : ParentDecayFigure

/-! ## Problem data and figure-derived evidence -/

/-- Numerical scales and query time stated alongside the graph. -/
structure MatchesProblemReadouts (setup : RadioactiveDecaySetup) : Prop where
  parentCountScale : setup.parentCountAxisScale = 2000000
  timeScaleSeconds : timeInSeconds setup.timeAxisScale = 10
  queryTimeSeconds : timeInSeconds setup.queryTime = 27

/-!
Primary-image evidence: the axes are labelled `t` and `N`, the endpoint scales
are `t_s` and `N_s`, and a magenta decreasing exponential occupies a ten-by-ten
grid. The curve crosses half of `N_s` at horizontal grid column two and
vertical row five. The last two fields interpret that calibrated crossing as
the sample's half-population point; neither field concerns the requested
activity at `27 s`.
-/
structure MatchesSuppliedParentDecayFigure
    (setup : RadioactiveDecaySetup) : Prop where
  horizontalAxis : setup.figure.horizontalAxisLabel = "t"
  verticalAxis : setup.figure.verticalAxisLabel = "N"
  horizontalScale : setup.figure.horizontalScaleLabel = "t_s"
  verticalScale : setup.figure.verticalScaleLabel = "N_s"
  originShown : setup.figure.originLabelShown = true
  tenHorizontalIntervals : setup.figure.horizontalGridIntervalCount = 10
  tenVerticalIntervals : setup.figure.verticalGridIntervalCount = 10
  magentaCurve : setup.figure.curveColor = .magenta
  decreasingCurve : setup.figure.curveTrend = .decreasing
  exponentialCurve : setup.figure.curveShape = .exponential
  startsAtTopLeft : setup.figure.curveStartsAtTopLeft = true
  approachesTimeAxis : setup.figure.curveApproachesTimeAxis = true
  halfHeightAtColumnTwo : setup.figure.halfHeightCrossingColumn = 2
  halfHeightAtRowFive : setup.figure.halfHeightRowFromBottom = 5
  initialPopulationIsVerticalScale :
    setup.sample.initialExpectedParentCount = setup.parentCountAxisScale
  halfLifeLocatedByGrid :
    timeInSeconds setup.halfLifeReadFromFigure =
      (setup.figure.halfHeightCrossingColumn : ℝ) /
        setup.figure.horizontalGridIntervalCount *
          timeInSeconds setup.timeAxisScale
  curveAtHalfPopulation :
    setup.sample.expectedParentCountAt setup.halfLifeReadFromFigure =
      setup.parentCountAxisScale / 2

/-- Positive, nondegenerate parameters of the radioactive-decay scenario. -/
structure HasPhysicalRadioactiveParameters
    (setup : RadioactiveDecaySetup) : Prop where
  populationScalePositive : 0 < (setup.parentCountAxisScale : ℝ)
  timeScalePositive : 0 < timeInSeconds setup.timeAxisScale
  halfLifePositive : 0 < timeInSeconds setup.halfLifeReadFromFigure
  queryTimePositive : 0 < timeInSeconds setup.queryTime
  decayConstantPositive :
    0 < decayConstantInPerSecond setup.sample.decayConstant

/-! ## Governing radioactive-decay laws -/

/-!
The standard exponential parent-population law and `A(t) = λ N(t)`. Both are
general governing laws quantified over every elapsed time. In particular,
they do not state a numerical activity at the queried time.
-/
structure SatisfiesRadioactiveDecayLaws
    (setup : RadioactiveDecaySetup) : Prop where
  exponentialParentPopulation : ∀ time : TimeQuantity,
    (setup.sample.expectedParentCountAt time : ℝ) =
      (setup.sample.initialExpectedParentCount : ℝ) *
        Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant *
            timeInSeconds time))
  activityIsDecayRateTimesPopulation : ∀ time : TimeQuantity,
    activityInBecquerels (setup.sample.activityAt time) =
      decayConstantInPerSecond setup.sample.decayConstant *
        (setup.sample.expectedParentCountAt time : ℝ)

/-! ## Answer choices and current target -/

/-- The four answer labels printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Becquerel value printed beside each answer label. -/
def displayedActivityInBecquerels : AnswerChoice → ℝ
  | .A => 30
  | .B => 120
  | .C => 60
  | .D => 6

/-- The answer choices are reported to the nearest whole becquerel. -/
def wholeBecquerelRoundingTolerance : ℝ := 1 / 2

/-!
A displayed choice agrees with the physical prediction when the exact model
activity lies within half a becquerel of the displayed whole-number value.
-/
def IsCorrectRoundedAnswerChoice
    (setup : RadioactiveDecaySetup) (choice : AnswerChoice) : Prop :=
  |activityInBecquerels (setup.sample.activityAt setup.queryTime) -
      displayedActivityInBecquerels choice| ≤
    wholeBecquerelRoundingTolerance

/-!
The graph's two-second half-life fixes `λ = log 2 / 2 s⁻¹`. Combining this
with `N_s = 2.00 × 10^6`, the exponential population law, and `A = λN` gives
the exact model expression below at `27 s`. It lies within half a becquerel
of `60 Bq`, so the recorded answer is choice C.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0576:target`.
-/
theorem activity_at_twenty_seven_seconds_rounds_to_sixty_becquerels
    (setup : RadioactiveDecaySetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedParentDecayFigure setup)
    (hPhysical : HasPhysicalRadioactiveParameters setup)
    (hDecay : SatisfiesRadioactiveDecayLaws setup) :
    activityInBecquerels (setup.sample.activityAt setup.queryTime) =
        (Real.log 2 / 2) * 2000000 *
          Real.exp (-(Real.log 2 / 2 * 27)) ∧
      |activityInBecquerels (setup.sample.activityAt setup.queryTime) - 60| ≤
          wholeBecquerelRoundingTolerance ∧
      IsCorrectRoundedAnswerChoice setup .C := by
  have hHalfLifeSeconds :
      timeInSeconds setup.halfLifeReadFromFigure = 2 := by
    rw [hFigure.halfLifeLocatedByGrid,
      hFigure.halfHeightAtColumnTwo,
      hFigure.tenHorizontalIntervals,
      hReadouts.timeScaleSeconds]
    norm_num
  have hInitialPopulation :
      (setup.sample.initialExpectedParentCount : ℝ) = 2000000 := by
    rw [hFigure.initialPopulationIsVerticalScale, hReadouts.parentCountScale]
    norm_num
  have hHalfPopulation :
      (setup.sample.expectedParentCountAt setup.halfLifeReadFromFigure : ℝ) =
        1000000 := by
    rw [hFigure.curveAtHalfPopulation, hReadouts.parentCountScale]
    norm_num
  have hHalfDecay :=
    hDecay.exponentialParentPopulation setup.halfLifeReadFromFigure
  rw [hHalfPopulation, hInitialPopulation, hHalfLifeSeconds] at hHalfDecay
  have hExpHalf :
      Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant * 2)) =
        (1 : ℝ) / 2 := by
    nlinarith [hHalfDecay]
  have hExpNegLogTwo :
      Real.exp (-(Real.log 2)) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hDecayConstant :
      decayConstantInPerSecond setup.sample.decayConstant =
        Real.log 2 / 2 := by
    have hExponents :=
      Real.exp_injective (hExpHalf.trans hExpNegLogTwo.symm)
    linarith
  have hQueryPopulation :=
    hDecay.exponentialParentPopulation setup.queryTime
  rw [hInitialPopulation, hReadouts.queryTimeSeconds] at hQueryPopulation
  have hActivityExact :
      activityInBecquerels (setup.sample.activityAt setup.queryTime) =
        (Real.log 2 / 2) * 2000000 *
          Real.exp (-(Real.log 2 / 2 * 27)) := by
    calc
      activityInBecquerels (setup.sample.activityAt setup.queryTime) =
          decayConstantInPerSecond setup.sample.decayConstant *
            (setup.sample.expectedParentCountAt setup.queryTime : ℝ) :=
        hDecay.activityIsDecayRateTimesPopulation setup.queryTime
      _ = decayConstantInPerSecond setup.sample.decayConstant *
          (2000000 *
            Real.exp
              (-(decayConstantInPerSecond setup.sample.decayConstant * 27))) := by
        rw [hQueryPopulation]
      _ = (Real.log 2 / 2) * 2000000 *
          Real.exp (-(Real.log 2 / 2 * 27)) := by
        rw [hDecayConstant]
        ring
  have hQueryExponential :
      Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant * 27)) =
        ((1 : ℝ) / 2) ^ 13 *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
    calc
      Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant * 27)) =
          Real.exp
            ((13 : ℝ) *
                (-(decayConstantInPerSecond setup.sample.decayConstant * 2)) +
              (-(decayConstantInPerSecond setup.sample.decayConstant))) := by
        congr 1
        ring
      _ = Real.exp
            ((13 : ℝ) *
              (-(decayConstantInPerSecond setup.sample.decayConstant * 2))) *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
        rw [Real.exp_add]
      _ = (Real.exp
              (-(decayConstantInPerSecond setup.sample.decayConstant * 2))) ^
            13 *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
        simpa using congrArg
          (fun value : ℝ =>
            value *
              Real.exp
                (-(decayConstantInPerSecond setup.sample.decayConstant)))
          (Real.exp_nat_mul
            (-(decayConstantInPerSecond setup.sample.decayConstant * 2)) 13)
      _ = ((1 : ℝ) / 2) ^ 13 *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
        rw [hExpHalf]
  have hExpOneSecondSquare :
      (Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant))) ^ 2 =
        (1 : ℝ) / 2 := by
    calc
      (Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant))) ^ 2 =
          Real.exp
            ((2 : ℝ) *
              (-(decayConstantInPerSecond setup.sample.decayConstant))) := by
        exact (Real.exp_nat_mul
          (-(decayConstantInPerSecond setup.sample.decayConstant)) 2).symm
      _ = Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant * 2)) := by
        congr 1
        ring
      _ = (1 : ℝ) / 2 := hExpHalf
  have hLogTwoLower : (69 / 100 : ℝ) < Real.log 2 := by
    have hExpUpper := Real.exp_bound'
      (x := (69 / 100 : ℝ)) (by norm_num) (by norm_num)
      (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hExpUpper
    have hExpLog : Real.exp (Real.log 2) = (2 : ℝ) :=
      Real.exp_log (by norm_num)
    rw [← Real.exp_lt_exp, hExpLog]
    nlinarith
  have hLogTwoUpper : Real.log 2 < (7 / 10 : ℝ) := by
    have hExpLower := Real.sum_le_exp_of_nonneg
      (x := (7 / 10 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at hExpLower
    have hExpLog : Real.exp (Real.log 2) = (2 : ℝ) :=
      Real.exp_log (by norm_num)
    rw [← Real.exp_lt_exp, hExpLog]
    nlinarith
  have hDecayConstantLower :
      (345 / 1000 : ℝ) <
        decayConstantInPerSecond setup.sample.decayConstant := by
    rw [hDecayConstant]
    nlinarith
  have hDecayConstantUpper :
      decayConstantInPerSecond setup.sample.decayConstant <
        (35 / 100 : ℝ) := by
    rw [hDecayConstant]
    nlinarith
  have hExpOneSecondPositive :
      0 <
        Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant)) :=
    Real.exp_pos _
  have hExpOneSecondLower :
      (707 / 1000 : ℝ) <
        Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
    by_contra h
    have hLe :
        Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) ≤
          (707 / 1000 : ℝ) :=
      le_of_not_gt h
    have hSquareLe :
        (Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant))) ^ 2 ≤
          (707 / 1000 : ℝ) ^ 2 := by
      nlinarith
    rw [hExpOneSecondSquare] at hSquareLe
    norm_num at hSquareLe
  have hExpOneSecondUpper :
      Real.exp
          (-(decayConstantInPerSecond setup.sample.decayConstant)) <
        (708 / 1000 : ℝ) := by
    by_contra h
    have hGe :
        (708 / 1000 : ℝ) ≤
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) :=
      le_of_not_gt h
    have hSquareGe :
        (708 / 1000 : ℝ) ^ 2 ≤
          (Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant))) ^ 2 := by
      nlinarith
    rw [hExpOneSecondSquare] at hSquareGe
    norm_num at hSquareGe
  have hProductLower :
      (345 / 1000 : ℝ) * (707 / 1000 : ℝ) <
        decayConstantInPerSecond setup.sample.decayConstant *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
    calc
      (345 / 1000 : ℝ) * (707 / 1000 : ℝ) <
          decayConstantInPerSecond setup.sample.decayConstant *
            (707 / 1000 : ℝ) := by
        exact mul_lt_mul_of_pos_right hDecayConstantLower (by norm_num)
      _ < decayConstantInPerSecond setup.sample.decayConstant *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
        exact mul_lt_mul_of_pos_left hExpOneSecondLower
          hPhysical.decayConstantPositive
  have hProductUpper :
      decayConstantInPerSecond setup.sample.decayConstant *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) <
        (35 / 100 : ℝ) * (708 / 1000 : ℝ) := by
    calc
      decayConstantInPerSecond setup.sample.decayConstant *
          Real.exp
            (-(decayConstantInPerSecond setup.sample.decayConstant)) <
          (35 / 100 : ℝ) *
            Real.exp
              (-(decayConstantInPerSecond setup.sample.decayConstant)) := by
        exact mul_lt_mul_of_pos_right hDecayConstantUpper
          hExpOneSecondPositive
      _ < (35 / 100 : ℝ) * (708 / 1000 : ℝ) := by
        exact mul_lt_mul_of_pos_left hExpOneSecondUpper (by norm_num)
  have hActivityScaled :
      activityInBecquerels (setup.sample.activityAt setup.queryTime) =
        (15625 / 64 : ℝ) *
          (decayConstantInPerSecond setup.sample.decayConstant *
            Real.exp
              (-(decayConstantInPerSecond setup.sample.decayConstant))) := by
    calc
      activityInBecquerels (setup.sample.activityAt setup.queryTime) =
          decayConstantInPerSecond setup.sample.decayConstant *
            (setup.sample.expectedParentCountAt setup.queryTime : ℝ) :=
        hDecay.activityIsDecayRateTimesPopulation setup.queryTime
      _ = decayConstantInPerSecond setup.sample.decayConstant *
          (2000000 *
            Real.exp
              (-(decayConstantInPerSecond setup.sample.decayConstant * 27))) := by
        rw [hQueryPopulation]
      _ = decayConstantInPerSecond setup.sample.decayConstant *
          (2000000 *
            (((1 : ℝ) / 2) ^ 13 *
              Real.exp
                (-(decayConstantInPerSecond setup.sample.decayConstant)))) := by
        rw [hQueryExponential]
      _ = (15625 / 64 : ℝ) *
          (decayConstantInPerSecond setup.sample.decayConstant *
            Real.exp
              (-(decayConstantInPerSecond setup.sample.decayConstant))) := by
        ring
  have hActivityLower :
      (119 / 2 : ℝ) <
        activityInBecquerels (setup.sample.activityAt setup.queryTime) := by
    rw [hActivityScaled]
    nlinarith
  have hActivityUpper :
      activityInBecquerels (setup.sample.activityAt setup.queryTime) <
        (121 / 2 : ℝ) := by
    rw [hActivityScaled]
    nlinarith
  have hRounded :
      |activityInBecquerels (setup.sample.activityAt setup.queryTime) - 60| ≤
        wholeBecquerelRoundingTolerance := by
    rw [wholeBecquerelRoundingTolerance, abs_le]
    constructor <;> nlinarith
  refine ⟨hActivityExact, hRounded, ?_⟩
  simpa [IsCorrectRoundedAnswerChoice, displayedActivityInBecquerels] using
    hRounded

end PhyXMiniProblems.ProblemPhyXMini0576
