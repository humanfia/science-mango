import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0599

open Dimension

/-!
# Reading a relativistic time-dilation graph

The supplied graph plots a coordinate-time interval `Delta t` against the
dimensionless speed parameter `beta`.  Its horizontal axis runs from `0` to
`0.8`, with `0.4` marked at the midpoint.  The vertical scale is labelled
`Delta t_a = 14.0 s`.  In the primary image, the curve at `beta = 0` lies on
the fourth of seven equal vertical grid divisions, so the graph calibrates
the zero-speed (proper) interval to `8 s`.

The question asks for the interval at `v = 0.98 c`, outside the displayed
horizontal range.  Thus the figure supplies the zero-speed calibration and
the Lorentz time-dilation law supplies the extrapolation.  The physical
intervals and speed below are unit-independent Physlib quantities; real
numbers are used only for named-unit readouts, dimensionless speed ratios,
normalized drawing coordinates, and displayed answer values.

Assumption/target split:

* `MatchesSuppliedTimeDilationFigure` transcribes axes, ticks, the scale label,
  and the zero-speed grid height from the image;
* `MatchesProblemReadouts` connects that drawing to physical durations and
  records the stated `v/c = 0.98`;
* `SatisfiesLorentzTimeDilation` states the generic time-dilation law for all
  nonnegative subluminal speed parameters;
* the `8 s` proper interval, the interval at `0.98 c`, and answer C occur only
  as conclusions below.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A physical speed carrying length-per-time dimension. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical duration in seconds, as on the vertical axis. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Read a physical speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Physlib's exact vacuum speed of light in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Frames and primary-figure vocabulary -/

/-- The rest frame of the clock and the frame in which `Delta t` is plotted. -/
inductive InertialFrameLabel where
  | properClockRest
  | graphObserver
  deriving DecidableEq, Repr

/-- The two axes visible in the supplied graph. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Literal mathematical labels printed on the graph. -/
inductive FigureAxisLabel where
  | beta
  | deltaTSeconds
  deriving DecidableEq, Repr

/-- The scale annotation printed at the upper end of the vertical axis. -/
inductive FigureScaleLabel where
  | deltaTA
  deriving DecidableEq, Repr

/-!
Literal information carried by `phyx_data/test_image/599.png`.

`normalizedCurveHeight` is a dimensionless drawing coordinate: `0` is the
bottom axis and `1` is the horizontal line carrying the `Delta t_a` scale.
It is not itself a physical duration.
-/
structure TimeDilationFigure where
  axisLabel : FigureAxis → FigureAxisLabel
  verticalScaleLabel : FigureScaleLabel
  betaMinimum : ℝ
  betaMidpointTick : ℝ
  betaMaximum : ℝ
  verticalGridDivisionCount : ℕ
  printedVerticalScaleSeconds : ℝ
  normalizedCurveHeight : ℝ → ℝ
  curveDrawn : Bool
  curveRisesNonlinearly : Bool

/-! ## Independent physical setup -/

/-!
The coordinate interval at each speed parameter, proper interval, axis-scale
interval, and stated physical speed are independent quantities.  In
particular, no field is defined from the recorded `40 s` answer.
-/
structure RelativisticIntervalSetup where
  figure : TimeDilationFigure
  properIntervalFrame : InertialFrameLabel
  coordinateIntervalFrame : InertialFrameLabel
  properInterval : DurationQuantity
  coordinateIntervalAtBeta : ℝ → DurationQuantity
  verticalAxisScaleInterval : DurationQuantity
  statedRelativeSpeed : SpeedQuantity

/-- The dimensionless speed parameter `beta = v/c` in coherent SI readouts. -/
def speedFractionOfLight (setup : RelativisticIntervalSetup) : ℝ :=
  speedInMetersPerSecond setup.statedRelativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-! ## Scenario, figure/data readouts, and governing physics -/

/-- The two duration roles belong to the inertial frames used by time dilation. -/
structure MatchesTimeDilationScenario
    (setup : RelativisticIntervalSetup) : Prop where
  properIntervalMeasuredInClockRestFrame :
    setup.properIntervalFrame = .properClockRest
  plottedIntervalsMeasuredInObserverFrame :
    setup.coordinateIntervalFrame = .graphObserver

/-!
Primary-image evidence.  The raster, rather than the auxiliary caption, shows
the curve at four sevenths of the vertical scale when `beta = 0`.
-/
structure MatchesSuppliedTimeDilationFigure
    (figure : TimeDilationFigure) : Prop where
  horizontalAxisIsBeta : figure.axisLabel .horizontal = .beta
  verticalAxisIsDeltaTSeconds :
    figure.axisLabel .vertical = .deltaTSeconds
  topScaleIsDeltaTA : figure.verticalScaleLabel = .deltaTA
  betaAxisStartsAtZero : figure.betaMinimum = 0
  betaAxisMidpointIsPointFour : figure.betaMidpointTick = (2 / 5 : ℝ)
  betaAxisEndsAtPointEight : figure.betaMaximum = (4 / 5 : ℝ)
  sevenEqualVerticalGridDivisions : figure.verticalGridDivisionCount = 7
  printedScaleIsFourteenSeconds : figure.printedVerticalScaleSeconds = 14
  curveIsShown : figure.curveDrawn = true
  curveIsDepictedAsRisingNonlinearly : figure.curveRisesNonlinearly = true
  zeroSpeedCurveHeight : figure.normalizedCurveHeight 0 = (4 / 7 : ℝ)

/-!
The `14 s` scale and `v = 0.98 c` are stated data.  On the displayed beta
range, the curve height is connected to the corresponding dimensionful
coordinate interval.  This relation contains no readout at the queried
`beta = 0.98`, which lies outside the graph's displayed range.
-/
structure MatchesProblemReadouts
    (setup : RelativisticIntervalSetup) : Prop where
  physicalAxisScaleMatchesPrintedScale :
    durationInSeconds setup.verticalAxisScaleInterval =
      setup.figure.printedVerticalScaleSeconds
  statedSpeedIsPointNineEightC :
    speedFractionOfLight setup = (49 / 50 : ℝ)
  displayedCurveRepresentsIntervals :
    ∀ beta,
      setup.figure.betaMinimum ≤ beta →
      beta ≤ setup.figure.betaMaximum →
      durationInSeconds (setup.coordinateIntervalAtBeta beta) =
        setup.figure.normalizedCurveHeight beta *
          durationInSeconds setup.verticalAxisScaleInterval

/-- Positivity and the nonnegative subluminal regime required by the model. -/
structure HasPhysicalRelativisticParameters
    (setup : RelativisticIntervalSetup) : Prop where
  positiveVacuumSpeed : 0 < vacuumSpeedOfLightInMetersPerSecond
  positiveProperInterval : 0 < durationInSeconds setup.properInterval
  positiveVerticalScale :
    0 < durationInSeconds setup.verticalAxisScaleInterval
  statedSpeedNonnegative : 0 ≤ speedFractionOfLight setup
  statedSpeedSubluminal : speedFractionOfLight setup < 1
  coordinateIntervalsPositive :
    ∀ beta, 0 ≤ beta → beta < 1 →
      0 < durationInSeconds (setup.coordinateIntervalAtBeta beta)

/-!
The governing special-relativistic law.  A coordinate interval at speed
parameter `beta` equals the proper interval multiplied by Physlib's Lorentz
factor.  It is stated for arbitrary nonnegative subluminal `beta`, rather
than only for the numerical target of this problem.
-/
structure SatisfiesLorentzTimeDilation
    (setup : RelativisticIntervalSetup) : Prop where
  timeDilationLaw :
    ∀ beta, 0 ≤ beta → beta < 1 →
      durationInSeconds (setup.coordinateIntervalAtBeta beta) =
        LorentzGroup.γ beta * durationInSeconds setup.properInterval

/-! ## Derived calibration and queried interval -/

/-!
Four of the seven equal vertical divisions of a `14 s` scale calibrate the
curve at `beta = 0` to `8 s`.  Since `gamma(0) = 1`, this is also the proper
interval.  The value is a consequence of the image and law, not a premise.
-/
lemma properInterval_seconds_eq_eight
    (setup : RelativisticIntervalSetup)
    (_figure : MatchesSuppliedTimeDilationFigure setup.figure)
    (_data : MatchesProblemReadouts setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_timeDilation : SatisfiesLorentzTimeDilation setup) :
    durationInSeconds setup.properInterval = 8 := by
  have hzero :
      durationInSeconds (setup.coordinateIntervalAtBeta 0) = 8 := by
    calc
      durationInSeconds (setup.coordinateIntervalAtBeta 0) =
          setup.figure.normalizedCurveHeight 0 *
            durationInSeconds setup.verticalAxisScaleInterval := by
        apply _data.displayedCurveRepresentsIntervals
        · rw [_figure.betaAxisStartsAtZero]
        · rw [_figure.betaAxisEndsAtPointEight]
          norm_num
      _ = 8 := by
        rw [_figure.zeroSpeedCurveHeight,
          _data.physicalAxisScaleMatchesPrintedScale,
          _figure.printedScaleIsFourteenSeconds]
        norm_num
  have htimeAtZero :=
    _timeDilation.timeDilationLaw 0 (by norm_num) (by norm_num)
  simpa using htimeAtZero.symm.trans hzero

/-!
At the stated speed, the observer-frame interval is the calibrated `8 s`
proper interval multiplied by Physlib's Lorentz factor at `49/50`.
-/
lemma intervalAtStatedSpeed_exactFormula
    (setup : RelativisticIntervalSetup)
    (_figure : MatchesSuppliedTimeDilationFigure setup.figure)
    (_data : MatchesProblemReadouts setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_timeDilation : SatisfiesLorentzTimeDilation setup) :
    durationInSeconds
        (setup.coordinateIntervalAtBeta (speedFractionOfLight setup)) =
      LorentzGroup.γ (49 / 50 : ℝ) * 8 := by
  rw [_timeDilation.timeDilationLaw
      (speedFractionOfLight setup)
      _physical.statedSpeedNonnegative
      _physical.statedSpeedSubluminal,
    _data.statedSpeedIsPointNineEightC,
    properInterval_seconds_eq_eight setup _figure _data _physical _timeDilation]

/-! ## Displayed answers and formalization target -/

/-- Labels of the four whole-second choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 28
  | .B => 56
  | .C => 40
  | .D => 12

/-- The answer label recorded by the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-! Agreement with a displayed whole-second value after nearest-second rounding. -/
def MatchesDisplayedTimeChoice
    (duration : DurationQuantity) (choice : AnswerChoice) : Prop :=
  |durationInSeconds duration - choice.seconds| ≤ (1 / 2 : ℝ)

/-- The chosen value is strictly closer than every alternative displayed value. -/
def IsUniqueClosestTimeChoice
    (duration : DurationQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |durationInSeconds duration - choice.seconds| <
      |durationInSeconds duration - other.seconds|

/-!
Physics formalization target `thm:physics:phyx_mini_0599:target`.

The image calibrates an `8 s` proper interval.  At `v/c = 0.98`, time
dilation gives `gamma(0.98) * 8`, approximately `40.2 s`, which rounds to
`40 s` and uniquely selects recorded answer C.
-/
theorem problem_phyx_mini_0599
    (setup : RelativisticIntervalSetup)
    (_scenario : MatchesTimeDilationScenario setup)
    (_figure : MatchesSuppliedTimeDilationFigure setup.figure)
    (_data : MatchesProblemReadouts setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_timeDilation : SatisfiesLorentzTimeDilation setup) :
    durationInSeconds
          (setup.coordinateIntervalAtBeta (speedFractionOfLight setup)) =
        LorentzGroup.γ (49 / 50 : ℝ) * 8 ∧
      MatchesDisplayedTimeChoice
        (setup.coordinateIntervalAtBeta (speedFractionOfLight setup))
        recordedAnswerChoice ∧
      IsUniqueClosestTimeChoice
        (setup.coordinateIntervalAtBeta (speedFractionOfLight setup))
        recordedAnswerChoice := by
  have hinterval :=
    intervalAtStatedSpeed_exactFormula
      setup _figure _data _physical _timeDilation
  have hsqrt_sq : (Real.sqrt 99) ^ 2 = (99 : ℝ) := by
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 99 := Real.sqrt_nonneg _
  have hsqrt_pos : 0 < Real.sqrt 99 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_lt_ten : Real.sqrt 99 < 10 := by
    nlinarith
  have hsqrt_gt : (800 / 81 : ℝ) < Real.sqrt 99 := by
    nlinarith
  have hbounds :
      40 < LorentzGroup.γ (49 / 50 : ℝ) * 8 ∧
        LorentzGroup.γ (49 / 50 : ℝ) * 8 < (81 / 2 : ℝ) := by
    norm_num [LorentzGroup.γ]
    rw [show 50 / Real.sqrt 99 * 8 = 400 / Real.sqrt 99 by ring]
    constructor
    · apply (lt_div_iff₀ hsqrt_pos).2
      nlinarith
    · apply (div_lt_iff₀ hsqrt_pos).2
      nlinarith
  rcases hbounds with ⟨hlower, hupper⟩
  refine ⟨hinterval, ?_, ?_⟩
  · unfold MatchesDisplayedTimeChoice
    rw [hinterval]
    simp only [recordedAnswerChoice, AnswerChoice.seconds]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · unfold IsUniqueClosestTimeChoice
    intro other hother
    rw [hinterval]
    cases other with
    | A =>
        simp only [recordedAnswerChoice, AnswerChoice.seconds]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
    | B =>
        simp only [recordedAnswerChoice, AnswerChoice.seconds]
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith
    | C =>
        simp [recordedAnswerChoice] at hother
    | D =>
        simp only [recordedAnswerChoice, AnswerChoice.seconds]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith

end PhyXMiniProblems.ProblemPhyXMini0599
