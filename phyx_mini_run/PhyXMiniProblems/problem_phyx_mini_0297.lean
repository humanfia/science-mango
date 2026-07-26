import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0297

open Dimension

/-!
# Angular frequency of counter-propagating waves from an antinode reversal

Two equal-amplitude, equal-wavelength sinusoidal waves travel in opposite
directions on the same string.  Their superposition is the standing wave shown
in the primary figure at two instants: the solid curve has antinode `A` at its
upward extreme and the dashed curve has the same antinode at its downward
extreme.  The reversal takes `6.0 ms`; horizontal ticks are `10 cm` apart and
the full vertical height `H` is `1.80 cm`.

Physlib dimensionful quantities represent lengths, times, speeds, wave
numbers, and angular frequencies.  Real scalars occur only as readouts in
named units, as dimensionless sine phases, and as displayed answer values.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- A nonnegative physical length, used for amplitudes and wavelengths. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial coordinate or transverse displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed time coordinate relative to an arbitrary time origin. -/
abbrev TimeCoordinateQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative elapsed time or oscillation period. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative wave-number magnitude; radians are dimensionless. -/
abbrev WaveNumberMagnitude : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative angular-frequency magnitude; radians are dimensionless. -/
abbrev AngularFrequencyMagnitude : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The common nonnegative propagation speed of disturbances on the string. -/
abbrev StringWaveSpeed : Type := DimSpeed

/-- Read a nonnegative length in the selected length unit. -/
def lengthMagnitudeReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a signed axial coordinate or transverse displacement. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- Read a signed time coordinate in the selected time unit. -/
def timeCoordinateReadout
    (unit : TimeUnit) (time : TimeCoordinateQuantity) : ℝ :=
  (time { UnitChoices.SI with time := unit }).val

/-- Read a nonnegative duration in the selected time unit. -/
def durationReadout
    (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration { UnitChoices.SI with time := unit }).val : ℝ)

/-- Read wave number in radians per selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberMagnitude) : ℝ :=
  ((waveNumber { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyMagnitude) : ℝ :=
  ((frequency { UnitChoices.SI with time := unit }).val : ℝ)

/-- Read speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : StringWaveSpeed) : ℝ :=
  ((speed { UnitChoices.SI with
      length := lengthUnit
      time := timeUnit }).val : ℝ)

/-- Radian-per-second readout requested by the problem. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyMagnitude) : ℝ :=
  angularFrequencyReadout TimeUnit.seconds frequency

/-! ## Wave roles and primary-figure labels -/

/-- The component whose equation is supplied and the component being queried. -/
inductive ComponentWave where
  | givenWave
  | otherWave
  deriving DecidableEq, Repr

/-- Direction of travel along the labelled horizontal axis. -/
inductive PropagationDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Sign of the temporal phase in `k x ± omega t`. -/
def temporalPhaseSign : PropagationDirection → ℝ
  | .negativeX => 1
  | .positiveX => -1

/-- The two displayed extrema of the resultant standing wave. -/
inductive Snapshot where
  | upwardExtreme
  | downwardExtreme
  deriving DecidableEq, Repr

/-- Line styles distinguishing the two snapshots. -/
inductive CurveStyle where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- The coordinate axes printed in the primary figure. -/
inductive Axis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The literal coordinate labels printed beside the axes. -/
inductive AxisLabel where
  | x
  | y
  deriving DecidableEq, Repr

/-- Physical roles of the two letter labels in the primary figure. -/
inductive FigureRole where
  | trackedAntinode
  | peakToTroughHeight
  deriving DecidableEq, Repr

/-- Literal letter labels printed on the figure. -/
inductive FigureLabel where
  | A
  | H
  deriving DecidableEq, Repr

/-- The temporal relation asserted for the two pictured extrema. -/
inductive SnapshotRelation where
  | consecutiveOppositeExtrema
  deriving DecidableEq, Repr

/-!
Dimensionful figure data.  The numerical readouts and geometric relations are
kept out of this structure and stated in `MatchesProblemAndPrimaryFigure`.
-/
structure StandingWaveFigure where
  axisLabel : Axis → AxisLabel
  figureLabel : FigureRole → FigureLabel
  curveStyle : Snapshot → CurveStyle
  snapshotRelation : SnapshotRelation
  tickSpacing : LengthMagnitude
  peakToTroughHeight : LengthMagnitude
  trackedAntinodePosition : SignedLengthQuantity
  snapshotTime : Snapshot → TimeCoordinateQuantity
  elapsedExtremeTransit : DurationQuantity

/-!
Independent physical quantities and observables for the two component waves.
Neither component angular frequency is assigned a numerical value here.
-/
structure CounterPropagatingStringWaveSetup where
  figure : StandingWaveFigure
  amplitude : ComponentWave → LengthMagnitude
  wavelength : ComponentWave → LengthMagnitude
  waveNumber : ComponentWave → WaveNumberMagnitude
  angularFrequency : ComponentWave → AngularFrequencyMagnitude
  period : ComponentWave → DurationQuantity
  commonPropagationSpeed : StringWaveSpeed
  propagationDirection : ComponentWave → PropagationDirection
  componentDisplacement :
    ComponentWave → SignedLengthQuantity → TimeCoordinateQuantity →
      SignedLengthQuantity
  resultantDisplacement :
    SignedLengthQuantity → TimeCoordinateQuantity → SignedLengthQuantity

/-!
Problem-statement data and calibrated readouts from the supplied bitmap.

The solid and dashed curves are consecutive opposite extrema of the same
standing-wave antinode.  Nodes are separated by two `10 cm` tick intervals,
so the component wavelength spans four intervals; the labelled antinode `A`
is at the fifth tick.  `H` is the full upward-to-downward displacement span.
No field gives the requested angular frequency or selects answer D.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : CounterPropagatingStringWaveSetup) : Prop where
  horizontalAxisIsX : setup.figure.axisLabel .horizontal = .x
  verticalAxisIsY : setup.figure.axisLabel .vertical = .y
  antinodeLabelIsA : setup.figure.figureLabel .trackedAntinode = .A
  heightLabelIsH : setup.figure.figureLabel .peakToTroughHeight = .H
  upwardCurveIsSolid : setup.figure.curveStyle .upwardExtreme = .solid
  downwardCurveIsDashed : setup.figure.curveStyle .downwardExtreme = .dashed
  snapshotsAreConsecutiveOppositeExtrema :
    setup.figure.snapshotRelation = .consecutiveOppositeExtrema
  givenEquationTravelsTowardNegativeX :
    setup.propagationDirection .givenWave = .negativeX
  otherWaveTravelsTowardPositiveX :
    setup.propagationDirection .otherWave = .positiveX
  equalComponentAmplitudes :
    setup.amplitude .givenWave = setup.amplitude .otherWave
  equalComponentWavelengths :
    setup.wavelength .givenWave = setup.wavelength .otherWave
  tickSpacingCentimeters :
    lengthMagnitudeReadout LengthUnit.centimeters setup.figure.tickSpacing = 10
  heightCentimeters :
    lengthMagnitudeReadout LengthUnit.centimeters
        setup.figure.peakToTroughHeight = 9 / 5
  extremeTransitMilliseconds :
    durationReadout TimeUnit.milliseconds
        setup.figure.elapsedExtremeTransit = 6
  snapshotTimesDifferByTransit :
    ∀ unit : TimeUnit,
      timeCoordinateReadout unit
          (setup.figure.snapshotTime .downwardExtreme) =
        timeCoordinateReadout unit
            (setup.figure.snapshotTime .upwardExtreme) +
          durationReadout unit setup.figure.elapsedExtremeTransit
  wavelengthSpansFourTicks :
    ∀ (wave : ComponentWave) (unit : LengthUnit),
      lengthMagnitudeReadout unit (setup.wavelength wave) =
        4 * lengthMagnitudeReadout unit setup.figure.tickSpacing
  antinodeAIsAtFifthTick :
    ∀ unit : LengthUnit,
      signedLengthReadout unit setup.figure.trackedAntinodePosition =
        5 * lengthMagnitudeReadout unit setup.figure.tickSpacing
  upwardExtremeDisplacement :
    ∀ unit : LengthUnit,
      signedLengthReadout unit
          (setup.resultantDisplacement setup.figure.trackedAntinodePosition
            (setup.figure.snapshotTime .upwardExtreme)) =
        lengthMagnitudeReadout unit setup.figure.peakToTroughHeight / 2
  downwardExtremeDisplacement :
    ∀ unit : LengthUnit,
      signedLengthReadout unit
          (setup.resultantDisplacement setup.figure.trackedAntinodePosition
            (setup.figure.snapshotTime .downwardExtreme)) =
        -(lengthMagnitudeReadout unit setup.figure.peakToTroughHeight / 2)

/-- Positivity assumptions selecting the nondegenerate physical branch. -/
structure HasPhysicalWaveParameters
    (setup : CounterPropagatingStringWaveSetup) : Prop where
  amplitudesPositive :
    ∀ wave,
      0 < lengthMagnitudeReadout LengthUnit.meters (setup.amplitude wave)
  wavelengthsPositive :
    ∀ wave,
      0 < lengthMagnitudeReadout LengthUnit.meters (setup.wavelength wave)
  waveNumbersPositive :
    ∀ wave, 0 < waveNumberReadout LengthUnit.meters (setup.waveNumber wave)
  angularFrequenciesPositive :
    ∀ wave,
      0 < angularFrequencyInRadiansPerSecond (setup.angularFrequency wave)
  periodsPositive :
    ∀ wave, 0 < durationReadout TimeUnit.seconds (setup.period wave)
  propagationSpeedPositive :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds
      setup.commonPropagationSpeed
  tickSpacingPositive :
    0 < lengthMagnitudeReadout LengthUnit.meters setup.figure.tickSpacing
  heightPositive :
    0 < lengthMagnitudeReadout LengthUnit.meters
      setup.figure.peakToTroughHeight
  transitTimePositive :
    0 < durationReadout TimeUnit.seconds setup.figure.elapsedExtremeTransit

/-!
Generic laws for two sinusoidal waves on one string:

* `k lambda = 2 pi` and `omega = k v` for each component;
* `omega T = 2 pi` for each component period;
* the stated zero-phase forms `y_m sin(kx ± omega t)`;
* linear superposition of transverse displacements;
* consecutive upward/downward antinode extrema are separated by half a period.

These laws contain neither `500 pi / 3`, `520`, nor any answer label.
-/
structure SatisfiesCounterPropagatingSinusoidalWaveLaws
    (setup : CounterPropagatingStringWaveSetup) : Prop where
  waveNumberWavelengthRelation :
    ∀ (wave : ComponentWave) (unit : LengthUnit),
      waveNumberReadout unit (setup.waveNumber wave) *
          lengthMagnitudeReadout unit (setup.wavelength wave) =
        2 * Real.pi
  angularFrequencyWaveSpeedRelation :
    ∀ wave,
      angularFrequencyReadout TimeUnit.seconds
          (setup.angularFrequency wave) =
        waveNumberReadout LengthUnit.meters (setup.waveNumber wave) *
          speedReadout LengthUnit.meters TimeUnit.seconds
            setup.commonPropagationSpeed
  angularFrequencyPeriodRelation :
    ∀ (wave : ComponentWave) (unit : TimeUnit),
      angularFrequencyReadout unit (setup.angularFrequency wave) *
          durationReadout unit (setup.period wave) =
        2 * Real.pi
  componentSinusoidalWaveform :
    ∀ (wave : ComponentWave) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit) (position : SignedLengthQuantity)
        (time : TimeCoordinateQuantity),
      signedLengthReadout lengthUnit
          (setup.componentDisplacement wave position time) =
        lengthMagnitudeReadout lengthUnit (setup.amplitude wave) *
          Real.sin
            (waveNumberReadout lengthUnit (setup.waveNumber wave) *
                signedLengthReadout lengthUnit position +
              temporalPhaseSign (setup.propagationDirection wave) *
                angularFrequencyReadout timeUnit
                  (setup.angularFrequency wave) *
                timeCoordinateReadout timeUnit time)
  linearSuperposition :
    ∀ (lengthUnit : LengthUnit) (position : SignedLengthQuantity)
        (time : TimeCoordinateQuantity),
      signedLengthReadout lengthUnit
          (setup.resultantDisplacement position time) =
        signedLengthReadout lengthUnit
            (setup.componentDisplacement .givenWave position time) +
          signedLengthReadout lengthUnit
            (setup.componentDisplacement .otherWave position time)
  consecutiveOppositeExtremaAreHalfPeriod :
    setup.figure.snapshotRelation = .consecutiveOppositeExtrema →
      ∀ unit : TimeUnit,
        durationReadout unit (setup.period .otherWave) =
          2 * durationReadout unit setup.figure.elapsedExtremeTransit

/-! ## Exact consequence and displayed answer -/

/-- Labels of the four angular-frequency choices in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Radian-per-second value printed beside each answer label. -/
def AnswerChoice.radiansPerSecond : AnswerChoice → ℝ
  | .A => 440
  | .B => 480
  | .C => 500
  | .D => 520

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a value displayed to the nearest ten radians per second.  The
strict half-width excludes midpoint ties.
-/
def MatchesNearestTenDisplay
    (angularFrequencyRadiansPerSecond : ℝ) (choice : AnswerChoice) : Prop :=
  |angularFrequencyRadiansPerSecond - choice.radiansPerSecond| < 5

/-!
The `6.0 ms` reversal is half a period, so the period is `12.0 ms` and
`omega = 2 pi / T = 500 pi / 3` radians per second.
-/
lemma otherWaveAngularFrequency_exact
    (setup : CounterPropagatingStringWaveSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesCounterPropagatingSinusoidalWaveLaws setup) :
    angularFrequencyInRadiansPerSecond
        (setup.angularFrequency .otherWave) =
      500 * Real.pi / 3 := by
  have hperiod_ms :=
    _laws.consecutiveOppositeExtremaAreHalfPeriod
      _figure.snapshotsAreConsecutiveOppositeExtrema TimeUnit.milliseconds
  have hfrequency_period_ms :=
    _laws.angularFrequencyPeriodRelation
      ComponentWave.otherWave TimeUnit.milliseconds
  have hfrequency_ms :
      angularFrequencyReadout TimeUnit.milliseconds
          (setup.angularFrequency .otherWave) =
        Real.pi / 6 := by
    rw [_figure.extremeTransitMilliseconds] at hperiod_ms
    rw [hperiod_ms] at hfrequency_period_ms
    nlinarith
  have hconversion :
      angularFrequencyInRadiansPerSecond
          (setup.angularFrequency .otherWave) =
        1000 *
          angularFrequencyReadout TimeUnit.milliseconds
            (setup.angularFrequency .otherWave) := by
    have h_units_val := congrArg WithDim.val
      ((setup.angularFrequency .otherWave).2
        {UnitChoices.SI with time := TimeUnit.milliseconds}
        {UnitChoices.SI with time := TimeUnit.seconds})
    unfold angularFrequencyInRadiansPerSecond angularFrequencyReadout
    rw [h_units_val]
    norm_num [UnitChoices.dimScale, TimeUnit.milliseconds,
      TimeUnit.seconds, TimeUnit.scale, TimeUnit.div_eq_val,
      NNReal.rpow_neg_one, NNReal.smul_def]
    apply Or.inl
    change ((1 / 1000 : ℝ)⁻¹) = 1000
    norm_num
  rw [hconversion, hfrequency_ms]
  ring

/-!
The exact value `500 pi / 3` is approximately `523.6 rad/s`, hence it is
displayed to the nearest ten as `5.2 × 10^2 rad/s`, answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0297:target`.
-/
theorem problem_phyx_mini_0297
    (setup : CounterPropagatingStringWaveSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesCounterPropagatingSinusoidalWaveLaws setup) :
    angularFrequencyInRadiansPerSecond
          (setup.angularFrequency .otherWave) =
        500 * Real.pi / 3 ∧
      MatchesNearestTenDisplay
        (angularFrequencyInRadiansPerSecond
          (setup.angularFrequency .otherWave)) .D := by
  have hexact :=
    otherWaveAngularFrequency_exact setup _figure _physical _laws
  refine ⟨hexact, ?_⟩
  rw [hexact]
  unfold MatchesNearestTenDisplay
  change |500 * Real.pi / 3 - 520| < 5
  have hcos_lower : 0 < Real.cos (309 / 200 : ℝ) := by
    have hc0 :
        (9812 / 10000 : ℝ) < Real.cos (309 / 1600 : ℝ) := by
      have hbound :=
        Real.cos_bound (x := (309 / 1600 : ℝ))
          (by norm_num [abs_of_nonneg])
      rw [abs_le] at hbound
      norm_num [abs_of_nonneg] at hbound
      nlinarith
    have hc0_nonneg : 0 ≤ Real.cos (309 / 1600 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hsq0 :
        (9812 / 10000 : ℝ) ^ 2 ≤
          Real.cos (309 / 1600 : ℝ) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hc0_nonneg).2 hc0.le
    have hc1 :
        (925 / 1000 : ℝ) < Real.cos (309 / 800 : ℝ) := by
      rw [show (309 / 800 : ℝ) = 2 * (309 / 1600 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith
    have hc1_nonneg : 0 ≤ Real.cos (309 / 800 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hsq1 :
        (925 / 1000 : ℝ) ^ 2 ≤
          Real.cos (309 / 800 : ℝ) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hc1_nonneg).2 hc1.le
    have hc2 :
        (71 / 100 : ℝ) < Real.cos (309 / 400 : ℝ) := by
      rw [show (309 / 400 : ℝ) = 2 * (309 / 800 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith
    have hc2_nonneg : 0 ≤ Real.cos (309 / 400 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hsq2 :
        (71 / 100 : ℝ) ^ 2 ≤ Real.cos (309 / 400 : ℝ) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hc2_nonneg).2 hc2.le
    rw [show (309 / 200 : ℝ) = 2 * (309 / 400 : ℝ) by
        norm_num,
      Real.cos_two_mul]
    nlinarith
  have hpi_lower : (309 / 100 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (309 / 100 : ℝ) := le_of_not_gt h
    have hcos_nonpos :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (x := Real.pi / 2) (y := (309 / 200 : ℝ))
        (by positivity) (by nlinarith [Real.two_le_pi]) (by nlinarith)
    rw [Real.cos_pi_div_two] at hcos_nonpos
    linarith
  have hcos_upper : Real.cos (63 / 40 : ℝ) < 0 := by
    have hc0 :
        Real.cos (63 / 320 : ℝ) < (9807 / 10000 : ℝ) := by
      have hbound :=
        Real.cos_bound (x := (63 / 320 : ℝ))
          (by norm_num [abs_of_nonneg])
      rw [abs_le] at hbound
      norm_num [abs_of_nonneg] at hbound
      nlinarith
    have hc0_nonneg : 0 ≤ Real.cos (63 / 320 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hsq0 :
        Real.cos (63 / 320 : ℝ) ^ 2 ≤
          (9807 / 10000 : ℝ) ^ 2 :=
      (sq_le_sq₀ hc0_nonneg (by norm_num)).2 hc0.le
    have hc1 :
        Real.cos (63 / 160 : ℝ) < (9236 / 10000 : ℝ) := by
      rw [show (63 / 160 : ℝ) = 2 * (63 / 320 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith
    have hc1_nonneg : 0 ≤ Real.cos (63 / 160 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hsq1 :
        Real.cos (63 / 160 : ℝ) ^ 2 ≤
          (9236 / 10000 : ℝ) ^ 2 :=
      (sq_le_sq₀ hc1_nonneg (by norm_num)).2 hc1.le
    have hc2 :
        Real.cos (63 / 80 : ℝ) < (7061 / 10000 : ℝ) := by
      rw [show (63 / 80 : ℝ) = 2 * (63 / 160 : ℝ) by
          norm_num,
        Real.cos_two_mul]
      nlinarith
    have hc2_nonneg : 0 ≤ Real.cos (63 / 80 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hsq2 :
        Real.cos (63 / 80 : ℝ) ^ 2 ≤
          (7061 / 10000 : ℝ) ^ 2 :=
      (sq_le_sq₀ hc2_nonneg (by norm_num)).2 hc2.le
    rw [show (63 / 40 : ℝ) = 2 * (63 / 80 : ℝ) by
        norm_num,
      Real.cos_two_mul]
    nlinarith
  have hpi_upper : Real.pi < (63 / 20 : ℝ) := by
    by_contra h
    have hpi_ge : (63 / 20 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hcos_nonneg :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (x := (63 / 40 : ℝ)) (y := Real.pi / 2)
        (by norm_num) (by nlinarith [Real.pi_pos]) (by nlinarith)
    rw [Real.cos_pi_div_two] at hcos_nonneg
    linarith
  rw [abs_lt]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0297
