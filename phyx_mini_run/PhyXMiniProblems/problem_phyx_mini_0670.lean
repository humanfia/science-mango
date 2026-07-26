import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0670

open Dimension

/-!
# Distance from a piecewise-constant acceleration graph

A particle moves along the `x` axis, starts from rest, and is observed for
`20 s`.  The supplied acceleration--time graph has three horizontal pieces:
`2 m/s²` from `0 s` to `10 s`, `0 m/s²` from `10 s` to `15 s`, and
`-3 m/s²` from `15 s` to `20 s`.

Position, distance, duration, velocity, and acceleration are represented by
dimension-tagged Physlib quantities.  Real numbers are used only for named
unit readouts and for the scalar time coordinate in seconds used by the graph,
derivatives, and integrals.

Assumption/target boundary:

* `MatchesParticleScenario` records one-dimensional motion, initial rest, and
  the `20 s` observation duration;
* `MatchesSuppliedAccelerationFigure` records the axis labels, units, grid,
  jump times, and three plotted acceleration levels;
* `SatisfiesOneDimensionalKinematics` supplies the generic derivative and
  path-length laws; and
* the velocity profile, exact distance `525/2 m`, and nearest displayed choice
  `C` occur only in conclusions below.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- The physical dimension of velocity, length divided by time. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed one-dimensional position or displacement. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical path length. -/
abbrev DistanceQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed one-dimensional velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A signed one-dimensional acceleration component. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- Read a signed position in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (position : SignedLengthQuantity) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a nonnegative path length in a selected length unit. -/
def distanceReadout
    (unit : LengthUnit) (distance : DistanceQuantity) : ℝ :=
  ((distance {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed velocity in coherent length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a signed acceleration in coherent length and time units. -/
def signedAccelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Position readout in metres. -/
def positionInMeters (position : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters position

/-- Path-length readout in metres. -/
def distanceInMeters (distance : DistanceQuantity) : ℝ :=
  distanceReadout LengthUnit.meters distance

/-- Duration readout in seconds. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Signed velocity readout in metres per second. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Signed acceleration readout in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  signedAccelerationReadout
    LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Figure geometry and particle observables -/

/-- The one-dimensional coordinate axis used in the scenario. -/
inductive SpatialAxis where
  | x
  deriving DecidableEq, Repr

/-- Physical quantities labelling the two graph axes. -/
inductive AccelerationGraphAxisQuantity where
  | time
  | accelerationX
  deriving DecidableEq, Repr

/-- The three horizontal pieces visible in the acceleration graph. -/
inductive AccelerationPlateau where
  | zeroToTenSeconds
  | tenToFifteenSeconds
  | fifteenToTwentySeconds
  deriving DecidableEq, Fintype, Repr

/-!
The acceleration--time figure.  Its plotted function is a scalar readout in
the named axis units, while the particle's acceleration remains a dimensionful
quantity in `ParticleMotionSetup`.
-/
structure AccelerationTimeFigure where
  horizontalAxisQuantity : AccelerationGraphAxisQuantity
  verticalAxisQuantity : AccelerationGraphAxisQuantity
  horizontalAxisTimeUnit : TimeUnit
  verticalAxisLengthUnit : LengthUnit
  verticalAxisTimeUnit : TimeUnit
  xAxisMinimumSeconds : ℝ
  xAxisMaximumSeconds : ℝ
  yAxisMinimumMetersPerSecondSquared : ℝ
  yAxisMaximumMetersPerSecondSquared : ℝ
  horizontalGridSpacingSeconds : ℝ
  verticalGridSpacingMetersPerSecondSquared : ℝ
  horizontalGridDivisionCount : ℕ
  verticalGridDivisionCount : ℕ
  plottedAccelerationMetersPerSecondSquared : ℝ → ℝ
  plateauDrawnHorizontal : AccelerationPlateau → Bool
  verticalJumpShownAtTenSeconds : Bool
  verticalJumpShownAtFifteenSeconds : Bool

/-!
The particle's time-dependent observables.  Function arguments are elapsed
seconds from the graph origin.  Distance traveled is an independent physical
observable related to velocity only by the governing kinematic law below.
-/
structure ParticleMotionSetup where
  motionAxis : SpatialAxis
  observationDuration : TimeQuantity
  positionAtSeconds : ℝ → SignedLengthQuantity
  velocityAtSeconds : ℝ → SignedVelocityQuantity
  accelerationAtSeconds : ℝ → SignedAccelerationQuantity
  distanceTraveledBySeconds : ℝ → DistanceQuantity
  figure : AccelerationTimeFigure

/-!
The right-continuous scalar acceleration profile transcribed from the raster.
Values at the idealized jump instants do not affect its time integral.  The
zero value outside the displayed interval makes no physical claim there.
-/
def accelerationProfileFromFigure (timeSeconds : ℝ) : ℝ :=
  if 0 ≤ timeSeconds ∧ timeSeconds < 10 then 2
  else if 10 ≤ timeSeconds ∧ timeSeconds < 15 then 0
  else if 15 ≤ timeSeconds ∧ timeSeconds ≤ 20 then -3
  else 0

/-! ## Scenario data, figure readouts, and governing laws -/

/-- Written scenario data: motion is along `x`, starts from rest, and lasts `20 s`. -/
structure MatchesParticleScenario (setup : ParticleMotionSetup) : Prop where
  motionIsAlongXAxis : setup.motionAxis = .x
  startsFromRest :
    velocityInMetersPerSecond (setup.velocityAtSeconds 0) = 0
  observationDurationIsTwentySeconds :
    timeInSeconds setup.observationDuration = 20

/-!
Exact readout of the primary raster, including axis labels and units, grid
geometry, the two vertical jumps, and all three acceleration plateaus.  It
contains no velocity, distance, or answer-choice value.
-/
structure MatchesSuppliedAccelerationFigure
    (setup : ParticleMotionSetup) : Prop where
  horizontalAxisIsTime : setup.figure.horizontalAxisQuantity = .time
  verticalAxisIsAccelerationX :
    setup.figure.verticalAxisQuantity = .accelerationX
  horizontalAxisUsesSeconds :
    setup.figure.horizontalAxisTimeUnit = TimeUnit.seconds
  verticalAxisUsesMeters :
    setup.figure.verticalAxisLengthUnit = LengthUnit.meters
  verticalAxisUsesSeconds :
    setup.figure.verticalAxisTimeUnit = TimeUnit.seconds
  xAxisStartsAtZeroSeconds : setup.figure.xAxisMinimumSeconds = 0
  xAxisEndsAtTwentySeconds : setup.figure.xAxisMaximumSeconds = 20
  yAxisStartsAtMinusThree :
    setup.figure.yAxisMinimumMetersPerSecondSquared = -3
  yAxisEndsAtTwo : setup.figure.yAxisMaximumMetersPerSecondSquared = 2
  horizontalGridSpacingIsFiveSeconds :
    setup.figure.horizontalGridSpacingSeconds = 5
  verticalGridSpacingIsOne :
    setup.figure.verticalGridSpacingMetersPerSecondSquared = 1
  fourHorizontalGridDivisions : setup.figure.horizontalGridDivisionCount = 4
  fiveVerticalGridDivisions : setup.figure.verticalGridDivisionCount = 5
  everyPlateauIsHorizontal :
    ∀ plateau, setup.figure.plateauDrawnHorizontal plateau = true
  jumpAtTenSecondsShown : setup.figure.verticalJumpShownAtTenSeconds = true
  jumpAtFifteenSecondsShown :
    setup.figure.verticalJumpShownAtFifteenSeconds = true
  plottedCurveHasStepProfile :
    ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (0 : ℝ) 20 →
      setup.figure.plottedAccelerationMetersPerSecondSquared timeSeconds =
        accelerationProfileFromFigure timeSeconds
  plottedCurveIsParticleAcceleration :
    ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (0 : ℝ) 20 →
      accelerationInMetersPerSecondSquared
          (setup.accelerationAtSeconds timeSeconds) =
        setup.figure.plottedAccelerationMetersPerSecondSquared timeSeconds

/-!
One-dimensional kinematics in the SI coordinate chart printed on the graph.
The acceleration derivative law excludes the two finite jump times, while
velocity continuity rules out impulses.  Path length is the integral of speed,
not signed velocity.  None of these generic laws fixes the requested distance.
-/
structure SatisfiesOneDimensionalKinematics
    (setup : ParticleMotionSetup) : Prop where
  velocityIsPositionDerivative :
    ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Ioo (0 : ℝ) 20 →
      HasDerivAt
        (fun time => positionInMeters (setup.positionAtSeconds time))
        (velocityInMetersPerSecond
          (setup.velocityAtSeconds timeSeconds))
        timeSeconds
  accelerationIsVelocityDerivativeAwayFromJumps :
    ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Ioo (0 : ℝ) 20 →
      timeSeconds ≠ 10 → timeSeconds ≠ 15 →
      HasDerivAt
        (fun time =>
          velocityInMetersPerSecond (setup.velocityAtSeconds time))
        (accelerationInMetersPerSecondSquared
          (setup.accelerationAtSeconds timeSeconds))
        timeSeconds
  velocityIsContinuousOnObservationInterval :
    ContinuousOn
      (fun time => velocityInMetersPerSecond (setup.velocityAtSeconds time))
      (Set.Icc (0 : ℝ) 20)
  distanceIsIntegralOfSpeed :
    ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (0 : ℝ) 20 →
      distanceInMeters (setup.distanceTraveledBySeconds timeSeconds) =
        ∫ time in (0 : ℝ)..timeSeconds,
          |velocityInMetersPerSecond (setup.velocityAtSeconds time)|

/-! ## Derived motion, answer choices, and formalization target -/

/-!
Integrating the graph from the initial rest condition yields the continuous
velocity profile `2t`, `20`, and `65 - 3t` on the three displayed intervals.
-/
lemma velocity_profile_from_acceleration_figure
    (setup : ParticleMotionSetup)
    (hScenario : MatchesParticleScenario setup)
    (hFigure : MatchesSuppliedAccelerationFigure setup)
    (hKinematics : SatisfiesOneDimensionalKinematics setup) :
    (∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (0 : ℝ) 10 →
      velocityInMetersPerSecond (setup.velocityAtSeconds timeSeconds) =
        2 * timeSeconds) ∧
      (∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (10 : ℝ) 15 →
        velocityInMetersPerSecond (setup.velocityAtSeconds timeSeconds) =
          20) ∧
      (∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (15 : ℝ) 20 →
        velocityInMetersPerSecond (setup.velocityAtSeconds timeSeconds) =
          65 - 3 * timeSeconds) := by
  let v : ℝ → ℝ := fun timeSeconds =>
    velocityInMetersPerSecond (setup.velocityAtSeconds timeSeconds)
  have hvContinuous : ContinuousOn v (Set.Icc (0 : ℝ) 20) := by
    simpa [v] using hKinematics.velocityIsContinuousOnObservationInterval
  have hFirstDerivative :
      ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Ioo (0 : ℝ) 10 →
        HasDerivAt v 2 timeSeconds := by
    intro timeSeconds ht
    have htObservation : timeSeconds ∈ Set.Ioo (0 : ℝ) 20 := by
      constructor <;> linarith [ht.1, ht.2]
    have htClosed : timeSeconds ∈ Set.Icc (0 : ℝ) 20 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAcceleration :
        accelerationInMetersPerSecondSquared
            (setup.accelerationAtSeconds timeSeconds) = 2 := by
      rw [hFigure.plottedCurveIsParticleAcceleration timeSeconds htClosed,
        hFigure.plottedCurveHasStepProfile timeSeconds htClosed]
      simp [accelerationProfileFromFigure, ht.1.le, ht.2]
    simpa [v, hAcceleration] using
      hKinematics.accelerationIsVelocityDerivativeAwayFromJumps
        timeSeconds htObservation (by linarith [ht.2]) (by linarith [ht.2])
  have hSecondDerivative :
      ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Ioo (10 : ℝ) 15 →
        HasDerivAt v 0 timeSeconds := by
    intro timeSeconds ht
    have htObservation : timeSeconds ∈ Set.Ioo (0 : ℝ) 20 := by
      constructor <;> linarith [ht.1, ht.2]
    have htClosed : timeSeconds ∈ Set.Icc (0 : ℝ) 20 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAcceleration :
        accelerationInMetersPerSecondSquared
            (setup.accelerationAtSeconds timeSeconds) = 0 := by
      rw [hFigure.plottedCurveIsParticleAcceleration timeSeconds htClosed,
        hFigure.plottedCurveHasStepProfile timeSeconds htClosed]
      simp [accelerationProfileFromFigure, ht.1.le, ht.2,
        not_lt_of_ge ht.1.le]
    simpa [v, hAcceleration] using
      hKinematics.accelerationIsVelocityDerivativeAwayFromJumps
        timeSeconds htObservation (by linarith [ht.1]) (by linarith [ht.2])
  have hThirdDerivative :
      ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Ioo (15 : ℝ) 20 →
        HasDerivAt v (-3) timeSeconds := by
    intro timeSeconds ht
    have htObservation : timeSeconds ∈ Set.Ioo (0 : ℝ) 20 := by
      constructor <;> linarith [ht.1, ht.2]
    have htClosed : timeSeconds ∈ Set.Icc (0 : ℝ) 20 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAcceleration :
        accelerationInMetersPerSecondSquared
            (setup.accelerationAtSeconds timeSeconds) = -3 := by
      rw [hFigure.plottedCurveIsParticleAcceleration timeSeconds htClosed,
        hFigure.plottedCurveHasStepProfile timeSeconds htClosed]
      simp [accelerationProfileFromFigure, ht.1.le, ht.2.le,
        show ¬timeSeconds < 10 by linarith [ht.1],
        show ¬timeSeconds < 15 by linarith [ht.1]]
    simpa [v, hAcceleration] using
      hKinematics.accelerationIsVelocityDerivativeAwayFromJumps
        timeSeconds htObservation (by linarith [ht.1]) (by linarith [ht.1])
  have hFirst :
      ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (0 : ℝ) 10 →
        v timeSeconds = 2 * timeSeconds := by
    intro timeSeconds ht
    rcases eq_or_lt_of_le ht.1 with hZero | hPositive
    · subst timeSeconds
      simpa [v] using hScenario.startsFromRest
    · have hContinuous :
          ContinuousOn v (Set.Icc (0 : ℝ) timeSeconds) :=
        hvContinuous.mono (by
          intro x hx
          constructor
          · exact hx.1
          · linarith [hx.2, ht.2])
      have hDerivative :
          ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) timeSeconds →
            HasDerivAt v 2 x := by
        intro x hx
        exact hFirstDerivative x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      obtain ⟨c, hc, hSlope⟩ :=
        exists_hasDerivAt_eq_slope
          v (fun _ : ℝ => (2 : ℝ)) hPositive hContinuous hDerivative
      have hvZero : v 0 = 0 := by
        simpa [v] using hScenario.startsFromRest
      rw [hvZero] at hSlope
      field_simp [ne_of_gt hPositive] at hSlope
      linarith
  have hSecond :
      ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (10 : ℝ) 15 →
        v timeSeconds = 20 := by
    intro timeSeconds ht
    rcases eq_or_lt_of_le ht.1 with hTen | hAfterTen
    · subst timeSeconds
      have hAtTen := hFirst 10 (by norm_num)
      norm_num at hAtTen
      exact hAtTen
    · have hContinuous :
          ContinuousOn v (Set.Icc (10 : ℝ) timeSeconds) :=
        hvContinuous.mono (by
          intro x hx
          constructor
          · linarith [hx.1]
          · linarith [hx.2, ht.2])
      have hDerivative :
          ∀ x : ℝ, x ∈ Set.Ioo (10 : ℝ) timeSeconds →
            HasDerivAt v 0 x := by
        intro x hx
        exact hSecondDerivative x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      obtain ⟨c, hc, hSlope⟩ :=
        exists_hasDerivAt_eq_slope
          v (fun _ : ℝ => (0 : ℝ)) hAfterTen hContinuous hDerivative
      have hvTen : v 10 = 20 := by
        have hAtTen := hFirst 10 (by norm_num)
        norm_num at hAtTen
        exact hAtTen
      rw [hvTen] at hSlope
      field_simp [ne_of_gt hAfterTen] at hSlope
      linarith
  have hThird :
      ∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (15 : ℝ) 20 →
        v timeSeconds = 65 - 3 * timeSeconds := by
    intro timeSeconds ht
    rcases eq_or_lt_of_le ht.1 with hFifteen | hAfterFifteen
    · subst timeSeconds
      have hAtFifteen := hSecond 15 (by norm_num)
      norm_num
      exact hAtFifteen
    · have hContinuous :
          ContinuousOn v (Set.Icc (15 : ℝ) timeSeconds) :=
        hvContinuous.mono (by
          intro x hx
          constructor
          · linarith [hx.1]
          · exact le_trans hx.2 ht.2)
      have hDerivative :
          ∀ x : ℝ, x ∈ Set.Ioo (15 : ℝ) timeSeconds →
            HasDerivAt v (-3) x := by
        intro x hx
        exact hThirdDerivative x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      obtain ⟨c, hc, hSlope⟩ :=
        exists_hasDerivAt_eq_slope
          v (fun _ : ℝ => (-3 : ℝ)) hAfterFifteen hContinuous hDerivative
      have hvFifteen : v 15 = 20 := by
        exact hSecond 15 (by norm_num)
      rw [hvFifteen] at hSlope
      field_simp [ne_of_gt hAfterFifteen] at hSlope
      linarith
  exact ⟨by simpa [v] using hFirst, by simpa [v] using hSecond,
    by simpa [v] using hThird⟩

/-!
The path length accumulated in the first `20 s` is exactly
`100 + 100 + 125/2 = 525/2 m`.  The velocity stays nonnegative, ending at
`5 m/s`, so the speed integral has no reversal correction.
-/
lemma distance_traveled_in_first_twenty_seconds
    (setup : ParticleMotionSetup)
    (hScenario : MatchesParticleScenario setup)
    (hFigure : MatchesSuppliedAccelerationFigure setup)
    (hKinematics : SatisfiesOneDimensionalKinematics setup) :
    distanceInMeters
        (setup.distanceTraveledBySeconds
          (timeInSeconds setup.observationDuration)) =
      525 / 2 := by
  rw [hScenario.observationDurationIsTwentySeconds]
  rw [hKinematics.distanceIsIntegralOfSpeed 20 (by norm_num)]
  let v : ℝ → ℝ := fun timeSeconds =>
    velocityInMetersPerSecond (setup.velocityAtSeconds timeSeconds)
  change (∫ timeSeconds in (0 : ℝ)..20, |v timeSeconds|) = 525 / 2
  have hProfile :
      (∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (0 : ℝ) 10 →
        v timeSeconds = 2 * timeSeconds) ∧
        (∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (10 : ℝ) 15 →
          v timeSeconds = 20) ∧
        (∀ timeSeconds : ℝ, timeSeconds ∈ Set.Icc (15 : ℝ) 20 →
          v timeSeconds = 65 - 3 * timeSeconds) := by
    simpa [v] using
      velocity_profile_from_acceleration_figure
        setup hScenario hFigure hKinematics
  have hvContinuous : ContinuousOn v (Set.Icc (0 : ℝ) 20) := by
    simpa [v] using hKinematics.velocityIsContinuousOnObservationInterval
  have hSpeedContinuous :
      ContinuousOn (fun timeSeconds => |v timeSeconds|)
        (Set.Icc (0 : ℝ) 20) :=
    hvContinuous.abs
  have hFirstIntegrable :
      IntervalIntegrable (fun timeSeconds => |v timeSeconds|)
        MeasureTheory.volume 0 10 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (hSpeedContinuous.mono (by
        intro x hx
        constructor
        · exact hx.1
        · linarith [hx.2]))
  have hSecondIntegrable :
      IntervalIntegrable (fun timeSeconds => |v timeSeconds|)
        MeasureTheory.volume 10 15 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (hSpeedContinuous.mono (by
        intro x hx
        constructor <;> linarith [hx.1, hx.2]))
  have hThirdIntegrable :
      IntervalIntegrable (fun timeSeconds => |v timeSeconds|)
        MeasureTheory.volume 15 20 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (hSpeedContinuous.mono (by
        intro x hx
        constructor <;> linarith [hx.1, hx.2]))
  have hFirstIntegral :
      (∫ timeSeconds in (0 : ℝ)..10, |v timeSeconds|) = 100 := by
    calc
      (∫ timeSeconds in (0 : ℝ)..10, |v timeSeconds|) =
          ∫ timeSeconds in (0 : ℝ)..10, 2 * timeSeconds := by
        apply intervalIntegral.integral_congr
        intro timeSeconds ht
        have ht' : timeSeconds ∈ Set.Icc (0 : ℝ) 10 := by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 10)] using ht
        change |v timeSeconds| = 2 * timeSeconds
        rw [hProfile.1 timeSeconds ht',
          abs_of_nonneg (by linarith [ht'.1])]
      _ = 100 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        norm_num
  have hSecondIntegral :
      (∫ timeSeconds in (10 : ℝ)..15, |v timeSeconds|) = 100 := by
    calc
      (∫ timeSeconds in (10 : ℝ)..15, |v timeSeconds|) =
          ∫ _timeSeconds in (10 : ℝ)..15, (20 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro timeSeconds ht
        have ht' : timeSeconds ∈ Set.Icc (10 : ℝ) 15 := by
          simpa [Set.uIcc_of_le (by norm_num : (10 : ℝ) ≤ 15)] using ht
        change |v timeSeconds| = (20 : ℝ)
        rw [hProfile.2.1 timeSeconds ht', abs_of_nonneg (by norm_num)]
      _ = 100 := by norm_num
  have hThirdIntegral :
      (∫ timeSeconds in (15 : ℝ)..20, |v timeSeconds|) = 125 / 2 := by
    calc
      (∫ timeSeconds in (15 : ℝ)..20, |v timeSeconds|) =
          ∫ timeSeconds in (15 : ℝ)..20, 65 - 3 * timeSeconds := by
        apply intervalIntegral.integral_congr
        intro timeSeconds ht
        have ht' : timeSeconds ∈ Set.Icc (15 : ℝ) 20 := by
          simpa [Set.uIcc_of_le (by norm_num : (15 : ℝ) ≤ 20)] using ht
        change |v timeSeconds| = 65 - 3 * timeSeconds
        rw [hProfile.2.2 timeSeconds ht',
          abs_of_nonneg (by linarith [ht'.2])]
      _ = 125 / 2 := by
        rw [intervalIntegral.integral_sub]
        · rw [intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul]
          rw [integral_id]
          norm_num
        · exact continuous_const.intervalIntegrable 15 20
        · exact
            (continuous_const.mul continuous_id).intervalIntegrable 15 20
  rw [← intervalIntegral.integral_add_adjacent_intervals
      hFirstIntegrable (hSecondIntegrable.trans hThirdIntegrable),
    ← intervalIntegral.integral_add_adjacent_intervals
      hSecondIntegrable hThirdIntegrable,
    hFirstIntegral, hSecondIntegral, hThirdIntegral]
  norm_num

/-- The four answer labels displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Distance readouts in metres printed beside the four answer labels. -/
def displayedDistanceInMeters : AnswerChoice → ℝ
  | .A => 178
  | .B => 251
  | .C => 263
  | .D => 432

/-- The answer label recorded in the dataset metadata; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed answer is nearest to an exact distance readout. -/
def IsNearestDisplayedDistance
    (exactDistanceMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |exactDistanceMeters - displayedDistanceInMeters choice| ≤
      |exactDistanceMeters - displayedDistanceInMeters other|

/-!
The exact distance is `262.5 m`.  Because the choices are displayed as whole
metres, the nearest listed readout is `263 m`, answer C.

This formalizes `thm:physics:phyx_mini_0670:target`.
-/
theorem problem_phyx_mini_0670
    (setup : ParticleMotionSetup)
    (hScenario : MatchesParticleScenario setup)
    (hFigure : MatchesSuppliedAccelerationFigure setup)
    (hKinematics : SatisfiesOneDimensionalKinematics setup) :
    distanceInMeters
        (setup.distanceTraveledBySeconds
          (timeInSeconds setup.observationDuration)) =
        525 / 2 ∧
      IsNearestDisplayedDistance
        (distanceInMeters
          (setup.distanceTraveledBySeconds
            (timeInSeconds setup.observationDuration)))
        recordedDatasetAnswer := by
  have hDistance :=
    distance_traveled_in_first_twenty_seconds
      setup hScenario hFigure hKinematics
  constructor
  · exact hDistance
  · rw [hDistance]
    unfold IsNearestDisplayedDistance
    intro other
    cases other <;>
      norm_num [recordedDatasetAnswer, displayedDistanceInMeters, abs_of_nonneg,
        abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0670
