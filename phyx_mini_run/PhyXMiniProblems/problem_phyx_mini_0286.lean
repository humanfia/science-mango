import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Beetle distance from transverse and longitudinal sand-wave arrivals

A sudden beetle motion launches transverse and longitudinal disturbances along
the same beetle-to-scorpion path.  The scorpion detects both at its nearest
leg.  Since the longitudinal wave is faster, the difference between the two
travel durations determines the path length labeled `d` in the supplied
figure.

Lengths, durations, and propagation speeds below are genuine unit-independent
Physlib quantities.  Real numbers occur only as coherent readouts in named
units and as the numerical values printed in the problem and answer list.

Assumption/target split:

* `MatchesProblemAndFigure` records the two stated speed readouts, the measured
  `4.0 ms` arrival delay, the beetle/scorpion roles, and the primary image's
  `d`, `v_t`, and `v_l` labels;
* `HasPhysicalParameters` records positivity and nondegeneracy;
* `SatisfiesCommonPathWaveTravelModel` states constant-speed travel on the
  common path and identifies the measured delay with the transverse arrival
  time minus the longitudinal arrival time;
* the derived `0.30 m`, `30 cm`, and answer-D conclusions occur only in the
  final theorem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0286

open Dimension

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical separation, independent of the selected length unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, independent of the selected time unit. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical propagation speed with dimension length per time. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical duration in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in coherent units of length per time. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metre readout of the beetle-to-scorpion separation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the four displayed answers. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Second readout used in the constant-speed propagation law. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Millisecond readout used for the stated arrival-time difference. -/
def durationInMilliseconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.milliseconds duration

/-- Metre-per-second readout of a sand-wave propagation speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Wave roles, apparatus roles, and primary-figure labels -/

/-- The two modes of sand-surface disturbance named in the problem. -/
inductive SandWaveMode where
  | transverse
  | longitudinal
  deriving DecidableEq, Repr

/-- The emitting and detecting endpoints of the timing experiment. -/
inductive DetectionEndpoint where
  | beetleMotionSource
  | scorpionNearestLeg
  deriving DecidableEq, Repr

/-- The two animals shown in the supplied image. -/
inductive FigureObject where
  | scorpion
  | beetle
  deriving DecidableEq, Repr

/-- Vertical placement of an object or label in the source image. -/
inductive FigureLevel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The distance label printed on the central double-headed arrow. -/
inductive FigureDistanceLabel where
  | d
  deriving DecidableEq, Repr

/-- The velocity-vector labels printed beside the two wave modes. -/
inductive FigureVelocityLabel where
  | v_t
  | v_l
  deriving DecidableEq, Repr

/--
Qualitative geometry and labels read from the primary bitmap.  The locations
of the velocity labels are kept as visual evidence only; they do not assert
that either wave begins at a different physical source.
-/
structure SandScorpionFigure where
  objectAt : FigureLevel → FigureObject
  distanceArrowEndpoints : FigureLevel × FigureLevel
  displayedDistanceLabel : FigureDistanceLabel
  displayedVelocityLabel : SandWaveMode → FigureVelocityLabel
  velocityLabelAt : SandWaveMode → FigureLevel
  displayedVelocityArrowCount : SandWaveMode → ℕ

/-!
The physical observables in the detection experiment.  In particular,
`beetleDistance` is an independent unknown: it is not defined using the
recorded answer or either wave speed.
-/
structure SandWaveDetectionSetup where
  beetleDistance : LengthQuantity
  propagationSpeed : SandWaveMode → SpeedQuantity
  travelDuration : SandWaveMode → DurationQuantity
  arrivalTimeDifference : DurationQuantity
  emissionEndpoint : DetectionEndpoint
  detectionEndpoint : DetectionEndpoint
  figure : SandScorpionFigure

/-! ## Problem data, figure evidence, and governing laws -/

/-!
Numerical readouts from the prose and qualitative labels from the primary
image.  This interface contains no numerical value for `beetleDistance`.
-/
structure MatchesProblemAndFigure (setup : SandWaveDetectionSetup) : Prop where
  transverseSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.propagationSpeed .transverse) = 50
  longitudinalSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.propagationSpeed .longitudinal) = 150
  measuredArrivalDifferenceMilliseconds :
    durationInMilliseconds setup.arrivalTimeDifference = 4
  suddenMotionIsAtBeetle :
    setup.emissionEndpoint = .beetleMotionSource
  detectionIsAtNearestScorpionLeg :
    setup.detectionEndpoint = .scorpionNearestLeg
  upperObjectIsScorpion :
    setup.figure.objectAt .upper = .scorpion
  lowerObjectIsBeetle :
    setup.figure.objectAt .lower = .beetle
  distanceArrowRunsBetweenLevels :
    setup.figure.distanceArrowEndpoints = (.lower, .upper)
  distanceArrowLabel :
    setup.figure.displayedDistanceLabel = .d
  transverseVectorLabel :
    setup.figure.displayedVelocityLabel .transverse = .v_t
  longitudinalVectorLabel :
    setup.figure.displayedVelocityLabel .longitudinal = .v_l
  transverseLabelsAreLower :
    setup.figure.velocityLabelAt .transverse = .lower
  longitudinalLabelsAreUpper :
    setup.figure.velocityLabelAt .longitudinal = .upper
  twoTransverseArrowsShown :
    setup.figure.displayedVelocityArrowCount .transverse = 2
  twoLongitudinalArrowsShown :
    setup.figure.displayedVelocityArrowCount .longitudinal = 2

/-- Positivity and temporal ordering for a nondegenerate detection event. -/
structure HasPhysicalParameters (setup : SandWaveDetectionSetup) : Prop where
  beetleDistancePositive :
    0 < lengthInMeters setup.beetleDistance
  propagationSpeedsPositive :
    ∀ mode, 0 < speedInMetersPerSecond (setup.propagationSpeed mode)
  travelDurationsNonnegative :
    ∀ mode, 0 ≤ durationInSeconds (setup.travelDuration mode)
  arrivalDifferencePositive :
    0 < durationInSeconds setup.arrivalTimeDifference
  longitudinalArrivesFirst :
    durationInSeconds (setup.travelDuration .longitudinal) <
      durationInSeconds (setup.travelDuration .transverse)

/-!
The ideal common-path time-of-flight model.  Each mode obeys
`distance = speed × travel duration`, and simultaneous emission makes the
measured lag the transverse duration minus the longitudinal duration.  These
are governing laws and contain no requested distance value or answer choice.
-/
structure SatisfiesCommonPathWaveTravelModel
    (setup : SandWaveDetectionSetup) : Prop where
  constantSpeedPropagation :
    ∀ mode,
      speedInMetersPerSecond (setup.propagationSpeed mode) *
          durationInSeconds (setup.travelDuration mode) =
        lengthInMeters setup.beetleDistance
  arrivalDifferenceRelation :
    durationInSeconds setup.arrivalTimeDifference =
      durationInSeconds (setup.travelDuration .transverse) -
        durationInSeconds (setup.travelDuration .longitudinal)

/-! ## Derived relation, displayed answers, and formalization target -/

/-!
For two modes traversing the same distance, the arrival lag gives

`d = Δt / (1 / v_t - 1 / v_l)`.

This is a derived general relation, not a premise of the final result.
-/
lemma distanceInMeters_eq_arrivalDifference_div_reciprocalSpeedGap
    (setup : SandWaveDetectionSetup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesCommonPathWaveTravelModel setup) :
    lengthInMeters setup.beetleDistance =
      durationInSeconds setup.arrivalTimeDifference /
        (1 / speedInMetersPerSecond (setup.propagationSpeed .transverse) -
          1 / speedInMetersPerSecond
            (setup.propagationSpeed .longitudinal)) := by
  have htransverseSpeed :
      0 < speedInMetersPerSecond (setup.propagationSpeed .transverse) :=
    _physical.propagationSpeedsPositive .transverse
  have hlongitudinalSpeed :
      0 < speedInMetersPerSecond (setup.propagationSpeed .longitudinal) :=
    _physical.propagationSpeedsPositive .longitudinal
  have hlongitudinalDuration :
      0 < durationInSeconds (setup.travelDuration .longitudinal) := by
    apply pos_of_mul_pos_right
      (a := speedInMetersPerSecond (setup.propagationSpeed .longitudinal))
    · rw [_laws.constantSpeedPropagation .longitudinal]
      exact _physical.beetleDistancePositive
    · exact le_of_lt hlongitudinalSpeed
  have hdurationProduct :
      speedInMetersPerSecond (setup.propagationSpeed .transverse) *
          durationInSeconds (setup.travelDuration .longitudinal) <
        speedInMetersPerSecond (setup.propagationSpeed .transverse) *
          durationInSeconds (setup.travelDuration .transverse) :=
    mul_lt_mul_of_pos_left
      _physical.longitudinalArrivesFirst htransverseSpeed
  rw [_laws.constantSpeedPropagation .transverse,
    ← _laws.constantSpeedPropagation .longitudinal] at hdurationProduct
  have hspeedOrder :
      speedInMetersPerSecond (setup.propagationSpeed .transverse) <
        speedInMetersPerSecond (setup.propagationSpeed .longitudinal) :=
    lt_of_mul_lt_mul_right hdurationProduct
      (le_of_lt hlongitudinalDuration)
  have hreciprocalSpeedGap :
      0 <
        1 / speedInMetersPerSecond (setup.propagationSpeed .transverse) -
          1 / speedInMetersPerSecond
            (setup.propagationSpeed .longitudinal) :=
    sub_pos.mpr
      (one_div_lt_one_div_of_lt htransverseSpeed hspeedOrder)
  have htransverseDuration :
      durationInSeconds (setup.travelDuration .transverse) =
        lengthInMeters setup.beetleDistance /
          speedInMetersPerSecond (setup.propagationSpeed .transverse) := by
    apply (eq_div_iff (ne_of_gt htransverseSpeed)).2
    nlinarith only [_laws.constantSpeedPropagation .transverse]
  have hlongitudinalDuration' :
      durationInSeconds (setup.travelDuration .longitudinal) =
        lengthInMeters setup.beetleDistance /
          speedInMetersPerSecond (setup.propagationSpeed .longitudinal) := by
    apply (eq_div_iff (ne_of_gt hlongitudinalSpeed)).2
    nlinarith only [_laws.constantSpeedPropagation .longitudinal]
  rw [_laws.arrivalDifferenceRelation, htransverseDuration,
    hlongitudinalDuration']
  apply (eq_div_iff (ne_of_gt hreciprocalSpeedGap)).2
  field_simp

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance in centimetres printed beside each answer label. -/
def AnswerChoice.centimeters : AnswerChoice → ℝ
  | .A => 20
  | .B => 25
  | .C => 35
  | .D => 30

/-- A modeled physical distance agrees exactly with a displayed choice. -/
def MatchesAnswerChoice
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters distance = choice.centimeters

/-!
With `v_t = 50 m/s`, `v_l = 150 m/s`, and `Δt = 4.0 ms`, the
beetle-to-scorpion distance is exactly `0.30 m = 30 cm`, which is answer D.

This formalizes `thm:physics:phyx_mini_0286:target`.
-/
theorem beetleDistance_is_thirtyCentimeters_and_choiceD
    (setup : SandWaveDetectionSetup)
    (_problemAndFigure : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesCommonPathWaveTravelModel setup) :
    lengthInMeters setup.beetleDistance = (3 : ℝ) / 10 ∧
      lengthInCentimeters setup.beetleDistance = 30 ∧
      MatchesAnswerChoice setup.beetleDistance .D := by
  have milliseconds_eq_seconds (duration : DurationQuantity) :
      durationInMilliseconds duration =
        1000 * durationInSeconds duration := by
    have h := congrArg (fun x : WithDim T𝓭 NNReal => (x.val : ℝ))
      (duration.2
        ({UnitChoices.SI with time := TimeUnit.seconds} : UnitChoices)
        ({UnitChoices.SI with time := TimeUnit.milliseconds} : UnitChoices))
    change durationInMilliseconds duration = _ at h
    norm_num [UnitChoices.dimScale, TimeUnit.milliseconds, TimeUnit.scale,
      TimeUnit.div_eq_val, TimeUnit.seconds, NNReal.smul_def] at h ⊢
    exact h
  have centimeters_eq_meters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
      (length.2
        ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
        ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices))
    change lengthInCentimeters length = _ at h
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.scale,
      LengthUnit.div_eq_val, LengthUnit.meters, NNReal.smul_def] at h ⊢
    exact h
  have harrivalDifference :
      durationInSeconds setup.arrivalTimeDifference = (1 : ℝ) / 250 := by
    nlinarith only [
      _problemAndFigure.measuredArrivalDifferenceMilliseconds,
      milliseconds_eq_seconds setup.arrivalTimeDifference]
  have hdistance :=
    distanceInMeters_eq_arrivalDifference_div_reciprocalSpeedGap
      setup _physical _laws
  rw [_problemAndFigure.transverseSpeedMetersPerSecond,
    _problemAndFigure.longitudinalSpeedMetersPerSecond,
    harrivalDifference] at hdistance
  norm_num at hdistance
  have hdistanceCentimeters :
      lengthInCentimeters setup.beetleDistance = 30 := by
    rw [centimeters_eq_meters, hdistance]
    norm_num
  exact ⟨hdistance, hdistanceCentimeters,
    (show MatchesAnswerChoice setup.beetleDistance .D by
      simpa [MatchesAnswerChoice, AnswerChoice.centimeters] using
        hdistanceCentimeters)⟩

end PhyXMiniProblems.ProblemPhyXMini0286
