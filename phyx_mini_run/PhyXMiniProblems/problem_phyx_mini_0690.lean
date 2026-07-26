import Mathlib.Geometry.Euclidean.Triangle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0690

open Dimension

/-!
# Two cars driving to a lake

Towns `A` and `B` are 80 km apart. Car 1 drives from `A` to the lake `L`,
while car 2 drives from `B` to `L`. The supplied map shows a 40 degree angle
between `AB` and car 1's route `AL`. Both cars leave and arrive simultaneously,
after 2.50 hours, and car 1 travels at 90 km/h.

Speeds and durations are unit-independent Physlib quantities. The map is
modeled as a Euclidean plane whose scalar coordinate readouts are kilometres;
real numbers therefore occur only as map-coordinate readouts, angle readouts,
unit readouts, and displayed answer values.

Assumption/target boundary:

* `MatchesDrivingScenario` records only the simultaneous meeting scenario.
* `MatchesSuppliedFigure` records the objects, route endpoints, 80 km baseline,
  and 40 degree angle read directly from the primary raster.
* `MatchesProblemReadouts` records the common 2.50 h duration and car 1's
  90 km/h speed.
* `SatisfiesStraightRouteKinematics` is the governing constant-speed law
  `distance = speed * time` for each route.
* The exact cosine-rule value of car 2's speed, and the fact that 68.8 km/h is
  the closest displayed answer, occur only in the final theorem conclusion.
-/

/-! ## Dimensionful quantities and scalar unit readouts -/

/-- A nonnegative, unit-independent physical duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical duration in hours. -/
def durationInHours (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := TimeUnit.hours}).val : ℝ)

/-- Read a physical speed in kilometres per hour. -/
def speedInKilometresPerHour (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
      length := LengthUnit.kilometers, time := TimeUnit.hours}).val : ℝ)

/-- Convert a degree readout to the radian-valued angle used by Mathlib. -/
def angleInRadiansFromDegrees (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Map labels and physical setup -/

/-- Place labels printed on the primary map. -/
inductive PlaceLabel where
  | townA
  | townB
  | lakeL
  deriving DecidableEq, Fintype, Repr

/-- The two labeled cars in the primary map. -/
inductive CarLabel where
  | car1
  | car2
  deriving DecidableEq, Fintype, Repr

/--
A point of the Euclidean map. Its two real coordinates and its metric distance
are read in kilometres; this is a coordinate readout, not a physical-quantity
alias.
-/
abbrev KilometreMapPoint : Type := EuclideanSpace ℝ (Fin 2)

/-- Qualitative and numerical information printed on the supplied map. -/
structure LakeMeetingFigure where
  placeShown : PlaceLabel → Bool
  carShown : CarLabel → Bool
  straightRouteShown : CarLabel → Bool
  routeEndpoints : CarLabel → PlaceLabel × PlaceLabel
  dashedTownConnectionShown : Bool
  townSeparationLabelKilometres : ℝ
  angleAtTownALabelDegrees : ℝ

/-!
All independent quantities in the problem. In particular, car 2's speed is a
free physical observable; it is not defined from an answer choice.
-/
structure LakeMeetingSetup where
  positionOnMap : PlaceLabel → KilometreMapPoint
  speed : CarLabel → SpeedQuantity
  commonDrivingDuration : DurationQuantity
  leftSimultaneously : Bool
  arrivedSimultaneouslyAtLake : Bool
  figure : LakeMeetingFigure

/-- Euclidean map-distance readout in kilometres. -/
def mapDistanceInKilometres
    (setup : LakeMeetingSetup) (first second : PlaceLabel) : ℝ :=
  dist (setup.positionOnMap first) (setup.positionOnMap second)

/-- The map angle `first-center-second`, measured in radians. -/
def mapAngleAt
    (setup : LakeMeetingSetup)
    (first center second : PlaceLabel) : ℝ :=
  EuclideanGeometry.angle
    (setup.positionOnMap first)
    (setup.positionOnMap center)
    (setup.positionOnMap second)

/-! ## Scenario, figure readouts, numerical data, and governing laws -/

/-- The simultaneous-departure and simultaneous-arrival facts in the prose. -/
structure MatchesDrivingScenario (setup : LakeMeetingSetup) : Prop where
  bothCarsLeaveSimultaneously : setup.leftSimultaneously = true
  bothCarsArriveSimultaneouslyAtLake :
    setup.arrivedSimultaneouslyAtLake = true

/-!
Evidence read from the supplied raster. The route for car 1 is `A-L`, the
route for car 2 is `B-L`, the dashed baseline `A-B` is labeled 80 km, and the
angle from `AB` to `AL` at `A` is labeled 40 degrees.
-/
structure MatchesSuppliedFigure (setup : LakeMeetingSetup) : Prop where
  everyPlaceIsShown : ∀ place, setup.figure.placeShown place = true
  bothCarsAreShown : ∀ car, setup.figure.carShown car = true
  bothStraightRoutesAreShown :
    ∀ car, setup.figure.straightRouteShown car = true
  carOneRouteRunsFromAToLake :
    setup.figure.routeEndpoints .car1 = (.townA, .lakeL)
  carTwoRouteRunsFromBToLake :
    setup.figure.routeEndpoints .car2 = (.townB, .lakeL)
  dashedLineConnectsTheTowns :
    setup.figure.dashedTownConnectionShown = true
  townSeparationLabelIsEightyKilometres :
    setup.figure.townSeparationLabelKilometres = 80
  angleLabelAtTownAIsFortyDegrees :
    setup.figure.angleAtTownALabelDegrees = 40
  townSeparationLabelMatchesMapGeometry :
    mapDistanceInKilometres setup .townA .townB =
      setup.figure.townSeparationLabelKilometres
  angleLabelMatchesMapGeometry :
    mapAngleAt setup .townB .townA .lakeL =
      angleInRadiansFromDegrees setup.figure.angleAtTownALabelDegrees

/-! Numerical physical readouts stated in the problem text. -/
structure MatchesProblemReadouts (setup : LakeMeetingSetup) : Prop where
  commonDrivingDurationIsTwoPointFiveHours :
    durationInHours setup.commonDrivingDuration = 5 / 2
  carOneSpeedIsNinetyKilometresPerHour :
    speedInKilometresPerHour (setup.speed .car1) = 90

/-!
Nondegeneracy and positivity conditions for the depicted physical branch.
None fixes car 2's speed or selects an answer choice.
-/
structure HasPhysicalLakeMeetingParameters
    (setup : LakeMeetingSetup) : Prop where
  commonDrivingDurationPositive :
    0 < durationInHours setup.commonDrivingDuration
  carOneSpeedPositive :
    0 < speedInKilometresPerHour (setup.speed .car1)
  carTwoSpeedPositive :
    0 < speedInKilometresPerHour (setup.speed .car2)
  townsAreDistinct :
    setup.positionOnMap .townA ≠ setup.positionOnMap .townB
  lakeIsNotTownA :
    setup.positionOnMap .lakeL ≠ setup.positionOnMap .townA
  lakeIsNotTownB :
    setup.positionOnMap .lakeL ≠ setup.positionOnMap .townB

/-!
The governing straight-route, constant-speed kinematics for the two cars.
The same duration appears in both equations because the cars leave and arrive
simultaneously. No numerical value for car 2's speed occurs in these laws.
-/
structure SatisfiesStraightRouteKinematics
    (setup : LakeMeetingSetup) : Prop where
  carOneDistanceEqualsSpeedTimesTime :
    mapDistanceInKilometres setup .townA .lakeL =
      speedInKilometresPerHour (setup.speed .car1) *
        durationInHours setup.commonDrivingDuration
  carTwoDistanceEqualsSpeedTimesTime :
    mapDistanceInKilometres setup .townB .lakeL =
      speedInKilometresPerHour (setup.speed .car2) *
        durationInHours setup.commonDrivingDuration

/-! ## Multiple-choice values and formalization target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed printed beside each answer choice, in kilometres per hour. -/
def AnswerChoice.speedInKilometresPerHour : AnswerChoice → ℝ
  | .A => 671 / 10
  | .B => 273 / 5
  | .C => 344 / 5
  | .D => 327 / 10

/-!
A choice is closest when its displayed speed has no greater absolute error
than any other displayed speed. This preserves the multiple-choice semantics
without asserting that a rounded displayed value is the exact physical speed.
-/
def IsClosestAnswerChoice (speed : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |speed - AnswerChoice.speedInKilometresPerHour selected| ≤
      |speed - AnswerChoice.speedInKilometresPerHour other|

/-!
The cosine rule gives the exact speed readout shown in the first conjunct.
Numerically it is about `68.641 km/h`, so the recorded `68.8 km/h` is modeled
faithfully as the closest offered answer (choice C), rather than as a false
exact equality.

Blueprint label: `thm:physics:phyx_mini_0690:target`.
-/
theorem carTwoSpeed_is_answerChoiceC
    (setup : LakeMeetingSetup)
    (hScenario : MatchesDrivingScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalLakeMeetingParameters setup)
    (hKinematics : SatisfiesStraightRouteKinematics setup) :
    speedInKilometresPerHour (setup.speed .car2) =
        Real.sqrt
          ((80 : ℝ) ^ 2 + ((90 : ℝ) * (5 / 2)) ^ 2 -
            2 * 80 * (90 * (5 / 2)) *
              Real.cos (angleInRadiansFromDegrees 40)) /
          (5 / 2) ∧
      IsClosestAnswerChoice
        (speedInKilometresPerHour (setup.speed .car2)) .C := by
  let v := speedInKilometresPerHour (setup.speed .car2)
  have hTownDistance :
      mapDistanceInKilometres setup .townA .townB = 80 :=
    hFigure.townSeparationLabelMatchesMapGeometry.trans
      hFigure.townSeparationLabelIsEightyKilometres
  have hCarOneDistance :
      mapDistanceInKilometres setup .townA .lakeL =
        (90 : ℝ) * (5 / 2) := by
    calc
      mapDistanceInKilometres setup .townA .lakeL =
          speedInKilometresPerHour (setup.speed .car1) *
            durationInHours setup.commonDrivingDuration :=
        hKinematics.carOneDistanceEqualsSpeedTimesTime
      _ = (90 : ℝ) * (5 / 2) := by
        rw [hReadouts.carOneSpeedIsNinetyKilometresPerHour,
          hReadouts.commonDrivingDurationIsTwoPointFiveHours]
  have hCarTwoDistance :
      mapDistanceInKilometres setup .townB .lakeL = v * (5 / 2) := by
    calc
      mapDistanceInKilometres setup .townB .lakeL =
          speedInKilometresPerHour (setup.speed .car2) *
            durationInHours setup.commonDrivingDuration :=
        hKinematics.carTwoDistanceEqualsSpeedTimesTime
      _ = v * (5 / 2) := by
        rw [hReadouts.commonDrivingDurationIsTwoPointFiveHours]
  have hAngle :
      mapAngleAt setup .townB .townA .lakeL =
        angleInRadiansFromDegrees 40 := by
    rw [hFigure.angleLabelMatchesMapGeometry,
      hFigure.angleLabelAtTownAIsFortyDegrees]
  have hTownDistance' :
      dist (setup.positionOnMap .townB) (setup.positionOnMap .townA) = 80 := by
    rw [dist_comm]
    exact hTownDistance
  have hCarOneDistance' :
      dist (setup.positionOnMap .lakeL) (setup.positionOnMap .townA) =
        (90 : ℝ) * (5 / 2) := by
    rw [dist_comm]
    exact hCarOneDistance
  have hCarTwoDistance' :
      dist (setup.positionOnMap .townB) (setup.positionOnMap .lakeL) =
        v * (5 / 2) :=
    hCarTwoDistance
  have hAngle' :
      EuclideanGeometry.angle
          (setup.positionOnMap .townB)
          (setup.positionOnMap .townA)
          (setup.positionOnMap .lakeL) =
        angleInRadiansFromDegrees 40 :=
    hAngle
  have hSpeedSquare :
      (v * (5 / 2)) ^ 2 =
        (80 : ℝ) ^ 2 + ((90 : ℝ) * (5 / 2)) ^ 2 -
          2 * 80 * (90 * (5 / 2)) *
            Real.cos (angleInRadiansFromDegrees 40) := by
    simpa [pow_two, hTownDistance', hCarOneDistance',
      hCarTwoDistance', hAngle'] using
      (EuclideanGeometry.law_cos
        (setup.positionOnMap .townB)
        (setup.positionOnMap .townA)
        (setup.positionOnMap .lakeL))
  have hSpeedPositive : 0 < v :=
    hPhysical.carTwoSpeedPositive
  have hSquareRoot :
      Real.sqrt
          ((80 : ℝ) ^ 2 + ((90 : ℝ) * (5 / 2)) ^ 2 -
            2 * 80 * (90 * (5 / 2)) *
              Real.cos (angleInRadiansFromDegrees 40)) =
        v * (5 / 2) := by
    rw [← hSpeedSquare]
    exact Real.sqrt_sq (mul_nonneg hSpeedPositive.le (by norm_num))
  have hSpeedExact :
      v =
        Real.sqrt
          ((80 : ℝ) ^ 2 + ((90 : ℝ) * (5 / 2)) ^ 2 -
            2 * 80 * (90 * (5 / 2)) *
              Real.cos (angleInRadiansFromDegrees 40)) /
          (5 / 2) := by
    nlinarith

  have hFortyDegrees :
      angleInRadiansFromDegrees 40 = 2 * Real.pi / 9 := by
    unfold angleInRadiansFromDegrees
    ring
  have hCosPolynomial :
      4 * Real.cos (2 * Real.pi / 9) ^ 3 -
          3 * Real.cos (2 * Real.pi / 9) = -(1 / 2 : ℝ) := by
    calc
      4 * Real.cos (2 * Real.pi / 9) ^ 3 -
            3 * Real.cos (2 * Real.pi / 9) =
          Real.cos (3 * (2 * Real.pi / 9)) :=
        (Real.cos_three_mul (2 * Real.pi / 9)).symm
      _ = Real.cos (Real.pi - Real.pi / 3) := by
        congr 1
        ring
      _ = -Real.cos (Real.pi / 3) := Real.cos_pi_sub _
      _ = -(1 / 2 : ℝ) := by rw [Real.cos_pi_div_three]
  have hCosUpper :
      Real.cos (angleInRadiansFromDegrees 40) < (39 / 50 : ℝ) := by
    rw [hFortyDegrees]
    by_contra h
    push Not at h
    have hFactor :
        0 < 4 * (Real.cos (2 * Real.pi / 9) ^ 2 +
            Real.cos (2 * Real.pi / 9) * (39 / 50) +
              (39 / 50 : ℝ) ^ 2) - 3 := by
      nlinarith [
        sq_nonneg (Real.cos (2 * Real.pi / 9) - (39 / 50 : ℝ))]
    have hProduct :
        0 ≤ (Real.cos (2 * Real.pi / 9) - (39 / 50 : ℝ)) *
          (4 * (Real.cos (2 * Real.pi / 9) ^ 2 +
            Real.cos (2 * Real.pi / 9) * (39 / 50) +
              (39 / 50 : ℝ) ^ 2) - 3) :=
      mul_nonneg (sub_nonneg.mpr h) hFactor.le
    nlinarith
  have hSpeedLower : (1359 / 20 : ℝ) ≤ v := by
    by_contra h
    push Not at h
    have hProduct :
        0 < ((1359 / 20 : ℝ) - v) * ((1359 / 20 : ℝ) + v) := by
      exact mul_pos (sub_pos.mpr h) (by nlinarith)
    nlinarith

  change v =
      Real.sqrt
        ((80 : ℝ) ^ 2 + ((90 : ℝ) * (5 / 2)) ^ 2 -
          2 * 80 * (90 * (5 / 2)) *
            Real.cos (angleInRadiansFromDegrees 40)) /
        (5 / 2) ∧
      IsClosestAnswerChoice v .C
  constructor
  · exact hSpeedExact
  · unfold IsClosestAnswerChoice
    intro other
    cases other
    case A =>
      simp only [AnswerChoice.speedInKilometresPerHour]
      by_cases hC : (344 / 5 : ℝ) ≤ v
      · rw [abs_of_nonneg (sub_nonneg.mpr hC),
            abs_of_nonneg
              (sub_nonneg.mpr (by nlinarith : (671 / 10 : ℝ) ≤ v))]
        norm_num at *
        linarith
      · have hvC : v ≤ (344 / 5 : ℝ) := le_of_not_ge hC
        rw [abs_of_nonpos (sub_nonpos.mpr hvC),
            abs_of_nonneg
              (sub_nonneg.mpr (by nlinarith : (671 / 10 : ℝ) ≤ v))]
        norm_num at *
        linarith
    case B =>
      simp only [AnswerChoice.speedInKilometresPerHour]
      by_cases hC : (344 / 5 : ℝ) ≤ v
      · rw [abs_of_nonneg (sub_nonneg.mpr hC),
            abs_of_nonneg
              (sub_nonneg.mpr (by nlinarith : (273 / 5 : ℝ) ≤ v))]
        norm_num at *
        linarith
      · have hvC : v ≤ (344 / 5 : ℝ) := le_of_not_ge hC
        rw [abs_of_nonpos (sub_nonpos.mpr hvC),
            abs_of_nonneg
              (sub_nonneg.mpr (by nlinarith : (273 / 5 : ℝ) ≤ v))]
        norm_num at *
        linarith
    case C => simp
    case D =>
      simp only [AnswerChoice.speedInKilometresPerHour]
      by_cases hC : (344 / 5 : ℝ) ≤ v
      · rw [abs_of_nonneg (sub_nonneg.mpr hC),
            abs_of_nonneg
              (sub_nonneg.mpr (by nlinarith : (327 / 10 : ℝ) ≤ v))]
        norm_num at *
        linarith
      · have hvC : v ≤ (344 / 5 : ℝ) := le_of_not_ge hC
        rw [abs_of_nonpos (sub_nonpos.mpr hvC),
            abs_of_nonneg
              (sub_nonneg.mpr (by nlinarith : (327 / 10 : ℝ) ≤ v))]
        norm_num at *
        linarith

end PhyXMiniProblems.ProblemPhyXMini0690
