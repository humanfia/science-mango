import Mathlib.Geometry.Euclidean.Triangle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Equal-time race along and across a two-sided snake

The physical snake has total length `420 m` and is laid out as two straight
segments meeting at `105°`; one segment is `240 m`.  Olaf follows the full
snake, whereas Inge follows the straight chord from tail to head.  Lengths,
durations, and speeds are unit-independent Physlib quantities.  Real numbers
occur only as calibrated readouts, planar coordinates in metres, angles in
radians, and displayed answer values.

The supplied raster shows the tail at the left, a bend near the upper right,
and the tongue-bearing head below that bend.  It contains no printed metric
labels, so the numerical geometry is kept in the separate problem-data and
angle-readout predicates below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0680

open Dimension

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of any chosen unit system. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, independent of any chosen unit system. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical speed from Physlib's unit-independent speed API. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({UnitChoices.SI with length := unit} : UnitChoices)).val : ℝ)

/-- Read a physical duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration ({UnitChoices.SI with time := unit} : UnitChoices)).val : ℝ)

/-- Read a physical speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed ({UnitChoices.SI with
    length := lengthUnit, time := timeUnit} : UnitChoices)).val : ℝ)

/-- Convert the degree value printed in the problem to a radian readout. -/
def radiansFromDegrees (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Race, route, and primary-figure vocabulary -/

/-- The three physically distinguished points along the laid-out snake. -/
inductive SnakeVertex where
  | tail
  | bend
  | head
  deriving DecidableEq, Fintype, Repr

/-- The two straight pieces of the snake, in tail-to-head order. -/
inductive SnakeSide where
  | tailToBend
  | bendToHead
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint of each oriented straight side. -/
def SnakeSide.startVertex : SnakeSide → SnakeVertex
  | .tailToBend => .tail
  | .bendToHead => .bend

/-- Final endpoint of each oriented straight side. -/
def SnakeSide.finishVertex : SnakeSide → SnakeVertex
  | .tailToBend => .bend
  | .bendToHead => .head

/-- The two named children who run the race. -/
inductive Runner where
  | Inge
  | Olaf
  deriving DecidableEq, Fintype, Repr

/-- The direct chord and the route following the snake itself. -/
inductive RaceRoute where
  | directTailToHead
  | alongSnake
  deriving DecidableEq, Fintype, Repr

/-- Qualitative park features visibly present in the supplied raster. -/
inductive ParkFigureFeature where
  | colorfulPatternedSnake
  | severalTrees
  | windingPath
  | adjacentWater
  deriving DecidableEq, Fintype, Repr

/--
Planar physical layout associated with the primary figure.  Coordinates are
metre readouts; physical distances themselves remain `LengthQuantity` values.
-/
structure SnakeParkFigure where
  pointMeters : SnakeVertex → EuclideanSpace ℝ (Fin 2)
  featureShown : ParkFigureFeature → Bool
  twoStraightRunsShown : Bool
  tailShownLeftOfBend : Bool
  headShownBelowBend : Bool
  headHasForkedTongue : Bool
  printedMetricLabelsPresent : Bool

/--
Independent observables and assignments in the race.  In particular, Olaf's
speed and the tail-to-head chord length are not defined from the answer choice.
-/
structure SnakeRaceSetup where
  totalSnakeLength : LengthQuantity
  sideLength : SnakeSide → LengthQuantity
  directTailToHeadDistance : LengthQuantity
  runnerRoute : Runner → RaceRoute
  runnerStart : Runner → SnakeVertex
  runnerFinish : Runner → SnakeVertex
  runnerMovesAtConstantSpeed : Runner → Bool
  runnerSpeed : Runner → SpeedQuantity
  runnerElapsedTime : Runner → DurationQuantity
  startsAtSameMoment : Bool
  figure : SnakeParkFigure

/-- The physical distance assigned to either possible race route. -/
def routeDistance
    (setup : SnakeRaceSetup) : RaceRoute → LengthQuantity
  | .directTailToHead => setup.directTailToHeadDistance
  | .alongSnake => setup.totalSnakeLength

/-! ## Scenario, primary-image evidence, and numerical readouts -/

/-- Runner identities, endpoints, routes, and constant-speed roles from the prose. -/
structure MatchesSnakeRaceScenario (setup : SnakeRaceSetup) : Prop where
  IngeStartsAtTail : setup.runnerStart .Inge = .tail
  OlafStartsAtTail : setup.runnerStart .Olaf = .tail
  IngeFinishesAtHead : setup.runnerFinish .Inge = .head
  OlafFinishesAtHead : setup.runnerFinish .Olaf = .head
  IngeTakesDirectRoute : setup.runnerRoute .Inge = .directTailToHead
  OlafRunsAlongSnake : setup.runnerRoute .Olaf = .alongSnake
  IngeRunsAtConstantSpeed : setup.runnerMovesAtConstantSpeed .Inge = true
  OlafRunsAtConstantSpeed : setup.runnerMovesAtConstantSpeed .Olaf = true
  simultaneousStart : setup.startsAtSameMoment = true

/--
Qualitative evidence and bend geometry read from `680.png`.  The angle is a
given geometric datum, not a conclusion about either runner's speed.
-/
structure MatchesSuppliedSnakeFigure (setup : SnakeRaceSetup) : Prop where
  allParkFeaturesShown : ∀ feature, setup.figure.featureShown feature = true
  twoStraightRuns : setup.figure.twoStraightRunsShown = true
  tailAtLeft : setup.figure.tailShownLeftOfBend = true
  headBelowBend : setup.figure.headShownBelowBend = true
  tongueIdentifiesHead : setup.figure.headHasForkedTongue = true
  noPrintedMetricLabels : setup.figure.printedMetricLabelsPresent = false
  bendAngleIs105Degrees :
    EuclideanGeometry.angle
        (setup.figure.pointMeters .tail)
        (setup.figure.pointMeters .bend)
        (setup.figure.pointMeters .head) =
      radiansFromDegrees 105

/--
Numerical data stated in the problem.  Which of the two sides has length
`240 m` is deliberately left open because the prose does not name that side.
No value for Olaf's speed or the derived second side occurs here.
-/
structure MatchesProblemReadouts (setup : SnakeRaceSetup) : Prop where
  totalLengthMeters :
    lengthReadout LengthUnit.meters setup.totalSnakeLength = 420
  oneSideLengthMeters :
    ∃ side : SnakeSide,
      lengthReadout LengthUnit.meters (setup.sideLength side) = 240
  IngeSpeedKilometersPerHour :
    speedReadout LengthUnit.kilometers TimeUnit.hours
        (setup.runnerSpeed .Inge) = 12

/-! ## Geometric and kinematic laws -/

/--
The two dimensionful side lengths realize the two straight planar segments;
the direct route realizes the endpoint chord; and the route along the snake is
the sum of its two sides.  The cosine rule itself is supplied by Mathlib as
`EuclideanGeometry.law_cos` and is therefore not postulated as a custom law.
-/
structure SatisfiesTwoStraightSideGeometry
    (setup : SnakeRaceSetup) : Prop where
  sideLengthMatchesPlanarDistance : ∀ side : SnakeSide,
    lengthReadout LengthUnit.meters (setup.sideLength side) =
      dist
        (setup.figure.pointMeters side.startVertex)
        (setup.figure.pointMeters side.finishVertex)
  directLengthMatchesEndpointChord :
    lengthReadout LengthUnit.meters setup.directTailToHeadDistance =
      dist
        (setup.figure.pointMeters .tail)
        (setup.figure.pointMeters .head)
  totalRouteIsSideSum : ∀ unit : LengthUnit,
    lengthReadout unit setup.totalSnakeLength =
      lengthReadout unit (setup.sideLength .tailToBend) +
        lengthReadout unit (setup.sideLength .bendToHead)

/-- Positivity conditions selecting the physical branch of lengths and times. -/
structure HasPhysicalRaceParameters (setup : SnakeRaceSetup) : Prop where
  totalLengthPositive : ∀ unit,
    0 < lengthReadout unit setup.totalSnakeLength
  sideLengthsPositive : ∀ side unit,
    0 < lengthReadout unit (setup.sideLength side)
  directDistancePositive : ∀ unit,
    0 < lengthReadout unit setup.directTailToHeadDistance
  runnerSpeedsPositive : ∀ runner lengthUnit timeUnit,
    0 < speedReadout lengthUnit timeUnit (setup.runnerSpeed runner)
  runnerTimesPositive : ∀ runner timeUnit,
    0 < durationReadout timeUnit (setup.runnerElapsedTime runner)

/--
For each constant-speed runner, distance equals speed times elapsed time in
every coherent choice of length and time units.  This is the governing
uniform-motion law and contains no numerical value for Olaf's speed.
-/
structure SatisfiesConstantSpeedRaceKinematics
    (setup : SnakeRaceSetup) : Prop where
  distanceEqualsSpeedTimesTime : ∀ runner lengthUnit timeUnit,
    lengthReadout lengthUnit
        (routeDistance setup (setup.runnerRoute runner)) =
      speedReadout lengthUnit timeUnit (setup.runnerSpeed runner) *
        durationReadout timeUnit (setup.runnerElapsedTime runner)

/--
The condition imposed by the question: after the simultaneous start, the two
runners reach the common endpoint at the same time.  It equates durations but
does not constrain Olaf's speed to any proposed answer value.
-/
structure ReachesHeadAtSameTime (setup : SnakeRaceSetup) : Prop where
  equalElapsedTimes : ∀ unit : TimeUnit,
    durationReadout unit (setup.runnerElapsedTime .Olaf) =
      durationReadout unit (setup.runnerElapsedTime .Inge)

/-! ## Derived chord, displayed choices, and current target -/

/-- Labels of the four speeds printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed readout in kilometres per hour printed beside each answer label. -/
def displayedSpeedKilometersPerHour : AnswerChoice → ℝ
  | .A => 16
  | .B => 24
  | .C => 15
  | .D => 18

/-- Agreement with a speed displayed to the nearest `0.1 km/h`. -/
def MatchesDisplayedSpeed
    (speed : SpeedQuantity) (choice : AnswerChoice) : Prop :=
  |speedReadout LengthUnit.kilometers TimeUnit.hours speed -
      displayedSpeedKilometersPerHour choice| < 1 / 20

/--
The unstated side is `180 m`; applying Mathlib's cosine rule to the three
planar vertices gives the exact endpoint-chord readout.  This derived geometry
is a lemma, not a premise of the race theorem.
-/
lemma directTailToHeadDistanceMeters
    (setup : SnakeRaceSetup)
    (_figure : MatchesSuppliedSnakeFigure setup)
    (_data : MatchesProblemReadouts setup)
    (_geometry : SatisfiesTwoStraightSideGeometry setup)
    (_physical : HasPhysicalRaceParameters setup) :
    lengthReadout LengthUnit.meters setup.directTailToHeadDistance =
      Real.sqrt
        ((240 : ℝ) ^ 2 + (180 : ℝ) ^ 2 -
          2 * 240 * 180 * Real.cos (radiansFromDegrees 105)) := by
  rcases _data.oneSideLengthMeters with ⟨side, hside⟩
  have hsum := _geometry.totalRouteIsSideSum LengthUnit.meters
  rw [_data.totalLengthMeters] at hsum
  have hcos := EuclideanGeometry.law_cos
    (setup.figure.pointMeters .tail)
    (setup.figure.pointMeters .bend)
    (setup.figure.pointMeters .head)
  have htailToBend :
      lengthReadout LengthUnit.meters
          (setup.sideLength .tailToBend) =
        dist (setup.figure.pointMeters .tail)
          (setup.figure.pointMeters .bend) := by
    simpa only [SnakeSide.startVertex, SnakeSide.finishVertex] using
      _geometry.sideLengthMatchesPlanarDistance .tailToBend
  have hbendToHead :
      lengthReadout LengthUnit.meters
          (setup.sideLength .bendToHead) =
        dist (setup.figure.pointMeters .bend)
          (setup.figure.pointMeters .head) := by
    simpa only [SnakeSide.startVertex, SnakeSide.finishVertex] using
      _geometry.sideLengthMatchesPlanarDistance .bendToHead
  rw [← _geometry.directLengthMatchesEndpointChord,
    ← htailToBend,
    dist_comm (setup.figure.pointMeters .head)
      (setup.figure.pointMeters .bend),
    ← hbendToHead,
    _figure.bendAngleIs105Degrees] at hcos
  have hd_nonneg :
      0 ≤ lengthReadout LengthUnit.meters setup.directTailToHeadDistance :=
    (_physical.directDistancePositive LengthUnit.meters).le
  cases side with
  | tailToBend =>
      have hother :
          lengthReadout LengthUnit.meters
              (setup.sideLength .bendToHead) = 180 := by
        linarith
      calc
        lengthReadout LengthUnit.meters setup.directTailToHeadDistance =
            Real.sqrt
              ((lengthReadout LengthUnit.meters
                  setup.directTailToHeadDistance) ^ 2) :=
          (Real.sqrt_sq hd_nonneg).symm
        _ = Real.sqrt
              ((240 : ℝ) ^ 2 + (180 : ℝ) ^ 2 -
                2 * 240 * 180 *
                  Real.cos (radiansFromDegrees 105)) := by
          congr 1
          rw [hside, hother] at hcos
          nlinarith
  | bendToHead =>
      have hother :
          lengthReadout LengthUnit.meters
              (setup.sideLength .tailToBend) = 180 := by
        linarith
      calc
        lengthReadout LengthUnit.meters setup.directTailToHeadDistance =
            Real.sqrt
              ((lengthReadout LengthUnit.meters
                  setup.directTailToHeadDistance) ^ 2) :=
          (Real.sqrt_sq hd_nonneg).symm
        _ = Real.sqrt
              ((240 : ℝ) ^ 2 + (180 : ℝ) ^ 2 -
                2 * 240 * 180 *
                  Real.cos (radiansFromDegrees 105)) := by
          congr 1
          rw [hother, hside] at hcos
          nlinarith

/--
Equal travel times imply that Olaf's speed is Inge's speed multiplied by the
route-length ratio.  The exact trigonometric expression is approximately
`15.0356 km/h`, hence it agrees with the displayed `15.0 km/h` answer C, and
no other displayed choice lies in that one-decimal rounding interval.

Blueprint label: `thm:physics:phyx_mini_0680:target`.
-/
theorem problem_phyx_mini_0680
    (setup : SnakeRaceSetup)
    (_scenario : MatchesSnakeRaceScenario setup)
    (_figure : MatchesSuppliedSnakeFigure setup)
    (_data : MatchesProblemReadouts setup)
    (_geometry : SatisfiesTwoStraightSideGeometry setup)
    (_physical : HasPhysicalRaceParameters setup)
    (_kinematics : SatisfiesConstantSpeedRaceKinematics setup)
    (_sameFinish : ReachesHeadAtSameTime setup) :
    speedReadout LengthUnit.kilometers TimeUnit.hours
        (setup.runnerSpeed .Olaf) =
        (12 * 420) /
          Real.sqrt
            ((240 : ℝ) ^ 2 + (180 : ℝ) ^ 2 -
              2 * 240 * 180 * Real.cos (radiansFromDegrees 105)) ∧
      MatchesDisplayedSpeed (setup.runnerSpeed .Olaf) .C ∧
      ∀ choice : AnswerChoice,
        MatchesDisplayedSpeed (setup.runnerSpeed .Olaf) choice → choice = .C := by
  have lengthReadout_kilometers (length : LengthQuantity) :
      lengthReadout LengthUnit.kilometers length =
        lengthReadout LengthUnit.meters length / 1000 := by
    have hscale := length.property
      ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
      ({UnitChoices.SI with length := LengthUnit.kilometers} : UnitChoices)
    change
      length ({UnitChoices.SI with
          length := LengthUnit.kilometers} : UnitChoices) =
        UnitChoices.dimScale
            ({UnitChoices.SI with
              length := LengthUnit.meters} : UnitChoices)
            ({UnitChoices.SI with
              length := LengthUnit.kilometers} : UnitChoices) L𝓭 •
          length ({UnitChoices.SI with
            length := LengthUnit.meters} : UnitChoices) at hscale
    have hdim :
        UnitChoices.dimScale
            ({UnitChoices.SI with
              length := LengthUnit.meters} : UnitChoices)
            ({UnitChoices.SI with
              length := LengthUnit.kilometers} : UnitChoices) L𝓭 =
          (1000 : NNReal)⁻¹ := by
      ext
      norm_num [UnitChoices.dimScale, LengthUnit.kilometers,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
        Dimension.L𝓭]
      rfl
    change
      (((length ({UnitChoices.SI with
        length := LengthUnit.kilometers} : UnitChoices)).val : NNReal) : ℝ) =
        (((length ({UnitChoices.SI with
          length := LengthUnit.meters} : UnitChoices)).val : NNReal) : ℝ) / 1000
    rw [hscale, hdim]
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul, NNReal.coe_inv]
    norm_num
    ring
  let chordFormula : ℝ :=
    Real.sqrt
      ((240 : ℝ) ^ 2 + (180 : ℝ) ^ 2 -
        2 * 240 * 180 * Real.cos (radiansFromDegrees 105))
  have hchordMeters :
      lengthReadout LengthUnit.meters setup.directTailToHeadDistance =
        chordFormula := by
    exact directTailToHeadDistanceMeters setup _figure _data _geometry _physical
  have hchordKilometers :
      lengthReadout LengthUnit.kilometers setup.directTailToHeadDistance =
        chordFormula / 1000 := by
    rw [lengthReadout_kilometers, hchordMeters]
  have htotalKilometers :
      lengthReadout LengthUnit.kilometers setup.totalSnakeLength =
        420 / 1000 := by
    rw [lengthReadout_kilometers, _data.totalLengthMeters]
  have hInge := _kinematics.distanceEqualsSpeedTimesTime
    Runner.Inge LengthUnit.kilometers TimeUnit.hours
  have hOlaf := _kinematics.distanceEqualsSpeedTimesTime
    Runner.Olaf LengthUnit.kilometers TimeUnit.hours
  rw [_scenario.IngeTakesDirectRoute] at hInge
  rw [_scenario.OlafRunsAlongSnake] at hOlaf
  change
    lengthReadout LengthUnit.kilometers setup.directTailToHeadDistance =
      speedReadout LengthUnit.kilometers TimeUnit.hours
          (setup.runnerSpeed .Inge) *
        durationReadout TimeUnit.hours (setup.runnerElapsedTime .Inge) at hInge
  change
    lengthReadout LengthUnit.kilometers setup.totalSnakeLength =
      speedReadout LengthUnit.kilometers TimeUnit.hours
          (setup.runnerSpeed .Olaf) *
        durationReadout TimeUnit.hours (setup.runnerElapsedTime .Olaf) at hOlaf
  rw [hchordKilometers, _data.IngeSpeedKilometersPerHour] at hInge
  rw [htotalKilometers, _sameFinish.equalElapsedTimes TimeUnit.hours] at hOlaf
  have hchordPositive : 0 < chordFormula := by
    rw [← hchordMeters]
    exact _physical.directDistancePositive LengthUnit.meters
  have hspeed :
      speedReadout LengthUnit.kilometers TimeUnit.hours
          (setup.runnerSpeed .Olaf) =
        (12 * 420) / chordFormula := by
    apply (eq_div_iff hchordPositive.ne').2
    calc
      speedReadout LengthUnit.kilometers TimeUnit.hours
            (setup.runnerSpeed .Olaf) * chordFormula =
          speedReadout LengthUnit.kilometers TimeUnit.hours
              (setup.runnerSpeed .Olaf) *
            (12000 *
              durationReadout TimeUnit.hours
                (setup.runnerElapsedTime .Inge)) := by
        congr 1
        linarith
      _ = 12000 *
            (speedReadout LengthUnit.kilometers TimeUnit.hours
                (setup.runnerSpeed .Olaf) *
              durationReadout TimeUnit.hours
                (setup.runnerElapsedTime .Inge)) := by ring
      _ = 12000 * (420 / 1000) := by rw [← hOlaf]
      _ = 12 * 420 := by norm_num
  have hangle :
      radiansFromDegrees 105 = Real.pi / 3 + Real.pi / 4 := by
    unfold radiansFromDegrees
    ring
  have hsqrtSix :
      Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    have h := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) 2
    norm_num at h
    exact h
  have hcos :
      Real.cos (radiansFromDegrees 105) =
        (Real.sqrt 2 - Real.sqrt 6) / 4 := by
    rw [hangle, Real.cos_add, Real.cos_pi_div_three,
      Real.sin_pi_div_three, Real.cos_pi_div_four,
      Real.sin_pi_div_four, hsqrtSix]
    ring
  have hsqrtTwoLower : (1414 : ℝ) / 1000 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hsqrtTwoUpper : Real.sqrt 2 < (1415 : ℝ) / 1000 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hsqrtSixLower : (2449 : ℝ) / 1000 < Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      Real.sqrt_nonneg 6]
  have hsqrtSixUpper : Real.sqrt 6 < (2450 : ℝ) / 1000 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      Real.sqrt_nonneg 6]
  have hcosLower :
      (-259 : ℝ) / 1000 < Real.cos (radiansFromDegrees 105) := by
    rw [hcos]
    linarith
  have hcosUpper :
      Real.cos (radiansFromDegrees 105) < (-258 : ℝ) / 1000 := by
    rw [hcos]
    linarith
  have hradicandPositive :
      0 <
        (240 : ℝ) ^ 2 + (180 : ℝ) ^ 2 -
          2 * 240 * 180 * Real.cos (radiansFromDegrees 105) := by
    nlinarith
  have hchordSquared :
      chordFormula ^ 2 =
        (240 : ℝ) ^ 2 + (180 : ℝ) ^ 2 -
          2 * 240 * 180 * Real.cos (radiansFromDegrees 105) := by
    dsimp [chordFormula]
    exact Real.sq_sqrt hradicandPositive.le
  have hchordLower : (3349 : ℝ) / 10 < chordFormula := by
    have hnonneg : 0 ≤ chordFormula := by
      dsimp [chordFormula]
      exact Real.sqrt_nonneg _
    nlinarith
  have hchordUpper : chordFormula < 337 := by
    have hnonneg : 0 ≤ chordFormula := by
      dsimp [chordFormula]
      exact Real.sqrt_nonneg _
    nlinarith
  have hspeedLower : (1495 : ℝ) / 100 < (12 * 420) / chordFormula := by
    apply (lt_div_iff₀ hchordPositive).2
    nlinarith
  have hspeedUpper : (12 * 420) / chordFormula < (1505 : ℝ) / 100 := by
    apply (div_lt_iff₀ hchordPositive).2
    nlinarith
  refine ⟨hspeed, ?_, ?_⟩
  · rw [MatchesDisplayedSpeed, displayedSpeedKilometersPerHour, hspeed, abs_lt]
    constructor <;> norm_num at hspeedLower hspeedUpper ⊢ <;> linarith
  · intro choice hchoice
    cases choice with
    | A =>
        exfalso
        rw [MatchesDisplayedSpeed, displayedSpeedKilometersPerHour,
          hspeed, abs_lt] at hchoice
        norm_num at hchoice hspeedUpper
        linarith
    | B =>
        exfalso
        rw [MatchesDisplayedSpeed, displayedSpeedKilometersPerHour,
          hspeed, abs_lt] at hchoice
        norm_num at hchoice hspeedUpper
        linarith
    | C => rfl
    | D =>
        exfalso
        rw [MatchesDisplayedSpeed, displayedSpeedKilometersPerHour,
          hspeed, abs_lt] at hchoice
        norm_num at hchoice hspeedUpper
        linarith

end PhyXMiniProblems.ProblemPhyXMini0680
