import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0674

open Dimension

/-!
# Stopping position of a car crossing an intersection

North is the positive longitudinal direction.  The blue car's nose crosses
from the south edge to the north edge of a `28.0 m`-wide intersection in
`3.10 s`, while its constant acceleration has magnitude `2.10 m/s²` and
points south.  The question asks for the nose's distance from the south edge
when the car stops.

Lengths, times, signed velocities, and signed accelerations are represented by
unit-independent Physlib quantities.  Real numbers occur only as calibrated
readouts, figure annotations, and displayed answer values.  In particular,
the stopping position is an independent trajectory value and is not defined
from the recorded answer.

Assumption/target split:

* governing laws: one-dimensional constant-acceleration position and velocity
  evolution, with north chosen positive;
* previous-part results: none;
* data and figure readouts: the `4.52 m` blue-car length, `28.0 m` edge
  separation, `3.10 s` crossing interval, `2.10 m/s²` southward acceleration,
  the two perpendicular roadways, compass directions, car placements, and the
  `a_R`, `v_B`, and `a_B` arrows;
* current target conclusions: the exact stopping-distance expression, its
  agreement with `35.9 m` to the displayed tenth-metre precision, and choice C
  being the closest displayed answer.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A physical length or signed longitudinal position. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time coordinate or time interval. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A signed one-dimensional velocity, with north represented by positive readout. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A signed one-dimensional acceleration. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical length in the length unit of a coherent unit choice. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  (length units).val

/-- Read a physical time in the time unit of a coherent unit choice. -/
def timeReadout (units : UnitChoices) (time : TimeQuantity) : ℝ :=
  (time units).val

/-- Read a signed velocity in the speed unit induced by a coherent unit choice. -/
def velocityReadout
    (units : UnitChoices) (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity units).val

/-- Read a signed acceleration in the acceleration unit induced by a unit choice. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration units).val

/-! ## Primary-image vocabulary -/

/-- The two cars distinguished by color in the supplied figure. -/
inductive CarColor where
  | red
  | blue
  deriving DecidableEq, Fintype, Repr

/-- Cardinal directions printed on the compass rose. -/
inductive CardinalDirection where
  | north
  | east
  | south
  | west
  deriving DecidableEq, Fintype, Repr

/-- Literal compass labels shown in the image. -/
inductive CompassLabel where
  | N
  | E
  | S
  | W
  deriving DecidableEq, Fintype, Repr

/-- The two perpendicular roadway axes visible in the image. -/
inductive RoadwayAxis where
  | northSouth
  | eastWest
  deriving DecidableEq, Fintype, Repr

/-- Approach lanes in which the two cars are drawn. -/
inductive FigurePlacement where
  | southApproach
  | westApproach
  deriving DecidableEq, Fintype, Repr

/-- The near and far intersection edges relevant to the blue car. -/
inductive IntersectionEdge where
  | south
  | north
  | west
  | east
  deriving DecidableEq, Fintype, Repr

/-- Literal vector labels printed beside the arrows in the supplied figure. -/
inductive FigureVectorLabel where
  | aR
  | vB
  | aB
  deriving DecidableEq, Fintype, Repr

/-- Qualitative geometry and labels transcribed from the primary bitmap. -/
structure IntersectionFigure where
  roadwayAxis : CarColor → RoadwayAxis
  carPlacement : CarColor → FigurePlacement
  vectorOwner : FigureVectorLabel → CarColor
  vectorDirection : FigureVectorLabel → CardinalDirection
  compassDirection : CompassLabel → CardinalDirection
  widthMarkerNearEdge : IntersectionEdge
  widthMarkerFarEdge : IntersectionEdge
  widthLabelMeters : ℝ

/-! ## Physical setup -/

/-!
The physical quantities of the blue-car trajectory and the supplied figure.
The stopping time and stopping position are unconstrained fields here; their
physical relations occur only in the premise predicates below.
-/
structure RoadIntersectionSetup where
  blueCarLength : LengthQuantity
  intersectionWidth : LengthQuantity
  southEdgePosition : LengthQuantity
  northEdgePosition : LengthQuantity
  southEdgeCrossingTime : TimeQuantity
  northEdgeCrossingTime : TimeQuantity
  stopTime : TimeQuantity
  blueNosePosition : TimeQuantity → LengthQuantity
  blueVelocity : TimeQuantity → SignedVelocityQuantity
  blueAcceleration : SignedAccelerationQuantity
  figure : IntersectionFigure

/-! ## Stated data and primary-image evidence -/

/--
Numerical data stated in the prose, read in SI units.  The acceleration is
signed because north is positive, so the stated southward `2.10 m/s²` is
represented by `-2.10`.
-/
structure MatchesProblemStatement (setup : RoadIntersectionSetup) : Prop where
  blueCarLengthMeters :
    lengthReadout UnitChoices.SI setup.blueCarLength = 452 / 100
  intersectionWidthMeters :
    lengthReadout UnitChoices.SI setup.intersectionWidth = 28
  edgeSeparationMeters :
    lengthReadout UnitChoices.SI setup.northEdgePosition -
        lengthReadout UnitChoices.SI setup.southEdgePosition =
      lengthReadout UnitChoices.SI setup.intersectionWidth
  noseAtSouthEdgeInitially :
    setup.blueNosePosition setup.southEdgeCrossingTime =
      setup.southEdgePosition
  noseAtNorthEdgeAfterCrossing :
    setup.blueNosePosition setup.northEdgeCrossingTime =
      setup.northEdgePosition
  edgeCrossingTimeSeconds :
    timeReadout UnitChoices.SI setup.northEdgeCrossingTime -
        timeReadout UnitChoices.SI setup.southEdgeCrossingTime =
      31 / 10
  signedAccelerationMetersPerSecondSquared :
    accelerationReadout UnitChoices.SI setup.blueAcceleration = -(21 / 10)

/--
Primary-image readout: the blue car is on the south approach and points north,
the red car is on the west approach, `a_R` points east, `v_B` points north,
`a_B` points south, and the `28.0 m` marker spans the south and north edges.
-/
structure MatchesPrimaryFigure (setup : RoadIntersectionSetup) : Prop where
  blueRoadwayIsNorthSouth : setup.figure.roadwayAxis .blue = .northSouth
  redRoadwayIsEastWest : setup.figure.roadwayAxis .red = .eastWest
  blueCarOnSouthApproach : setup.figure.carPlacement .blue = .southApproach
  redCarOnWestApproach : setup.figure.carPlacement .red = .westApproach
  redAccelerationOwner : setup.figure.vectorOwner .aR = .red
  blueVelocityOwner : setup.figure.vectorOwner .vB = .blue
  blueAccelerationOwner : setup.figure.vectorOwner .aB = .blue
  redAccelerationPointsEast :
    setup.figure.vectorDirection .aR = .east
  blueVelocityPointsNorth :
    setup.figure.vectorDirection .vB = .north
  blueAccelerationPointsSouth :
    setup.figure.vectorDirection .aB = .south
  compassN : setup.figure.compassDirection .N = .north
  compassE : setup.figure.compassDirection .E = .east
  compassS : setup.figure.compassDirection .S = .south
  compassW : setup.figure.compassDirection .W = .west
  widthMarkerStartsAtSouthEdge :
    setup.figure.widthMarkerNearEdge = .south
  widthMarkerEndsAtNorthEdge :
    setup.figure.widthMarkerFarEdge = .north
  widthMarkerLabelMeters : setup.figure.widthLabelMeters = 28
  widthMarkerAgreesWithPhysicalWidth :
    setup.figure.widthLabelMeters =
      lengthReadout UnitChoices.SI setup.intersectionWidth

/-!
Positivity, direction, and the defining readout of the selected future stop.
These conditions identify the physical branch but do not constrain the
stopping position or mention a displayed answer.
-/
structure HasPhysicalStoppingEvent (setup : RoadIntersectionSetup) : Prop where
  carLengthPositive :
    0 < lengthReadout UnitChoices.SI setup.blueCarLength
  intersectionWidthPositive :
    0 < lengthReadout UnitChoices.SI setup.intersectionWidth
  northEdgeNorthOfSouthEdge :
    lengthReadout UnitChoices.SI setup.southEdgePosition <
      lengthReadout UnitChoices.SI setup.northEdgePosition
  northEdgeCrossedLater :
    timeReadout UnitChoices.SI setup.southEdgeCrossingTime <
      timeReadout UnitChoices.SI setup.northEdgeCrossingTime
  initialVelocityPointsNorth :
    0 < velocityReadout UnitChoices.SI
      (setup.blueVelocity setup.southEdgeCrossingTime)
  accelerationPointsSouth :
    accelerationReadout UnitChoices.SI setup.blueAcceleration < 0
  selectedStopOccursLater :
    timeReadout UnitChoices.SI setup.southEdgeCrossingTime <
      timeReadout UnitChoices.SI setup.stopTime
  velocityAtSelectedStop :
    velocityReadout UnitChoices.SI (setup.blueVelocity setup.stopTime) = 0

/-! ## Governing constant-acceleration laws -/

/--
One-dimensional constant-acceleration kinematics, stated relative to the
instant when the blue car's nose reaches the south edge.  The same relations
hold in every coherent choice of units.  This interface contains no stopping
distance, answer value, or answer label.
-/
structure SatisfiesConstantAccelerationKinematics
    (setup : RoadIntersectionSetup) : Prop where
  velocityEvolution : ∀ units time,
    velocityReadout units (setup.blueVelocity time) =
      velocityReadout units
          (setup.blueVelocity setup.southEdgeCrossingTime) +
        accelerationReadout units setup.blueAcceleration *
          (timeReadout units time -
            timeReadout units setup.southEdgeCrossingTime)
  positionEvolution : ∀ units time,
    lengthReadout units (setup.blueNosePosition time) =
      lengthReadout units
          (setup.blueNosePosition setup.southEdgeCrossingTime) +
        velocityReadout units
            (setup.blueVelocity setup.southEdgeCrossingTime) *
          (timeReadout units time -
            timeReadout units setup.southEdgeCrossingTime) +
        (1 / 2) * accelerationReadout units setup.blueAcceleration *
          (timeReadout units time -
            timeReadout units setup.southEdgeCrossingTime) ^ 2

/-! ## Derived kinematics and displayed answer -/

/-- The requested signed northward distance of the stopped nose from the south edge. -/
def stoppingDistanceInMeters (setup : RoadIntersectionSetup) : ℝ :=
  lengthReadout UnitChoices.SI (setup.blueNosePosition setup.stopTime) -
    lengthReadout UnitChoices.SI setup.southEdgePosition

/--
The crossing data determine the blue car's speed as its nose enters the
intersection.  This is the first of the two constant-acceleration calculations
used by the problem.
-/
lemma initialVelocity_from_edgeCrossing
    (setup : RoadIntersectionSetup)
    (_problem : MatchesProblemStatement setup)
    (_laws : SatisfiesConstantAccelerationKinematics setup) :
    velocityReadout UnitChoices.SI
        (setup.blueVelocity setup.southEdgeCrossingTime) =
      (28 - (1 / 2) * (-(21 / 10)) * (31 / 10) ^ 2) / (31 / 10) := by
  have hposition :=
    _laws.positionEvolution UnitChoices.SI setup.northEdgeCrossingTime
  have hsouth :=
    congrArg (lengthReadout UnitChoices.SI)
      _problem.noseAtSouthEdgeInitially
  have hnorth :=
    congrArg (lengthReadout UnitChoices.SI)
      _problem.noseAtNorthEdgeAfterCrossing
  rw [hnorth, hsouth, _problem.edgeCrossingTimeSeconds,
    _problem.signedAccelerationMetersPerSecondSquared] at hposition
  have hsep := _problem.edgeSeparationMeters
  rw [_problem.intersectionWidthMeters] at hsep
  norm_num at hposition hsep ⊢
  linarith

/--
Using the future zero-velocity event gives the exact SI stopping distance
before rounding to a displayed answer.
-/
lemma stoppingDistance_exact
    (setup : RoadIntersectionSetup)
    (_problem : MatchesProblemStatement setup)
    (_physical : HasPhysicalStoppingEvent setup)
    (_laws : SatisfiesConstantAccelerationKinematics setup) :
    stoppingDistanceInMeters setup =
      (((28 : ℝ) + (1 / 2) * (21 / 10) * (31 / 10) ^ 2) /
          (31 / 10)) ^ 2 /
        (2 * (21 / 10)) := by
  have hv0 := initialVelocity_from_edgeCrossing setup _problem _laws
  have hvel := _laws.velocityEvolution UnitChoices.SI setup.stopTime
  have hpos := _laws.positionEvolution UnitChoices.SI setup.stopTime
  have hsouth :=
    congrArg (lengthReadout UnitChoices.SI)
      _problem.noseAtSouthEdgeInitially
  rw [_physical.velocityAtSelectedStop,
    _problem.signedAccelerationMetersPerSecondSquared] at hvel
  rw [hsouth, _problem.signedAccelerationMetersPerSecondSquared] at hpos
  unfold stoppingDistanceInMeters
  rw [hpos, hv0]
  norm_num at hvel ⊢
  nlinarith [hvel]

/-- Labels of the four stopping-distance choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The distance in metres printed beside an answer label. -/
def displayedStoppingDistanceMeters : AnswerChoice → ℝ
  | .A => 183 / 10
  | .B => 345 / 10
  | .C => 359 / 10
  | .D => 276 / 10

/-- A choice is closest to the stopping distance among all displayed values. -/
def IsClosestDisplayedStoppingDistance
    (setup : RoadIntersectionSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |stoppingDistanceInMeters setup -
        displayedStoppingDistanceMeters choice| ≤
      |stoppingDistanceInMeters setup -
        displayedStoppingDistanceMeters alternative|

/-!
The exact kinematic result is within `0.05 m` of `35.9 m`, so rounding to the
precision of the choices selects C, and C is the closest displayed value.

This formalizes blueprint label `thm:physics:phyx_mini_0674:target`.
-/
theorem problem_phyx_mini_0674
    (setup : RoadIntersectionSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalStoppingEvent setup)
    (_laws : SatisfiesConstantAccelerationKinematics setup) :
    stoppingDistanceInMeters setup =
        (((28 : ℝ) + (1 / 2) * (21 / 10) * (31 / 10) ^ 2) /
            (31 / 10)) ^ 2 /
          (2 * (21 / 10)) ∧
      |stoppingDistanceInMeters setup -
          displayedStoppingDistanceMeters .C| ≤ 1 / 20 ∧
      displayedStoppingDistanceMeters .C = 359 / 10 ∧
      IsClosestDisplayedStoppingDistance setup .C := by
  have hdist := stoppingDistance_exact setup _problem _physical _laws
  refine ⟨hdist, ?_, rfl, ?_⟩
  · rw [hdist]
    norm_num [displayedStoppingDistanceMeters, abs_of_nonneg, abs_of_nonpos]
  · intro alternative
    cases alternative <;> rw [hdist] <;>
      norm_num [displayedStoppingDistanceMeters, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0674
