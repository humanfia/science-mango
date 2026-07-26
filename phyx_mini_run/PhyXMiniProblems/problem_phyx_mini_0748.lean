import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Velocity of a motorist relative to a police car

Two perpendicular highways meet at the origin of the supplied diagram.  The
police car `P` is on the positive horizontal ray and travels toward the
intersection; the motorist `M` is on the positive vertical ray and also
travels toward the intersection.  Their instantaneous speeds are `80 km/h`
and `60 km/h`, respectively.

Positions and velocities below are unit-independent Physlib dimensionful
quantities whose values are vectors in the Euclidean diagram plane.  Real
vectors occur only as readouts in named units and as the dimensionless unit
directions from the figure.  In particular, the velocity of `M` relative to
`P` is independent setup data constrained by the classical relative-velocity
law; it is not defined to be the recorded answer.

Assumption/target boundary:

* `MatchesProblemReadouts` contains the four stated distance and speed data.
* `MatchesSuppliedFigure` records the two roads, positions, and arrow
  directions visible in the image.
* `ObeysClassicalRelativeKinematics` contains only governing kinematic laws.
* There are no previous-part results.
* The vector `(80 km/h) iHat - (60 km/h) jHat` occurs only in the conclusion
  of the final theorem and in the table of displayed answer choices.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0748

open Dimension

/-! ## Dimensionful physical quantities and readouts -/

/-- The two-dimensional Euclidean vector space of the road diagram. -/
abbrev DiagramVector : Type := EuclideanSpace ℝ (Fin 2)

/-- A nonnegative, unit-independent physical distance. -/
abbrev DistanceQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent planar position carrying the dimension of length. -/
abbrev PlanarPosition : Type :=
  Dimensionful (WithDim L𝓭 DiagramVector)

/-- A unit-independent planar velocity carrying dimension length per time. -/
abbrev PlanarVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) DiagramVector)

/-- Unit choices used for kilometer-per-hour readouts. -/
def kilometerHourUnits : UnitChoices :=
  { UnitChoices.SI with
    length := LengthUnit.kilometers
    time := TimeUnit.hours }

/-- Read a physical distance in metres. -/
def distanceInMeters (distance : DistanceQuantity) : ℝ :=
  ((distance UnitChoices.SI).val : ℝ)

/-- Read a nonnegative physical speed in kilometers per hour. -/
def speedInKilometersPerHour (speed : DimSpeed) : ℝ :=
  ((speed kilometerHourUnits).val : ℝ)

/-- Read a planar position as its `(x,y)` coordinate vector in metres. -/
def positionInMeters (position : PlanarPosition) : DiagramVector :=
  (position UnitChoices.SI).val

/-- Read a planar velocity as its `(x,y)` component vector in km/h. -/
def velocityInKilometersPerHour
    (velocity : PlanarVelocity) : DiagramVector :=
  (velocity kilometerHourUnits).val

/-! ## Coordinate geometry and figure labels -/

/-- The unit vector `iHat` in the positive horizontal direction. -/
def iHat : DiagramVector :=
  EuclideanSpace.single (0 : Fin 2) 1

/-- The unit vector `jHat` in the positive vertical direction. -/
def jHat : DiagramVector :=
  EuclideanSpace.single (1 : Fin 2) 1

/-- The coordinate vector of the highway intersection. -/
def intersectionOrigin : DiagramVector := 0

/-- The two vehicles labelled in the problem and primary image. -/
inductive VehicleLabel where
  | policeP
  | motoristM
  deriving DecidableEq, Fintype, Repr

/-- The perpendicular highways drawn through the coordinate origin. -/
inductive HighwayLabel where
  | horizontalX
  | verticalY
  deriving DecidableEq, Fintype, Repr

/-- The positive coordinate direction of each highway. -/
def highwayDirection : HighwayLabel → DiagramVector
  | .horizontalX => iHat
  | .verticalY => jHat

/-! ## Physical setup -/

/-!
The relative velocity is stored independently from both laboratory-frame
velocities.  Its relation to them is supplied later by a governing law, so no
answer component is built into this structure.
-/
structure IntersectingHighwaysSetup where
  intersectionPosition : PlanarPosition
  vehicleHighway : VehicleLabel → HighwayLabel
  distanceFromIntersection : VehicleLabel → DistanceQuantity
  position : VehicleLabel → PlanarPosition
  speedMagnitude : VehicleLabel → DimSpeed
  travelDirection : VehicleLabel → DiagramVector
  velocity : VehicleLabel → PlanarVelocity
  motoristVelocityRelativeToPolice : PlanarVelocity

/-! ## Assumptions: physical parameters, source data, and figure readouts -/

/-- Positivity and unit-direction conditions for a nondegenerate snapshot. -/
structure HasPhysicalParameters
    (setup : IntersectingHighwaysSetup) : Prop where
  positiveDistance :
    ∀ vehicle, 0 < distanceInMeters (setup.distanceFromIntersection vehicle)
  positiveSpeed :
    ∀ vehicle, 0 < speedInKilometersPerHour (setup.speedMagnitude vehicle)
  unitTravelDirection :
    ∀ vehicle, ‖setup.travelDirection vehicle‖ = 1

/-!
The four numerical physical data stated in the prose.  The distance readouts
are in metres.  The speed equalities use Physlib's dimensionful constant for
one kilometer per hour, rather than treating speeds as bare real scalars.
-/
structure MatchesProblemReadouts
    (setup : IntersectingHighwaysSetup) : Prop where
  policeDistanceMeters :
    distanceInMeters (setup.distanceFromIntersection .policeP) = 800
  motoristDistanceMeters :
    distanceInMeters (setup.distanceFromIntersection .motoristM) = 600
  policeSpeedMagnitude :
    setup.speedMagnitude .policeP =
      (80 : NNReal) • DimSpeed.oneKilometerPerHour
  motoristSpeedMagnitude :
    setup.speedMagnitude .motoristM =
      (60 : NNReal) • DimSpeed.oneKilometerPerHour

/-!
Primary-image geometry.  Both cars are shown on positive coordinate rays,
while both velocity arrows point toward the origin: `P` leftward and `M`
downward.  This predicate contains no relative-velocity answer.
-/
structure MatchesSuppliedFigure
    (setup : IntersectingHighwaysSetup) : Prop where
  intersectionAtOrigin :
    positionInMeters setup.intersectionPosition = intersectionOrigin
  policeUsesHorizontalHighway :
    setup.vehicleHighway .policeP = .horizontalX
  motoristUsesVerticalHighway :
    setup.vehicleHighway .motoristM = .verticalY
  policePositionOnPositiveXAxis :
    positionInMeters (setup.position .policeP) =
      distanceInMeters (setup.distanceFromIntersection .policeP) • iHat
  motoristPositionOnPositiveYAxis :
    positionInMeters (setup.position .motoristM) =
      distanceInMeters (setup.distanceFromIntersection .motoristM) • jHat
  policeArrowPointsLeft :
    setup.travelDirection .policeP = -iHat
  motoristArrowPointsDown :
    setup.travelDirection .motoristM = -jHat

/-!
The governing instantaneous kinematics.  The first field interprets each
speed magnitude and unit direction as a vector velocity in any unit system.
The second is the classical Galilean definition

`velocity of M relative to P = velocity of M - velocity of P`.

Neither law contains the requested numerical relative-velocity components.
-/
structure ObeysClassicalRelativeKinematics
    (setup : IntersectingHighwaysSetup) : Prop where
  velocityFromSpeedAndDirection :
    ∀ (vehicle : VehicleLabel) (units : UnitChoices),
      (setup.velocity vehicle units).val =
        ((setup.speedMagnitude vehicle units).val : ℝ) •
          setup.travelDirection vehicle
  relativeVelocityLaw :
    ∀ units : UnitChoices,
      (setup.motoristVelocityRelativeToPolice units).val =
        (setup.velocity .motoristM units).val -
          (setup.velocity .policeP units).val

/-! ## Displayed choices and formalization target -/

/-- Labels of the four answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The kilometer-per-hour vector printed beside each answer label. -/
def AnswerChoice.velocityVector : AnswerChoice → DiagramVector
  | .A => 60 • iHat - 80 • jHat
  | .B => 80 • iHat + 60 • jHat
  | .C => 80 • iHat - 60 • jHat
  | .D => 60 • iHat + 80 • jHat

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The motorist's velocity relative to the police car is
`(80 km/h) iHat - (60 km/h) jHat`, which is displayed answer C.

This formalizes `thm:physics:phyx_mini_0748:target`.
-/
theorem motorist_velocity_relative_to_police
    (setup : IntersectingHighwaysSetup)
    (parameters : HasPhysicalParameters setup)
    (readouts : MatchesProblemReadouts setup)
    (figure : MatchesSuppliedFigure setup)
    (kinematics : ObeysClassicalRelativeKinematics setup) :
    velocityInKilometersPerHour
        setup.motoristVelocityRelativeToPolice =
      80 • iHat - 60 • jHat := by
  unfold velocityInKilometersPerHour
  rw [kinematics.relativeVelocityLaw]
  repeat' rw [kinematics.velocityFromSpeedAndDirection]
  rw [readouts.motoristSpeedMagnitude, readouts.policeSpeedMagnitude]
  rw [figure.motoristArrowPointsDown, figure.policeArrowPointsLeft]
  simp [kilometerHourUnits, DimSpeed.oneKilometerPerHour,
    CarriesDimension.toDimensionful_apply_apply]
  module

end PhyXMiniProblems.ProblemPhyXMini0748
