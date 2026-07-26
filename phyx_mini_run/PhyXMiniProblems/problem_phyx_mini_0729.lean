import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0729

open Dimension

/-!
# A traffic shock wave

A uniformly spaced stream of cars moving at `25 m/s` encounters a packed
stream moving at `5 m/s`.  In the fast stream, a car-plus-buffer cell has
length `L` and is followed by an empty gap `d`; in the slow stream those
length-`L` cells are adjacent.  A car slows abruptly when it joins the slow
stream.  Conservation of vehicle number determines the velocity of the
interface (the traffic shock wave).

The phrase "twice that amount" refers to the separation that made the shock
stationary in the preceding part of the textbook problem.  Accordingly, this
formalization keeps both a stationary reference regime and the current regime,
whose gap is twice the stationary gap.

Length and vehicle-speed magnitudes are unit-independent Physlib quantities.
The signed shock velocity is also dimensionful; its sign is positive in the
downstream traffic direction.  Real numbers are used only for coherent-SI
readouts, schematic drawing coordinates, and displayed answer values.

Assumption/target split:

* governing law: vehicle-number flux is conserved across the moving shock;
* previous-part result: the reference shock is stationary;
* figure/data readouts: the labels `L`, `d`, `v`, `v_s`, `Car`, and `Buffer`,
  ordered cars on one horizontal road, `v = 25 m/s`, `v_s = 5 m/s`,
  `L = 12 m`, uniform streams, abrupt last-instant slowing, and a current gap
  twice the stationary-reference gap;
* current target: the magnitude of the current shock velocity is `2.5 m/s`
  (answer choice C).
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- The physical dimension of a signed one-dimensional velocity. -/
def velocityDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-!
A signed, unit-independent velocity along the road.  Positive values point
downstream, in the direction of the two magenta velocity arrows in the image.
-/
abbrev SignedRoadVelocity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a nonnegative physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a signed road velocity in metres per second. -/
def velocityInMetersPerSecond (velocity : SignedRoadVelocity) : ℝ :=
  (velocity UnitChoices.SI).val

/-! ## Traffic regimes and primary-image vocabulary -/

/-- The preceding stationary case and the present twice-separated case. -/
inductive ShockRegime where
  | stationaryReference
  | current
  deriving DecidableEq, Fintype, Repr

/-- The two orientations along the one-dimensional road. -/
inductive RoadDirection where
  | downstream
  | upstream
  deriving DecidableEq, Repr

/-- Vehicle colors visible from left to right in image `729.png`. -/
inductive VehicleColor where
  | blue
  | red
  | green
  | yellow
  | lightBlue
  | darkBlue
  deriving DecidableEq, Repr

/-- Text and symbol labels printed in the supplied traffic diagram. -/
inductive TrafficFigureLabel where
  | car
  | buffer
  | cellLengthL
  | separationD
  | fastSpeedV
  | slowSpeedVs
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and schematic evidence transcribed from the primary image.
Coordinates are drawing coordinates, not physical positions or lengths.
-/
structure TrafficShockFigure where
  vehicleShown : Fin 6 → Bool
  vehicleColor : Fin 6 → VehicleColor
  horizontalDrawingCoordinate : Fin 6 → ℝ
  labelShown : TrafficFigureLabel → Bool
  dashedCarAndBufferCellShown : Fin 3 → Bool
  speedArrowShown : Bool
  slowSpeedArrowShown : Bool
  speedArrowDirection : RoadDirection
  slowSpeedArrowDirection : RoadDirection
  allVehiclesShareHorizontalRoad : Bool

/-!
The independent physical quantities in the two traffic configurations.
`addedLengthPerJoiningCar` is the pictured car-plus-buffer length `L` and also
the spacing of the packed slow stream.  `fastCarGap` is the pictured empty
distance `d` between consecutive length-`L` cells in the fast stream.

The shock velocity in each regime is an unknown observable.  In particular,
the current velocity is not defined from the answer choice or the conservation
law.
-/
structure TrafficShockSetup where
  figure : TrafficShockFigure
  addedLengthPerJoiningCar : LengthQuantity
  fastCarGap : ShockRegime → LengthQuantity
  fastCarSpeed : DimSpeed
  slowCarSpeed : DimSpeed
  shockVelocity : ShockRegime → SignedRoadVelocity
  fastCarsUniformlySpaced : Bool
  slowCarsUniformlySpaced : Bool
  eachFastCarAddsOneCellWhenJoining : Bool
  eachFastCarSlowsAbruptlyAtLastInstant : Bool

/-!
The nonnegative speed of a shock is the magnitude of its signed downstream
velocity.  This definition only forgets direction; it does not impose a value.
-/
def shockSpeedInMetersPerSecond
    (setup : TrafficShockSetup) (regime : ShockRegime) : ℝ :=
  |velocityInMetersPerSecond (setup.shockVelocity regime)|

/-! ## Figure evidence, stated data, and physical admissibility -/

/-- Facts read from the primary image rather than inferred from its scale. -/
structure MatchesPrimaryTrafficShockFigure
    (setup : TrafficShockSetup) : Prop where
  everyVehicleShown : ∀ index, setup.figure.vehicleShown index = true
  colorsAppearLeftToRight :
    setup.figure.vehicleColor (0 : Fin 6) = .blue ∧
      setup.figure.vehicleColor (1 : Fin 6) = .red ∧
      setup.figure.vehicleColor (2 : Fin 6) = .green ∧
      setup.figure.vehicleColor (3 : Fin 6) = .yellow ∧
      setup.figure.vehicleColor (4 : Fin 6) = .lightBlue ∧
      setup.figure.vehicleColor (5 : Fin 6) = .darkBlue
  vehiclesOrderedLeftToRight :
    ∀ i j, i.val < j.val →
      setup.figure.horizontalDrawingCoordinate i <
        setup.figure.horizontalDrawingCoordinate j
  everyPrintedLabelShown : ∀ label, setup.figure.labelShown label = true
  dashedCellsShown :
    ∀ index, setup.figure.dashedCarAndBufferCellShown index = true
  fastSpeedArrowShown : setup.figure.speedArrowShown = true
  slowSpeedArrowShown : setup.figure.slowSpeedArrowShown = true
  fastSpeedArrowPointsDownstream :
    setup.figure.speedArrowDirection = .downstream
  slowSpeedArrowPointsDownstream :
    setup.figure.slowSpeedArrowDirection = .downstream
  commonHorizontalRoadShown :
    setup.figure.allVehiclesShareHorizontalRoad = true

/-!
Numerical and qualitative data stated in the problem.  The current gap is
twice the stationary-reference gap, not twice `L`; this records the antecedent
of "twice that amount" from the preceding stationary subproblem.
-/
structure MatchesTrafficShockProblemData
    (setup : TrafficShockSetup) : Prop where
  fastSpeedMetersPerSecond :
    speedInMetersPerSecond setup.fastCarSpeed = 25
  slowSpeedMetersPerSecond :
    speedInMetersPerSecond setup.slowCarSpeed = 5
  addedLengthMeters :
    lengthInMeters setup.addedLengthPerJoiningCar = 12
  currentGapTwiceStationaryGap :
    lengthInMeters (setup.fastCarGap .current) =
      2 * lengthInMeters (setup.fastCarGap .stationaryReference)
  fastStreamUniform : setup.fastCarsUniformlySpaced = true
  slowStreamUniform : setup.slowCarsUniformlySpaced = true
  oneCellAddedPerJoiningCar :
    setup.eachFastCarAddsOneCellWhenJoining = true
  abruptLastInstantSlowdown :
    setup.eachFastCarSlowsAbruptlyAtLastInstant = true

/-! Positivity and ordering conditions for the depicted physical branch. -/
structure HasPhysicalTrafficShockParameters
    (setup : TrafficShockSetup) : Prop where
  addedLengthPositive :
    0 < lengthInMeters setup.addedLengthPerJoiningCar
  everyFastGapPositive :
    ∀ regime, 0 < lengthInMeters (setup.fastCarGap regime)
  slowSpeedPositive :
    0 < speedInMetersPerSecond setup.slowCarSpeed
  fastStreamIsFaster :
    speedInMetersPerSecond setup.slowCarSpeed <
      speedInMetersPerSecond setup.fastCarSpeed

/-! ## Previous-part result and governing traffic law -/

/-!
The preceding subproblem identifies the reference separation by requiring the
shock to remain stationary.  This is a permitted previous-part result; it says
nothing about the current shock velocity.
-/
structure HasStationaryShockPreviousPart
    (setup : TrafficShockSetup) : Prop where
  referenceShockIsStationary :
    velocityInMetersPerSecond
      (setup.shockVelocity .stationaryReference) = 0

/-!
Conservation of vehicle number across a shock moving at signed velocity `w`.
Relative to the shock, fast cars arrive with speed `v - w` and occupy one cell
of length `L + d`, while slow cars leave with speed `v_s - w` and occupy one
packed cell of length `L`.  Equality of the two number fluxes,

`(v - w) / (L + d) = (v_s - w) / L`,

is stated below in a denominator-free but dimensionally equivalent form for
both regimes.  No numerical value of the current wave speed occurs here.
-/
structure SatisfiesVehicleNumberConservationAcrossShock
    (setup : TrafficShockSetup) : Prop where
  numberFluxBalance :
    ∀ regime,
      (speedInMetersPerSecond setup.fastCarSpeed -
          velocityInMetersPerSecond (setup.shockVelocity regime)) *
          lengthInMeters setup.addedLengthPerJoiningCar =
        (speedInMetersPerSecond setup.slowCarSpeed -
            velocityInMetersPerSecond (setup.shockVelocity regime)) *
          (lengthInMeters setup.addedLengthPerJoiningCar +
            lengthInMeters (setup.fastCarGap regime))

/-! ## Derived separations and requested shock speed -/

/-!
With `v = 25 m/s` and `v_s = 5 m/s`, the separation that makes the shock
stationary is four times the added car-plus-buffer length.
-/
lemma stationaryGap_eq_four_times_addedLength
    (setup : TrafficShockSetup)
    (hData : MatchesTrafficShockProblemData setup)
    (hPhysical : HasPhysicalTrafficShockParameters setup)
    (hPrevious : HasStationaryShockPreviousPart setup)
    (hConservation : SatisfiesVehicleNumberConservationAcrossShock setup) :
    lengthInMeters (setup.fastCarGap .stationaryReference) =
      4 * lengthInMeters setup.addedLengthPerJoiningCar := by
  have hFlux :=
    hConservation.numberFluxBalance ShockRegime.stationaryReference
  rw [hData.fastSpeedMetersPerSecond, hData.slowSpeedMetersPerSecond,
    hPrevious.referenceShockIsStationary] at hFlux
  nlinarith

/-!
The current gap is twice the stationary gap, hence eight times `L` and
numerically `96 m` for `L = 12 m`.
-/
lemma currentGap_eq_ninetySixMeters
    (setup : TrafficShockSetup)
    (hData : MatchesTrafficShockProblemData setup)
    (hPhysical : HasPhysicalTrafficShockParameters setup)
    (hPrevious : HasStationaryShockPreviousPart setup)
    (hConservation : SatisfiesVehicleNumberConservationAcrossShock setup) :
    lengthInMeters (setup.fastCarGap .current) = 96 := by
  have hStationaryGap :=
    stationaryGap_eq_four_times_addedLength setup hData hPhysical hPrevious
      hConservation
  rw [hData.currentGapTwiceStationaryGap, hStationaryGap,
    hData.addedLengthMeters]
  norm_num

/-- The speed values printed beside answer labels A--D. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed answer-choice speed in metres per second. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 3 / 2
  | .B => 2
  | .C => 5 / 2
  | .D => 3

/-!
For a gap twice the stationary separation, conservation of vehicle number
gives a downstream signed velocity of `2.5 m/s`; therefore the requested
speed magnitude is `2.5 m/s`, displayed as answer choice C.

The figure premise is retained even though the numerical algebra uses its
metric content through the separately stated data and conservation premises.
-/
theorem trafficShockWave_speed
    (setup : TrafficShockSetup)
    (hFigure : MatchesPrimaryTrafficShockFigure setup)
    (hData : MatchesTrafficShockProblemData setup)
    (hPhysical : HasPhysicalTrafficShockParameters setup)
    (hPrevious : HasStationaryShockPreviousPart setup)
    (hConservation : SatisfiesVehicleNumberConservationAcrossShock setup) :
    shockSpeedInMetersPerSecond setup .current =
      AnswerChoice.C.speedInMetersPerSecond := by
  have hCurrentGap :=
    currentGap_eq_ninetySixMeters setup hData hPhysical hPrevious hConservation
  have hFlux := hConservation.numberFluxBalance ShockRegime.current
  rw [hData.fastSpeedMetersPerSecond, hData.slowSpeedMetersPerSecond,
    hData.addedLengthMeters, hCurrentGap] at hFlux
  have hVelocity :
      velocityInMetersPerSecond (setup.shockVelocity .current) = 5 / 2 := by
    nlinarith
  rw [shockSpeedInMetersPerSecond, hVelocity]
  norm_num [AnswerChoice.speedInMetersPerSecond]

end PhyXMiniProblems.ProblemPhyXMini0729
