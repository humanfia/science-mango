import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0797

open Dimension

/-!
# Airplane ground velocity in an eastward wind

An airplane has velocity `240 km/h` due north relative to the air.  The air
has velocity `100 km/h` due east relative to the earth.  The supplied diagram
places these two vectors head to tail and labels their diagonal resultant by
`v_P/E`, the airplane's velocity relative to the earth.

Velocities below are unit-independent Physlib quantities.  Their value in a
chosen coherent unit system is a vector in the two-dimensional Euclidean
plane; real numbers are used only for measured component, speed, and angle
readouts.

Assumption/target split:

* governing laws: a heading and nonnegative speed determine the corresponding
  relative-velocity vector, and Galilean relative velocities compose by vector
  addition;
* previous-part results: none;
* data and figure readouts: the due-north compass heading, `240 km/h` airspeed,
  `100 km/h` eastward wind, three vector labels and arrows, the head-to-tail
  triangle, three airplane images, the compass rose, and the symbolic angle
  `alpha` shown between `v_P/A` and `v_P/E`;
* current target: the airplane-earth velocity vector has north/east components
  `240` and `100` in kilometres per hour, hence speed `260 km/h` and displayed
  answer B.
-/

/-! ## Dimensionful planar velocities and unit readouts -/

/-- The physical dimension `L T⁻¹` of velocity. -/
def velocityDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/--
A physical planar velocity, independent of the units chosen to read its two
signed Cartesian components.
-/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- A coherent unit choice whose length and time units are kilometres and hours. -/
def kilometerHourUnits : UnitChoices :=
  { UnitChoices.SI with
    length := LengthUnit.kilometers
    time := TimeUnit.hours }

/-- Read a physical planar velocity in an arbitrary coherent unit system. -/
def velocityReadout
    (units : UnitChoices) (velocity : PlanarVelocityQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (velocity units).val

/-- Read the signed Cartesian components of a velocity in kilometres per hour. -/
def velocityInKilometersPerHour
    (velocity : PlanarVelocityQuantity) : EuclideanSpace ℝ (Fin 2) :=
  velocityReadout kilometerHourUnits velocity

/-- The speed (Euclidean norm) of a velocity, in kilometres per hour. -/
def speedInKilometersPerHour (velocity : PlanarVelocityQuantity) : ℝ :=
  ‖velocityInKilometersPerHour velocity‖

/-- The dimensionless unit vector pointing east in the diagram. -/
def eastHat : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single (0 : Fin 2) 1

/-- The dimensionless unit vector pointing north in the diagram. -/
def northHat : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single (1 : Fin 2) 1

/-! ## Physical systems, directions, and relative-velocity labels -/

/-- The three systems occurring in the relative-velocity subscripts. -/
inductive PhysicalSystem where
  | airplane
  | air
  | earth
  deriving DecidableEq, Fintype, Repr

/-- Cardinal headings printed by the compass rose or stated in the prose. -/
inductive CardinalDirection where
  | north
  | east
  | south
  | west
  deriving DecidableEq, Fintype, Repr

/-- Directions used for the three arrows in the supplied vector diagram. -/
inductive DiagramDirection where
  | dueNorth
  | dueEast
  | northEast
  deriving DecidableEq, Fintype, Repr

/-- The three literal relative-velocity labels in image `797.png`. -/
inductive RelativeVelocityLabel where
  | airRelativeEarth
  | planeRelativeAir
  | planeRelativeEarth
  deriving DecidableEq, Fintype, Repr

/-- The moving system named by the numerator of a velocity label. -/
def movingSystem : RelativeVelocityLabel → PhysicalSystem
  | .airRelativeEarth => .air
  | .planeRelativeAir => .airplane
  | .planeRelativeEarth => .airplane

/-- The reference system named by the denominator of a velocity label. -/
def referenceSystem : RelativeVelocityLabel → PhysicalSystem
  | .airRelativeEarth => .earth
  | .planeRelativeAir => .air
  | .planeRelativeEarth => .earth

/-- The unit vector assigned to each compass direction. -/
def cardinalUnitVector : CardinalDirection → EuclideanSpace ℝ (Fin 2)
  | .north => northHat
  | .east => eastHat
  | .south => -northHat
  | .west => -eastHat

/-! ## Primary-figure vocabulary -/

/-- The three vertices of the head-to-tail velocity triangle. -/
inductive DiagramPoint where
  | origin
  | northLegEndpoint
  | resultantEndpoint
  deriving DecidableEq, Fintype, Repr

/--
Typed evidence exposed by the supplied raster.  A missing magnitude is
represented by `none`; in particular, the image does not print the requested
magnitude beside `v_P/E`.
-/
structure AirplaneVelocityFigure where
  showsArrow : RelativeVelocityLabel → Bool
  arrowDirection : RelativeVelocityLabel → DiagramDirection
  arrowTail : RelativeVelocityLabel → DiagramPoint
  arrowHead : RelativeVelocityLabel → DiagramPoint
  displayedMagnitudeKilometersPerHour :
    RelativeVelocityLabel → Option ℝ
  showsCompassDirection : CardinalDirection → Bool
  airplaneImageCount : ℕ
  showsAlphaSymbol : Bool
  alphaFirstRay : RelativeVelocityLabel
  alphaSecondRay : RelativeVelocityLabel
  showsHeadToTailVelocityTriangle : Bool

/-!
The independent physical velocities, instrument/report readouts, and diagram.
The airplane-earth velocity is a field to be constrained by the composition
law; it is not defined from answer choice B or from the number `260`.
-/
structure AirplaneWindSetup where
  relativeVelocity : RelativeVelocityLabel → PlanarVelocityQuantity
  compassHeading : CardinalDirection
  reportedWindDirection : CardinalDirection
  airSpeedIndicatorKilometersPerHour : ℝ
  reportedWindSpeedKilometersPerHour : ℝ
  driftAngleRadians : ℝ
  figure : AirplaneVelocityFigure

/-! ## Problem data, figure evidence, and governing laws -/

/-- The two directions stated in the prose. -/
structure MatchesStatedDirections (setup : AirplaneWindSetup) : Prop where
  compassIndicatesDueNorth : setup.compassHeading = .north
  westToEastWind : setup.reportedWindDirection = .east

/-- The numerical instrument and weather-report readouts from the problem. -/
structure MatchesProblemReadouts (setup : AirplaneWindSetup) : Prop where
  airSpeedIndicatorReads240 :
    setup.airSpeedIndicatorKilometersPerHour = 240
  windReportReads100 :
    setup.reportedWindSpeedKilometersPerHour = 100

/--
The labels, directions, endpoints, magnitudes, airplanes, compass rose, and
angle mark visible in image `797.png`.  No ground-speed or numerical `alpha`
answer is included here.
-/
structure MatchesSuppliedFigure (setup : AirplaneWindSetup) : Prop where
  airEarthArrowShown : setup.figure.showsArrow .airRelativeEarth = true
  planeAirArrowShown : setup.figure.showsArrow .planeRelativeAir = true
  planeEarthArrowShown : setup.figure.showsArrow .planeRelativeEarth = true
  airEarthArrowEast :
    setup.figure.arrowDirection .airRelativeEarth = .dueEast
  planeAirArrowNorth :
    setup.figure.arrowDirection .planeRelativeAir = .dueNorth
  planeEarthArrowNorthEast :
    setup.figure.arrowDirection .planeRelativeEarth = .northEast
  planeAirStartsAtOrigin :
    setup.figure.arrowTail .planeRelativeAir = .origin
  planeAirEndsAtNorthVertex :
    setup.figure.arrowHead .planeRelativeAir = .northLegEndpoint
  airEarthStartsAtNorthVertex :
    setup.figure.arrowTail .airRelativeEarth = .northLegEndpoint
  airEarthEndsAtResultantVertex :
    setup.figure.arrowHead .airRelativeEarth = .resultantEndpoint
  planeEarthStartsAtOrigin :
    setup.figure.arrowTail .planeRelativeEarth = .origin
  planeEarthEndsAtResultantVertex :
    setup.figure.arrowHead .planeRelativeEarth = .resultantEndpoint
  airEarthMagnitudePrinted :
    setup.figure.displayedMagnitudeKilometersPerHour
        .airRelativeEarth = some 100
  planeAirMagnitudePrinted :
    setup.figure.displayedMagnitudeKilometersPerHour
        .planeRelativeAir = some 240
  requestedGroundMagnitudeNotPrinted :
    setup.figure.displayedMagnitudeKilometersPerHour
        .planeRelativeEarth = none
  compassRoseShown :
    ∀ direction : CardinalDirection,
      setup.figure.showsCompassDirection direction = true
  threeAirplaneImages : setup.figure.airplaneImageCount = 3
  alphaShown : setup.figure.showsAlphaSymbol = true
  alphaFromNorthwardVector :
    setup.figure.alphaFirstRay = .planeRelativeAir
  alphaToResultantVector :
    setup.figure.alphaSecondRay = .planeRelativeEarth
  headToTailTriangleShown :
    setup.figure.showsHeadToTailVelocityTriangle = true

/--
The measurement interpretation used in the textbook model: the compass and
air-speed indicator determine the plane-through-air vector, while the wind
report determines the air-through-earth vector.  This law contains neither
the airplane-earth vector nor its requested speed.
-/
structure ObeysDirectionalMeasurementModel
    (setup : AirplaneWindSetup) : Prop where
  airSpeedNonnegative : 0 ≤ setup.airSpeedIndicatorKilometersPerHour
  windSpeedNonnegative : 0 ≤ setup.reportedWindSpeedKilometersPerHour
  planeThroughAirVector :
    velocityInKilometersPerHour
        (setup.relativeVelocity .planeRelativeAir) =
      setup.airSpeedIndicatorKilometersPerHour •
        cardinalUnitVector setup.compassHeading
  airThroughEarthVector :
    velocityInKilometersPerHour
        (setup.relativeVelocity .airRelativeEarth) =
      setup.reportedWindSpeedKilometersPerHour •
        cardinalUnitVector setup.reportedWindDirection

/--
The Galilean relative-velocity composition law, stated in every coherent unit
system rather than only for the numerical kilometre/hour readout.
-/
structure ObeysGalileanVelocityComposition
    (setup : AirplaneWindSetup) : Prop where
  planeEarthIsPlaneAirPlusAirEarth :
    ∀ units : UnitChoices,
      velocityReadout units
          (setup.relativeVelocity .planeRelativeEarth) =
        velocityReadout units
            (setup.relativeVelocity .planeRelativeAir) +
          velocityReadout units
            (setup.relativeVelocity .airRelativeEarth)

/--
The figure-derived role of `alpha`: it is the undirected angle from the north
unit vector to the airplane-earth velocity vector.  The raster supplies the
role and symbol, but no numerical value.
-/
structure RepresentsFigureDriftAngle (setup : AirplaneWindSetup) : Prop where
  alphaIsAngleFromNorth :
    setup.driftAngleRadians =
      InnerProductGeometry.angle northHat
        (velocityInKilometersPerHour
          (setup.relativeVelocity .planeRelativeEarth))

/-! ## Displayed answers and target -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The speed in kilometres per hour printed beside each answer label. -/
def displayedGroundSpeedKilometersPerHour : AnswerChoice → ℝ
  | .A => 160
  | .B => 260
  | .C => 290
  | .D => 410

/-- A displayed choice agrees with the physical airplane-earth speed. -/
def MatchesDisplayedGroundSpeed
    (setup : AirplaneWindSetup) (choice : AnswerChoice) : Prop :=
  speedInKilometersPerHour
      (setup.relativeVelocity .planeRelativeEarth) =
    displayedGroundSpeedKilometersPerHour choice

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
The plane's ground-velocity readout is `240 n-hat + 100 e-hat` kilometres per
hour.  Its speed is therefore `260 km/h`, agreeing with displayed answer B.

Blueprint: `thm:physics:phyx_mini_0797:target`.
-/
theorem problem_phyx_mini_0797
    (setup : AirplaneWindSetup)
    (_directions : MatchesStatedDirections setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedFigure setup)
    (_measurementModel : ObeysDirectionalMeasurementModel setup)
    (_composition : ObeysGalileanVelocityComposition setup)
    (_alpha : RepresentsFigureDriftAngle setup) :
    velocityInKilometersPerHour
        (setup.relativeVelocity .planeRelativeEarth) =
      240 • northHat + 100 • eastHat ∧
      speedInKilometersPerHour
          (setup.relativeVelocity .planeRelativeEarth) = 260 ∧
        MatchesDisplayedGroundSpeed setup .B := by
  have hPlaneThroughAir :
      velocityInKilometersPerHour
          (setup.relativeVelocity .planeRelativeAir) =
        (240 : ℝ) • northHat := by
    simpa [cardinalUnitVector, _readouts.airSpeedIndicatorReads240,
      _directions.compassIndicatesDueNorth] using
      _measurementModel.planeThroughAirVector
  have hAirThroughEarth :
      velocityInKilometersPerHour
          (setup.relativeVelocity .airRelativeEarth) =
        (100 : ℝ) • eastHat := by
    simpa [cardinalUnitVector, _readouts.windReportReads100,
      _directions.westToEastWind] using
      _measurementModel.airThroughEarthVector
  have hComposition :
      velocityInKilometersPerHour
          (setup.relativeVelocity .planeRelativeEarth) =
        velocityInKilometersPerHour
            (setup.relativeVelocity .planeRelativeAir) +
          velocityInKilometersPerHour
            (setup.relativeVelocity .airRelativeEarth) := by
    simpa [velocityInKilometersPerHour] using
      _composition.planeEarthIsPlaneAirPlusAirEarth kilometerHourUnits
  have hGroundVelocity :
      velocityInKilometersPerHour
          (setup.relativeVelocity .planeRelativeEarth) =
        240 • northHat + 100 • eastHat := by
    calc
      velocityInKilometersPerHour
          (setup.relativeVelocity .planeRelativeEarth) =
          velocityInKilometersPerHour
              (setup.relativeVelocity .planeRelativeAir) +
            velocityInKilometersPerHour
              (setup.relativeVelocity .airRelativeEarth) := hComposition
      _ = 240 • northHat + 100 • eastHat := by
        rw [hPlaneThroughAir, hAirThroughEarth]
        exact_mod_cast rfl
  have hGroundSpeed :
      speedInKilometersPerHour
          (setup.relativeVelocity .planeRelativeEarth) = 260 := by
    rw [speedInKilometersPerHour, hGroundVelocity, EuclideanSpace.norm_eq]
    norm_num [northHat, eastHat, Fin.sum_univ_two]
    have hsq : (Real.sqrt (67600 : ℝ)) ^ 2 = 67600 := by
      norm_num
    have hnonneg : 0 ≤ Real.sqrt (67600 : ℝ) :=
      Real.sqrt_nonneg _
    nlinarith
  refine ⟨hGroundVelocity, hGroundSpeed, ?_⟩
  simpa [MatchesDisplayedGroundSpeed,
    displayedGroundSpeedKilometersPerHour] using hGroundSpeed

end PhyXMiniProblems.ProblemPhyXMini0797
