import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0610

open Dimension

/-!
# Area of a fluorescent tube's illuminated spacetime region

A horizontal fluorescent tube of physical length `L` is at rest in the
station frame `S`. It is bright yellow from station time `0` through `T`.
The diagram uses `x` horizontally and the length-valued coordinate `ct`
vertically, so its yellow worldsheet region has a physical area.

The train frame `S'` and its speed `v` are retained as part of the setup even
though the requested area is measured in `S` and is therefore independent of
`v`. Lengths, durations, speeds, event coordinates, and area are represented
by Physlib dimensionful quantities. Real numbers occur only at explicit
named-unit readout boundaries.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical tube length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent spatial or `ct` coordinate. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A signed one-dimensional physical velocity, including `v` and `c`. -/
abbrev SignedSpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed position or `ct` coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (coordinate : SignedLengthQuantity) : ℝ :=
  (coordinate {UnitChoices.SI with length := unit}).val

/-- Read a duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  ((time {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SignedSpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a physical plot area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-! ## Frames, events, and primary-image vocabulary -/

/-- The station frame `S` and the rocket-train frame `S'`. -/
inductive InertialFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Repr

/-- The two physical endpoints of the fluorescent tube. -/
inductive TubeEndpoint where
  | right
  | left
  deriving DecidableEq, Repr

/-- The switch transition represented by an endpoint event. -/
inductive TubeSwitchTransition where
  | lightsOn
  | lightsOff
  deriving DecidableEq, Repr

/-- Events numbered `1` through `4` in the supplied spacetime diagram. -/
inductive EventLabel where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- Tube endpoint represented by each numbered event. -/
def eventEndpoint : EventLabel → TubeEndpoint
  | .one => .right
  | .two => .left
  | .three => .right
  | .four => .left

/-- Turning-on or turning-off transition represented by each event. -/
def eventSwitchTransition : EventLabel → TubeSwitchTransition
  | .one => .lightsOn
  | .two => .lightsOn
  | .three => .lightsOff
  | .four => .lightsOff

/-- A point in an `x`--`ct` plot; both coordinates have length dimension. -/
structure SpacetimeDiagramPoint where
  x : SignedLengthQuantity
  ct : SignedLengthQuantity

/-- The physical quantities represented by the two drawn axes. -/
inductive DiagramAxisQuantity where
  | spatialPositionX
  | lightScaledTimeCt
  deriving DecidableEq, Repr

/-- The four corners of the yellow rectangle in image 610. -/
inductive RectangleCorner where
  | lowerRight
  | lowerLeft
  | upperRight
  | upperLeft
  deriving DecidableEq, Fintype, Repr

/-- Boundary segments of the yellow rectangle. -/
inductive RectangleEdge where
  | bottom
  | right
  | top
  | left
  deriving DecidableEq, Fintype, Repr

/-- Solid and dashed line styles visible on the rectangle boundary. -/
inductive BoundaryLineStyle where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- Colors relevant to the tube and shaded diagram region. -/
inductive TubeOrRegionColor where
  | white
  | brightYellow
  deriving DecidableEq, Repr

/-- Literal labels visible in the primary raster. -/
inductive DiagramTextLabel where
  | eventOne
  | eventTwo
  | eventThree
  | eventFour
  | xAxis
  | ctAxis
  | negativeL
  | cT
  deriving DecidableEq, Fintype, Repr

/-- Direction of the train's motion along the common spatial axis. -/
inductive AxisDirection where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Relationship between the spatial axes of the two frames. -/
inductive SpatialAxisRelationship where
  | coincident
  | other
  deriving DecidableEq, Repr

/-!
Presentation information transcribed from image 610. The corner assignment,
axis meanings, labels, yellow fill, and solid/dashed boundary styles are raw
figure evidence; this structure contains no area value or formula.
-/
structure FluorescentTubeSpacetimeFigure where
  horizontalAxisQuantity : DiagramAxisQuantity
  verticalAxisQuantity : DiagramAxisQuantity
  showsTextLabel : DiagramTextLabel → Bool
  eventAtCorner : RectangleCorner → EventLabel
  boundaryStyle : RectangleEdge → BoundaryLineStyle
  interiorColor : TubeOrRegionColor

/-! ## Independent physical setup -/

/-!
The tube, train, events, illuminated worldsheet, and a general area assignment
for regions in the `S` plot. The area map is not defined from `c`, `L`, or
`T`; its required geometric behavior is stated separately below.
-/
structure FluorescentTubeSpacetimeSetup where
  tubeRestFrame : InertialFrameLabel
  stationPlotFrame : InertialFrameLabel
  trainRestFrame : InertialFrameLabel
  trainMotionDirection : AxisDirection
  frameSpatialAxisRelationship : SpatialAxisRelationship
  tubeColorBeforeLighting : TubeOrRegionColor
  tubeColorWhileLit : TubeOrRegionColor
  tubeColorAfterSwitchOff : TubeOrRegionColor
  tubeLengthL : LengthQuantity
  litDurationT : TimeQuantity
  relativeTrainVelocityV : SignedSpeedQuantity
  stationTimeOfEvent : EventLabel → TimeQuantity
  coordinateOfEvent : InertialFrameLabel → EventLabel → SpacetimeDiagramPoint
  tubeIsLitAtStationDiagramPoint : SpacetimeDiagramPoint → Prop
  yellowRegionInS : Set SpacetimeDiagramPoint
  areaOfRegionInSPlot : Set SpacetimeDiagramPoint → DimArea
  figure : FluorescentTubeSpacetimeFigure

/-- Spatial-coordinate readout of an event in a chosen frame. -/
def eventXReadout
    (setup : FluorescentTubeSpacetimeSetup)
    (unit : LengthUnit) (frame : InertialFrameLabel)
    (event : EventLabel) : ℝ :=
  signedLengthReadout unit (setup.coordinateOfEvent frame event).x

/-- `ct`-coordinate readout of an event in a chosen frame. -/
def eventCtReadout
    (setup : FluorescentTubeSpacetimeSetup)
    (unit : LengthUnit) (frame : InertialFrameLabel)
    (event : EventLabel) : ℝ :=
  signedLengthReadout unit (setup.coordinateOfEvent frame event).ct

/-- Spatial-coordinate readout of an arbitrary diagram point. -/
def pointXReadout
    (unit : LengthUnit) (point : SpacetimeDiagramPoint) : ℝ :=
  signedLengthReadout unit point.x

/-- `ct`-coordinate readout of an arbitrary diagram point. -/
def pointCtReadout
    (unit : LengthUnit) (point : SpacetimeDiagramPoint) : ℝ :=
  signedLengthReadout unit point.ct

/-! ## Scenario and figure/data assumptions -/

/-- Qualitative frame, motion, and tube-color assignments from the prose. -/
structure MatchesFluorescentTubeScenario
    (setup : FluorescentTubeSpacetimeSetup) : Prop where
  tubeIsFixedInStationFrame : setup.tubeRestFrame = .S
  requestedPlotUsesStationFrame : setup.stationPlotFrame = .S
  trainCarriesPrimedFrame : setup.trainRestFrame = .SPrime
  trainMovesFromLeftToRight : setup.trainMotionDirection = .positive
  frameSpatialAxesCoincide :
    setup.frameSpatialAxisRelationship = .coincident
  tubeInitiallyWhite : setup.tubeColorBeforeLighting = .white
  tubeBrightYellowWhileLit : setup.tubeColorWhileLit = .brightYellow
  tubeReturnsToWhite : setup.tubeColorAfterSwitchOff = .white

/-!
Literal figure appearance and the four corner/event assignments. In
particular, the primary raster places events `1,2,3,4` at lower-right,
lower-left, upper-right, upper-left respectively.
-/
structure MatchesPrimarySpacetimeFigure
    (setup : FluorescentTubeSpacetimeSetup) : Prop where
  horizontalAxisIsX :
    setup.figure.horizontalAxisQuantity = .spatialPositionX
  verticalAxisIsCt :
    setup.figure.verticalAxisQuantity = .lightScaledTimeCt
  everyPrintedLabelIsShown :
    ∀ label, setup.figure.showsTextLabel label = true
  lowerRightIsEventOne :
    setup.figure.eventAtCorner .lowerRight = .one
  lowerLeftIsEventTwo :
    setup.figure.eventAtCorner .lowerLeft = .two
  upperRightIsEventThree :
    setup.figure.eventAtCorner .upperRight = .three
  upperLeftIsEventFour :
    setup.figure.eventAtCorner .upperLeft = .four
  bottomBoundaryIsSolid :
    setup.figure.boundaryStyle .bottom = .solid
  rightBoundaryIsSolid :
    setup.figure.boundaryStyle .right = .solid
  topBoundaryIsDashed :
    setup.figure.boundaryStyle .top = .dashed
  leftBoundaryIsDashed :
    setup.figure.boundaryStyle .left = .dashed
  shadedRegionIsBrightYellow :
    setup.figure.interiorColor = .brightYellow

/-!
Calibrated event data from the prose and primary figure. Events `1` and `2`
occur at station time zero, while `3` and `4` occur at `T`. The right-end
events have `x = 0`, and the left-end events have `x = -L`. Event `1` is
also the origin of the primed diagram, as stipulated in the problem.
-/
structure MatchesEventCoordinateData
    (setup : FluorescentTubeSpacetimeSetup) : Prop where
  eventOneAtInitialTime :
    ∀ unit, timeReadout unit (setup.stationTimeOfEvent .one) = 0
  eventTwoAtInitialTime :
    ∀ unit, timeReadout unit (setup.stationTimeOfEvent .two) = 0
  eventThreeAtFinalTime :
    ∀ unit,
      timeReadout unit (setup.stationTimeOfEvent .three) =
        timeReadout unit setup.litDurationT
  eventFourAtFinalTime :
    ∀ unit,
      timeReadout unit (setup.stationTimeOfEvent .four) =
        timeReadout unit setup.litDurationT
  eventOneAtRightEndInS :
    ∀ unit, eventXReadout setup unit .S .one = 0
  eventThreeAtRightEndInS :
    ∀ unit, eventXReadout setup unit .S .three = 0
  eventTwoAtLeftEndInS :
    ∀ unit,
      eventXReadout setup unit .S .two =
        -lengthReadout unit setup.tubeLengthL
  eventFourAtLeftEndInS :
    ∀ unit,
      eventXReadout setup unit .S .four =
        -lengthReadout unit setup.tubeLengthL
  eventOneAtPrimedSpatialOrigin :
    ∀ unit, eventXReadout setup unit .SPrime .one = 0
  eventOneAtPrimedTimeOrigin :
    ∀ unit, eventCtReadout setup unit .SPrime .one = 0

/-! ## Physical and geometric laws -/

/-- Positivity and subluminality conditions on the physical parameters. -/
structure HasPhysicalParameters
    (setup : FluorescentTubeSpacetimeSetup) : Prop where
  tubeLengthPositive :
    0 < lengthReadout LengthUnit.meters setup.tubeLengthL
  litDurationPositive :
    0 < timeReadout TimeUnit.seconds setup.litDurationT
  vacuumLightSpeedPositive :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds
      DimSpeed.speedOfLight
  trainMovesWithPositiveSpeed :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds
      setup.relativeTrainVelocityV
  trainSpeedIsSubluminal :
    speedReadout LengthUnit.meters TimeUnit.seconds
        setup.relativeTrainVelocityV <
      speedReadout LengthUnit.meters TimeUnit.seconds
        DimSpeed.speedOfLight

/-!
The vertical coordinate convention `ct = c t`, stated for every event and
compatible pair of named units. This is the governing coordinate law, not an
assumption about the yellow region's area.
-/
structure SatisfiesLightScaledTimeCoordinate
    (setup : FluorescentTubeSpacetimeSetup) : Prop where
  stationFrameCtEqualsLightSpeedTimesTime :
    ∀ (event : EventLabel) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      eventCtReadout setup lengthUnit .S event =
        speedReadout lengthUnit timeUnit DimSpeed.speedOfLight *
          timeReadout timeUnit (setup.stationTimeOfEvent event)

/-!
The yellow set is exactly the set of lit-tube events and, in the station
plot, has the axis-aligned bounds determined by events `2`, `1`, and `3`.
These membership facts specify the illuminated worldsheet without assigning
it the requested area.
-/
structure SatisfiesIlluminatedTubeWorldsheet
    (setup : FluorescentTubeSpacetimeSetup) : Prop where
  yellowRegionRepresentsExactlyTheLitEvents :
    ∀ point,
      point ∈ setup.yellowRegionInS ↔
        setup.tubeIsLitAtStationDiagramPoint point
  yellowRegionHasEventRectangleBounds :
    ∀ point,
      point ∈ setup.yellowRegionInS ↔
        eventXReadout setup LengthUnit.meters .S .two ≤
            pointXReadout LengthUnit.meters point ∧
          pointXReadout LengthUnit.meters point ≤
            eventXReadout setup LengthUnit.meters .S .one ∧
          eventCtReadout setup LengthUnit.meters .S .one ≤
            pointCtReadout LengthUnit.meters point ∧
          pointCtReadout LengthUnit.meters point ≤
            eventCtReadout setup LengthUnit.meters .S .three

/-!
The ordinary area law for the axis-aligned rectangle bounded by the numbered
events. It relates the region's area to its coordinate width and height; it
does not contain the requested expression `c L T`.
-/
structure SatisfiesAxisAlignedRectangleAreaLaw
    (setup : FluorescentTubeSpacetimeSetup) : Prop where
  yellowRectangleAreaIsWidthTimesHeight :
    ∀ unit : LengthUnit,
      areaReadout unit
          (setup.areaOfRegionInSPlot setup.yellowRegionInS) =
        (eventXReadout setup unit .S .one -
            eventXReadout setup unit .S .two) *
          (eventCtReadout setup unit .S .three -
            eventCtReadout setup unit .S .one)

/-! ## Printed choices and target -/

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The literal symbolic expression printed beside each choice. -/
def printedAnswerExpression : AnswerChoice → String
  | .A => "cLT"
  | .B => "c/LT"
  | .C => "2cLT"
  | .D => "cL/T"

/-- Answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
The area of the bright-yellow region in the station-frame `x`--`ct` plot is
`c L T` in every compatible choice of length and time units. The right-hand
side has area dimension because `c T` and `L` are both lengths. This is
choice A.

This formalizes `thm:physics:phyx_mini_0610:target`.
-/
theorem problem_phyx_mini_0610
    (setup : FluorescentTubeSpacetimeSetup)
    (hScenario : MatchesFluorescentTubeScenario setup)
    (hFigure : MatchesPrimarySpacetimeFigure setup)
    (hEventData : MatchesEventCoordinateData setup)
    (hPhysical : HasPhysicalParameters setup)
    (hCtCoordinate : SatisfiesLightScaledTimeCoordinate setup)
    (hWorldsheet : SatisfiesIlluminatedTubeWorldsheet setup)
    (hRectangleArea : SatisfiesAxisAlignedRectangleAreaLaw setup) :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      areaReadout lengthUnit
          (setup.areaOfRegionInSPlot setup.yellowRegionInS) =
        speedReadout lengthUnit timeUnit DimSpeed.speedOfLight *
          lengthReadout lengthUnit setup.tubeLengthL *
          timeReadout timeUnit setup.litDurationT := by
  intro lengthUnit timeUnit
  rw [hRectangleArea.yellowRectangleAreaIsWidthTimesHeight lengthUnit]
  rw [hEventData.eventOneAtRightEndInS lengthUnit,
    hEventData.eventTwoAtLeftEndInS lengthUnit]
  rw [hCtCoordinate.stationFrameCtEqualsLightSpeedTimesTime
      .three lengthUnit timeUnit,
    hCtCoordinate.stationFrameCtEqualsLightSpeedTimesTime
      .one lengthUnit timeUnit]
  rw [hEventData.eventThreeAtFinalTime timeUnit,
    hEventData.eventOneAtInitialTime timeUnit]
  ring

end PhyXMiniProblems.ProblemPhyXMini0610
