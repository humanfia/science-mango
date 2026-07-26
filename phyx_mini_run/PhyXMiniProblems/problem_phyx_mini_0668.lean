import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0668

open Dimension

/-!
# Average speed from an oil-drop pattern

A moving car releases one oil drop every five seconds.  The supplied figure
shows six successive drops, with the span from the first to the last labeled
`600 m`.  Thus the shown section contains five release intervals.

Lengths, durations, and speeds below are unit-independent Physlib quantities.
Real numbers are used only for coherent SI readouts, one-dimensional road
coordinates, and the displayed numerical answer.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout used by the road-span annotation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical duration as a real scalar in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Second readout used by the periodic-release law. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Read a physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Scenario and primary-figure vocabulary -/

/-- The six successive oil marks visible in the primary image, from left to right. -/
inductive OilDropMark where
  | drop0
  | drop1
  | drop2
  | drop3
  | drop4
  | drop5
  deriving DecidableEq, Fintype, Repr

/-- Adjacency in the release order of the six visible oil drops. -/
inductive ConsecutiveOilDrops : OilDropMark → OilDropMark → Prop where
  | drop0_drop1 : ConsecutiveOilDrops .drop0 .drop1
  | drop1_drop2 : ConsecutiveOilDrops .drop1 .drop2
  | drop2_drop3 : ConsecutiveOilDrops .drop2 .drop3
  | drop3_drop4 : ConsecutiveOilDrops .drop3 .drop4
  | drop4_drop5 : ConsecutiveOilDrops .drop4 .drop5

/-- Orientation of the road segment in the supplied image. -/
inductive RoadOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Direction of the car along the one-dimensional road coordinate. -/
inductive RoadDirection where
  | increasingCoordinate
  | decreasingCoordinate
  deriving DecidableEq, Repr

/-- Direction in which an oil drop falls from the engine to the pavement. -/
inductive OilFallDirection where
  | verticallyDown
  | other
  deriving DecidableEq, Repr

/-- Physical kind of the moving object in the scenario. -/
inductive MovingObjectKind where
  | car
  | other
  deriving DecidableEq, Repr

/-- Color of the pair of center lines visible on the road. -/
inductive RoadMarkingColor where
  | yellow
  | other
  deriving DecidableEq, Repr

/-- Named objects and annotations directly visible in the primary image. -/
inductive FigureFeature where
  | roadSurface
  | firstYellowCenterLine
  | secondYellowCenterLine
  | drop0
  | drop1
  | drop2
  | drop3
  | drop4
  | drop5
  | leftSpanArrow
  | rightSpanArrow
  | spanLabel600m
  deriving DecidableEq, Fintype, Repr

/-!
Primary-image evidence from `phyx_data/test_image/668.png`.
Coordinates are metre readouts along the horizontal road axis; the physical
road length itself is retained separately in `OilDropRoadSetup`.
-/
structure OilDropPatternFigure where
  shows : FigureFeature → Bool
  roadOrientation : RoadOrientation
  centerLineCount : ℕ
  centerLineColor : RoadMarkingColor
  spanStart : OilDropMark
  spanEnd : OilDropMark
  dropCoordinateMeters : OilDropMark → ℝ
  printedSpanMeters : ℝ

/-!
Independent physical quantities and observables in the problem.  In
particular, `averageSpeed` is not defined from the answer choice.
-/
structure OilDropRoadSetup where
  figure : OilDropPatternFigure
  movingObjectKind : MovingObjectKind
  carDirection : RoadDirection
  fallDirection : OilFallDirection
  roadSectionLength : LengthQuantity
  dropInterval : TimeQuantity
  averageSpeed : DimSpeed
  dropReleaseTimeSeconds : OilDropMark → ℝ
  carPositionMetersAtSecond : ℝ → ℝ
  dropImpactPositionMeters : OilDropMark → ℝ

/-! ## Assumptions: scenario, figure/data readouts, and governing laws -/

/-- Qualitative information stated in the physical scenario. -/
structure MatchesOilDropCarScenario (setup : OilDropRoadSetup) : Prop where
  movingObjectIsCar : setup.movingObjectKind = .car
  carMovesInFigureOrder : setup.carDirection = .increasingCoordinate
  oilFallsStraightDown : setup.fallDirection = .verticallyDown
  impactCoordinatesMatchFigure :
    ∀ drop, setup.dropImpactPositionMeters drop =
      setup.figure.dropCoordinateMeters drop

/-!
Readouts and qualitative geometry obtained from the supplied figure.  The
six-constructor type `OilDropMark` records the number of shown drops; the
fields below identify the first and last marks as the endpoints of the
`600 m` arrow.
-/
structure MatchesSuppliedOilDropFigure
    (figure : OilDropPatternFigure) : Prop where
  everyNamedFeatureShown : ∀ feature, figure.shows feature = true
  roadIsHorizontal : figure.roadOrientation = .horizontal
  twoCenterLines : figure.centerLineCount = 2
  centerLinesAreYellow : figure.centerLineColor = .yellow
  spanStartsAtFirstDrop : figure.spanStart = .drop0
  spanEndsAtLastDrop : figure.spanEnd = .drop5
  firstDropCoordinate : figure.dropCoordinateMeters .drop0 = 0
  lastDropCoordinate :
    figure.dropCoordinateMeters .drop5 = figure.printedSpanMeters
  printedRoadSpan : figure.printedSpanMeters = 600
  consecutiveDropsAppearInOrder :
    ∀ {first second}, ConsecutiveOilDrops first second →
      figure.dropCoordinateMeters first < figure.dropCoordinateMeters second

/-!
Numerical problem data connect the physical duration and road length to their
SI readouts.  Neither field mentions the requested average-speed value.
-/
structure MatchesProblemReadouts (setup : OilDropRoadSetup) : Prop where
  dropIntervalIsFiveSeconds : timeInSeconds setup.dropInterval = 5
  roadLengthMatchesPrintedSpan :
    lengthInMeters setup.roadSectionLength = setup.figure.printedSpanMeters

/-!
The idealized kinematics used in the problem:

* consecutive drops are released one physical `dropInterval` apart;
* a vertically falling drop records the car's horizontal release position;
* average speed over the shown section is endpoint displacement divided by
  endpoint elapsed time.

These are governing relations, not the requested numerical conclusion.
-/
structure SatisfiesOilDropKinematics (setup : OilDropRoadSetup) : Prop where
  periodicRelease :
    ∀ {first second}, ConsecutiveOilDrops first second →
      setup.dropReleaseTimeSeconds second -
          setup.dropReleaseTimeSeconds first =
        timeInSeconds setup.dropInterval
  verticalDropRecordsReleasePosition :
    ∀ drop, setup.dropImpactPositionMeters drop =
      setup.carPositionMetersAtSecond (setup.dropReleaseTimeSeconds drop)
  positiveEndpointElapsedTime :
    setup.dropReleaseTimeSeconds .drop0 <
      setup.dropReleaseTimeSeconds .drop5
  averageSpeedLaw :
    speedInMetersPerSecond setup.averageSpeed =
      (setup.carPositionMetersAtSecond
            (setup.dropReleaseTimeSeconds .drop5) -
          setup.carPositionMetersAtSecond
            (setup.dropReleaseTimeSeconds .drop0)) /
        (setup.dropReleaseTimeSeconds .drop5 -
          setup.dropReleaseTimeSeconds .drop0)

/-! ## Derived relations and target -/

/-- Six visible drops determine five equal release intervals. -/
lemma endpointElapsedTime_eq_five_intervals
    (setup : OilDropRoadSetup)
    (hKinematics : SatisfiesOilDropKinematics setup) :
    setup.dropReleaseTimeSeconds .drop5 -
        setup.dropReleaseTimeSeconds .drop0 =
      5 * timeInSeconds setup.dropInterval := by
  linear_combination
    hKinematics.periodicRelease ConsecutiveOilDrops.drop0_drop1 +
    hKinematics.periodicRelease ConsecutiveOilDrops.drop1_drop2 +
    hKinematics.periodicRelease ConsecutiveOilDrops.drop2_drop3 +
    hKinematics.periodicRelease ConsecutiveOilDrops.drop3_drop4 +
    hKinematics.periodicRelease ConsecutiveOilDrops.drop4_drop5

/-- The first-to-last car displacement is the span printed in the figure. -/
lemma endpointCarDisplacement_eq_printedSpan
    (setup : OilDropRoadSetup)
    (hScenario : MatchesOilDropCarScenario setup)
    (hFigure : MatchesSuppliedOilDropFigure setup.figure)
    (hKinematics : SatisfiesOilDropKinematics setup) :
    setup.carPositionMetersAtSecond
          (setup.dropReleaseTimeSeconds .drop5) -
        setup.carPositionMetersAtSecond
          (setup.dropReleaseTimeSeconds .drop0) =
      setup.figure.printedSpanMeters := by
  rw [← hKinematics.verticalDropRecordsReleasePosition .drop5,
    ← hKinematics.verticalDropRecordsReleasePosition .drop0,
    hScenario.impactCoordinatesMatchFigure .drop5,
    hScenario.impactCoordinatesMatchFigure .drop0,
    hFigure.lastDropCoordinate,
    hFigure.firstDropCoordinate]
  ring

/--
The car's average speed over the first-to-last oil-drop span is `24 m/s`.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0668:target`.
-/
theorem averageSpeedOfCarOverShownSection
    (setup : OilDropRoadSetup)
    (hScenario : MatchesOilDropCarScenario setup)
    (hFigure : MatchesSuppliedOilDropFigure setup.figure)
    (hReadouts : MatchesProblemReadouts setup)
    (hKinematics : SatisfiesOilDropKinematics setup) :
    speedInMetersPerSecond setup.averageSpeed = 24 := by
  rw [hKinematics.averageSpeedLaw,
    endpointCarDisplacement_eq_printedSpan setup hScenario hFigure hKinematics,
    endpointElapsedTime_eq_five_intervals setup hKinematics,
    hFigure.printedRoadSpan,
    hReadouts.dropIntervalIsFiveSeconds]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0668
