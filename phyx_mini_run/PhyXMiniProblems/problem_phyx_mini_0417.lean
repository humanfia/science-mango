import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0417

open Dimension

/-!
# Work done by a gas in a triangular pressure-volume cycle

The primary figure shows a gas traversing the clockwise triangular cycle

* `lowerLeft = (200 cm³, 1 atm)`,
* `upperLeft = (200 cm³, 3 atm)`, and
* `lowerRight = (600 cm³, 1 atm)`.

The path first goes vertically upward, then diagonally down and to the right,
and finally horizontally back to the left.  Pressure, volume, and work retain
physical dimensions.  Real numbers occur only as explicitly unit-labelled
readouts, diagram coordinates, conversion factors, and answer values.

The exact standard-atmosphere conversion gives `40.53 J`.  Since the source is
a coarse multiple-choice question, the final theorem also states that the
displayed `40 J` answer is the unique nearest listed choice.
-/

/-! ## Dimensionful quantities and named unit readouts -/

/-- A nonnegative physical volume carrying dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Thermodynamic pressure, represented by Physlib's dimensionful type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed work, represented by Physlib's dimensionful energy type. -/
abbrev WorkQuantity : Type := DimEnergy

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal axis of the figure. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Standard-atmosphere readout used on the vertical axis of the figure. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Joule readout of a signed physical work quantity. -/
def workInJoules (work : WorkQuantity) : ℝ :=
  (work UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-!
The exact energy in one atmosphere-cubic-centimetre.  The numerator is
Physlib's grounded standard-atmosphere value in pascals, and `10⁶ cm³ = 1 m³`.
-/
def joulesPerAtmosphereCubicCentimeter : ℝ :=
  101325 / 10 ^ 6

/-! ## Thermodynamic states, cycle, and primary-figure vocabulary -/

/-- Geometric names for the three unlabeled marked vertices in the bitmap. -/
inductive CycleVertex where
  | lowerLeft
  | upperLeft
  | lowerRight
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs, in their displayed traversal order. -/
inductive CycleLeg where
  | lowerLeftToUpperLeft
  | upperLeftToLowerRight
  | lowerRightToLowerLeft
  deriving DecidableEq, Fintype, Repr

/-- Pressure and volume at one equilibrium state of the gas. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity

/-- Thermodynamic regime needed for reading boundary work from a `pV` path. -/
inductive ProcessRegime where
  | quasistatic
  deriving DecidableEq, Repr

/-- Geometric shape of each depicted cycle leg. -/
inductive PathShape where
  | straightSegment
  deriving DecidableEq, Repr

/-- Direction of a leg's arrow in the primary bitmap. -/
inductive PathDirection where
  | verticallyUp
  | diagonallyDownAndRight
  | horizontallyLeft
  deriving DecidableEq, Repr

/-- Orientation of the complete loop in the pressure-volume plane. -/
inductive TraversalDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- The Cartesian axes of the supplied pressure-volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to an axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside an axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | atmospheres
  deriving DecidableEq, Repr

/-- Literal variable symbol printed beside an axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-!
Structured transcription of image `417.png`.  The physical plotted coordinates
remain dimensionful; the matching predicate below supplies their scalar axis
readouts.  No work value is stored in the figure.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  axisMinimum : FigureAxis → ℝ
  axisMaximum : FigureAxis → ℝ
  axisTickVisible : FigureAxis → ℝ → Bool
  plottedVolume : CycleVertex → VolumeQuantity
  plottedPressure : CycleVertex → PressureQuantity
  vertexMarkerVisible : CycleVertex → Bool
  arrowVisibleOn : CycleLeg → Bool

/-!
The gas cycle and its signed work quantities.  Each leg work and the net work
are independent dimensionful fields.  In particular, none is defined from an
answer choice or assigned the requested numerical result.
-/
structure TriangularPVCycleSetup where
  stateAt : CycleVertex → ThermodynamicState
  legStart : CycleLeg → CycleVertex
  legFinish : CycleLeg → CycleVertex
  legRegime : CycleLeg → ProcessRegime
  legShape : CycleLeg → PathShape
  legDirection : CycleLeg → PathDirection
  traversalDirection : TraversalDirection
  workDoneByGasOnLeg : CycleLeg → WorkQuantity
  netWorkDoneByGasPerCycle : WorkQuantity
  figure : PressureVolumeFigure

/-! ## Problem data and primary-figure readouts -/

/-!
Exact transcription of the prose and primary bitmap: `V` is horizontal in
`cm³`, `p` is vertical in atmospheres, and the three arrows form the clockwise
cycle through `(200,1)`, `(200,3)`, and `(600,1)`.  No work value occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TriangularPVCycleSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalAxisUnitIsAtmospheres :
    setup.figure.axisDisplayUnit .vertical = .atmospheres
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  horizontalAxisRange :
    setup.figure.axisMinimum .horizontal = 0 ∧
      setup.figure.axisMaximum .horizontal = 600
  verticalAxisRange :
    setup.figure.axisMinimum .vertical = 0 ∧
      setup.figure.axisMaximum .vertical = 3
  horizontalTicksVisible :
    setup.figure.axisTickVisible .horizontal 0 = true ∧
      setup.figure.axisTickVisible .horizontal 200 = true ∧
      setup.figure.axisTickVisible .horizontal 400 = true ∧
      setup.figure.axisTickVisible .horizontal 600 = true
  verticalTicksVisible :
    setup.figure.axisTickVisible .vertical 0 = true ∧
      setup.figure.axisTickVisible .vertical 1 = true ∧
      setup.figure.axisTickVisible .vertical 2 = true ∧
      setup.figure.axisTickVisible .vertical 3 = true
  plottedCoordinatesAreGasStates : ∀ vertex : CycleVertex,
    setup.figure.plottedVolume vertex = (setup.stateAt vertex).volume ∧
      setup.figure.plottedPressure vertex = (setup.stateAt vertex).pressure
  lowerLeftCoordinates :
    volumeInCubicCentimeters
        (setup.figure.plottedVolume .lowerLeft) = 200 ∧
      pressureInAtmospheres
        (setup.figure.plottedPressure .lowerLeft) = 1
  upperLeftCoordinates :
    volumeInCubicCentimeters
        (setup.figure.plottedVolume .upperLeft) = 200 ∧
      pressureInAtmospheres
        (setup.figure.plottedPressure .upperLeft) = 3
  lowerRightCoordinates :
    volumeInCubicCentimeters
        (setup.figure.plottedVolume .lowerRight) = 600 ∧
      pressureInAtmospheres
        (setup.figure.plottedPressure .lowerRight) = 1
  firstLegEndpoints :
    setup.legStart .lowerLeftToUpperLeft = .lowerLeft ∧
      setup.legFinish .lowerLeftToUpperLeft = .upperLeft
  secondLegEndpoints :
    setup.legStart .upperLeftToLowerRight = .upperLeft ∧
      setup.legFinish .upperLeftToLowerRight = .lowerRight
  thirdLegEndpoints :
    setup.legStart .lowerRightToLowerLeft = .lowerRight ∧
      setup.legFinish .lowerRightToLowerLeft = .lowerLeft
  allLegsAreStraight : ∀ leg, setup.legShape leg = .straightSegment
  firstArrowDirection :
    setup.legDirection .lowerLeftToUpperLeft = .verticallyUp
  secondArrowDirection :
    setup.legDirection .upperLeftToLowerRight = .diagonallyDownAndRight
  thirdArrowDirection :
    setup.legDirection .lowerRightToLowerLeft = .horizontallyLeft
  completeTraversalIsClockwise :
    setup.traversalDirection = .clockwise
  allVertexMarkersVisible : ∀ vertex,
    setup.figure.vertexMarkerVisible vertex = true
  allDirectionArrowsVisible : ∀ leg,
    setup.figure.arrowVisibleOn leg = true

/-- Positivity conditions selecting physically meaningful pressure and volume. -/
structure HasPhysicalPressureVolumeCoordinates
    (setup : TriangularPVCycleSetup) : Prop where
  pressurePositive : ∀ vertex,
    0 < pressureInPascals (setup.stateAt vertex).pressure
  volumePositive : ∀ vertex,
    0 < volumeInCubicMeters (setup.stateAt vertex).volume

/-!
The implicit modeling condition that makes the plotted gas pressure applicable
to boundary work along every leg.  This premise assigns no numerical work.
-/
structure IsQuasistaticCycle (setup : TriangularPVCycleSetup) : Prop where
  everyLegIsQuasistatic : ∀ leg,
    setup.legRegime leg = .quasistatic

/-! ## Governing work laws -/

/-!
Boundary work for a quasistatic straight leg.  Linear pressure variation makes
`∫ p dV` equal average endpoint pressure times the signed volume change.  The
last factor performs the exact conversion from `atm·cm³` to joules.  This law
is generic over all legs and contains none of this problem's derived works.
-/
structure SatisfiesStraightLegBoundaryWorkLaw
    (setup : TriangularPVCycleSetup) : Prop where
  workForQuasistaticStraightLeg : ∀ leg,
    setup.legRegime leg = .quasistatic →
      setup.legShape leg = .straightSegment →
        workInJoules (setup.workDoneByGasOnLeg leg) =
          ((pressureInAtmospheres
                (setup.stateAt (setup.legStart leg)).pressure +
              pressureInAtmospheres
                (setup.stateAt (setup.legFinish leg)).pressure) / 2) *
            (volumeInCubicCentimeters
                (setup.stateAt (setup.legFinish leg)).volume -
              volumeInCubicCentimeters
                (setup.stateAt (setup.legStart leg)).volume) *
              joulesPerAtmosphereCubicCentimeter

/-!
Additivity of work over the three consecutive legs of one cycle.  This is a
general composition law and does not assign a numerical value to net work.
-/
structure SatisfiesCycleWorkAdditivity
    (setup : TriangularPVCycleSetup) : Prop where
  netWorkIsSumOfLegWorks :
    workInJoules setup.netWorkDoneByGasPerCycle =
      workInJoules
          (setup.workDoneByGasOnLeg .lowerLeftToUpperLeft) +
        workInJoules
          (setup.workDoneByGasOnLeg .upperLeftToLowerRight) +
        workInJoules
          (setup.workDoneByGasOnLeg .lowerRightToLowerLeft)

/-! ## Derived work and displayed answer -/

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Work readout in joules printed beside each answer label. -/
def displayedWorkInJoules : AnswerChoice → ℝ
  | .A => 20
  | .B => 80
  | .C => 40
  | .D => 0

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A displayed answer is uniquely nearest to the exact physical work readout.
This comparison is appropriate here because the listed values are coarse while
one standard atmosphere is exactly `101325 Pa`.
-/
def IsUniqueNearestDisplayedChoice
    (setup : TriangularPVCycleSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |workInJoules setup.netWorkDoneByGasPerCycle -
        displayedWorkInJoules choice| <
      |workInJoules setup.netWorkDoneByGasPerCycle -
        displayedWorkInJoules other|

/-!
The vertical leg does no work, the diagonal expansion does `81.06 J`, and the
horizontal compression does `-40.53 J`.  These are derived conclusions, not
fields of any problem-data or governing-law premise.
-/
lemma workDoneByGasOnTriangularCycleLegs
    (setup : TriangularPVCycleSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_quasistatic : IsQuasistaticCycle setup)
    (_workLaw : SatisfiesStraightLegBoundaryWorkLaw setup) :
    workInJoules
        (setup.workDoneByGasOnLeg .lowerLeftToUpperLeft) = 0 ∧
      workInJoules
        (setup.workDoneByGasOnLeg .upperLeftToLowerRight) = 4053 / 50 ∧
      workInJoules
        (setup.workDoneByGasOnLeg .lowerRightToLowerLeft) = -(4053 / 100) := by
  have lowerLeftVolume :
      volumeInCubicCentimeters (setup.stateAt .lowerLeft).volume = 200 := by
    rw [← (_figure.plottedCoordinatesAreGasStates .lowerLeft).1]
    exact _figure.lowerLeftCoordinates.1
  have lowerLeftPressure :
      pressureInAtmospheres (setup.stateAt .lowerLeft).pressure = 1 := by
    rw [← (_figure.plottedCoordinatesAreGasStates .lowerLeft).2]
    exact _figure.lowerLeftCoordinates.2
  have upperLeftVolume :
      volumeInCubicCentimeters (setup.stateAt .upperLeft).volume = 200 := by
    rw [← (_figure.plottedCoordinatesAreGasStates .upperLeft).1]
    exact _figure.upperLeftCoordinates.1
  have upperLeftPressure :
      pressureInAtmospheres (setup.stateAt .upperLeft).pressure = 3 := by
    rw [← (_figure.plottedCoordinatesAreGasStates .upperLeft).2]
    exact _figure.upperLeftCoordinates.2
  have lowerRightVolume :
      volumeInCubicCentimeters (setup.stateAt .lowerRight).volume = 600 := by
    rw [← (_figure.plottedCoordinatesAreGasStates .lowerRight).1]
    exact _figure.lowerRightCoordinates.1
  have lowerRightPressure :
      pressureInAtmospheres (setup.stateAt .lowerRight).pressure = 1 := by
    rw [← (_figure.plottedCoordinatesAreGasStates .lowerRight).2]
    exact _figure.lowerRightCoordinates.2
  have verticalWork :=
    _workLaw.workForQuasistaticStraightLeg .lowerLeftToUpperLeft
      (_quasistatic.everyLegIsQuasistatic .lowerLeftToUpperLeft)
      (_figure.allLegsAreStraight .lowerLeftToUpperLeft)
  have diagonalWork :=
    _workLaw.workForQuasistaticStraightLeg .upperLeftToLowerRight
      (_quasistatic.everyLegIsQuasistatic .upperLeftToLowerRight)
      (_figure.allLegsAreStraight .upperLeftToLowerRight)
  have horizontalWork :=
    _workLaw.workForQuasistaticStraightLeg .lowerRightToLowerLeft
      (_quasistatic.everyLegIsQuasistatic .lowerRightToLowerLeft)
      (_figure.allLegsAreStraight .lowerRightToLowerLeft)
  rw [_figure.firstLegEndpoints.1, _figure.firstLegEndpoints.2,
    lowerLeftPressure, upperLeftPressure, lowerLeftVolume, upperLeftVolume]
    at verticalWork
  rw [_figure.secondLegEndpoints.1, _figure.secondLegEndpoints.2,
    upperLeftPressure, lowerRightPressure, upperLeftVolume, lowerRightVolume]
    at diagonalWork
  rw [_figure.thirdLegEndpoints.1, _figure.thirdLegEndpoints.2,
    lowerRightPressure, lowerLeftPressure, lowerRightVolume, lowerLeftVolume]
    at horizontalWork
  norm_num [joulesPerAtmosphereCubicCentimeter] at verticalWork diagonalWork horizontalWork ⊢
  exact ⟨verticalWork, diagonalWork, horizontalWork⟩

/-!
The clockwise triangular loop has exact standard-atmosphere work
`40.53 J = 4053/100 J`.  Of the listed values, `40 J` (choice C) is uniquely
nearest and is the answer recorded by the dataset.

Blueprint: `thm:physics:phyx_mini_0417:target`.
-/
theorem netWorkDoneByGasPerTriangularCycle
    (setup : TriangularPVCycleSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalPressureVolumeCoordinates setup)
    (_quasistatic : IsQuasistaticCycle setup)
    (_workLaw : SatisfiesStraightLegBoundaryWorkLaw setup)
    (_additivity : SatisfiesCycleWorkAdditivity setup) :
    workInJoules setup.netWorkDoneByGasPerCycle = 4053 / 100 ∧
      IsUniqueNearestDisplayedChoice setup recordedAnswerChoice ∧
      displayedWorkInJoules recordedAnswerChoice = 40 ∧
      recordedAnswerChoice = .C := by
  obtain ⟨verticalWork, diagonalWork, horizontalWork⟩ :=
    workDoneByGasOnTriangularCycleLegs setup _figure _quasistatic _workLaw
  have netWork := _additivity.netWorkIsSumOfLegWorks
  rw [verticalWork, diagonalWork, horizontalWork] at netWork
  norm_num at netWork
  refine ⟨netWork, ?_, by rfl, rfl⟩
  intro other other_ne
  rw [netWork]
  cases other <;>
    norm_num [recordedAnswerChoice, displayedWorkInJoules] at *

end PhyXMiniProblems.ProblemPhyXMini0417
