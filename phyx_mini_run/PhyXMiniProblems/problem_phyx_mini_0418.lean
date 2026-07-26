import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0418

open Dimension

/-!
# Maximum pressure in a triangular pressure--volume cycle

The primary image shows a triangular cycle with vertices

* left base: `(200 cm³, 100 kPa)`,
* apex: `(500 cm³, p_max)`, and
* right base: `(800 cm³, 100 kPa)`.

Its arrows traverse left base to apex, apex to right base, and right base back
to left base, so the cycle is clockwise.  The auxiliary caption's description
of a rightward first leg conflicts with the base arrow in the bitmap; the
bitmap is the designated primary evidence.  The gas does `60 J` of net work
per cycle.

Pressure, volume, and work below remain dimensionful physical quantities.
Real numbers occur only as explicitly named unit readouts, diagram ticks,
conversion factors, and displayed multiple-choice values.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the axes, ticks, three vertex
  coordinates, straight legs, arrow directions, and clockwise orientation;
* `UsesGivenCycleWork` records the independently stated `60 J` net work;
* `HasPhysicalCycleParameters` records positivity and the meaning of
  `p_max` as the greatest vertex pressure;
* `SatisfiesTriangularCycleBoundaryWorkLaw` states the general fact that net
  boundary work is the signed enclosed `pV` area; and
* `maximumPressure_eq_three_hundred_kilopascals` is the requested conclusion.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical volume with dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Thermodynamic pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed work, using Physlib's energy dimension. -/
abbrev WorkQuantity : Type := DimEnergy

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal figure axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Kilopascal readout used on the vertical figure axis. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Joule readout of a signed physical work quantity. -/
def workInJoules (work : WorkQuantity) : ℝ :=
  (work UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- The conversion `1 kPa * cm³ = 10⁻³ J`. -/
def joulesPerKilopascalCubicCentimeter : ℝ := 1 / 1000

/-! ## Gas cycle and literal figure vocabulary -/

/-- The physical kind of working substance stated by the problem. -/
inductive WorkingSubstance where
  | gas
  deriving DecidableEq, Repr

/-- The three unlabeled black vertices of the triangular cycle. -/
inductive CycleVertex where
  | leftBase
  | apex
  | rightBase
  deriving DecidableEq, Fintype, Repr

/-- The directed sides, listed in the order shown by the arrowheads. -/
inductive CycleLeg where
  | leftBaseToApex
  | apexToRightBase
  | rightBaseToLeftBase
  deriving DecidableEq, Fintype, Repr

/-- The two Cartesian axes in the supplied pressure--volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity assigned to a figure axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside a figure axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | kilopascals
  deriving DecidableEq, Repr

/-- Literal mathematical symbol printed beside a figure axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Geometry of each side of the depicted cycle. -/
inductive PathShape where
  | straightSegment
  deriving DecidableEq, Repr

/-- Directions of the three arrowheads in the primary bitmap. -/
inductive ArrowDirection where
  | upAndRight
  | downAndRight
  | left
  deriving DecidableEq, Repr

/-- Orientation of a closed path in the `pV` plane. -/
inductive CycleOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-!
The visible content of the supplied diagram.  Numeric ticks are scalar
readouts in the units named by the axes; the thermodynamic state coordinates
remain separate dimensionful quantities in `TriangularPVCycleSetup`.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  volumeTickVisible : ℝ → Bool
  pressureTickVisible : ℝ → Bool
  maximumPressureTickVisible : Bool
  vertexVisible : CycleVertex → Bool
  arrowVisible : CycleLeg → Bool
  pathShape : CycleLeg → PathShape
  arrowDirection : CycleLeg → ArrowDirection

/-!
The independent physical data of the cyclic gas process.  In particular,
`maximumPressure` and `netWorkDoneByGas` are independent dimensionful fields;
neither is defined from an answer choice or from the requested value.
-/
structure TriangularPVCycleSetup where
  workingSubstance : WorkingSubstance
  volumeAt : CycleVertex → VolumeQuantity
  pressureAt : CycleVertex → PressureQuantity
  maximumPressure : PressureQuantity
  netWorkDoneByGas : WorkQuantity
  legStart : CycleLeg → CycleVertex
  legFinish : CycleLeg → CycleVertex
  orientation : CycleOrientation
  figure : PressureVolumeFigure

/-! ## Figure/data readouts and physical assumptions -/

/-!
Exact transcription of the problem statement and primary bitmap.  The apex
lies halfway between the `400` and `600 cm³` ticks, hence at `500 cm³`.
The field equating its pressure to `maximumPressure` records the meaning of
the printed `p_max` tick but gives that pressure no numerical value.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : TriangularPVCycleSetup) : Prop where
  substanceIsGas : setup.workingSubstance = .gas
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalUnitIsKilopascals :
    setup.figure.axisDisplayUnit .vertical = .kilopascals
  horizontalSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalSymbolIsP : setup.figure.axisSymbol .vertical = .p
  displayedVolumeTicks :
    setup.figure.volumeTickVisible 0 = true ∧
      setup.figure.volumeTickVisible 200 = true ∧
      setup.figure.volumeTickVisible 400 = true ∧
      setup.figure.volumeTickVisible 600 = true ∧
      setup.figure.volumeTickVisible 800 = true
  displayedPressureTicks :
    setup.figure.pressureTickVisible 0 = true ∧
      setup.figure.pressureTickVisible 100 = true
  maximumPressureTickIsShown :
    setup.figure.maximumPressureTickVisible = true
  everyVertexIsShown : ∀ vertex, setup.figure.vertexVisible vertex = true
  everyArrowIsShown : ∀ leg, setup.figure.arrowVisible leg = true
  leftBaseVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.volumeAt .leftBase) = 200
  apexVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.volumeAt .apex) = 500
  rightBaseVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.volumeAt .rightBase) = 800
  leftBasePressureKilopascals :
    pressureInKilopascals (setup.pressureAt .leftBase) = 100
  rightBasePressureKilopascals :
    pressureInKilopascals (setup.pressureAt .rightBase) = 100
  apexPressureIsMaximum : setup.pressureAt .apex = setup.maximumPressure
  leftToApexEndpoints :
    setup.legStart .leftBaseToApex = .leftBase ∧
      setup.legFinish .leftBaseToApex = .apex
  apexToRightEndpoints :
    setup.legStart .apexToRightBase = .apex ∧
      setup.legFinish .apexToRightBase = .rightBase
  rightToLeftEndpoints :
    setup.legStart .rightBaseToLeftBase = .rightBase ∧
      setup.legFinish .rightBaseToLeftBase = .leftBase
  everyLegIsStraight : ∀ leg, setup.figure.pathShape leg = .straightSegment
  leftToApexArrow :
    setup.figure.arrowDirection .leftBaseToApex = .upAndRight
  apexToRightArrow :
    setup.figure.arrowDirection .apexToRightBase = .downAndRight
  rightToLeftArrow :
    setup.figure.arrowDirection .rightBaseToLeftBase = .left
  arrowsGiveClockwiseOrientation : setup.orientation = .clockwise

/-- The independently stated net work done by the gas during one cycle. -/
structure UsesGivenCycleWork (setup : TriangularPVCycleSetup) : Prop where
  netWorkPerCycleJoules : workInJoules setup.netWorkDoneByGas = 60

/-!
Positivity and ordering conditions for the physical branch, including the
literal meaning of the name `maximumPressure`.  These conditions do not fix
its numerical value.
-/
structure HasPhysicalCycleParameters
    (setup : TriangularPVCycleSetup) : Prop where
  volumePositive :
    ∀ vertex, 0 < volumeInCubicMeters (setup.volumeAt vertex)
  pressurePositive :
    ∀ vertex, 0 < pressureInPascals (setup.pressureAt vertex)
  maximumPressurePositive : 0 < pressureInPascals setup.maximumPressure
  maximumBoundsVertexPressures :
    ∀ vertex,
      pressureInPascals (setup.pressureAt vertex) ≤
        pressureInPascals setup.maximumPressure
  apexStrictlyAboveBase :
    pressureInKilopascals (setup.pressureAt .leftBase) <
      pressureInKilopascals setup.maximumPressure

/-! ## Governing boundary-work law -/

/-- Clockwise cycles do positive net work by the gas; reversal changes sign. -/
def orientationSign : CycleOrientation → ℝ
  | .clockwise => 1
  | .counterclockwise => -1

/-!
Unsigned triangular area in the displayed `kPa * cm³` coordinates.  For the
pictured horizontal base, this is `base * height / 2`.
-/
def triangularPVAreaInKilopascalCubicCentimeters
    (setup : TriangularPVCycleSetup) : ℝ :=
  (volumeInCubicCentimeters (setup.volumeAt .rightBase) -
      volumeInCubicCentimeters (setup.volumeAt .leftBase)) *
    (pressureInKilopascals (setup.pressureAt .apex) -
      pressureInKilopascals (setup.pressureAt .leftBase)) / 2

/-!
For a closed triangular cycle made of straight quasistatic legs, boundary
work by the gas equals the orientation sign times the enclosed `pV` area,
after converting the displayed axis units to joules.  This is a general
governing relation and contains neither `300 kPa` nor an answer label.
-/
structure SatisfiesTriangularCycleBoundaryWorkLaw
    (setup : TriangularPVCycleSetup) : Prop where
  boundaryWorkEqualsSignedArea :
    (∀ leg, setup.figure.pathShape leg = .straightSegment) →
      workInJoules setup.netWorkDoneByGas =
        orientationSign setup.orientation *
          triangularPVAreaInKilopascalCubicCentimeters setup *
            joulesPerKilopascalCubicCentimeter

/-! ## Derived pressure rise and requested answer -/

/-!
Combining the independent `60 J` work datum with the general enclosed-area
law and the figure coordinates gives a `200 kPa` rise from the base to the
apex.  This is a derived lemma, not an assumption field.
-/
lemma maximumPressureRise_eq_two_hundred_kilopascals
    (setup : TriangularPVCycleSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_work : UsesGivenCycleWork setup)
    (_workLaw : SatisfiesTriangularCycleBoundaryWorkLaw setup) :
    pressureInKilopascals setup.maximumPressure -
        pressureInKilopascals (setup.pressureAt .leftBase) = 200 := by
  sorry

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilopascal value printed beside each answer label. -/
def displayedMaximumPressureKilopascals : AnswerChoice → ℝ
  | .A => 200
  | .B => 250
  | .C => 300
  | .D => 400

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A maximum pressure agrees with the value printed beside an answer choice. -/
def MaximumPressureMatchesChoice
    (pressure : PressureQuantity) (choice : AnswerChoice) : Prop :=
  pressureInKilopascals pressure =
    displayedMaximumPressureKilopascals choice

/-!
The triangle has base `600 cm³` and pressure height `p_max - 100 kPa`.
The clockwise enclosed-area law therefore gives
`60 J = (1/2)(600 cm³)(p_max - 100 kPa)`, after the factor
`10⁻³ J/(kPa * cm³)`, so `p_max = 300 kPa`, recorded answer C.

Blueprint label: `thm:physics:phyx_mini_0418:target`.
-/
theorem maximumPressure_eq_three_hundred_kilopascals
    (setup : TriangularPVCycleSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_work : UsesGivenCycleWork setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_workLaw : SatisfiesTriangularCycleBoundaryWorkLaw setup) :
    pressureInKilopascals setup.maximumPressure = 300 ∧
      MaximumPressureMatchesChoice
        setup.maximumPressure recordedAnswerChoice := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0418
