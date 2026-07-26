import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0408

open Dimension

/-!
# Heat difference between two rectangular pressure--volume paths

The primary image shows two directed processes taking the same gas from the
lower-left state `i = (V_i, p_i)` to the upper-right state
`f = (2 V_i, 2 p_i)`.

* Path `A` first moves vertically at volume `V_i`, then expands horizontally
  at pressure `2 p_i`.
* Path `B` first expands horizontally at pressure `p_i`, then moves vertically
  at volume `2 V_i`.

Thus all four arrows in the bitmap point from `i` toward `f`; the auxiliary
caption's description of a closed-cycle direction is not used.  Work is
positive when done by the gas and heat is positive when transferred into the
gas, so the first law is written `Q = U_f - U_i + W_by`.

Pressure, volume, heat, work, and internal energy retain physical dimensions.
Real numbers below occur only as coherent SI readouts or as dimensionless
figure multipliers.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A signed physical volume, with dimension `L^3`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure, with dimension `M L⁻¹ T⁻²`. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy, used for heat, work, and internal energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical pressure in SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read heat, work, or internal energy in SI joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## State, path, and figure vocabulary -/

/-- The two endpoint states and two unlabeled corners of the rectangle. -/
inductive StateLabel where
  | i
  | upperLeft
  | lowerRight
  | f
  deriving DecidableEq, Repr

/-- The two routes labelled `A` and `B` in the primary image. -/
inductive ProcessPath where
  | A
  | B
  deriving DecidableEq, Repr

/-- The four directed straight segments displayed in the image. -/
inductive ProcessLeg where
  | iToUpperLeft
  | upperLeftToF
  | iToLowerRight
  | lowerRightToF
  deriving DecidableEq, Repr

/-- Initial state of a directed process leg. -/
def ProcessLeg.initialState : ProcessLeg → StateLabel
  | .iToUpperLeft => .i
  | .upperLeftToF => .upperLeft
  | .iToLowerRight => .i
  | .lowerRightToF => .lowerRight

/-- Final state of a directed process leg. -/
def ProcessLeg.finalState : ProcessLeg → StateLabel
  | .iToUpperLeft => .upperLeft
  | .upperLeftToF => .f
  | .iToLowerRight => .lowerRight
  | .lowerRightToF => .f

/-- First leg of either displayed route from `i` to `f`. -/
def ProcessPath.firstLeg : ProcessPath → ProcessLeg
  | .A => .iToUpperLeft
  | .B => .iToLowerRight

/-- Second leg of either displayed route from `i` to `f`. -/
def ProcessPath.secondLeg : ProcessPath → ProcessLeg
  | .A => .upperLeftToF
  | .B => .lowerRightToF

/-- Initial state of either complete displayed route. -/
def ProcessPath.initialState (_path : ProcessPath) : StateLabel := .i

/-- Final state of either complete displayed route. -/
def ProcessPath.finalState (_path : ProcessPath) : StateLabel := .f

/-- Thermodynamic constraint represented by a straight segment. -/
inductive ProcessKind where
  | isochoric
  | isobaric
  deriving DecidableEq, Repr

/-- Orientation of a segment in the pressure--volume plane. -/
inductive SegmentOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Which physical quantity is assigned to an axis. -/
inductive AxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- The two relative pressure labels printed on the vertical axis. -/
inductive PressureAxisLabel where
  | pInitial
  | twicePInitial
  deriving DecidableEq, Repr

/-- The two relative volume labels printed on the horizontal axis. -/
inductive VolumeAxisLabel where
  | VInitial
  | twiceVInitial
  deriving DecidableEq, Repr

/-!
Qualitative evidence retained from the primary bitmap.  The physical
coordinates live in `GasProcessSetup`; this structure stores visible axes,
endpoint dots and labels, route labels, segments, and directed arrows.
-/
structure PressureVolumeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  originZeroShown : Bool
  initialPointShown : Bool
  finalPointShown : Bool
  initialLabelShown : Bool
  finalLabelShown : Bool
  routeLabelShown : ProcessPath → Bool
  pressureAxisLabelShown : PressureAxisLabel → Bool
  volumeAxisLabelShown : VolumeAxisLabel → Bool
  processSegmentShown : ProcessLeg → Bool
  arrowStart : ProcessLeg → StateLabel
  arrowFinish : ProcessLeg → StateLabel
  segmentOrientation : ProcessLeg → SegmentOrientation

/-- Closed-system interpretation used for the fixed sample of gas. -/
inductive ThermodynamicSystemBoundary where
  | closedFixedGas
  deriving DecidableEq, Repr

/-!
Independent thermodynamic quantities for the displayed process.  Internal
energy is state-dependent, whereas heat and work along a complete process are
path-dependent.  No field fixes the requested heat difference.
-/
structure GasProcessSetup where
  boundary : ThermodynamicSystemBoundary
  figure : PressureVolumeFigure
  pressureAt : StateLabel → PressureQuantity
  volumeAt : StateLabel → VolumeQuantity
  internalEnergyAt : StateLabel → EnergyQuantity
  processKind : ProcessLeg → ProcessKind
  workDoneByGasOnLeg : ProcessLeg → EnergyQuantity
  workDoneByGasAlong : ProcessPath → EnergyQuantity
  heatTransferredIntoGasAlong : ProcessPath → EnergyQuantity

/-- The physical pressure denoted by `p_i` in the figure. -/
def initialPressure (setup : GasProcessSetup) : PressureQuantity :=
  setup.pressureAt .i

/-- The physical volume denoted by `V_i` in the figure. -/
def initialVolume (setup : GasProcessSetup) : VolumeQuantity :=
  setup.volumeAt .i

/-! ## Problem statement and primary-figure readouts -/

/-- The scenario concerns a fixed sample of gas in a closed system. -/
structure MatchesProblemStatement (setup : GasProcessSetup) : Prop where
  boundaryIsClosedFixedGas : setup.boundary = .closedFixedGas

/-!
Exact transcription of the primary image.  Besides axes, labels, segment
orientations, and arrows, it records the four relative coordinates

`i = (V_i,p_i)`, `upperLeft = (V_i,2p_i)`,
`lowerRight = (2V_i,p_i)`, and `f = (2V_i,2p_i)`.

No heat, work, or internal-energy value occurs in this figure-data structure.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : GasProcessSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  originZeroIsShown : setup.figure.originZeroShown = true
  initialPointIsShown : setup.figure.initialPointShown = true
  finalPointIsShown : setup.figure.finalPointShown = true
  initialLabelIsShown : setup.figure.initialLabelShown = true
  finalLabelIsShown : setup.figure.finalLabelShown = true
  bothRouteLabelsAreShown :
    ∀ path : ProcessPath, setup.figure.routeLabelShown path = true
  bothPressureLabelsAreShown :
    ∀ label : PressureAxisLabel,
      setup.figure.pressureAxisLabelShown label = true
  bothVolumeLabelsAreShown :
    ∀ label : VolumeAxisLabel,
      setup.figure.volumeAxisLabelShown label = true
  everySegmentIsShown :
    ∀ leg : ProcessLeg, setup.figure.processSegmentShown leg = true
  everyArrowHasItsDisplayedEndpoints : ∀ leg : ProcessLeg,
    setup.figure.arrowStart leg = leg.initialState ∧
      setup.figure.arrowFinish leg = leg.finalState
  leftLegIsVertical :
    setup.figure.segmentOrientation .iToUpperLeft = .vertical
  upperLegIsHorizontal :
    setup.figure.segmentOrientation .upperLeftToF = .horizontal
  lowerLegIsHorizontal :
    setup.figure.segmentOrientation .iToLowerRight = .horizontal
  rightLegIsVertical :
    setup.figure.segmentOrientation .lowerRightToF = .vertical
  leftLegIsIsochoric : setup.processKind .iToUpperLeft = .isochoric
  upperLegIsIsobaric : setup.processKind .upperLeftToF = .isobaric
  lowerLegIsIsobaric : setup.processKind .iToLowerRight = .isobaric
  rightLegIsIsochoric : setup.processKind .lowerRightToF = .isochoric
  pressureAtUpperLeftIsTwiceInitial :
    pressureInPascals (setup.pressureAt .upperLeft) =
      2 * pressureInPascals (initialPressure setup)
  pressureAtLowerRightIsInitial :
    pressureInPascals (setup.pressureAt .lowerRight) =
      pressureInPascals (initialPressure setup)
  pressureAtFinalIsTwiceInitial :
    pressureInPascals (setup.pressureAt .f) =
      2 * pressureInPascals (initialPressure setup)
  volumeAtUpperLeftIsInitial :
    volumeInCubicMetres (setup.volumeAt .upperLeft) =
      volumeInCubicMetres (initialVolume setup)
  volumeAtLowerRightIsTwiceInitial :
    volumeInCubicMetres (setup.volumeAt .lowerRight) =
      2 * volumeInCubicMetres (initialVolume setup)
  volumeAtFinalIsTwiceInitial :
    volumeInCubicMetres (setup.volumeAt .f) =
      2 * volumeInCubicMetres (initialVolume setup)

/-- Positivity conditions selecting physical pressure and volume coordinates. -/
structure HasPhysicalPressureVolumeCoordinates
    (setup : GasProcessSetup) : Prop where
  pressurePositive :
    ∀ state : StateLabel, 0 < pressureInPascals (setup.pressureAt state)
  volumePositive :
    ∀ state : StateLabel, 0 < volumeInCubicMetres (setup.volumeAt state)

/-! ## Governing work and energy laws -/

/-!
Quasistatic pressure--volume boundary work.  Constant-volume legs do no work;
on a constant-pressure leg, work by the gas is `p (V_finish - V_start)`.
This law is stated uniformly for every leg and contains no heat difference.
-/
structure SatisfiesQuasistaticBoundaryWorkLaw
    (setup : GasProcessSetup) : Prop where
  isochoricLegHasZeroWork : ∀ leg : ProcessLeg,
    setup.processKind leg = .isochoric →
      energyInJoules (setup.workDoneByGasOnLeg leg) = 0
  isobaricLegWork : ∀ leg : ProcessLeg,
    setup.processKind leg = .isobaric →
      energyInJoules (setup.workDoneByGasOnLeg leg) =
        pressureInPascals (setup.pressureAt leg.initialState) *
          (volumeInCubicMetres (setup.volumeAt leg.finalState) -
            volumeInCubicMetres (setup.volumeAt leg.initialState))

/-- Work on either complete route is the sum of its two leg works. -/
structure SatisfiesPathWorkAdditivity
    (setup : GasProcessSetup) : Prop where
  workAlongTwoLegPath : ∀ path : ProcessPath,
    energyInJoules (setup.workDoneByGasAlong path) =
      energyInJoules (setup.workDoneByGasOnLeg path.firstLeg) +
        energyInJoules (setup.workDoneByGasOnLeg path.secondLeg)

/-!
The closed-system first law on either complete path.  Heat is positive into
the gas and boundary work is positive when done by the gas.  Both paths have
the same endpoint states, but no heat value or heat difference is prescribed.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : GasProcessSetup) : Prop where
  firstLawOnPath : ∀ path : ProcessPath,
    energyInJoules (setup.heatTransferredIntoGasAlong path) =
      energyInJoules (setup.internalEnergyAt path.finalState) -
          energyInJoules (setup.internalEnergyAt path.initialState) +
        energyInJoules (setup.workDoneByGasAlong path)

/-! ## Recorded multiple-choice metadata -/

/-- The four answer labels printed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless coefficient of `p_i V_i` displayed by each answer choice. -/
def AnswerChoice.displayedCoefficient : AnswerChoice → ℝ
  | .A => 0
  | .B => 2
  | .C => 1
  | .D => -1

/-- The dataset records choice C; this is metadata and is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-! ## Main target -/

/-!
The first law gives the same internal-energy change on both routes.  Path A's
horizontal expansion occurs at `2p_i`, while path B's occurs at `p_i`; the
isochoric legs do no work.  Therefore `Q_A - Q_B = p_i V_i`, expressed here
in coherent SI units.

Blueprint label: `thm:physics:phyx_mini_0408:target`.
-/
theorem heatDifferenceBetweenPaths_eq_initialPressure_mul_initialVolume
    (setup : GasProcessSetup)
    (_scenario : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalPressureVolumeCoordinates setup)
    (_boundaryWork : SatisfiesQuasistaticBoundaryWorkLaw setup)
    (_workAdditivity : SatisfiesPathWorkAdditivity setup)
    (_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules (setup.heatTransferredIntoGasAlong .A) -
        energyInJoules (setup.heatTransferredIntoGasAlong .B) =
      pressureInPascals (initialPressure setup) *
        volumeInCubicMetres (initialVolume setup) := by
  have h_left := _boundaryWork.isochoricLegHasZeroWork
    .iToUpperLeft _figure.leftLegIsIsochoric
  have h_upper := _boundaryWork.isobaricLegWork
    .upperLeftToF _figure.upperLegIsIsobaric
  have h_lower := _boundaryWork.isobaricLegWork
    .iToLowerRight _figure.lowerLegIsIsobaric
  have h_right := _boundaryWork.isochoricLegHasZeroWork
    .lowerRightToF _figure.rightLegIsIsochoric
  have h_work_A := _workAdditivity.workAlongTwoLegPath .A
  have h_work_B := _workAdditivity.workAlongTwoLegPath .B
  have h_heat_A := _firstLaw.firstLawOnPath .A
  have h_heat_B := _firstLaw.firstLawOnPath .B
  simp only [ProcessLeg.initialState, ProcessLeg.finalState,
    ProcessPath.firstLeg, ProcessPath.secondLeg, ProcessPath.initialState,
    ProcessPath.finalState] at h_upper h_lower h_work_A h_work_B h_heat_A h_heat_B
  rw [_figure.pressureAtUpperLeftIsTwiceInitial,
    _figure.volumeAtFinalIsTwiceInitial,
    _figure.volumeAtUpperLeftIsInitial] at h_upper
  rw [_figure.volumeAtLowerRightIsTwiceInitial] at h_lower
  simp only [initialPressure, initialVolume] at h_upper h_lower ⊢
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0408
