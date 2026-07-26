import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Work done on a gas during a constant-pressure expansion

This file formalizes problem `phyx_mini_0403`.  The supplied pressure-volume
diagram shows a gas expanding along a horizontal segment from the state labelled
`i` to the state labelled `f`.  The exact plotted readouts are

* `i`: `V = 100 cm³` and `p = 400 kPa`;
* `f`: `V = 300 cm³` and `p = 400 kPa`.

Pressure, volume, and work remain dimensionful physical quantities.  Real
numbers occur only as explicitly named readouts in pascals, kilopascals, cubic
metres, cubic centimetres, or joules, and as displayed answer values.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose and bitmap readouts;
* `HasPhysicalPressureVolumeCoordinates` records positivity of the states;
* `SatisfiesConstantPressureBoundaryWorkLaw` states `W_by = p ΔV` for an
  isobaric process;
* `UsesWorkOnGasSignConvention` states `W_on = -W_by`; and
* `workDoneOnGas_eq_negative_eighty_joules` derives the requested result.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0403

open Dimension

/-! ## Dimensionful quantities and named unit readouts -/

/-- A nonnegative physical volume, carrying dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Thermodynamic pressure, represented by Physlib's dimensionful pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed mechanical work, represented by Physlib's dimensionful energy type. -/
abbrev WorkQuantity : Type := DimEnergy

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal axis of the figure. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Kilopascal readout used on the vertical axis of the figure. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Joule readout of a signed physical work quantity. -/
def workInJoules (work : WorkQuantity) : ℝ :=
  (work UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Thermodynamic states, process, and figure vocabulary -/

/-- The two state labels printed in the supplied diagram. -/
inductive StateLabel where
  | i
  | f
  deriving DecidableEq, Repr

/-- Pressure and volume at one equilibrium state of the gas. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity

/-- The physical classification of the depicted process. -/
inductive ProcessKind where
  | constantPressure
  deriving DecidableEq, Repr

/-- The direction of volume change shown by the arrow. -/
inductive VolumeChangeDirection where
  | expansion
  deriving DecidableEq, Repr

/-- The two Cartesian axes in the pressure-volume diagram. -/
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

/-- Literal quantity symbol printed beside a figure axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Geometric appearance of the directed path in the `p`-`V` plane. -/
inductive PathGeometry where
  | horizontalStraightSegment
  deriving DecidableEq, Repr

/-!
Structured transcription of image `403.png`.  Physical coordinates are stored
as dimensionful quantities; the match predicate below supplies their labelled
numeric readouts.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  stateLabelVisible : StateLabel → Bool
  plottedPressure : StateLabel → PressureQuantity
  plottedVolume : StateLabel → VolumeQuantity
  pathStart : StateLabel
  pathFinish : StateLabel
  pathGeometry : PathGeometry
  directionArrowShown : Bool

/-!
The gas process and its two signed work quantities.  Neither work field is
defined from the answer table or assigned a numerical value here.
-/
structure ConstantPressureExpansionSetup where
  state : StateLabel → ThermodynamicState
  processKind : ProcessKind
  volumeChangeDirection : VolumeChangeDirection
  workDoneByGas : WorkQuantity
  workDoneOnGas : WorkQuantity
  figure : PressureVolumeFigure

/-! ## Problem data and primary-figure readouts -/

/-!
Exact transcription of the prose and primary bitmap: `p` is vertical in kPa,
`V` is horizontal in cm³, and the arrow runs horizontally from `i` to `f`.
No work value occurs in these fields.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : ConstantPressureExpansionSetup) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalAxisUnitIsKilopascals :
    setup.figure.axisDisplayUnit .vertical = .kilopascals
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  initialLabelVisible : setup.figure.stateLabelVisible .i = true
  finalLabelVisible : setup.figure.stateLabelVisible .f = true
  plottedCoordinatesAreGasStates : ∀ label : StateLabel,
    setup.figure.plottedPressure label = (setup.state label).pressure ∧
      setup.figure.plottedVolume label = (setup.state label).volume
  initialPressureKilopascals :
    pressureInKilopascals (setup.figure.plottedPressure .i) = 400
  finalPressureKilopascals :
    pressureInKilopascals (setup.figure.plottedPressure .f) = 400
  initialVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .i) = 100
  finalVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .f) = 300
  pathStartsAtInitialState : setup.figure.pathStart = .i
  pathFinishesAtFinalState : setup.figure.pathFinish = .f
  pathIsHorizontalAndStraight :
    setup.figure.pathGeometry = .horizontalStraightSegment
  directionArrowIsShown : setup.figure.directionArrowShown = true
  processIsAtConstantPressure : setup.processKind = .constantPressure
  processIsAnExpansion : setup.volumeChangeDirection = .expansion

/-- Positivity conditions selecting physically meaningful state coordinates. -/
structure HasPhysicalPressureVolumeCoordinates
    (setup : ConstantPressureExpansionSetup) : Prop where
  pressurePositive : ∀ label : StateLabel,
    0 < pressureInPascals (setup.state label).pressure
  volumePositive : ∀ label : StateLabel,
    0 < volumeInCubicMeters (setup.state label).volume

/-! ## Governing physical laws -/

/-!
Boundary work for an isobaric process, with work positive when done by the
gas: `W_by = p_i (V_f - V_i)`.  This is a general governing relation over the
setup's physical state variables; it contains no numerical work result.
-/
structure SatisfiesConstantPressureBoundaryWorkLaw
    (setup : ConstantPressureExpansionSetup) : Prop where
  boundaryWorkByGas :
    setup.processKind = .constantPressure →
      workInJoules setup.workDoneByGas =
        pressureInPascals (setup.state .i).pressure *
          (volumeInCubicMeters (setup.state .f).volume -
            volumeInCubicMeters (setup.state .i).volume)

/-!
The requested convention is work done *on* the gas.  It is the negative of
boundary work done by the gas.  This law fixes the sign convention without
supplying either numerical work value.
-/
structure UsesWorkOnGasSignConvention
    (setup : ConstantPressureExpansionSetup) : Prop where
  workOnIsNegativeWorkBy :
    workInJoules setup.workDoneOnGas = -workInJoules setup.workDoneByGas

/-! ## Answer choices and requested conclusion -/

/-- The four labels printed beside the multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Work-on-gas readout in joules printed beside each answer label. -/
def displayedWorkOnGasInJoules : AnswerChoice → ℝ
  | .A => 0
  | .B => 80
  | .C => -80
  | .D => -40

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
The constant-pressure boundary-work law and the exact figure readouts first
give `80 J` of work done by the gas.  This intermediate value is a conclusion,
not a field of any assumption structure.
-/
lemma workDoneByGas_eq_eighty_joules
    (setup : ConstantPressureExpansionSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_workLaw : SatisfiesConstantPressureBoundaryWorkLaw setup) :
    workInJoules setup.workDoneByGas = 80 := by
  have hPressure :
      pressureInPascals (setup.state .i).pressure = 400000 := by
    have hPlotted :=
      _problem.initialPressureKilopascals
    rw [_problem.plottedCoordinatesAreGasStates .i |>.1] at hPlotted
    unfold pressureInKilopascals at hPlotted
    linarith
  have hInitialVolume :
      volumeInCubicMeters (setup.state .i).volume = 1 / 10000 := by
    have hPlotted :=
      _problem.initialVolumeCubicCentimeters
    rw [_problem.plottedCoordinatesAreGasStates .i |>.2] at hPlotted
    unfold volumeInCubicCentimeters at hPlotted
    norm_num at hPlotted ⊢
    linarith
  have hFinalVolume :
      volumeInCubicMeters (setup.state .f).volume = 3 / 10000 := by
    have hPlotted :=
      _problem.finalVolumeCubicCentimeters
    rw [_problem.plottedCoordinatesAreGasStates .f |>.2] at hPlotted
    unfold volumeInCubicCentimeters at hPlotted
    norm_num at hPlotted ⊢
    linarith
  rw [_workLaw.boundaryWorkByGas _problem.processIsAtConstantPressure,
    hPressure, hInitialVolume, hFinalVolume]
  norm_num

/-!
Therefore the work done on the expanding gas is `-80 J`, corresponding to
displayed answer C.

Blueprint label: `thm:physics:phyx_mini_0403:target`.
-/
theorem workDoneOnGas_eq_negative_eighty_joules
    (setup : ConstantPressureExpansionSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalPressureVolumeCoordinates setup)
    (_workLaw : SatisfiesConstantPressureBoundaryWorkLaw setup)
    (_signConvention : UsesWorkOnGasSignConvention setup) :
    workInJoules setup.workDoneOnGas = -80 := by
  rw [_signConvention.workOnIsNegativeWorkBy,
    workDoneByGas_eq_eighty_joules setup _problem _workLaw]

end PhyXMiniProblems.ProblemPhyXMini0403
