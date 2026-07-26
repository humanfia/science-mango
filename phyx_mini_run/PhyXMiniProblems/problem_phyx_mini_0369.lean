import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Temperature of an isothermal ideal-gas process

This file formalizes problem `phyx_mini_0369`.  The primary pressure-volume
diagram shows `80 mol` of gas moving from state `1` to state `2` along two
different solid paths.  The curved path is identified as an isotherm by its
dashed red continuation.  The plotted endpoint coordinates are

* state `1`: `V = 2 m³` and `p = 100 kPa`;
* state `2`: `V = 1 m³` and `p = 200 kPa`.

Pressure, volume, absolute temperature, and the molar gas constant retain
their physical dimensions through Physlib.  Real numbers below occur only as
named-unit readouts, the amount-of-substance readout in moles (a base
dimension not present in Physlib's current `Dimension`), schematic figure
data, or displayed answer values.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose and bitmap readouts;
* `UsesTextbookMolarGasConstant` supplies the standard textbook calibration;
* `HasPhysicalThermodynamicParameters` supplies positivity;
* `ObeysMolarIdealGasAndIsothermalLaws` states the governing laws; and
* `isothermTemperature_matches_recordedAnswerA` derives the requested
  numerical temperature and its displayed answer choice.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0369

open Dimension

/-! ## Dimensionful thermodynamic quantities and named SI readouts -/

/-- A nonnegative physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical pressure, represented by Physlib's dimensionful pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative absolute temperature carrying the temperature dimension. -/
abbrev TemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-!
The molar gas constant, carrying energy-per-temperature dimensions.

Physlib's current `Dimension` has no amount-of-substance coordinate.  The
missing inverse-mole role is therefore paired explicitly with the gas
sample's scalar readout `amountInMoles` below.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used by the vertical axis of the primary figure. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- SI kelvin readout of an absolute temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/-- SI joule-per-mole-kelvin readout of the molar gas constant. -/
def molarGasConstantInJoulesPerMoleKelvin
    (gasConstant : MolarGasConstantQuantity) : ℝ :=
  ((gasConstant UnitChoices.SI).val : ℝ)

/-! ## Gas, state, process, and primary-figure vocabulary -/

/-- Equation-of-state model required to use the ideal-gas law. -/
inductive GasModel where
  | ideal
  deriving DecidableEq, Repr

/-!
The physical gas sample.  `amountInMoles` is an explicitly unit-labelled
readout, not a scalar replacement for the gas itself.
-/
structure GasSample where
  model : GasModel
  amountInMoles : ℝ

/-- The two equilibrium-state labels printed in the diagram. -/
inductive StateLabel where
  | state1
  | state2
  deriving DecidableEq, Repr

/-- The two solid routes drawn from state `1` to state `2`. -/
inductive ProcessPath where
  | straight
  | curved
  deriving DecidableEq, Repr

/-- Thermodynamic classification of a depicted process. -/
inductive ProcessKind where
  | unspecified
  | isothermal
  deriving DecidableEq, Repr

/-- Geometric appearance of a path in the `p`-`V` plane. -/
inductive PathGeometry where
  | straightSegment
  | curvedSegment
  deriving DecidableEq, Repr

/-- Visible line style used for a feature of the diagram. -/
inductive FigureLineStyle where
  | solidBlack
  | dashedRed
  deriving DecidableEq, Repr

/-- The two Cartesian axes in the primary bitmap. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical role assigned to each axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside an axis. -/
inductive AxisDisplayUnit where
  | cubicMeters
  | kilopascals
  deriving DecidableEq, Repr

/-- Quantity symbol printed beside an axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Text attached to the dashed red guide in the bitmap. -/
inductive FigureAnnotationLabel where
  | isotherm
  deriving DecidableEq, Repr

/-- Pressure, volume, and absolute temperature at one equilibrium state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : TemperatureQuantity

/-!
Structured transcription of image `369.png`.

The dashed red feature is treated as an annotation continuing the curved
solid path, rather than as a third gas process.  This matches the image: two
solid arrowed routes connect the same labelled endpoints, while the red
dashes and “Isotherm” text identify the curved route.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  stateLabelVisible : StateLabel → Bool
  plottedPressure : StateLabel → PressureQuantity
  plottedVolume : StateLabel → VolumeQuantity
  pathStart : ProcessPath → StateLabel
  pathFinish : ProcessPath → StateLabel
  pathGeometry : ProcessPath → PathGeometry
  pathLineStyle : ProcessPath → FigureLineStyle
  directionArrowShown : ProcessPath → Bool
  annotatedPath : ProcessPath
  annotationLineStyle : FigureLineStyle
  annotationLabel : FigureAnnotationLabel

/-!
The gas, its two states, and the two physical processes shown in the figure.

The isotherm temperature is an independent physical observable.  It is not
defined from either endpoint or from an answer choice; the governing
isothermal law below relates it to the endpoint temperatures.
-/
structure IdealGasTwoPathSetup where
  gas : GasSample
  state : StateLabel → ThermodynamicState
  processKind : ProcessPath → ProcessKind
  isothermTemperature : TemperatureQuantity
  molarGasConstant : MolarGasConstantQuantity
  figure : PressureVolumeFigure

/-! ## Problem statement and primary-figure readouts -/

/-!
Data stated in the prose or read directly from the primary bitmap.  Both
solid paths run from state `1` to state `2`; only the curved one is identified
by the dashed red isotherm annotation.  No numerical temperature occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : IdealGasTwoPathSetup) : Prop where
  gasUsesIdealModel : setup.gas.model = .ideal
  gasAmountIsEightyMoles : setup.gas.amountInMoles = 80
  horizontalAxisIsVolume : setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure : setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUnitIsCubicMeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicMeters
  verticalAxisUnitIsKilopascals :
    setup.figure.axisDisplayUnit .vertical = .kilopascals
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  bothStateLabelsVisible :
    setup.figure.stateLabelVisible .state1 = true ∧
      setup.figure.stateLabelVisible .state2 = true
  figureCoordinatesAreGasStates : ∀ state : StateLabel,
    setup.figure.plottedPressure state = (setup.state state).pressure ∧
      setup.figure.plottedVolume state = (setup.state state).volume
  state1PressureKilopascals :
    pressureInKilopascals (setup.figure.plottedPressure .state1) = 100
  state1VolumeCubicMeters :
    volumeInCubicMeters (setup.figure.plottedVolume .state1) = 2
  state2PressureKilopascals :
    pressureInKilopascals (setup.figure.plottedPressure .state2) = 200
  state2VolumeCubicMeters :
    volumeInCubicMeters (setup.figure.plottedVolume .state2) = 1
  bothPathsStartAtState1 :
    ∀ path : ProcessPath, setup.figure.pathStart path = .state1
  bothPathsFinishAtState2 :
    ∀ path : ProcessPath, setup.figure.pathFinish path = .state2
  straightPathGeometry :
    setup.figure.pathGeometry .straight = .straightSegment
  curvedPathGeometry : setup.figure.pathGeometry .curved = .curvedSegment
  bothProcessesAreSolidBlack :
    ∀ path : ProcessPath, setup.figure.pathLineStyle path = .solidBlack
  bothDirectionArrowsAreShown :
    ∀ path : ProcessPath, setup.figure.directionArrowShown path = true
  dashedGuideAnnotatesCurvedPath : setup.figure.annotatedPath = .curved
  annotationIsDashedRed :
    setup.figure.annotationLineStyle = .dashedRed
  annotationReadsIsotherm :
    setup.figure.annotationLabel = .isotherm
  curvedProcessIsIsothermal : setup.processKind .curved = .isothermal

/-!
The textbook value `8.31 J mol⁻¹ K⁻¹` for the molar gas constant.  This is a
calibration of a governing physical constant, not the requested temperature.
-/
structure UsesTextbookMolarGasConstant
    (setup : IdealGasTwoPathSetup) : Prop where
  gasConstantValue :
    molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant = 831 / 100

/-- Positivity conditions selecting physically meaningful thermodynamic states. -/
structure HasPhysicalThermodynamicParameters
    (setup : IdealGasTwoPathSetup) : Prop where
  amountPositive : 0 < setup.gas.amountInMoles
  gasConstantPositive :
    0 < molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant
  pressurePositive : ∀ state : StateLabel,
    0 < pressureInPascals (setup.state state).pressure
  volumePositive : ∀ state : StateLabel,
    0 < volumeInCubicMeters (setup.state state).volume
  stateTemperaturePositive : ∀ state : StateLabel,
    0 < temperatureInKelvins (setup.state state).temperature
  isothermTemperaturePositive :
    0 < temperatureInKelvins setup.isothermTemperature

/-! ## Governing thermodynamic laws -/

/-!
The molar ideal-gas equation `pV = nRT` at each labelled equilibrium state,
together with the defining physical behavior of an isothermal path: each of
its endpoint states has the common process temperature.

These are general governing relations.  They contain no numerical value for
the isotherm temperature and no answer-choice conclusion.
-/
structure ObeysMolarIdealGasAndIsothermalLaws
    (setup : IdealGasTwoPathSetup) : Prop where
  idealGasLawAt : ∀ state : StateLabel,
    pressureInPascals (setup.state state).pressure *
        volumeInCubicMeters (setup.state state).volume =
      setup.gas.amountInMoles *
        molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
          temperatureInKelvins (setup.state state).temperature
  endpointTemperatureOnIsothermalPath :
    ∀ (path : ProcessPath) (state : StateLabel),
      setup.processKind path = .isothermal →
      (state = setup.figure.pathStart path ∨
        state = setup.figure.pathFinish path) →
      (setup.state state).temperature = setup.isothermTemperature

/-! ## Exact value, whole-kelvin display, and answer choices -/

/-- A real-valued kelvin reading rounds to a specified whole kelvin. -/
def RoundsToNearestWholeKelvin
    (temperature wholeKelvins : ℝ) : Prop :=
  wholeKelvins - 1 / 2 ≤ temperature ∧
    temperature < wholeKelvins + 1 / 2

/-- Labels of the four answer choices in the supplied problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Whole-kelvin value printed beside each answer label. -/
def AnswerChoice.kelvins : AnswerChoice → ℝ
  | .A => 301
  | .B => 556
  | .C => 636
  | .D => 784

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
Using state `1`, the ideal-gas law gives

`T = (100000 Pa)(2 m³) / ((80 mol)(8.31 J mol⁻¹ K⁻¹))
   = 250000 / 831 K`.

The same product is visible at state `2`.  This intermediate exact result does
not use the whole-kelvin answer table.
-/
lemma isothermTemperature_exact_kelvins
    (setup : IdealGasTwoPathSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_constant : UsesTextbookMolarGasConstant setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : ObeysMolarIdealGasAndIsothermalLaws setup) :
    temperatureInKelvins setup.isothermTemperature =
      (250000 : ℝ) / 831 := by
  have hstate1PressureKilopascals :
      pressureInKilopascals (setup.state .state1).pressure = 100 := by
    rw [← (_problem.figureCoordinatesAreGasStates .state1).1]
    exact _problem.state1PressureKilopascals
  have hstate1PressurePascals :
      pressureInPascals (setup.state .state1).pressure = 100000 := by
    unfold pressureInKilopascals at hstate1PressureKilopascals
    linarith
  have hstate1Volume :
      volumeInCubicMeters (setup.state .state1).volume = 2 := by
    rw [← (_problem.figureCoordinatesAreGasStates .state1).2]
    exact _problem.state1VolumeCubicMeters
  have hstate1Temperature :
      (setup.state .state1).temperature = setup.isothermTemperature := by
    apply _laws.endpointTemperatureOnIsothermalPath .curved .state1
    · exact _problem.curvedProcessIsIsothermal
    · left
      exact (_problem.bothPathsStartAtState1 .curved).symm
  have hidealGas := _laws.idealGasLawAt .state1
  rw [hstate1PressurePascals, hstate1Volume,
    _problem.gasAmountIsEightyMoles, _constant.gasConstantValue,
    hstate1Temperature] at hidealGas
  norm_num at hidealGas ⊢
  linarith

/-!
The exact temperature `250000 / 831 K` lies in `[300.5 K, 301.5 K)`, so it
rounds to `301 K`, the value displayed as recorded answer A.

This formalizes blueprint label `thm:physics:phyx_mini_0369:target`.
-/
theorem isothermTemperature_matches_recordedAnswerA
    (setup : IdealGasTwoPathSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_constant : UsesTextbookMolarGasConstant setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : ObeysMolarIdealGasAndIsothermalLaws setup) :
    temperatureInKelvins setup.isothermTemperature =
        (250000 : ℝ) / 831 ∧
      RoundsToNearestWholeKelvin
        (temperatureInKelvins setup.isothermTemperature)
        (AnswerChoice.kelvins recordedAnswerChoice) := by
  have hexact :=
    isothermTemperature_exact_kelvins
      setup _problem _constant _physical _laws
  refine ⟨hexact, ?_⟩
  rw [hexact]
  norm_num [RoundsToNearestWholeKelvin, AnswerChoice.kelvins,
    recordedAnswerChoice]

end PhyXMiniProblems.ProblemPhyXMini0369
