import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0476

open Dimension

/-!
# Final pressure after isothermal expansion and isobaric compression

An ideal gas initially at `2 atm` and `200 °C` expands isothermally from
state `1` to state `2`, doubling its volume.  It is then compressed
isobarically to state `3`, where its volume again equals the initial volume.

Pressure, volume, absolute temperature, and amount of substance retain their
physical roles.  Real numbers below are explicitly unit readouts, relative
coordinates from the supplied pressure--volume diagram, physical-constant
calibrations, or displayed answer values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical volume with length-cubed dimension. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
Physlib does not currently expose amount of substance as a base dimension.
This interface therefore keeps the gas amount abstract while exposing its
calibrated scalar readout in moles.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- Convert a stored absolute temperature to a kelvin readout. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Convert a stored absolute temperature to a degrees-Celsius readout. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - (5463 / 20 : ℝ)

/-! ## Gas states, process labels, and diagram vocabulary -/

/-- The equation-of-state model used for the gas. -/
inductive GasModel where
  | ideal
  | unspecified
  deriving DecidableEq, Repr

/-- Labels printed beside the three black points in the supplied diagram. -/
inductive StateLabel where
  | state1
  | state2
  | state3
  deriving DecidableEq, Fintype, Repr

/-- Directed legs of the two-step process. -/
inductive ProcessLeg where
  | oneToTwo
  | twoToThree
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic constraint imposed on a process leg. -/
inductive ProcessKind where
  | isothermal
  | isobaric
  deriving DecidableEq, Repr

/-- Physical quantity represented by an axis of the diagram. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit or scale printed on an axis of the diagram. -/
inductive AxisUnit where
  | initialVolume
  | standardAtmosphere
  deriving DecidableEq, Repr

/-- Geometric appearance of a process path in the primary raster. -/
inductive PathGeometry where
  | decreasingCurve
  | horizontalSegment
  deriving DecidableEq, Repr

/-- Names of the two red dashed isotherms in the supplied diagram. -/
inductive IsothermLabel where
  | T1
  | T3
  deriving DecidableEq, Fintype, Repr

/-- A thermodynamic equilibrium state with dimensionful observables. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : GasVolume
  temperature : Temperature

/-!
Scalar coordinate fields are literal readouts from the supplied raster.  A
volume coordinate is measured in units of `V₁`; a pressure coordinate is
measured in standard atmospheres.
-/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisQuantity : AxisQuantity
  verticalAxisUnit : AxisUnit
  showsPressureTick : ℝ → Bool
  pointVolumeInInitialVolumeUnits : StateLabel → ℝ
  pointPressureInAtmospheres : StateLabel → ℝ
  showsStateLabel : StateLabel → Bool
  showsProcessPath : ProcessLeg → Bool
  processPathGeometry : ProcessLeg → PathGeometry
  showsDirectedArrow : ProcessLeg → Bool
  arrowStart : ProcessLeg → StateLabel
  arrowFinish : ProcessLeg → StateLabel
  showsIsotherm : IsothermLabel → Bool
  isothermPassesThrough : IsothermLabel → StateLabel

/-- The gas sample, its three states, the named processes, and the diagram. -/
structure TwoStepIdealGasProcess (amountScale : AmountOfSubstanceScale) where
  gasModel : GasModel
  gasAmount : amountScale.Quantity
  molarGasConstantJoulesPerMoleKelvin : ℝ
  temperatureStorageUnit : TemperatureUnit
  stateAt : StateLabel → ThermodynamicState
  processKind : ProcessLeg → ProcessKind
  pathStart : ProcessLeg → StateLabel
  pathFinish : ProcessLeg → StateLabel
  diagram : PressureVolumeDiagram

/-- Mole readout of the physical gas amount. -/
def gasAmountInMoles
    {amountScale : AmountOfSubstanceScale}
    (setup : TwoStepIdealGasProcess amountScale) : ℝ :=
  amountScale.inMoles setup.gasAmount

/-! ## Prose data, primary-image evidence, and governing laws -/

/-!
The data stated in the problem prose.  The initial pressure and temperature,
the two volume relations, and the identities of the process legs are fixed;
the final pressure is deliberately absent.
-/
structure MatchesProblemStatement
    {amountScale : AmountOfSubstanceScale}
    (setup : TwoStepIdealGasProcess amountScale) : Prop where
  idealGasModelSelected : setup.gasModel = .ideal
  initialPressureAtmospheres :
    pressureInAtmospheres (setup.stateAt .state1).pressure = 2
  initialTemperatureDegreesCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.stateAt .state1).temperature = 200
  expansionDoublesVolume :
    volumeInCubicMeters (setup.stateAt .state2).volume =
      2 * volumeInCubicMeters (setup.stateAt .state1).volume
  compressionReturnsToInitialVolume :
    volumeInCubicMeters (setup.stateAt .state3).volume =
      volumeInCubicMeters (setup.stateAt .state1).volume
  firstLegStartsAtState1 : setup.pathStart .oneToTwo = .state1
  firstLegFinishesAtState2 : setup.pathFinish .oneToTwo = .state2
  secondLegStartsAtState2 : setup.pathStart .twoToThree = .state2
  secondLegFinishesAtState3 : setup.pathFinish .twoToThree = .state3
  firstLegIsIsothermal : setup.processKind .oneToTwo = .isothermal
  secondLegIsIsobaric : setup.processKind .twoToThree = .isobaric

/-!
Exact qualitative and quantitative information transcribed from the primary
pressure--volume diagram.  In particular, state `2` is plotted at `1 atm`,
while no numeric pressure is assigned here to the final state `3`.
-/
structure MatchesPrimaryPressureVolumeDiagram
    {amountScale : AmountOfSubstanceScale}
    (setup : TwoStepIdealGasProcess amountScale) : Prop where
  horizontalAxisIsVolume :
    setup.diagram.horizontalAxisQuantity = .volume
  horizontalAxisUsesInitialVolume :
    setup.diagram.horizontalAxisUnit = .initialVolume
  verticalAxisIsPressure :
    setup.diagram.verticalAxisQuantity = .pressure
  verticalAxisUsesAtmospheres :
    setup.diagram.verticalAxisUnit = .standardAtmosphere
  pressureTicksShown :
    setup.diagram.showsPressureTick 0 = true ∧
      setup.diagram.showsPressureTick 1 = true ∧
      setup.diagram.showsPressureTick 2 = true
  state1Coordinate :
    setup.diagram.pointVolumeInInitialVolumeUnits .state1 = 1 ∧
      setup.diagram.pointPressureInAtmospheres .state1 = 2
  state2Coordinate :
    setup.diagram.pointVolumeInInitialVolumeUnits .state2 = 2 ∧
      setup.diagram.pointPressureInAtmospheres .state2 = 1
  state3VolumeCoordinate :
    setup.diagram.pointVolumeInInitialVolumeUnits .state3 = 1
  volumeCoordinatesRepresentPhysicalStates :
    ∀ state,
      volumeInCubicMeters (setup.stateAt state).volume =
        setup.diagram.pointVolumeInInitialVolumeUnits state *
          volumeInCubicMeters (setup.stateAt .state1).volume
  pressureCoordinatesRepresentPhysicalStates :
    ∀ state,
      pressureInAtmospheres (setup.stateAt state).pressure =
        setup.diagram.pointPressureInAtmospheres state
  everyStateLabelShown :
    ∀ state, setup.diagram.showsStateLabel state = true
  bothProcessPathsShown :
    ∀ leg, setup.diagram.showsProcessPath leg = true
  isothermalPathIsDecreasingCurve :
    setup.diagram.processPathGeometry .oneToTwo = .decreasingCurve
  isobaricPathIsHorizontal :
    setup.diagram.processPathGeometry .twoToThree = .horizontalSegment
  bothDirectedArrowsShown :
    ∀ leg, setup.diagram.showsDirectedArrow leg = true
  arrowDirectionsMatchProcesses :
    ∀ leg,
      setup.diagram.arrowStart leg = setup.pathStart leg ∧
        setup.diagram.arrowFinish leg = setup.pathFinish leg
  bothIsothermsShown :
    ∀ label, setup.diagram.showsIsotherm label = true
  T1PassesThroughState1 :
    setup.diagram.isothermPassesThrough .T1 = .state1
  T3PassesThroughState3 :
    setup.diagram.isothermPassesThrough .T3 = .state3
  T1IsHotterThanT3 :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.stateAt .state3).temperature <
      temperatureInKelvins setup.temperatureStorageUnit
        (setup.stateAt .state1).temperature

/-! Positivity assumptions selecting physically admissible gas states. -/
structure HasPhysicalThermodynamicParameters
    {amountScale : AmountOfSubstanceScale}
    (setup : TwoStepIdealGasProcess amountScale) : Prop where
  amountPositive : 0 < gasAmountInMoles setup
  molarGasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.stateAt state).pressure
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.stateAt state).volume
  absoluteTemperaturePositive :
    ∀ state,
      0 < temperatureInKelvins setup.temperatureStorageUnit
        (setup.stateAt state).temperature

/-!
Macroscopic laws used by the calculation:

* the SI ideal-gas equation `pV = nRT` at every labeled equilibrium state;
* equal endpoint temperatures for every isothermal leg;
* equal endpoint pressures for every isobaric leg.

These are general governing laws.  No field fixes the pressure of state `3`
or identifies an answer choice.
-/
structure ObeysIdealGasAndProcessLaws
    {amountScale : AmountOfSubstanceScale}
    (setup : TwoStepIdealGasProcess amountScale) : Prop where
  idealGasEquation :
    ∀ state,
      pressureInPascals (setup.stateAt state).pressure *
          volumeInCubicMeters (setup.stateAt state).volume =
        gasAmountInMoles setup *
          setup.molarGasConstantJoulesPerMoleKelvin *
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.stateAt state).temperature
  isothermalTemperatureLaw :
    ∀ leg, setup.processKind leg = .isothermal →
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.stateAt (setup.pathFinish leg)).temperature =
        temperatureInKelvins setup.temperatureStorageUnit
          (setup.stateAt (setup.pathStart leg)).temperature
  isobaricPressureLaw :
    ∀ leg, setup.processKind leg = .isobaric →
      pressureInPascals
          (setup.stateAt (setup.pathFinish leg)).pressure =
        pressureInPascals
          (setup.stateAt (setup.pathStart leg)).pressure

/-! ## Final pressure and displayed answer choices -/

/-- Pressure of the final state, read in standard atmospheres. -/
def finalPressureInAtmospheres
    {amountScale : AmountOfSubstanceScale}
    (setup : TwoStepIdealGasProcess amountScale) : ℝ :=
  pressureInAtmospheres (setup.stateAt .state3).pressure

/-- Labels of the four choices in the supplied problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Pressure in atmospheres printed beside each answer label. -/
def displayedPressureInAtmospheres : AnswerChoice → ℝ
  | .A => 3
  | .B => 2
  | .C => 1
  | .D => 4

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A choice is the unique displayed pressure equal to the physical result. -/
def IsUniqueMatchingPressureChoice
    (actualPressureInAtmospheres : ℝ) (choice : AnswerChoice) : Prop :=
  actualPressureInAtmospheres = displayedPressureInAtmospheres choice ∧
    ∀ other,
      actualPressureInAtmospheres = displayedPressureInAtmospheres other →
        other = choice

/-!
The requested final pressure is `1 atm`, and it uniquely matches choice `C`.
The conclusion is derived from the initial data and the two process laws; it
does not occur in any premise structure or readout definition.

Blueprint label: `thm:physics:phyx_mini_0476:target`.
-/
theorem finalPressure_is_one_atmosphere
    {amountScale : AmountOfSubstanceScale}
    (setup : TwoStepIdealGasProcess amountScale)
    (_hProblem : MatchesProblemStatement setup)
    (_hFigure : MatchesPrimaryPressureVolumeDiagram setup)
    (_hPhysical : HasPhysicalThermodynamicParameters setup)
    (_hLaws : ObeysIdealGasAndProcessLaws setup) :
    finalPressureInAtmospheres setup = 1 ∧
      IsUniqueMatchingPressureChoice
        (finalPressureInAtmospheres setup) .C := by
  have hPressurePascal :
      pressureInPascals (setup.stateAt .state3).pressure =
        pressureInPascals (setup.stateAt .state2).pressure := by
    have h := _hLaws.isobaricPressureLaw .twoToThree
      _hProblem.secondLegIsIsobaric
    rw [_hProblem.secondLegFinishesAtState3,
      _hProblem.secondLegStartsAtState2] at h
    exact h
  have hPressureAtmosphere :
      pressureInAtmospheres (setup.stateAt .state3).pressure =
        pressureInAtmospheres (setup.stateAt .state2).pressure := by
    unfold pressureInAtmospheres
    rw [hPressurePascal]
  have hStateTwoPressure :
      pressureInAtmospheres (setup.stateAt .state2).pressure = 1 := by
    rw [_hFigure.pressureCoordinatesRepresentPhysicalStates .state2]
    exact _hFigure.state2Coordinate.2
  have hFinalPressure : finalPressureInAtmospheres setup = 1 := by
    unfold finalPressureInAtmospheres
    exact hPressureAtmosphere.trans hStateTwoPressure
  constructor
  · exact hFinalPressure
  · unfold IsUniqueMatchingPressureChoice
    constructor
    · simpa [displayedPressureInAtmospheres] using hFinalPressure
    · intro other hOther
      rw [hFinalPressure] at hOther
      cases other with
      | A => norm_num [displayedPressureInAtmospheres] at hOther
      | B => norm_num [displayedPressureInAtmospheres] at hOther
      | C => rfl
      | D => norm_num [displayedPressureInAtmospheres] at hOther

end PhyXMiniProblems.ProblemPhyXMini0476
