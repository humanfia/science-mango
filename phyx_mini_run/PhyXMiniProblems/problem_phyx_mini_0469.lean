import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0469

open Dimension

/-!
# Temperature after compression in an automobile engine

A fixed amount of an air--gasoline-vapor mixture is compressed to one ninth
of its initial volume while the intake and exhaust valves are closed.  The
initial state is at `1.00 atm` and `27 °C`; the final pressure is `21.7 atm`.
The gas is modeled as ideal, so the endpoint states obey `pV = nRT`.

Pressure, volume, and absolute temperature retain physical types.  Real
numbers occur only as named unit readouts, the mole and gas-constant readouts
needed because Physlib has no amount-of-substance base dimension, and the
displayed answer values.  The final temperature is an independent state
observable and is not defined from the recorded answer.
-/

/-! ## Physical quantities and calibrated unit readouts -/

/-- A nonnegative physical volume carrying the dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-!
Read a physical pressure in standard atmospheres by comparison with
Physlib's dimensionful `DimPressure.standardAtmosphere`.
-/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-!
Read an absolute temperature in kelvins.  Physlib's `Temperature` stores a
nonnegative magnitude in an arbitrary zero-preserving unit, so the storage
unit remains explicit in the setup.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-!
The affine Celsius readout attached to an absolute temperature.  The offset
is `273.15 K = 5463/20 K`; Celsius is not treated as an absolute scale.
-/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - 5463 / 20

/-! ## Engine states, process data, and primary-figure vocabulary -/

/-- The two equilibrium states before and after compression. -/
inductive CompressionState where
  | initial
  | final
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic model selected for the cylinder contents. -/
inductive GasModel where
  | idealGas
  | other
  deriving DecidableEq, Repr

/-- Composition of the gas in the cylinder. -/
inductive CylinderContents where
  | airAndVaporizedGasoline
  | other
  deriving DecidableEq, Repr

/-- Position of an intake or exhaust valve during the compression stroke. -/
inductive ValvePosition where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Literal component labels printed in the supplied engine raster. -/
inductive EngineFigureLabel where
  | intakeValve
  | exhaustValve
  | fuelInjector
  | combustionChamber
  | fuelPump
  deriving DecidableEq, Fintype, Repr

/-- Physical engine components visibly depicted in the cross section. -/
inductive EngineFigureObject where
  | intakeValve
  | exhaustValve
  | fuelInjector
  | combustionChamber
  | fuelPump
  | piston
  | cylinder
  | timingGear
  | engineBlock
  | fuelLine
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative information retained from the primary raster.  The geometric
fields describe component placement and connectivity; they contain no
pressure, volume, or temperature readout.
-/
structure EngineCrossSectionFigure where
  showsLabel : EngineFigureLabel → Bool
  showsObject : EngineFigureObject → Bool
  labelPointsTo : EngineFigureLabel → EngineFigureObject
  isCrossSection : Bool
  pistonsAreInsideCylinders : Bool
  valvesAreAboveCombustionChambers : Bool
  fuelLineConnectsPumpToInjectors : Bool
  containsNumericalThermodynamicReadout : Bool

/-- Pressure, volume, and absolute temperature of one endpoint gas state. -/
structure CylinderGasState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
The physical setup.  `GasAmount` remains abstract and has a separate mole
readout, so amount of substance is not identified with a bare scalar type.
The state-dependent amount makes conservation during the closed-valve stroke
an explicit law rather than a fact hidden by construction.
-/
structure AutomobileEngineCompressionSetup (GasAmount : Type) where
  gasModel : GasModel
  cylinderContents : CylinderContents
  stateAt : CompressionState → CylinderGasState
  amountAt : CompressionState → GasAmount
  amountInMoles : GasAmount → ℝ
  molarGasConstantInAtmosphereCubicMetersPerMoleKelvin : ℝ
  temperatureStorageUnit : TemperatureUnit
  intakeValvePositionDuringCompression : ValvePosition
  exhaustValvePositionDuringCompression : ValvePosition
  figure : EngineCrossSectionFigure

/-- Pressure in atmospheres at a named endpoint. -/
def statePressureInAtmospheres
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (state : CompressionState) : ℝ :=
  pressureInAtmospheres (setup.stateAt state).pressure

/-- Volume in cubic metres at a named endpoint. -/
def stateVolumeInCubicMeters
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (state : CompressionState) : ℝ :=
  volumeInCubicMeters (setup.stateAt state).volume

/-- Absolute temperature in kelvins at a named endpoint. -/
def stateTemperatureInKelvin
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (state : CompressionState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.stateAt state).temperature

/-- Celsius temperature at a named endpoint. -/
def stateTemperatureInDegreesCelsius
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (state : CompressionState) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    (setup.stateAt state).temperature

/-! ## Assumptions: scenario, data readouts, figure evidence, and laws -/

/-!
Qualitative physical information from the prose.  Closed valves are recorded
here, while their consequence for gas amount is stated separately as a
process law.
-/
structure MatchesAutomobileEngineCompressionScenario
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount) : Prop where
  contentsAreAirAndVaporizedGasoline :
    setup.cylinderContents = .airAndVaporizedGasoline
  gasIsModeledAsIdeal : setup.gasModel = .idealGas
  intakeValveIsClosed :
    setup.intakeValvePositionDuringCompression = .closed
  exhaustValveIsClosed :
    setup.exhaustValvePositionDuringCompression = .closed

/-!
The four numerical readouts printed in the problem.  The final temperature
and all answer choices are absent.  `9.00 : 1` is expressed as
`V_final = V_initial / 9`.
-/
structure MatchesProblemReadouts
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount) : Prop where
  compressionRatioNineToOne :
    stateVolumeInCubicMeters setup .final =
      stateVolumeInCubicMeters setup .initial / 9
  initialPressureAtmospheres :
    statePressureInAtmospheres setup .initial = 1
  finalPressureAtmospheres :
    statePressureInAtmospheres setup .final = 217 / 10
  initialTemperatureDegreesCelsius :
    stateTemperatureInDegreesCelsius setup .initial = 27

/-! Facts read directly from the supplied cross-sectional engine raster. -/
structure MatchesSuppliedEngineFigure
    (figure : EngineCrossSectionFigure) : Prop where
  everyPrintedLabelIsShown : ∀ label, figure.showsLabel label = true
  everyNamedObjectIsShown : ∀ object, figure.showsObject object = true
  intakeValveLabelMapping :
    figure.labelPointsTo .intakeValve = .intakeValve
  exhaustValveLabelMapping :
    figure.labelPointsTo .exhaustValve = .exhaustValve
  fuelInjectorLabelMapping :
    figure.labelPointsTo .fuelInjector = .fuelInjector
  combustionChamberLabelMapping :
    figure.labelPointsTo .combustionChamber = .combustionChamber
  fuelPumpLabelMapping :
    figure.labelPointsTo .fuelPump = .fuelPump
  drawingIsCrossSection : figure.isCrossSection = true
  pistonsInsideCylinders : figure.pistonsAreInsideCylinders = true
  valvesAboveChambers : figure.valvesAreAboveCombustionChambers = true
  fuelSupplyConnection : figure.fuelLineConnectsPumpToInjectors = true
  noNumericalThermodynamicReadout :
    figure.containsNumericalThermodynamicReadout = false

/-- Positivity and nondegeneracy conditions for both gas states. -/
structure HasPhysicalCompressionParameters
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount) : Prop where
  pressurePositive :
    ∀ state, 0 < statePressureInAtmospheres setup state
  volumePositive :
    ∀ state, 0 < stateVolumeInCubicMeters setup state
  absoluteTemperaturePositive :
    ∀ state, 0 < stateTemperatureInKelvin setup state
  amountPositive :
    ∀ state, 0 < setup.amountInMoles (setup.amountAt state)
  molarGasConstantPositive :
    0 < setup.molarGasConstantInAtmosphereCubicMetersPerMoleKelvin

/-!
Closed intake and exhaust valves make the amount of gas at the two endpoint
states equal.  This is a process law, not a final-temperature relation.
-/
structure SatisfiesClosedCylinderAmountConservation
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount) : Prop where
  amountConserved : setup.amountAt .final = setup.amountAt .initial

/-!
The ideal-gas equation `pV = nRT`, applied uniformly at both endpoints in
coherent atmosphere, cubic-metre, mole, and kelvin readouts.  It does not
assign the unknown final temperature or select an answer choice.

Physlib's `IdealGas.ideal_gas_law` is specialized to its unitless statistical
mechanics model with `R = 1`; this local law preserves the dimensional engine
state and explicit unit readouts needed here.
-/
structure SatisfiesEndpointIdealGasLaw
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount) : Prop where
  idealGasLaw : ∀ state,
    statePressureInAtmospheres setup state *
        stateVolumeInCubicMeters setup state =
      setup.amountInMoles (setup.amountAt state) *
        setup.molarGasConstantInAtmosphereCubicMetersPerMoleKelvin *
          stateTemperatureInKelvin setup state

/-! ## Displayed answers and current conclusions -/

/-- Labels of the four choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Celsius value displayed beside each answer label. -/
def displayedTemperatureInDegreesCelsius : AnswerChoice → ℝ
  | .A => 420
  | .B => 450
  | .C => 530
  | .D => 500

/-- Dataset metadata recording the supplied answer label. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A computed temperature matches a choice printed to the nearest ten degrees
when it lies within five degrees of that displayed value.
-/
def RoundsToDisplayedTenDegrees
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (choice : AnswerChoice) : Prop :=
  |stateTemperatureInDegreesCelsius setup .final -
      displayedTemperatureInDegreesCelsius choice| < 5

/-- The selected displayed temperature is strictly closer than every rival. -/
def IsUniqueClosestDisplayedTemperature
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |stateTemperatureInDegreesCelsius setup .final -
        displayedTemperatureInDegreesCelsius choice| <
      |stateTemperatureInDegreesCelsius setup .final -
        displayedTemperatureInDegreesCelsius other|

/-!
The endpoint ideal-gas equations, conservation of gas amount, and supplied
ratios give the exact model value
`T_final = 144739/200 K = 90109/200 °C = 450.545 °C`.
-/
lemma final_temperature_exact
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalCompressionParameters setup)
    (hClosed : SatisfiesClosedCylinderAmountConservation setup)
    (hIdealGas : SatisfiesEndpointIdealGasLaw setup) :
    stateTemperatureInKelvin setup .final = (144739 / 200 : ℝ) ∧
      stateTemperatureInDegreesCelsius setup .final =
        (90109 / 200 : ℝ) := by
  have hInitialCelsius := hReadouts.initialTemperatureDegreesCelsius
  change stateTemperatureInKelvin setup .initial - 5463 / 20 = 27 at hInitialCelsius
  have hInitialKelvin :
      stateTemperatureInKelvin setup .initial = (6003 / 20 : ℝ) := by
    linarith
  have hAmountReadout :
      setup.amountInMoles (setup.amountAt .final) =
        setup.amountInMoles (setup.amountAt .initial) :=
    congrArg setup.amountInMoles hClosed.amountConserved
  let commonFactor : ℝ :=
    setup.amountInMoles (setup.amountAt .initial) *
      setup.molarGasConstantInAtmosphereCubicMetersPerMoleKelvin
  have hCommonFactorPositive : 0 < commonFactor := by
    exact mul_pos (hPhysical.amountPositive .initial)
      hPhysical.molarGasConstantPositive
  have hInitialLaw := hIdealGas.idealGasLaw .initial
  rw [hReadouts.initialPressureAtmospheres, hInitialKelvin] at hInitialLaw
  have hInitialLaw' :
      stateVolumeInCubicMeters setup .initial =
        commonFactor * (6003 / 20 : ℝ) := by
    simpa [commonFactor] using hInitialLaw
  have hFinalLaw := hIdealGas.idealGasLaw .final
  rw [hReadouts.finalPressureAtmospheres,
    hReadouts.compressionRatioNineToOne, hAmountReadout] at hFinalLaw
  have hFinalLaw' :
      (217 / 10 : ℝ) *
          (stateVolumeInCubicMeters setup .initial / 9) =
        commonFactor * stateTemperatureInKelvin setup .final := by
    simpa [commonFactor] using hFinalLaw
  have hCancel :
      commonFactor * (144739 / 200 : ℝ) =
        commonFactor * stateTemperatureInKelvin setup .final := by
    calc
      commonFactor * (144739 / 200 : ℝ) =
          (217 / 10 : ℝ) *
            (commonFactor * (6003 / 20 : ℝ) / 9) := by ring
      _ = (217 / 10 : ℝ) *
            (stateVolumeInCubicMeters setup .initial / 9) := by
              rw [hInitialLaw']
      _ = commonFactor * stateTemperatureInKelvin setup .final := hFinalLaw'
  have hFinalKelvin :
      stateTemperatureInKelvin setup .final = (144739 / 200 : ℝ) :=
    (mul_left_cancel₀ (ne_of_gt hCommonFactorPositive) hCancel).symm
  refine ⟨hFinalKelvin, ?_⟩
  change stateTemperatureInKelvin setup .final - 5463 / 20 =
    (90109 / 200 : ℝ)
  rw [hFinalKelvin]
  norm_num

/-!
Thus the final temperature is `450.545 °C` in the exact input model, which
rounds to the displayed `450 °C` and is uniquely closest to answer B.  The
primary-raster premise preserves the engine diagram without contributing any
thermodynamic number.

This formalizes blueprint label `thm:physics:phyx_mini_0469:target`.
-/
theorem problem_phyx_mini_0469
    {GasAmount : Type}
    (setup : AutomobileEngineCompressionSetup GasAmount)
    (hScenario : MatchesAutomobileEngineCompressionScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedEngineFigure setup.figure)
    (hPhysical : HasPhysicalCompressionParameters setup)
    (hClosed : SatisfiesClosedCylinderAmountConservation setup)
    (hIdealGas : SatisfiesEndpointIdealGasLaw setup) :
    stateTemperatureInKelvin setup .final = (144739 / 200 : ℝ) ∧
      stateTemperatureInDegreesCelsius setup .final =
        (90109 / 200 : ℝ) ∧
      RoundsToDisplayedTenDegrees setup .B ∧
      IsUniqueClosestDisplayedTemperature setup .B := by
  rcases final_temperature_exact setup hReadouts hPhysical hClosed hIdealGas with
    ⟨hFinalKelvin, hFinalCelsius⟩
  refine ⟨hFinalKelvin, hFinalCelsius, ?_, ?_⟩
  · unfold RoundsToDisplayedTenDegrees
    rw [hFinalCelsius]
    norm_num [displayedTemperatureInDegreesCelsius]
  · intro other hOther
    rw [hFinalCelsius]
    cases other <;>
      norm_num [displayedTemperatureInDegreesCelsius] at *

end PhyXMiniProblems.ProblemPhyXMini0469
