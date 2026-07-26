import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0438

open Dimension
open scoped BigOperators

/-!
# Power of an eight-cylinder Diesel engine

The supplied pressure--volume diagram depicts the ideal Diesel cycle
`1 → 2 → 3 → 4 → 1`: adiabatic compression, constant-pressure ignition,
adiabatic expansion, and constant-volume exhaust heat rejection.  The
physical input is a `1000 cm³` displacement, compression ratio `21`, intake
air with `γ = 1.40` at `25 °C` and one atmosphere, and `1000 J` of combustion
heat per cylinder cycle.  The engine has eight cylinders and runs at
`2400 rpm`.

Pressure, volume, absolute temperature, energy, heat capacity, frequency, and
power remain physical quantities.  Real numbers below are explicitly named
SI or displayed-unit readouts, mole readouts (amount of substance is not a
base dimension in Physlib), dimensionless ratios, or answer-choice values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical heat capacity carrying dimension energy/temperature. -/
abbrev HeatCapacityQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-!
The molar gas constant has the same Physlib dimensions as heat capacity.
Physlib's current dimension vector has no amount-of-substance coordinate, so
the inverse-mole role is supplied explicitly by the mole readout in the gas
sample below.
-/
abbrev MolarGasConstantQuantity : Type := HeatCapacityQuantity

/-- A nonnegative physical frequency carrying dimension `T⁻¹`. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical power carrying dimension energy/time. -/
abbrev PowerQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal axis of the figure. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Atmosphere readout used on the vertical axis of the figure. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Joule readout of a signed physical energy, heat transfer, or work. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Kelvin readout of a Physlib absolute temperature in its storage unit. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Joule-per-kelvin readout of a total heat capacity. -/
def heatCapacityInJoulesPerKelvin
    (heatCapacity : HeatCapacityQuantity) : ℝ :=
  ((heatCapacity UnitChoices.SI).val : ℝ)

/-- Joule-per-mole-kelvin readout of the molar gas constant. -/
def molarGasConstantInJoulesPerMoleKelvin
    (gasConstant : MolarGasConstantQuantity) : ℝ :=
  ((gasConstant UnitChoices.SI).val : ℝ)

/-- Per-second readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Revolutions-per-minute readout when the counted event is a revolution. -/
def frequencyInRevolutionsPerMinute (frequency : FrequencyQuantity) : ℝ :=
  60 * frequencyInHertz frequency

/-- Watt readout of a physical power. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Kilowatt readout used in the answer choices. -/
def powerInKilowatts (power : PowerQuantity) : ℝ :=
  powerInWatts power / 1000

/-! ## Numbered states, directed legs, and primary-figure vocabulary -/

/-- The four numbered equilibrium states printed in the diagram. -/
inductive CycleState where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- The four directed legs shown by the arrows in the diagram. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed Diesel-cycle leg. -/
def legSource : CycleLeg → CycleState
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final state of a directed Diesel-cycle leg. -/
def legTarget : CycleLeg → CycleState
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- Thermodynamic kind of a leg in the ideal Diesel cycle. -/
inductive ProcessKind where
  | adiabatic
  | constantPressureIgnition
  | constantVolumeExhaust
  deriving DecidableEq, Repr

/-- Process classification read from the primary image. -/
def displayedProcessKind : CycleLeg → ProcessKind
  | .oneToTwo => .adiabatic
  | .twoToThree => .constantPressureIgnition
  | .threeToFour => .adiabatic
  | .fourToOne => .constantVolumeExhaust

/-- Physical quantity represented by a plotted axis. -/
inductive AxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- Unit text printed beside an axis of the supplied bitmap. -/
inductive AxisDisplayUnit where
  | atmosphere
  | cubicCentimeter
  deriving DecidableEq, Repr

/-- Literal physical annotations visible in the primary bitmap. -/
inductive DiagramLabel where
  | stateOne
  | stateTwo
  | stateThree
  | stateFour
  | pressureMaximum
  | heatInputQH
  | ignition
  | adiabats
  | exhaust
  | heatRejectedQC
  deriving DecidableEq, Fintype, Repr

/-- Pressure, volume, and absolute temperature at one equilibrium state. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-- Structured transcription of image `438.png`. -/
structure DieselPVDiagram where
  plottedPressure : CycleState → DimPressure
  plottedVolume : CycleState → VolumeQuantity
  maximumPressure : DimPressure
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisDisplayUnit
  verticalAxisUnit : AxisDisplayUnit
  labelVisible : DiagramLabel → Bool
  /-- Whether a black cycle-direction arrowhead is printed on a process curve. -/
  arrowVisible : CycleLeg → Bool

/-! ## Working gas, cycle observables, and engine operation -/

/-- Equation-of-state model used for the cylinder's intake air. -/
inductive GasModel where
  | idealAir
  | other
  deriving DecidableEq, Repr

/-!
The gas sample is not replaced by a scalar.  Only its calibrated mole readout
is real-valued because amount of substance is absent from Physlib's current
five-coordinate `Dimension`.
-/
structure GasSample (AmountOfSubstance : Type) where
  model : GasModel
  sample : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ

/-!
The physical Diesel-cycle setup.  Signed heat is positive into the air and
signed work is positive when done by the air.  `outputPower` is an independent
observable constrained by the engine power law below; it is not defined from
an answer choice.
-/
structure DieselEngineCycle (AmountOfSubstance : Type) where
  gas : GasSample AmountOfSubstance
  state : CycleState → ThermodynamicState
  figure : DieselPVDiagram
  temperatureStorageUnit : TemperatureUnit
  molarGasConstant : MolarGasConstantQuantity
  heatCapacityAtConstantVolume : HeatCapacityQuantity
  heatCapacityAtConstantPressure : HeatCapacityQuantity
  internalEnergyAt : CycleState → DimEnergy
  heatTransferredIntoGasOn : CycleLeg → DimEnergy
  workDoneByGasOn : CycleLeg → DimEnergy
  processKind : CycleLeg → ProcessKind
  displacement : VolumeQuantity
  compressionRatio : ℝ
  heatCapacityRatio : ℝ
  fuelHeatPerCylinderCycle : DimEnergy
  cylinderCount : ℕ
  crankshaftRate : FrequencyQuantity
  cycleRatePerCylinder : FrequencyQuantity
  cyclesPerCrankRevolution : ℝ
  outputPower : PowerQuantity

/-- Mole readout of the physical air sample in one cylinder. -/
def amountOfAirInMoles
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : ℝ :=
  setup.gas.amountInMoles setup.gas.sample

/-- Kelvin readout at a numbered state. -/
def gasTemperatureInKelvins
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance)
    (state : CycleState) : ℝ :=
  temperatureInKelvins setup.temperatureStorageUnit
    (setup.state state).temperature

/-- Pascal readout at a numbered state. -/
def gasPressureInPascals
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance)
    (state : CycleState) : ℝ :=
  pressureInPascals (setup.state state).pressure

/-- Cubic-metre readout at a numbered state. -/
def gasVolumeInCubicMeters
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance)
    (state : CycleState) : ℝ :=
  volumeInCubicMeters (setup.state state).volume

/-- Signed joule readout of heat transferred into the gas on a leg. -/
def heatTransferredIntoGasInJoules
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.heatTransferredIntoGasOn leg)

/-- Signed joule readout of work done by the gas on a leg. -/
def workDoneByGasInJoules
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.workDoneByGasOn leg)

/-- Joule readout of internal energy at a numbered state. -/
def internalEnergyInJoules
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance)
    (state : CycleState) : ℝ :=
  energyInJoules (setup.internalEnergyAt state)

/-! ## Assumptions: prose data, figure readouts, and governing laws -/

/-!
Data stated in the prose.  It records no cycle work, efficiency, output power,
or answer choice.
-/
structure MatchesProblemStatement
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : Prop where
  gasIsIdealAir : setup.gas.model = .idealAir
  displacementIs1000CubicCentimeters :
    volumeInCubicCentimeters setup.displacement = 1000
  displacementIsMaximumMinusMinimum :
    volumeInCubicMeters setup.displacement =
      gasVolumeInCubicMeters setup .one -
        gasVolumeInCubicMeters setup .two
  compressionRatioIs21 : setup.compressionRatio = 21
  compressionRatioIsMaximumOverMinimum :
    setup.compressionRatio =
      gasVolumeInCubicMeters setup .one /
        gasVolumeInCubicMeters setup .two
  airHeatCapacityRatioIs1Point40 : setup.heatCapacityRatio = 1.40
  temperatureIsStoredInKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  intakeTemperatureIs25Celsius :
    gasTemperatureInKelvins setup .one = 273.15 + 25
  intakePressureIsOneAtmosphere :
    (setup.state .one).pressure = DimPressure.standardAtmosphere
  combustionHeatIs1000Joules :
    energyInJoules setup.fuelHeatPerCylinderCycle = 1000
  engineHasEightCylinders : setup.cylinderCount = 8
  crankshaftRateIs2400Rpm :
    frequencyInRevolutionsPerMinute setup.crankshaftRate = 2400

/-!
Exact transcription of the primary bitmap.  In particular, the curved
`1 → 2` leg is an adiabat; the auxiliary prose caption's claim that it is
vertical/isochoric is not used because the image is primary evidence.
-/
structure MatchesPrimaryPVDiagram
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimeters :
    setup.figure.horizontalAxisUnit = .cubicCentimeter
  verticalAxisUsesAtmospheres :
    setup.figure.verticalAxisUnit = .atmosphere
  everyPrintedLabelIsVisible :
    ∀ label, setup.figure.labelVisible label = true
  adiabaticDirectionArrowsAreVisible :
    setup.figure.arrowVisible .oneToTwo = true ∧
      setup.figure.arrowVisible .threeToFour = true
  nonadiabaticCycleDirectionArrowsAreNotPrinted :
    setup.figure.arrowVisible .twoToThree = false ∧
      setup.figure.arrowVisible .fourToOne = false
  plottedCoordinatesAreGasStates : ∀ state,
    setup.figure.plottedPressure state = (setup.state state).pressure ∧
      setup.figure.plottedVolume state = (setup.state state).volume
  displayedProcessKindsAgree :
    ∀ leg, setup.processKind leg = displayedProcessKind leg
  stateOneVolumeIs1050CubicCentimeters :
    volumeInCubicCentimeters (setup.state .one).volume = 1050
  stateTwoVolumeIs50CubicCentimeters :
    volumeInCubicCentimeters (setup.state .two).volume = 50
  stateFourSharesMaximumVolume :
    (setup.state .four).volume = (setup.state .one).volume
  stateThreeVolumeLiesBetweenExtremes :
    gasVolumeInCubicMeters setup .two < gasVolumeInCubicMeters setup .three ∧
      gasVolumeInCubicMeters setup .three < gasVolumeInCubicMeters setup .one
  stateOnePressureIsOneAtmosphere :
    pressureInAtmospheres (setup.state .one).pressure = 1
  statesTwoAndThreeAreAtMaximumPressure :
    (setup.state .two).pressure = setup.figure.maximumPressure ∧
      (setup.state .three).pressure = setup.figure.maximumPressure

/-- Positivity and nondegeneracy conditions for a physical Diesel cycle. -/
structure HasPhysicalDieselParameters
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : Prop where
  amountPositive : 0 < amountOfAirInMoles setup
  gasConstantPositive :
    0 < molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant
  pressurePositive : ∀ state, 0 < gasPressureInPascals setup state
  volumePositive : ∀ state, 0 < gasVolumeInCubicMeters setup state
  absoluteTemperaturePositive :
    ∀ state, 0 < gasTemperatureInKelvins setup state
  constantVolumeHeatCapacityPositive :
    0 < heatCapacityInJoulesPerKelvin
      setup.heatCapacityAtConstantVolume
  constantPressureHeatCapacityPositive :
    0 < heatCapacityInJoulesPerKelvin
      setup.heatCapacityAtConstantPressure
  compressionRatioGreaterThanOne : 1 < setup.compressionRatio
  heatCapacityRatioGreaterThanOne : 1 < setup.heatCapacityRatio
  crankshaftRatePositive : 0 < frequencyInHertz setup.crankshaftRate
  cycleRatePositive : 0 < frequencyInHertz setup.cycleRatePerCylinder

/-!
Macroscopic ideal-gas and first-law relations used by the Diesel model:

* `p V = n R T` at each equilibrium state;
* `Cₚ - Cᵥ = nR` and `γ = Cₚ/Cᵥ`;
* `T V^(γ-1)` is constant on each adiabatic leg;
* pressure is constant on ignition and volume is constant on exhaust;
* the corresponding heat/work relations and the first law hold on each leg.

These are general governing relations.  No field states the net work, output
power, or selected answer.
-/
structure SatisfiesIdealDieselCycleLaws
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : Prop where
  idealGasEquation : ∀ state,
    gasPressureInPascals setup state * gasVolumeInCubicMeters setup state =
      amountOfAirInMoles setup *
        molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
          gasTemperatureInKelvins setup state
  mayerRelation :
    heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantPressure -
        heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantVolume =
      amountOfAirInMoles setup *
        molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant
  heatCapacityRatioRelation :
    setup.heatCapacityRatio =
      heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantPressure /
        heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantVolume
  internalEnergyOfIdealAir : ∀ state,
    internalEnergyInJoules setup state =
      heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantVolume *
        gasTemperatureInKelvins setup state
  adiabaticTemperatureVolumeRelation : ∀ leg,
    setup.processKind leg = .adiabatic →
      gasTemperatureInKelvins setup (legSource leg) *
          Real.rpow (gasVolumeInCubicMeters setup (legSource leg))
            (setup.heatCapacityRatio - 1) =
        gasTemperatureInKelvins setup (legTarget leg) *
          Real.rpow (gasVolumeInCubicMeters setup (legTarget leg))
            (setup.heatCapacityRatio - 1)
  adiabaticHeatTransfer : ∀ leg,
    setup.processKind leg = .adiabatic →
      heatTransferredIntoGasInJoules setup leg = 0
  constantPressureRelation : ∀ leg,
    setup.processKind leg = .constantPressureIgnition →
      gasPressureInPascals setup (legSource leg) =
        gasPressureInPascals setup (legTarget leg)
  constantPressureHeatTransfer : ∀ leg,
    setup.processKind leg = .constantPressureIgnition →
      heatTransferredIntoGasInJoules setup leg =
        heatCapacityInJoulesPerKelvin
            setup.heatCapacityAtConstantPressure *
          (gasTemperatureInKelvins setup (legTarget leg) -
            gasTemperatureInKelvins setup (legSource leg))
  constantPressureBoundaryWork : ∀ leg,
    setup.processKind leg = .constantPressureIgnition →
      workDoneByGasInJoules setup leg =
        gasPressureInPascals setup (legSource leg) *
          (gasVolumeInCubicMeters setup (legTarget leg) -
            gasVolumeInCubicMeters setup (legSource leg))
  constantVolumeRelation : ∀ leg,
    setup.processKind leg = .constantVolumeExhaust →
      gasVolumeInCubicMeters setup (legSource leg) =
        gasVolumeInCubicMeters setup (legTarget leg)
  constantVolumeBoundaryWork : ∀ leg,
    setup.processKind leg = .constantVolumeExhaust →
      workDoneByGasInJoules setup leg = 0
  constantVolumeHeatTransfer : ∀ leg,
    setup.processKind leg = .constantVolumeExhaust →
      heatTransferredIntoGasInJoules setup leg =
        heatCapacityInJoulesPerKelvin
            setup.heatCapacityAtConstantVolume *
          (gasTemperatureInKelvins setup (legTarget leg) -
            gasTemperatureInKelvins setup (legSource leg))
  firstLawOnEachLeg : ∀ leg,
    heatTransferredIntoGasInJoules setup leg =
      internalEnergyInJoules setup (legTarget leg) -
        internalEnergyInJoules setup (legSource leg) +
          workDoneByGasInJoules setup leg

/-!
Fuel combustion supplies the measured heat on the constant-pressure ignition
leg.  This relates a source datum to a process observable without assuming any
net work or power result.
-/
structure ModelsConstantPressureFuelInjection
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : Prop where
  combustionHeatEntersOnTwoToThree :
    setup.heatTransferredIntoGasOn .twoToThree =
      setup.fuelHeatPerCylinderCycle

/-! ## Net work, engine timing, and answer choices -/

/-- Net work done by the gas in one cylinder during one complete cycle. -/
def netCycleWorkInJoules
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, workDoneByGasInJoules setup leg

/-!
The idealized operating convention needed to interpret the dataset's recorded
answer uses one thermodynamic cycle per crank revolution per cylinder.  The
power law is the general product of cylinder count, cycle frequency, and net
work per cycle; it does not contain a numerical power or an answer choice.
-/
structure SatisfiesEngineTimingAndPowerLaw
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance) : Prop where
  oneCyclePerCrankRevolution : setup.cyclesPerCrankRevolution = 1
  cycleRateFromCrankshaft :
    frequencyInHertz setup.cycleRatePerCylinder =
      setup.cyclesPerCrankRevolution *
        frequencyInHertz setup.crankshaftRate
  enginePowerRelation :
    powerInWatts setup.outputPower =
      (setup.cylinderCount : ℝ) *
        frequencyInHertz setup.cycleRatePerCylinder *
          netCycleWorkInJoules setup

/-- Labels of the four printed power choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilowatt value printed beside each answer label. -/
def displayedPowerInKilowatts : AnswerChoice → ℝ
  | .A => 132
  | .B => 26.4
  | .C => 240
  | .D => 211

/-- Dataset metadata: the recorded answer label is D (`211 kW`). -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A displayed choice is strictly nearest to the modeled physical power. -/
def IsNearestDisplayedPowerChoice
    (actualPowerInKilowatts : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |actualPowerInKilowatts - displayedPowerInKilowatts choice| <
        |actualPowerInKilowatts - displayedPowerInKilowatts otherChoice|

/-!
**Physics formalization target
(`thm:physics:phyx_mini_0438:target`).**

The ideal Diesel-cycle laws determine the work per cylinder cycle.  Combining
that result with eight cylinders and the stated rotational rate makes the
modeled output uniquely closest to answer D, whose displayed value is
`211 kW`.  Neither the net work, the output power, nor answer D occurs as a
premise conclusion.
-/
theorem dieselEnginePowerOutputIsAnswerD
    {AmountOfSubstance : Type}
    (setup : DieselEngineCycle AmountOfSubstance)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_physical : HasPhysicalDieselParameters setup)
    (h_cycle : SatisfiesIdealDieselCycleLaws setup)
    (h_fuel : ModelsConstantPressureFuelInjection setup)
    (h_operation : SatisfiesEngineTimingAndPowerLaw setup) :
    IsNearestDisplayedPowerChoice
      (powerInKilowatts setup.outputPower) .D := by
  have hKind12 :
      setup.processKind .oneToTwo = .adiabatic := by
    simpa [displayedProcessKind] using
      h_figure.displayedProcessKindsAgree .oneToTwo
  have hKind23 :
      setup.processKind .twoToThree = .constantPressureIgnition := by
    simpa [displayedProcessKind] using
      h_figure.displayedProcessKindsAgree .twoToThree
  have hKind34 :
      setup.processKind .threeToFour = .adiabatic := by
    simpa [displayedProcessKind] using
      h_figure.displayedProcessKindsAgree .threeToFour
  have hKind41 :
      setup.processKind .fourToOne = .constantVolumeExhaust := by
    simpa [displayedProcessKind] using
      h_figure.displayedProcessKindsAgree .fourToOne
  have hT1 :
      gasTemperatureInKelvins setup .one = 5963 / 20 := by
    rw [h_problem.intakeTemperatureIs25Celsius]
    norm_num
  have hV1 :
      gasVolumeInCubicMeters setup .one = 21 / 20000 := by
    have h := h_figure.stateOneVolumeIs1050CubicCentimeters
    unfold volumeInCubicCentimeters at h
    unfold gasVolumeInCubicMeters
    norm_num at h ⊢
    linarith only [h]
  have hV2 :
      gasVolumeInCubicMeters setup .two = 1 / 20000 := by
    have h := h_figure.stateTwoVolumeIs50CubicCentimeters
    unfold volumeInCubicCentimeters at h
    unfold gasVolumeInCubicMeters
    norm_num at h ⊢
    linarith only [h]
  have hP1 :
      gasPressureInPascals setup .one = 101325 := by
    rw [gasPressureInPascals, h_problem.intakePressureIsOneAtmosphere]
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      DimPressure.pascal, CarriesDimension.toDimensionful_apply_apply]
  have hRoot21Lower :
      (67 / 20 : ℝ) < Real.rpow 21 (2 / 5) := by
    rw [Real.rpow_eq_pow,
      show (2 / 5 : ℝ) = 2 * (5 : ℝ)⁻¹ by norm_num,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 21), Real.rpow_two]
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 5)]
    norm_num
  have hRoot21Upper :
      Real.rpow 21 (2 / 5) < (69 / 20 : ℝ) := by
    rw [Real.rpow_eq_pow,
      show (2 / 5 : ℝ) = 2 * (5 : ℝ)⁻¹ by norm_num,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 21), Real.rpow_two]
    rw [Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 5)]
    norm_num
  have hSmallRootLower :
      (9 / 25 : ℝ) < Real.rpow (2 / 25) (2 / 5) := by
    rw [Real.rpow_eq_pow,
      show (2 / 5 : ℝ) = 2 * (5 : ℝ)⁻¹ by norm_num,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2 / 25), Real.rpow_two]
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 5)]
    norm_num
  have hSmallRootUpper :
      Real.rpow (9 / 100) (2 / 5) < (2 / 5 : ℝ) := by
    rw [Real.rpow_eq_pow,
      show (2 / 5 : ℝ) = 2 * (5 : ℝ)⁻¹ by norm_num,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9 / 100), Real.rpow_two]
    rw [Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 5)]
    norm_num
  have hCvNe :
      heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantVolume ≠ 0 :=
    ne_of_gt h_physical.constantVolumeHeatCapacityPositive
  have hRatio := h_cycle.heatCapacityRatioRelation
  rw [h_problem.airHeatCapacityRatioIs1Point40] at hRatio
  field_simp [hCvNe] at hRatio
  have hCv :
      heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantVolume =
        (5 / 2 : ℝ) *
          (amountOfAirInMoles setup *
            molarGasConstantInJoulesPerMoleKelvin
              setup.molarGasConstant) := by
    have hMayer := h_cycle.mayerRelation
    nlinarith only [hRatio, hMayer]
  have hCp :
      heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantPressure =
        (7 / 2 : ℝ) *
          (amountOfAirInMoles setup *
            molarGasConstantInJoulesPerMoleKelvin
              setup.molarGasConstant) := by
    have hMayer := h_cycle.mayerRelation
    nlinarith only [hRatio, hMayer]
  have hNR :
      amountOfAirInMoles setup *
          molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant =
        85113 / 238520 := by
    have h := h_cycle.idealGasEquation .one
    rw [hP1, hV1, hT1] at h
    norm_num at h ⊢
    nlinarith only [h]
  have hT2 :
      gasTemperatureInKelvins setup .two =
        (5963 / 20 : ℝ) * Real.rpow 21 (2 / 5) := by
    have h :=
      h_cycle.adiabaticTemperatureVolumeRelation .oneToTwo hKind12
    simp only [legSource, legTarget] at h
    rw [h_problem.airHeatCapacityRatioIs1Point40, hV1, hV2, hT1,
      Real.rpow_eq_pow] at h
    norm_num at h
    rw [show (21 / 20000 : ℝ) = 21 * (1 / 20000) by norm_num,
      Real.mul_rpow (by norm_num) (by norm_num)] at h
    apply mul_right_cancel₀
      (ne_of_gt
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 20000)
          (2 / 5)))
    calc
      gasTemperatureInKelvins setup .two *
            (1 / 20000 : ℝ) ^ (2 / 5 : ℝ) =
          (5963 / 20 : ℝ) *
            ((21 : ℝ) ^ (2 / 5 : ℝ) *
              (1 / 20000 : ℝ) ^ (2 / 5 : ℝ)) := h.symm
      _ = ((5963 / 20 : ℝ) * (21 : ℝ) ^ (2 / 5 : ℝ)) *
          (1 / 20000 : ℝ) ^ (2 / 5 : ℝ) := by ring
  have hT2Lower : 990 < gasTemperatureInKelvins setup .two := by
    rw [hT2]
    nlinarith only [hRoot21Lower]
  have hT2Upper : gasTemperatureInKelvins setup .two < 1030 := by
    rw [hT2]
    nlinarith only [hRoot21Upper]
  have hQIgnition :
      heatTransferredIntoGasInJoules setup .twoToThree = 1000 := by
    unfold heatTransferredIntoGasInJoules
    rw [h_fuel.combustionHeatEntersOnTwoToThree]
    exact h_problem.combustionHeatIs1000Joules
  have hCpNumeric :
      heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantPressure =
        (7 / 2 : ℝ) * (85113 / 238520) := by
    rw [hCp, hNR]
  have hTemperatureRise :
      gasTemperatureInKelvins setup .three -
          gasTemperatureInKelvins setup .two =
        477040000 / 595791 := by
    have h :=
      h_cycle.constantPressureHeatTransfer .twoToThree hKind23
    simp only [legSource, legTarget] at h
    rw [hQIgnition, hCpNumeric] at h
    norm_num at h ⊢
    nlinarith only [h]
  have hT3Lower : 1790 < gasTemperatureInKelvins setup .three := by
    nlinarith only [hT2Lower, hTemperatureRise]
  have hT3Upper : gasTemperatureInKelvins setup .three < 1850 := by
    nlinarith only [hT2Upper, hTemperatureRise]
  have hGas2 := h_cycle.idealGasEquation .two
  have hGas3 := h_cycle.idealGasEquation .three
  have hPressure23 :=
    h_cycle.constantPressureRelation .twoToThree hKind23
  simp only [legSource, legTarget] at hPressure23
  rw [← hPressure23] at hGas3
  have hVolumeTemperatureCross :
      gasVolumeInCubicMeters setup .three *
          gasTemperatureInKelvins setup .two =
        gasVolumeInCubicMeters setup .two *
          gasTemperatureInKelvins setup .three := by
    apply mul_left_cancel₀
      (ne_of_gt (h_physical.pressurePositive .two))
    calc
      gasPressureInPascals setup .two *
            (gasVolumeInCubicMeters setup .three *
              gasTemperatureInKelvins setup .two) =
          (gasPressureInPascals setup .two *
              gasVolumeInCubicMeters setup .three) *
            gasTemperatureInKelvins setup .two := by ring
      _ = (amountOfAirInMoles setup *
              molarGasConstantInJoulesPerMoleKelvin
                setup.molarGasConstant *
              gasTemperatureInKelvins setup .three) *
            gasTemperatureInKelvins setup .two := by rw [hGas3]
      _ = (amountOfAirInMoles setup *
              molarGasConstantInJoulesPerMoleKelvin
                setup.molarGasConstant *
              gasTemperatureInKelvins setup .two) *
            gasTemperatureInKelvins setup .three := by ring
      _ = (gasPressureInPascals setup .two *
              gasVolumeInCubicMeters setup .two) *
            gasTemperatureInKelvins setup .three := by rw [hGas2]
      _ = gasPressureInPascals setup .two *
          (gasVolumeInCubicMeters setup .two *
            gasTemperatureInKelvins setup .three) := by ring
  let expansionVolumeRatio : ℝ :=
    gasVolumeInCubicMeters setup .three /
      gasVolumeInCubicMeters setup .one
  have hExpansionVolumeRatioPositive :
      0 < expansionVolumeRatio := by
    dsimp [expansionVolumeRatio]
    exact div_pos (h_physical.volumePositive .three)
      (h_physical.volumePositive .one)
  have hExpansionVolumeRatioEquation :
      expansionVolumeRatio * gasTemperatureInKelvins setup .two =
        gasTemperatureInKelvins setup .three / 21 := by
    dsimp [expansionVolumeRatio]
    rw [hV1]
    rw [hV2] at hVolumeTemperatureCross
    norm_num at hVolumeTemperatureCross ⊢
    field_simp
    nlinarith only [hVolumeTemperatureCross]
  have hExpansionVolumeRatioLower :
      (2 / 25 : ℝ) < expansionVolumeRatio := by
    by_contra hnot
    have hle : expansionVolumeRatio ≤ (2 / 25 : ℝ) :=
      le_of_not_gt hnot
    have hmul₁ :
        expansionVolumeRatio * gasTemperatureInKelvins setup .two <
          expansionVolumeRatio * 1030 :=
      mul_lt_mul_of_pos_left hT2Upper hExpansionVolumeRatioPositive
    have hmul₂ :
        expansionVolumeRatio * 1030 ≤ (2 / 25 : ℝ) * 1030 :=
      mul_le_mul_of_nonneg_right hle (by norm_num)
    nlinarith only [hExpansionVolumeRatioEquation, hT3Lower,
      lt_of_lt_of_le hmul₁ hmul₂]
  have hExpansionVolumeRatioUpper :
      expansionVolumeRatio < (9 / 100 : ℝ) := by
    by_contra hnot
    have hle : (9 / 100 : ℝ) ≤ expansionVolumeRatio :=
      le_of_not_gt hnot
    have hmul₁ :
        (9 / 100 : ℝ) * gasTemperatureInKelvins setup .two ≤
          expansionVolumeRatio * gasTemperatureInKelvins setup .two :=
      mul_le_mul_of_nonneg_right hle
        (by linarith only [hT2Lower])
    have hmul₂ :
        (9 / 100 : ℝ) * 990 <
          (9 / 100 : ℝ) * gasTemperatureInKelvins setup .two :=
      mul_lt_mul_of_pos_left hT2Lower (by norm_num)
    nlinarith only [hExpansionVolumeRatioEquation, hT3Upper, hmul₁, hmul₂]
  have hExpansionRootLower :
      (9 / 25 : ℝ) < Real.rpow expansionVolumeRatio (2 / 5) := by
    have hmono := Real.rpow_lt_rpow
      (show (0 : ℝ) ≤ 2 / 25 by norm_num)
      hExpansionVolumeRatioLower
      (show (0 : ℝ) < 2 / 5 by norm_num)
    change Real.rpow (2 / 25) (2 / 5) <
      Real.rpow expansionVolumeRatio (2 / 5) at hmono
    linarith only [hSmallRootLower, hmono]
  have hExpansionRootUpper :
      Real.rpow expansionVolumeRatio (2 / 5) < (2 / 5 : ℝ) := by
    have hmono := Real.rpow_lt_rpow
      (le_of_lt hExpansionVolumeRatioPositive)
      hExpansionVolumeRatioUpper
      (show (0 : ℝ) < 2 / 5 by norm_num)
    change Real.rpow expansionVolumeRatio (2 / 5) <
      Real.rpow (9 / 100) (2 / 5) at hmono
    linarith only [hSmallRootUpper, hmono]
  have hV3Factor :
      gasVolumeInCubicMeters setup .three =
        expansionVolumeRatio * (21 / 20000 : ℝ) := by
    dsimp [expansionVolumeRatio]
    rw [hV1]
    field_simp
  have hV4 :
      gasVolumeInCubicMeters setup .four = 21 / 20000 := by
    unfold gasVolumeInCubicMeters
    rw [h_figure.stateFourSharesMaximumVolume]
    exact hV1
  have hT4 :
      gasTemperatureInKelvins setup .four =
        gasTemperatureInKelvins setup .three *
          Real.rpow expansionVolumeRatio (2 / 5) := by
    have h :=
      h_cycle.adiabaticTemperatureVolumeRelation .threeToFour hKind34
    simp only [legSource, legTarget] at h
    rw [h_problem.airHeatCapacityRatioIs1Point40, hV4, hV3Factor,
      Real.rpow_eq_pow] at h
    norm_num at h
    rw [Real.mul_rpow (le_of_lt hExpansionVolumeRatioPositive)
      (by norm_num)] at h
    apply mul_right_cancel₀
      (ne_of_gt
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 21 / 20000)
          (2 / 5)))
    calc
      gasTemperatureInKelvins setup .four *
            (21 / 20000 : ℝ) ^ (2 / 5 : ℝ) =
          gasTemperatureInKelvins setup .three *
            (expansionVolumeRatio ^ (2 / 5 : ℝ) *
              (21 / 20000 : ℝ) ^ (2 / 5 : ℝ)) := h.symm
      _ = (gasTemperatureInKelvins setup .three *
            expansionVolumeRatio ^ (2 / 5 : ℝ)) *
          (21 / 20000 : ℝ) ^ (2 / 5 : ℝ) := by ring
  have hT4Lower : 640 < gasTemperatureInKelvins setup .four := by
    rw [hT4]
    have hmul := mul_lt_mul hT3Lower
      (le_of_lt hExpansionRootLower)
      (by norm_num : (0 : ℝ) < 9 / 25)
      (by linarith only [hT3Lower])
    exact
      (show (640 : ℝ) < 1790 * (9 / 25) by norm_num).trans hmul
  have hT4Upper : gasTemperatureInKelvins setup .four < 740 := by
    rw [hT4]
    have hmul := mul_lt_mul hT3Upper
      (le_of_lt hExpansionRootUpper)
      (Real.rpow_pos_of_pos hExpansionVolumeRatioPositive (2 / 5))
      (by norm_num : (0 : ℝ) ≤ 1850)
    simpa only [show (1850 : ℝ) * (2 / 5) = 740 by norm_num] using hmul
  have hCvNumeric :
      heatCapacityInJoulesPerKelvin
          setup.heatCapacityAtConstantVolume =
        (5 / 2 : ℝ) * (85113 / 238520) := by
    rw [hCv, hNR]
  have hFirst12 := h_cycle.firstLawOnEachLeg .oneToTwo
  have hFirst23 := h_cycle.firstLawOnEachLeg .twoToThree
  have hFirst34 := h_cycle.firstLawOnEachLeg .threeToFour
  have hFirst41 := h_cycle.firstLawOnEachLeg .fourToOne
  simp only [legSource, legTarget] at hFirst12 hFirst23 hFirst34 hFirst41
  have hNoHeat12 :=
    h_cycle.adiabaticHeatTransfer .oneToTwo hKind12
  have hNoHeat34 :=
    h_cycle.adiabaticHeatTransfer .threeToFour hKind34
  have hNoWork41 :=
    h_cycle.constantVolumeBoundaryWork .fourToOne hKind41
  have hLegSum :
      netCycleWorkInJoules setup =
        workDoneByGasInJoules setup .oneToTwo +
          workDoneByGasInJoules setup .twoToThree +
          workDoneByGasInJoules setup .threeToFour +
          workDoneByGasInJoules setup .fourToOne := by
    unfold netCycleWorkInJoules
    rw [show (Finset.univ : Finset CycleLeg) =
      {.oneToTwo, .twoToThree, .threeToFour, .fourToOne} by decide]
    simp
    ring
  have hNetWorkFromHeatAndExhaust :
      netCycleWorkInJoules setup =
        heatTransferredIntoGasInJoules setup .twoToThree +
          (internalEnergyInJoules setup .one -
            internalEnergyInJoules setup .four) := by
    linarith only [hLegSum, hNoHeat12, hNoHeat34, hNoWork41,
      hFirst12, hFirst23, hFirst34, hFirst41]
  have hU1 := h_cycle.internalEnergyOfIdealAir .one
  have hU4 := h_cycle.internalEnergyOfIdealAir .four
  rw [hCvNumeric, hT1] at hU1
  rw [hCvNumeric] at hU4
  have hNetWorkTemperature :
      netCycleWorkInJoules setup =
        1000 + (5 / 2 : ℝ) * (85113 / 238520) *
          ((5963 / 20 : ℝ) -
            gasTemperatureInKelvins setup .four) := by
    rw [hQIgnition] at hNetWorkFromHeatAndExhaust
    linear_combination hNetWorkFromHeatAndExhaust + hU1 - hU4
  have hNetWorkLower : 600 < netCycleWorkInJoules setup := by
    rw [hNetWorkTemperature]
    nlinarith only [hT4Upper]
  have hNetWorkUpper : netCycleWorkInJoules setup < 700 := by
    rw [hNetWorkTemperature]
    nlinarith only [hT4Lower]
  have hCrankshaftFrequency :
      frequencyInHertz setup.crankshaftRate = 40 := by
    have h := h_problem.crankshaftRateIs2400Rpm
    unfold frequencyInRevolutionsPerMinute at h
    linarith only [h]
  have hCycleFrequency :
      frequencyInHertz setup.cycleRatePerCylinder = 40 := by
    rw [h_operation.cycleRateFromCrankshaft,
      h_operation.oneCyclePerCrankRevolution, hCrankshaftFrequency]
    norm_num
  have hOutputPower :
      powerInKilowatts setup.outputPower =
        (8 : ℝ) * 40 * netCycleWorkInJoules setup / 1000 := by
    unfold powerInKilowatts
    rw [h_operation.enginePowerRelation,
      h_problem.engineHasEightCylinders, hCycleFrequency]
    norm_num
  have hOutputLower :
      192 < powerInKilowatts setup.outputPower := by
    rw [hOutputPower]
    nlinarith only [hNetWorkLower]
  have hOutputUpper :
      powerInKilowatts setup.outputPower < 224 := by
    rw [hOutputPower]
    nlinarith only [hNetWorkUpper]
  unfold IsNearestDisplayedPowerChoice
  intro otherChoice hOther
  rcases otherChoice with _ | _ | _ | _
  · change
      |powerInKilowatts setup.outputPower - 211| <
        |powerInKilowatts setup.outputPower - 132|
    rw [← sq_lt_sq]
    nlinarith only [hOutputLower]
  · simp only [displayedPowerInKilowatts]
    rw [← sq_lt_sq]
    nlinarith only [hOutputLower]
  · change
      |powerInKilowatts setup.outputPower - 211| <
        |powerInKilowatts setup.outputPower - 240|
    rw [← sq_lt_sq]
    nlinarith only [hOutputUpper]
  · exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0438
