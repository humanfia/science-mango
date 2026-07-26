import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0359

open Dimension

/-!
# Equilibrium position of a piston separating two ideal gases

A rigid cylindrical container of length `80 cm` is divided by a thin piston.
Initially the piston is clamped `30 cm` from the left end, with helium at
`5 atm` on the left and argon at `1 atm` on the right. The helium sample has
amount `1 mol`; the argon amount is determined from its initial ideal-gas
state. The cylinder is immersed in `1 L` of water, and the whole system is
initially at `25 °C`. After the piston is released, the gases reach common
mechanical and thermal equilibrium.

Lengths, area, volume, and pressure are represented by unit-independent
Physlib quantities. Real numbers occur only as explicit named-unit readouts,
amount-of-substance readouts in moles, and coherently calibrated physical
constants.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read an area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a volume in the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a pressure in coherent units selected by `units`. -/
def pressureReadout (units : UnitChoices) (pressure : DimPressure) : ℝ :=
  (pressure units).val

/-- Centimeter readout used for the cylinder and piston coordinates. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Square-centimeter readout of the cylinder cross-sectional area. -/
def areaInSquareCentimeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.centimeters area

/-- Cubic-centimeter readout of a physical volume. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.centimeters volume

/-- Liter readout, using `1 L = 1000 cm³`. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  volumeInCubicCentimeters volume / 1000

/-!
Atmosphere readout formed from Physlib's dimensionful standard atmosphere,
rather than identifying pressure with a bare real number.
-/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureReadout UnitChoices.SI pressure /
    pressureReadout UnitChoices.SI DimPressure.standardAtmosphere

/-!
Read an absolute `Temperature` in kelvin. Physlib stores a temperature in an
arbitrary zero-preserving unit, so the storage unit remains explicit.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Convert an absolute kelvin readout to degrees Celsius. -/
def kelvinToCelsius (temperatureKelvin : ℝ) : ℝ :=
  temperatureKelvin - 5463 / 20

/-! ## Figure vocabulary and physical setup -/

/-- The two gases named inside the compartments. -/
inductive GasSpecies where
  | helium
  | argon
  deriving DecidableEq, Fintype, Repr

/-- Initial clamped state and final equilibrium state. -/
inductive SystemState where
  | initial
  | finalEquilibrium
  deriving DecidableEq, Fintype, Repr

/-- Bodies whose temperatures are relevant to thermal equilibrium. -/
inductive ThermalBody where
  | heliumGas
  | argonGas
  | surroundingWater
  deriving DecidableEq, Fintype, Repr

/-- Associate each gas sample with its thermal body. -/
def gasThermalBody : GasSpecies → ThermalBody
  | .helium => .heliumGas
  | .argon => .argonGas

/-- The ideal/nonideal gas-model distinction stated in the prose. -/
inductive GasModel where
  | ideal
  | nonideal
  deriving DecidableEq, Repr

/-- Geometrical idealization of the vessel. -/
inductive ContainerModel where
  | rigidCylinder
  | other
  deriving DecidableEq, Repr

/-- Mechanical idealization of the separating piston. -/
inductive PistonModel where
  | thinFrictionlessImpermeable
  | other
  deriving DecidableEq, Repr

/-- Constraint imposed on the piston at a stage of the experiment. -/
inductive PistonConstraint where
  | clamped
  | releasedAndFree
  deriving DecidableEq, Repr

/-- Whether a solid body's heat capacity is retained in the thermal model. -/
inductive HeatCapacityTreatment where
  | neglected
  | retained
  deriving DecidableEq, Repr

/-!
Information read from the primary image. It distinguishes the left and right
regions, their gas labels, displayed pressures, widths, and the water
surrounding the cylinder. It contains no final piston position.
-/
structure PistonCylinderFigure where
  leftCompartmentGasLabel : GasSpecies
  rightCompartmentGasLabel : GasSpecies
  displayedPressure : GasSpecies → DimPressure
  displayedCompartmentWidth : GasSpecies → LengthQuantity
  showsSeparatingPiston : Bool
  showsCylinderSubmergedInWater : Bool
  showsWaterLabel : Bool

/-!
Independent physical quantities and observables of the experiment.

Physlib currently has no amount-of-substance dimension, so the amount type
and its calibrated mole readout are explicit parameters. A single sealed
sample of each gas is used at both states. The final piston position is an
independent physical observable, not a definition involving an answer choice.
-/
structure TwoGasPistonSetup (AmountOfSubstance : Type) where
  figure : PistonCylinderFigure
  gasSample : GasSpecies → AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  gasModel : GasSpecies → GasModel
  containerModel : ContainerModel
  pistonModel : PistonModel
  pistonConstraint : SystemState → PistonConstraint
  compartmentsAreSealed : Bool
  cylinderLength : LengthQuantity
  cylinderCrossSectionArea : AreaQuantity
  pistonPositionFromLeft : SystemState → LengthQuantity
  surroundingWaterVolume : VolumeQuantity
  pressure : SystemState → GasSpecies → DimPressure
  temperature : SystemState → ThermalBody → Temperature
  temperatureStorageUnit : TemperatureUnit
  universalGasConstantAtmCubicCentimetersPerMoleKelvin : ℝ
  cylinderHeatCapacityTreatment : HeatCapacityTreatment
  pistonHeatCapacityTreatment : HeatCapacityTreatment

/-- Mole readout of one of the two sealed gas samples. -/
def gasAmountInMoles
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance)
    (gas : GasSpecies) : ℝ :=
  setup.amountInMoles (setup.gasSample gas)

/-- Kelvin readout of a body's temperature in one system state. -/
def bodyTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance)
    (state : SystemState) (body : ThermalBody) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.temperature state body)

/-- Celsius readout of a body's temperature in one system state. -/
def bodyTemperatureInCelsius
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance)
    (state : SystemState) (body : ThermalBody) : ℝ :=
  kelvinToCelsius (bodyTemperatureInKelvin setup state body)

/-!
Axial width of a gas compartment. Helium occupies the portion to the left of
the piston and argon the remaining portion of the rigid cylinder.
-/
def chamberWidthInCentimeters
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance)
    (state : SystemState) : GasSpecies → ℝ
  | .helium => lengthInCentimeters (setup.pistonPositionFromLeft state)
  | .argon =>
      lengthInCentimeters setup.cylinderLength -
        lengthInCentimeters (setup.pistonPositionFromLeft state)

/-!
Cylindrical chamber volume `area * axial width`, read coherently in cubic
centimeters. This is the rigid-cylinder geometry law, not a condition on the
requested equilibrium position.
-/
def chamberVolumeInCubicCentimeters
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance)
    (state : SystemState) (gas : GasSpecies) : ℝ :=
  areaInSquareCentimeters setup.cylinderCrossSectionArea *
    chamberWidthInCentimeters setup state gas

/-!
The ideal-gas equation in one coherent collection of named-unit readouts.
The gas constant therefore has units `atm cm³ mol⁻¹ K⁻¹`.
-/
def ObeysIdealGasLaw
    (pressureAtmospheres volumeCubicCentimeters amountMoles
      gasConstant temperatureKelvin : ℝ) : Prop :=
  pressureAtmospheres * volumeCubicCentimeters =
    amountMoles * gasConstant * temperatureKelvin

/-! ## Assumptions supplied by the prose and primary image -/

/-- Qualitative idealizations and experimental sequence stated in the prose. -/
structure MatchesProblemScenario
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance) : Prop where
  eachGasIsIdeal : ∀ gas, setup.gasModel gas = .ideal
  cylinderIsRigidAndCylindrical : setup.containerModel = .rigidCylinder
  pistonIsThinFrictionlessAndImpermeable :
    setup.pistonModel = .thinFrictionlessImpermeable
  pistonInitiallyClamped : setup.pistonConstraint .initial = .clamped
  pistonUltimatelyReleased :
    setup.pistonConstraint .finalEquilibrium = .releasedAndFree
  gasCompartmentsRemainSealed : setup.compartmentsAreSealed = true
  cylinderHeatCapacityNeglected :
    setup.cylinderHeatCapacityTreatment = .neglected
  pistonHeatCapacityNeglected :
    setup.pistonHeatCapacityTreatment = .neglected

/-!
Numerical problem data and primary-image readouts. The source report restores
the garbled temperature in the raw text as `25 °C`. No final coordinate or
answer choice occurs in these fields.
-/
structure MatchesProblemAndFigureData
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance) : Prop where
  leftRegionLabel : setup.figure.leftCompartmentGasLabel = .helium
  rightRegionLabel : setup.figure.rightCompartmentGasLabel = .argon
  separatingPistonShown : setup.figure.showsSeparatingPiston = true
  submergedInWaterShown :
    setup.figure.showsCylinderSubmergedInWater = true
  waterLabelShown : setup.figure.showsWaterLabel = true
  figurePressuresAreInitialPressures :
    ∀ gas, setup.figure.displayedPressure gas = setup.pressure .initial gas
  figureHeliumWidthIsInitialPistonPosition :
    setup.figure.displayedCompartmentWidth .helium =
      setup.pistonPositionFromLeft .initial
  figureWidthsFillCylinder :
    lengthInCentimeters
          (setup.figure.displayedCompartmentWidth .helium) +
        lengthInCentimeters
          (setup.figure.displayedCompartmentWidth .argon) =
      lengthInCentimeters setup.cylinderLength
  cylinderLengthCentimeters :
    lengthInCentimeters setup.cylinderLength = 80
  initialPistonPositionCentimeters :
    lengthInCentimeters (setup.pistonPositionFromLeft .initial) = 30
  figureHeliumWidthCentimeters :
    lengthInCentimeters
      (setup.figure.displayedCompartmentWidth .helium) = 30
  figureArgonWidthCentimeters :
    lengthInCentimeters
      (setup.figure.displayedCompartmentWidth .argon) = 50
  initialHeliumPressureAtmospheres :
    pressureInAtmospheres (setup.pressure .initial .helium) = 5
  initialArgonPressureAtmospheres :
    pressureInAtmospheres (setup.pressure .initial .argon) = 1
  displayedHeliumPressureAtmospheres :
    pressureInAtmospheres (setup.figure.displayedPressure .helium) = 5
  displayedArgonPressureAtmospheres :
    pressureInAtmospheres (setup.figure.displayedPressure .argon) = 1
  heliumAmountMoles : gasAmountInMoles setup .helium = 1
  waterVolumeLiters : volumeInLiters setup.surroundingWaterVolume = 1
  initiallyUniformTemperature :
    ∀ body,
      setup.temperature .initial body =
        setup.temperature .initial .surroundingWater
  initialTemperatureCelsius :
    bodyTemperatureInCelsius setup .initial .surroundingWater = 25

/-- Positivity and nondegeneracy conditions selecting physical gas states. -/
structure HasPhysicalParameters
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance) : Prop where
  gasAmountsPositive : ∀ gas, 0 < gasAmountInMoles setup gas
  gasConstantPositive :
    0 < setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin
  crossSectionAreaPositive :
    0 < areaInSquareCentimeters setup.cylinderCrossSectionArea
  cylinderLengthPositive : 0 < lengthInCentimeters setup.cylinderLength
  pistonInsideCylinder :
    ∀ state,
      0 < lengthInCentimeters (setup.pistonPositionFromLeft state) ∧
        lengthInCentimeters (setup.pistonPositionFromLeft state) <
          lengthInCentimeters setup.cylinderLength
  pressuresPositive :
    ∀ state gas, 0 < pressureInAtmospheres (setup.pressure state gas)
  absoluteTemperaturesPositive :
    ∀ state body, 0 < bodyTemperatureInKelvin setup state body

/-!
Governing laws for the sealed ideal gases and their final equilibrium.

* both gas samples obey `PV = nRT` before and after release;
* the same `gasSample gas` occurs at both states, expressing amount
  conservation in each sealed compartment;
* final mechanical equilibrium gives equal gas pressures;
* final thermal equilibrium gives one common temperature for helium, argon,
  and the surrounding water.

These laws are generic and contain no numerical final piston position.
-/
structure SatisfiesIdealGasAndEquilibriumLaws
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance) : Prop where
  idealGasEquation :
    ∀ state gas,
      ObeysIdealGasLaw
        (pressureInAtmospheres (setup.pressure state gas))
        (chamberVolumeInCubicCentimeters setup state gas)
        (gasAmountInMoles setup gas)
        setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin
        (bodyTemperatureInKelvin setup state (gasThermalBody gas))
  finalMechanicalEquilibrium :
    setup.pressure .finalEquilibrium .helium =
      setup.pressure .finalEquilibrium .argon
  finalThermalEquilibrium :
    ∀ body,
      setup.temperature .finalEquilibrium body =
        setup.temperature .finalEquilibrium .surroundingWater

/-! ## Multiple-choice display and target -/

/-- Labels printed beside the four proposed piston positions. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Piston distance from the left end, in centimeters, printed by each choice. -/
def displayedPistonPositionInCentimeters : AnswerChoice → ℝ
  | .A => 60
  | .B => 30
  | .C => 50
  | .D => 40

/-- A choice exactly matches a derived piston-position readout. -/
def MatchesAnswerChoice (positionCentimeters : ℝ)
    (choice : AnswerChoice) : Prop :=
  positionCentimeters = displayedPistonPositionInCentimeters choice

/-- A selected answer is the unique displayed value matching the position. -/
def IsUniqueMatchingAnswer (positionCentimeters : ℝ)
    (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice positionCentimeters choice ∧
    ∀ otherChoice,
      MatchesAnswerChoice positionCentimeters otherChoice →
        otherChoice = choice

/-!
At the final common pressure and temperature, the ideal-gas equations make
the chamber-volume ratio equal to the conserved mole ratio. The initial
`5 atm × 30 cm` and `1 atm × 50 cm` states determine that ratio, yielding a
final helium width of `60 cm` in the `80 cm` cylinder. Thus choice A is the
unique matching displayed answer.

Blueprint: `thm:physics:phyx_mini_0359:target`.
-/
theorem problem_phyx_mini_0359
    {AmountOfSubstance : Type}
    (setup : TwoGasPistonSetup AmountOfSubstance)
    (hScenario : MatchesProblemScenario setup)
    (hData : MatchesProblemAndFigureData setup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesIdealGasAndEquilibriumLaws setup) :
    lengthInCentimeters
          (setup.pistonPositionFromLeft .finalEquilibrium) = 60 ∧
      IsUniqueMatchingAnswer
        (lengthInCentimeters
          (setup.pistonPositionFromLeft .finalEquilibrium)) .A := by
  have hHeInitial := hLaws.idealGasEquation .initial .helium
  have hArInitial := hLaws.idealGasEquation .initial .argon
  have hHeFinal := hLaws.idealGasEquation .finalEquilibrium .helium
  have hArFinal := hLaws.idealGasEquation .finalEquilibrium .argon
  have hInitialTemperature :
      bodyTemperatureInKelvin setup .initial (gasThermalBody .helium) =
        bodyTemperatureInKelvin setup .initial (gasThermalBody .argon) := by
    unfold bodyTemperatureInKelvin
    congr 1
    exact
      (hData.initiallyUniformTemperature (gasThermalBody .helium)).trans
        (hData.initiallyUniformTemperature (gasThermalBody .argon)).symm
  have hFinalTemperature :
      bodyTemperatureInKelvin setup .finalEquilibrium
          (gasThermalBody .helium) =
        bodyTemperatureInKelvin setup .finalEquilibrium
          (gasThermalBody .argon) := by
    unfold bodyTemperatureInKelvin
    congr 1
    exact
      (hLaws.finalThermalEquilibrium (gasThermalBody .helium)).trans
        (hLaws.finalThermalEquilibrium (gasThermalBody .argon)).symm
  have hFinalPressure :
      pressureInAtmospheres
          (setup.pressure .finalEquilibrium .helium) =
        pressureInAtmospheres
          (setup.pressure .finalEquilibrium .argon) :=
    congrArg pressureInAtmospheres hLaws.finalMechanicalEquilibrium
  simp only [ObeysIdealGasLaw, chamberVolumeInCubicCentimeters,
    chamberWidthInCentimeters] at hHeInitial hArInitial hHeFinal hArFinal
  rw [hData.initialHeliumPressureAtmospheres,
    hData.initialPistonPositionCentimeters, hData.heliumAmountMoles] at hHeInitial
  rw [hData.initialArgonPressureAtmospheres, hData.cylinderLengthCentimeters,
    hData.initialPistonPositionCentimeters] at hArInitial
  rw [hData.heliumAmountMoles] at hHeFinal
  rw [hData.cylinderLengthCentimeters] at hArFinal
  have hHeInitialRT :
      setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
          bodyTemperatureInKelvin setup .initial
            (gasThermalBody .helium) =
        150 * areaInSquareCentimeters setup.cylinderCrossSectionArea := by
    nlinarith [hHeInitial]
  have hArAmountEquation :
      50 * areaInSquareCentimeters setup.cylinderCrossSectionArea =
        gasAmountInMoles setup .argon *
          (150 * areaInSquareCentimeters
            setup.cylinderCrossSectionArea) := by
    calc
      50 * areaInSquareCentimeters setup.cylinderCrossSectionArea =
          gasAmountInMoles setup .argon *
            setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
              bodyTemperatureInKelvin setup .initial
                (gasThermalBody .argon) := by
        nlinarith [hArInitial]
      _ = gasAmountInMoles setup .argon *
            (setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
              bodyTemperatureInKelvin setup .initial
                (gasThermalBody .argon)) := by
        ring
      _ = gasAmountInMoles setup .argon *
            (setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
              bodyTemperatureInKelvin setup .initial
                (gasThermalBody .helium)) := by
        rw [hInitialTemperature]
      _ = gasAmountInMoles setup .argon *
            (150 * areaInSquareCentimeters
              setup.cylinderCrossSectionArea) := by
        rw [hHeInitialRT]
  have hArgonAmount :
      gasAmountInMoles setup .argon = (1 : ℝ) / 3 := by
    nlinarith [hArAmountEquation, hPhysical.crossSectionAreaPositive]
  have hFinalRT :
      setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
          bodyTemperatureInKelvin setup .finalEquilibrium
            (gasThermalBody .helium) =
        pressureInAtmospheres
            (setup.pressure .finalEquilibrium .helium) *
          (areaInSquareCentimeters setup.cylinderCrossSectionArea *
            lengthInCentimeters
              (setup.pistonPositionFromLeft .finalEquilibrium)) := by
    nlinarith [hHeFinal]
  have hFinalEquation :
      pressureInAtmospheres
          (setup.pressure .finalEquilibrium .helium) *
          (areaInSquareCentimeters setup.cylinderCrossSectionArea *
            (80 - lengthInCentimeters
              (setup.pistonPositionFromLeft .finalEquilibrium))) =
        ((1 : ℝ) / 3) *
          (pressureInAtmospheres
              (setup.pressure .finalEquilibrium .helium) *
            (areaInSquareCentimeters setup.cylinderCrossSectionArea *
              lengthInCentimeters
                (setup.pistonPositionFromLeft .finalEquilibrium))) := by
    calc
      _ = pressureInAtmospheres
            (setup.pressure .finalEquilibrium .argon) *
          (areaInSquareCentimeters setup.cylinderCrossSectionArea *
            (80 - lengthInCentimeters
              (setup.pistonPositionFromLeft .finalEquilibrium))) := by
        rw [hFinalPressure]
      _ = gasAmountInMoles setup .argon *
          setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
            bodyTemperatureInKelvin setup .finalEquilibrium
              (gasThermalBody .argon) := hArFinal
      _ = ((1 : ℝ) / 3) *
          setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
            bodyTemperatureInKelvin setup .finalEquilibrium
              (gasThermalBody .argon) := by
        rw [hArgonAmount]
      _ = ((1 : ℝ) / 3) *
          setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
            bodyTemperatureInKelvin setup .finalEquilibrium
              (gasThermalBody .helium) := by
        rw [hFinalTemperature]
      _ = ((1 : ℝ) / 3) *
          (setup.universalGasConstantAtmCubicCentimetersPerMoleKelvin *
            bodyTemperatureInKelvin setup .finalEquilibrium
              (gasThermalBody .helium)) := by
        ring
      _ = ((1 : ℝ) / 3) *
          (pressureInAtmospheres
              (setup.pressure .finalEquilibrium .helium) *
            (areaInSquareCentimeters setup.cylinderCrossSectionArea *
              lengthInCentimeters
                (setup.pistonPositionFromLeft .finalEquilibrium))) := by
        rw [hFinalRT]
  have hPositivePressureArea :
      0 <
        pressureInAtmospheres
            (setup.pressure .finalEquilibrium .helium) *
          areaInSquareCentimeters setup.cylinderCrossSectionArea :=
    mul_pos (hPhysical.pressuresPositive .finalEquilibrium .helium)
      hPhysical.crossSectionAreaPositive
  have hPosition :
      lengthInCentimeters
        (setup.pistonPositionFromLeft .finalEquilibrium) = 60 := by
    nlinarith [hFinalEquation, hPositivePressureArea]
  constructor
  · exact hPosition
  · rw [hPosition]
    constructor
    · norm_num [MatchesAnswerChoice, displayedPistonPositionInCentimeters]
    · intro otherChoice hOther
      cases otherChoice with
      | A => rfl
      | B =>
          norm_num [MatchesAnswerChoice,
            displayedPistonPositionInCentimeters] at hOther
      | C =>
          norm_num [MatchesAnswerChoice,
            displayedPistonPositionInCentimeters] at hOther
      | D =>
          norm_num [MatchesAnswerChoice,
            displayedPistonPositionInCentimeters] at hOther

end PhyXMiniProblems.ProblemPhyXMini0359
