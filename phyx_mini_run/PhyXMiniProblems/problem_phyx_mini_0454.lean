import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0454

open Dimension
open scoped BigOperators

/-!
# Cooling water in a loaded piston--cylinder with stops

The supplied piston--cylinder contains `0.1 kg` of water initially at
`500 °C` and `1000 kPa`. As heat leaves the closed system, the loaded piston
first moves at constant pressure until it reaches stops at half the initial
volume. Cooling then continues at constant volume to `25 °C`.

Heat is positive into the water and boundary work is positive when done by
the water. Physical mass, pressure, volume, energy, specific volume, specific
energy, area, acceleration, and absolute temperature retain dimensionful or
temperature types. Real numbers below are only named-unit readouts,
dimensionless vapor quality, figure ratios, or displayed answer values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical mass with dimension `M`. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical volume with dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative specific volume with dimension `L³ M⁻¹`. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹) NNReal)

/-- Signed specific energy with dimension `L² T⁻²`. -/
abbrev SpecificEnergyQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A nonnegative acceleration magnitude with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-!
An absolute temperature together with the zero-preserving unit in which its
magnitude is stored. Celsius is used only as an affine scalar readout.
-/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  storageUnit : TemperatureUnit

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout of a physical pressure. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-metre-per-kilogram readout of a physical specific volume. -/
def specificVolumeInCubicMetresPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  ((specificVolume UnitChoices.SI).val : ℝ)

/-- Joule readout of physical heat, work, or internal energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Kilojoule readout of physical heat, work, or internal energy. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Joule-per-kilogram readout of a physical specific energy. -/
def specificEnergyInJoulesPerKilogram
    (specificEnergy : SpecificEnergyQuantity) : ℝ :=
  (specificEnergy UnitChoices.SI).val

/-- Kilojoule-per-kilogram readout of a physical specific energy. -/
def specificEnergyInKilojoulesPerKilogram
    (specificEnergy : SpecificEnergyQuantity) : ℝ :=
  specificEnergyInJoulesPerKilogram specificEnergy / 1000

/-- Square-metre readout of the piston face area. -/
def areaInSquareMetres (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetresPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Kelvin readout of a measured absolute temperature. -/
def temperatureInKelvin (temperature : MeasuredTemperature) : ℝ :=
  let unitRatio : NNReal :=
    temperature.storageUnit / TemperatureUnit.kelvin
  temperature.absoluteTemperature.toReal * (unitRatio : ℝ)

/-- Celsius readout, using the exact affine offset `273.15 K`. -/
def temperatureInDegreesCelsius
    (temperature : MeasuredTemperature) : ℝ :=
  temperatureInKelvin temperature - 5463 / 20

/-! ## Process states, legs, and figure vocabulary -/

/-- The three equilibrium states needed for the two-stage cooling path. -/
inductive ProcessPoint where
  | initial
  | atStop
  | final
  deriving DecidableEq, Fintype, Repr

/-- The two consecutive legs of the cooling process. -/
inductive ProcessLeg where
  | pistonMoving
  | pistonOnStop
  deriving DecidableEq, Fintype, Repr

/-- Initial point of each directed process leg. -/
def legStart : ProcessLeg → ProcessPoint
  | .pistonMoving => .initial
  | .pistonOnStop => .atStop

/-- Final point of each directed process leg. -/
def legFinish : ProcessLeg → ProcessPoint
  | .pistonMoving => .atStop
  | .pistonOnStop => .final

/-- Mechanical constraint on a leg of the process. -/
inductive ProcessConstraint where
  | constantLoadPressure
  | constantVolumeAtStop
  deriving DecidableEq, Repr

/-- Constraint dictated by the loaded piston and the rigid stops. -/
def expectedConstraint : ProcessLeg → ProcessConstraint
  | .pistonMoving => .constantLoadPressure
  | .pistonOnStop => .constantVolumeAtStop

/-- The working substance named in the problem and raster. -/
inductive WorkingFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-- Literal symbolic or text labels visible in the primary raster. -/
inductive FigureLabel where
  | externalPressureP0
  | pistonMassMp
  | water
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative geometry and labels read from the supplied image. The numerical
half-volume placement comes from the prose and is recorded separately below.
-/
structure PistonCylinderFigure where
  printedText : FigureLabel → String
  labelShown : FigureLabel → Bool
  showsVerticalCylinderWalls : Bool
  showsMovablePistonAboveWater : Bool
  showsOpposedInternalStops : Bool
  showsExternalPressureAbovePiston : Bool

/-- A physical equilibrium state of the fixed water sample. -/
structure WaterEquilibriumState where
  temperature : MeasuredTemperature
  pressure : DimPressure
  volume : VolumeQuantity
  specificVolume : SpecificVolumeQuantity
  internalEnergy : DimEnergy
  specificInternalEnergy : SpecificEnergyQuantity

/-!
Independent observables and material-property functions for the apparatus.
Neither total heat transfer nor a selected answer is stored as a field.
-/
structure PistonCylinderCoolingSetup where
  fluid : WorkingFluid
  waterMass : MassQuantity
  stateAt : ProcessPoint → WaterEquilibriumState
  processConstraint : ProcessLeg → ProcessConstraint
  sameClosedWaterSample : Bool
  negligibleKineticEnergyChange : Bool
  negligiblePotentialEnergyChange : Bool
  externalPressureP0 : DimPressure
  pistonMassMp : MassQuantity
  pistonFaceArea : DimArea
  gravitationalAcceleration : AccelerationQuantity
  figure : PistonCylinderFigure
  saturationPressureAt : MeasuredTemperature → DimPressure
  saturatedLiquidSpecificVolumeAt :
    MeasuredTemperature → SpecificVolumeQuantity
  saturatedVaporSpecificVolumeAt :
    MeasuredTemperature → SpecificVolumeQuantity
  saturatedLiquidSpecificInternalEnergyAt :
    MeasuredTemperature → SpecificEnergyQuantity
  saturatedVaporSpecificInternalEnergyAt :
    MeasuredTemperature → SpecificEnergyQuantity
  finalVaporQuality : ℝ
  workDoneByWaterOnLeg : ProcessLeg → DimEnergy
  heatTransferredIntoWaterOnLeg : ProcessLeg → DimEnergy

/-! ## Derived scalar process observables -/

/-- Pressure due to `P₀` together with the piston weight, in pascals. -/
def loadedPistonPressureInPascals
    (setup : PistonCylinderCoolingSetup) : ℝ :=
  pressureInPascals setup.externalPressureP0 +
    massInKilograms setup.pistonMassMp *
      accelerationInMetresPerSecondSquared setup.gravitationalAcceleration /
        areaInSquareMetres setup.pistonFaceArea

/-- Total boundary work done by the water during both legs, in kilojoules. -/
def totalBoundaryWorkInKilojoules
    (setup : PistonCylinderCoolingSetup) : ℝ :=
  ∑ leg : ProcessLeg, energyInKilojoules (setup.workDoneByWaterOnLeg leg)

/-- Total signed heat transferred into the water during both legs, in kJ. -/
def totalHeatTransferIntoWaterInKilojoules
    (setup : PistonCylinderCoolingSetup) : ℝ :=
  ∑ leg : ProcessLeg,
    energyInKilojoules (setup.heatTransferredIntoWaterOnLeg leg)

/-- Total internal-energy change of the water, in kilojoules. -/
def internalEnergyChangeInKilojoules
    (setup : PistonCylinderCoolingSetup) : ℝ :=
  energyInKilojoules (setup.stateAt .final).internalEnergy -
    energyInKilojoules (setup.stateAt .initial).internalEnergy

/-! ## Assumptions: scenario, figure, data, and governing laws -/

/-- Qualitative closed-system and two-stage process assumptions. -/
structure MatchesPistonCylinderCoolingScenario
    (setup : PistonCylinderCoolingSetup) : Prop where
  workingFluidIsWater : setup.fluid = .water
  fixedClosedWaterSample : setup.sameClosedWaterSample = true
  kineticEnergyChangeNegligible :
    setup.negligibleKineticEnergyChange = true
  potentialEnergyChangeNegligible :
    setup.negligiblePotentialEnergyChange = true
  legConstraintsAgree :
    ∀ leg, setup.processConstraint leg = expectedConstraint leg

/-!
Primary-image evidence: the raster shows a water-filled cylinder, a movable
piston labelled `mₚ`, an external pressure `P₀`, and opposed internal stops.
-/
structure MatchesSuppliedPistonCylinderFigure
    (setup : PistonCylinderCoolingSetup) : Prop where
  externalPressureText :
    setup.figure.printedText .externalPressureP0 = "P₀"
  pistonMassText : setup.figure.printedText .pistonMassMp = "mₚ"
  waterText : setup.figure.printedText .water = "Water"
  everyLabelShown : ∀ label, setup.figure.labelShown label = true
  cylinderWallsShown : setup.figure.showsVerticalCylinderWalls = true
  pistonAboveWater : setup.figure.showsMovablePistonAboveWater = true
  internalStopsShown : setup.figure.showsOpposedInternalStops = true
  externalPressureAbovePiston :
    setup.figure.showsExternalPressureAbovePiston = true

/-!
Numerical data stated in the prose. The stop and final states have half the
initial total volume; no heat-transfer value occurs in these premises.
-/
structure MatchesProblemReadouts
    (setup : PistonCylinderCoolingSetup) : Prop where
  waterMassKilograms : massInKilograms setup.waterMass = 1 / 10
  initialTemperatureCelsius :
    temperatureInDegreesCelsius (setup.stateAt .initial).temperature = 500
  initialPressureKilopascals :
    pressureInKilopascals (setup.stateAt .initial).pressure = 1000
  finalTemperatureCelsius :
    temperatureInDegreesCelsius (setup.stateAt .final).temperature = 25
  stopAtHalfInitialVolume :
    volumeInCubicMetres (setup.stateAt .atStop).volume =
      (1 / 2 : ℝ) * volumeInCubicMetres (setup.stateAt .initial).volume
  finalVolumeFixedByStop :
    volumeInCubicMetres (setup.stateAt .final).volume =
      volumeInCubicMetres (setup.stateAt .atStop).volume

/-!
Rounded superheated-water and saturated-water property-table entries used in
the calculation. These are independent material data, not a heat-transfer
answer. At `1000 kPa, 500 °C`, `v₁ = 0.3541 m³/kg` and
`u₁ = 3124.3 kJ/kg`. At `25 °C`, the listed saturated endpoints determine
the final mixture quality and energy through the constitutive laws below.
-/
structure UsesWaterPropertyTableCalibration
    (setup : PistonCylinderCoolingSetup) : Prop where
  initialSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
        (setup.stateAt .initial).specificVolume = 3541 / 10000
  initialSpecificInternalEnergy :
    specificEnergyInKilojoulesPerKilogram
        (setup.stateAt .initial).specificInternalEnergy = 31243 / 10
  finalSaturationPressureKilopascals :
    pressureInKilopascals
        (setup.saturationPressureAt (setup.stateAt .final).temperature) =
      3169 / 1000
  finalSaturatedLiquidSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
        (setup.saturatedLiquidSpecificVolumeAt
          (setup.stateAt .final).temperature) = 1003 / 1000000
  finalSaturatedVaporSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
        (setup.saturatedVaporSpecificVolumeAt
          (setup.stateAt .final).temperature) = 4334 / 100
  finalSaturatedLiquidSpecificInternalEnergy :
    specificEnergyInKilojoulesPerKilogram
        (setup.saturatedLiquidSpecificInternalEnergyAt
          (setup.stateAt .final).temperature) = 10483 / 100
  finalSaturatedVaporSpecificInternalEnergy :
    specificEnergyInKilojoulesPerKilogram
        (setup.saturatedVaporSpecificInternalEnergyAt
          (setup.stateAt .final).temperature) = 12047 / 5

/-- Positivity and phase-range conditions selecting a physical process. -/
structure HasPhysicalPistonCylinderParameters
    (setup : PistonCylinderCoolingSetup) : Prop where
  waterMassPositive : 0 < massInKilograms setup.waterMass
  pressurePositive :
    ∀ point, 0 < pressureInPascals (setup.stateAt point).pressure
  volumePositive :
    ∀ point, 0 < volumeInCubicMetres (setup.stateAt point).volume
  pistonFaceAreaPositive : 0 < areaInSquareMetres setup.pistonFaceArea
  gravityPositive :
    0 < accelerationInMetresPerSecondSquared
      setup.gravitationalAcceleration
  finalQualityInRange : 0 ≤ setup.finalVaporQuality ∧
    setup.finalVaporQuality ≤ 1

/-!
Governing mechanics and thermodynamics:

* total volume and internal energy are mass times their specific values;
* the freely moving loaded piston maintains the pressure generated by `P₀`
  and `mₚ g/A` until it reaches the stop;
* the second leg is isochoric;
* the final state is a saturated water mixture whose `v` and `u` interpolate
  between saturated liquid and vapor using one vapor quality;
* quasistatic boundary work is `p ΔV`;
* on each closed-system leg, `Q_into = ΔU + W_by`.

These uniform laws do not contain the requested heat-transfer value or an
answer choice.
-/
structure SatisfiesLoadedPistonWaterLaws
    (setup : PistonCylinderCoolingSetup) : Prop where
  extensiveVolume : ∀ point,
    volumeInCubicMetres (setup.stateAt point).volume =
      massInKilograms setup.waterMass *
        specificVolumeInCubicMetresPerKilogram
          (setup.stateAt point).specificVolume
  extensiveInternalEnergy : ∀ point,
    energyInJoules (setup.stateAt point).internalEnergy =
      massInKilograms setup.waterMass *
        specificEnergyInJoulesPerKilogram
          (setup.stateAt point).specificInternalEnergy
  initialPressureBalancesPistonLoad :
    pressureInPascals (setup.stateAt .initial).pressure =
      loadedPistonPressureInPascals setup
  freePistonLegIsIsobaric :
    pressureInPascals (setup.stateAt .atStop).pressure =
      pressureInPascals (setup.stateAt .initial).pressure
  stoppedPistonLegIsIsochoric :
    volumeInCubicMetres (setup.stateAt .final).volume =
      volumeInCubicMetres (setup.stateAt .atStop).volume
  finalPressureIsSaturationPressure :
    (setup.stateAt .final).pressure =
      setup.saturationPressureAt (setup.stateAt .final).temperature
  finalMixtureSpecificVolume :
    specificVolumeInCubicMetresPerKilogram
        (setup.stateAt .final).specificVolume =
      specificVolumeInCubicMetresPerKilogram
          (setup.saturatedLiquidSpecificVolumeAt
            (setup.stateAt .final).temperature) +
        setup.finalVaporQuality *
          (specificVolumeInCubicMetresPerKilogram
              (setup.saturatedVaporSpecificVolumeAt
                (setup.stateAt .final).temperature) -
            specificVolumeInCubicMetresPerKilogram
              (setup.saturatedLiquidSpecificVolumeAt
                (setup.stateAt .final).temperature))
  finalMixtureSpecificInternalEnergy :
    specificEnergyInKilojoulesPerKilogram
        (setup.stateAt .final).specificInternalEnergy =
      specificEnergyInKilojoulesPerKilogram
          (setup.saturatedLiquidSpecificInternalEnergyAt
            (setup.stateAt .final).temperature) +
        setup.finalVaporQuality *
          (specificEnergyInKilojoulesPerKilogram
              (setup.saturatedVaporSpecificInternalEnergyAt
                (setup.stateAt .final).temperature) -
            specificEnergyInKilojoulesPerKilogram
              (setup.saturatedLiquidSpecificInternalEnergyAt
                (setup.stateAt .final).temperature))
  quasistaticBoundaryWork : ∀ leg,
    energyInJoules (setup.workDoneByWaterOnLeg leg) =
      pressureInPascals (setup.stateAt (legStart leg)).pressure *
        (volumeInCubicMetres (setup.stateAt (legFinish leg)).volume -
          volumeInCubicMetres (setup.stateAt (legStart leg)).volume)
  firstLawOnEachLeg : ∀ leg,
    energyInJoules (setup.heatTransferredIntoWaterOnLeg leg) =
      energyInJoules (setup.stateAt (legFinish leg)).internalEnergy -
          energyInJoules (setup.stateAt (legStart leg)).internalEnergy +
        energyInJoules (setup.workDoneByWaterOnLeg leg)

/-! ## Displayed choices and current target -/

/-- Labels of the four heat-transfer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed heat transfer in kilojoules printed beside each answer label. -/
def displayedHeatTransferInKilojoules : AnswerChoice → ℝ
  | .A => 0
  | .B => -571 / 5
  | .C => -177 / 10
  | .D => -7968 / 25

/-- The source dataset records choice D; this metadata is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The actual heat transfer rounds to a displayed value at two decimals. -/
def RoundsToDisplayedHundredth (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-- A choice displays the computed total heat transfer to two decimals. -/
def MatchesAnswerChoice
    (setup : PistonCylinderCoolingSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedHundredth
    (totalHeatTransferIntoWaterInKilojoules setup)
    (displayedHeatTransferInKilojoules choice)

/-- A choice is the unique displayed value matching the computed heat. -/
def IsUniqueMatchingAnswerChoice
    (setup : PistonCylinderCoolingSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
The moving-piston leg performs about `-17.705 kJ` of boundary work and the
fixed-volume leg performs none. Combining the property-table mixture
calculation with the first law gives a total heat transfer that rounds to
`-318.72 kJ`. Both statements are derived conclusions.
-/
lemma coolingProcessEnergyAccounting
    (setup : PistonCylinderCoolingSetup)
    (hScenario : MatchesPistonCylinderCoolingScenario setup)
    (hData : MatchesProblemReadouts setup)
    (hTable : UsesWaterPropertyTableCalibration setup)
    (hLaws : SatisfiesLoadedPistonWaterLaws setup) :
    totalBoundaryWorkInKilojoules setup = -3541 / 200 ∧
      totalHeatTransferIntoWaterInKilojoules setup =
        internalEnergyChangeInKilojoules setup +
          totalBoundaryWorkInKilojoules setup ∧
      RoundsToDisplayedHundredth
        (totalHeatTransferIntoWaterInKilojoules setup) (-7968 / 25) := by
  have hInitialVolume :
      volumeInCubicMetres (setup.stateAt .initial).volume =
        (3541 / 100000 : ℝ) := by
    rw [hLaws.extensiveVolume .initial, hData.waterMassKilograms,
      hTable.initialSpecificVolume]
    norm_num
  have hStopVolume :
      volumeInCubicMetres (setup.stateAt .atStop).volume =
        (3541 / 200000 : ℝ) := by
    rw [hData.stopAtHalfInitialVolume, hInitialVolume]
    norm_num
  have hFinalVolume :
      volumeInCubicMetres (setup.stateAt .final).volume =
        (3541 / 200000 : ℝ) := by
    rw [hData.finalVolumeFixedByStop, hStopVolume]
  have hInitialPressure :
      pressureInPascals (setup.stateAt .initial).pressure = 1000000 := by
    have h := hData.initialPressureKilopascals
    norm_num [pressureInKilopascals] at h ⊢
    linarith
  have hMovingWorkJoules :
      energyInJoules (setup.workDoneByWaterOnLeg .pistonMoving) =
        -17705 := by
    rw [hLaws.quasistaticBoundaryWork .pistonMoving]
    simp only [legStart, legFinish]
    rw [hInitialPressure, hStopVolume, hInitialVolume]
    norm_num
  have hStoppedWorkJoules :
      energyInJoules (setup.workDoneByWaterOnLeg .pistonOnStop) = 0 := by
    rw [hLaws.quasistaticBoundaryWork .pistonOnStop]
    simp only [legStart, legFinish]
    rw [hFinalVolume, hStopVolume]
    ring
  have hProcessLegUniv :
      (Finset.univ : Finset ProcessLeg) =
        {.pistonMoving, .pistonOnStop} := by
    decide
  have hSumProcessLegs (f : ProcessLeg → ℝ) :
      ∑ leg : ProcessLeg, f leg =
        f .pistonMoving + f .pistonOnStop := by
    rw [hProcessLegUniv, Finset.sum_insert (by decide),
      Finset.sum_singleton]
  have hTotalWork :
      totalBoundaryWorkInKilojoules setup = (-3541 / 200 : ℝ) := by
    classical
    norm_num [totalBoundaryWorkInKilojoules, hSumProcessLegs,
      energyInKilojoules,
      hMovingWorkJoules, hStoppedWorkJoules]
  have hMovingFirstLaw := hLaws.firstLawOnEachLeg .pistonMoving
  have hStoppedFirstLaw := hLaws.firstLawOnEachLeg .pistonOnStop
  simp only [legStart, legFinish] at hMovingFirstLaw hStoppedFirstLaw
  have hAccounting :
      totalHeatTransferIntoWaterInKilojoules setup =
        internalEnergyChangeInKilojoules setup +
          totalBoundaryWorkInKilojoules setup := by
    classical
    norm_num [totalHeatTransferIntoWaterInKilojoules,
      internalEnergyChangeInKilojoules, totalBoundaryWorkInKilojoules,
      hSumProcessLegs, energyInKilojoules] at hMovingFirstLaw hStoppedFirstLaw ⊢
    linarith
  have hInternalEnergyInKilojoules (point : ProcessPoint) :
      energyInKilojoules (setup.stateAt point).internalEnergy =
        massInKilograms setup.waterMass *
          specificEnergyInKilojoulesPerKilogram
            (setup.stateAt point).specificInternalEnergy := by
    unfold energyInKilojoules
      specificEnergyInKilojoulesPerKilogram
    rw [hLaws.extensiveInternalEnergy point]
    ring
  have hInitialInternalEnergy :
      energyInKilojoules (setup.stateAt .initial).internalEnergy =
        (31243 / 100 : ℝ) := by
    rw [hInternalEnergyInKilojoules, hData.waterMassKilograms,
      hTable.initialSpecificInternalEnergy]
    norm_num
  have hFinalSpecificVolume :
      specificVolumeInCubicMetresPerKilogram
          (setup.stateAt .final).specificVolume =
        (3541 / 20000 : ℝ) := by
    have h := hLaws.extensiveVolume .final
    rw [hFinalVolume, hData.waterMassKilograms] at h
    norm_num at h ⊢
    linarith
  have hMixtureVolume := hLaws.finalMixtureSpecificVolume
  rw [hFinalSpecificVolume,
    hTable.finalSaturatedLiquidSpecificVolume,
    hTable.finalSaturatedVaporSpecificVolume] at hMixtureVolume
  have hMixtureEnergy := hLaws.finalMixtureSpecificInternalEnergy
  rw [hTable.finalSaturatedLiquidSpecificInternalEnergy,
    hTable.finalSaturatedVaporSpecificInternalEnergy] at hMixtureEnergy
  have hFinalInternalEnergy :
      energyInKilojoules (setup.stateAt .final).internalEnergy =
        massInKilograms setup.waterMass *
          specificEnergyInKilojoulesPerKilogram
            (setup.stateAt .final).specificInternalEnergy :=
    hInternalEnergyInKilojoules .final
  constructor
  · exact hTotalWork
  constructor
  · exact hAccounting
  · rw [RoundsToDisplayedHundredth, abs_lt, hAccounting, hTotalWork,
      internalEnergyChangeInKilojoules, hFinalInternalEnergy,
      hInitialInternalEnergy, hData.waterMassKilograms]
    norm_num at hMixtureVolume hMixtureEnergy ⊢
    constructor <;> nlinarith

/-!
Therefore the signed heat transfer into the water is `-318.72 kJ` to the
precision displayed, uniquely selecting answer D.

This formalizes `thm:physics:phyx_mini_0454:target`.
-/
theorem problem_phyx_mini_0454
    (setup : PistonCylinderCoolingSetup)
    (hScenario : MatchesPistonCylinderCoolingScenario setup)
    (hFigure : MatchesSuppliedPistonCylinderFigure setup)
    (hData : MatchesProblemReadouts setup)
    (hTable : UsesWaterPropertyTableCalibration setup)
    (hPhysical : HasPhysicalPistonCylinderParameters setup)
    (hLaws : SatisfiesLoadedPistonWaterLaws setup) :
    RoundsToDisplayedHundredth
        (totalHeatTransferIntoWaterInKilojoules setup)
        (displayedHeatTransferInKilojoules .D) ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hRounding :=
    (coolingProcessEnergyAccounting setup hScenario hData hTable hLaws).2.2
  change
    RoundsToDisplayedHundredth
        (totalHeatTransferIntoWaterInKilojoules setup) (-7968 / 25) ∧
      (RoundsToDisplayedHundredth
          (totalHeatTransferIntoWaterInKilojoules setup) (-7968 / 25) ∧
        ∀ other : AnswerChoice,
          RoundsToDisplayedHundredth
            (totalHeatTransferIntoWaterInKilojoules setup)
            (displayedHeatTransferInKilojoules other) →
          other = .D)
  refine ⟨hRounding, hRounding, ?_⟩
  intro other hOther
  cases other with
  | A =>
      exfalso
      rw [RoundsToDisplayedHundredth, abs_lt] at hRounding hOther
      norm_num [displayedHeatTransferInKilojoules] at hRounding hOther
      linarith
  | B =>
      exfalso
      rw [RoundsToDisplayedHundredth, abs_lt] at hRounding hOther
      norm_num [displayedHeatTransferInKilojoules] at hRounding hOther
      linarith
  | C =>
      exfalso
      rw [RoundsToDisplayedHundredth, abs_lt] at hRounding hOther
      norm_num [displayedHeatTransferInKilojoules] at hRounding hOther
      linarith
  | D =>
      rfl

end PhyXMiniProblems.ProblemPhyXMini0454
