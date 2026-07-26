import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Heat supplied beneath a floating piston while upper water spills

This file formalizes problem `phyx_mini_0453`.  A thin insulated piston
separates two regions of water in a vertical open cylinder.  Heat supplied to
the lower `2 kg` water sample raises the piston; water above the piston spills
over the open rim until the piston reaches the `10 m` top.

The physical model distinguishes three kinds of assumptions.

* `MatchesProblemAndPrimaryFigure` records only prose and bitmap information.
* `UsesStandardEnvironmentAndWaterData` records standard `g`, standard
  atmospheric pressure, and rounded water-property-table readouts.
* `ObeysSpillingPistonCylinderLaws` records geometry, hydrostatics, mechanical
  equilibrium, quasistatic boundary work, internal-energy change, and the
  first law.

The requested heat is an independent dimensionful energy field.  No premise
fixes it, fixes either energy contribution, names an answer choice, or states
the theorem's numerical conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0453

open Dimension

/-! ## Dimensionful physical quantities and named SI readouts -/

/-- A physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical volume, with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical mass density, with dimension mass per volume. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- A physical acceleration, used here for the magnitude of gravity. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- An absolute thermodynamic temperature. -/
abbrev TemperatureQuantity : Type := Dimensionful (WithDim Θ𝓭 ℝ)

/-- Volume per unit mass, used to characterize a water equilibrium state. -/
abbrev SpecificVolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹) ℝ)

/-- Internal energy per unit mass. -/
abbrev SpecificEnergyQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Square-metre readout of a nonnegative physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilogram-per-cubic-metre readout of a mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  (density UnitChoices.SI).val

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Kelvin readout of an absolute temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  (temperature UnitChoices.SI).val

/-- Celsius readout obtained from the Kelvin readout by the standard offset. -/
def temperatureInDegreesCelsius (temperature : TemperatureQuantity) : ℝ :=
  temperatureInKelvins temperature - 27315 / 100

/-- Cubic-metre-per-kilogram readout of a specific volume. -/
def specificVolumeInCubicMetersPerKilogram
    (specificVolume : SpecificVolumeQuantity) : ℝ :=
  (specificVolume UnitChoices.SI).val

/-- Joule-per-kilogram readout of a specific internal energy. -/
def specificEnergyInJoulesPerKilogram
    (specificEnergy : SpecificEnergyQuantity) : ℝ :=
  (specificEnergy UnitChoices.SI).val

/-- Joule readout of a signed physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Kilojoule readout of a signed physical energy. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-! ## Apparatus, process, and primary-figure vocabulary -/

/-- Endpoint labels for the heating and spilling process. -/
inductive ProcessEndpoint where
  | initial
  | final
  deriving DecidableEq, Repr

/-- The two water regions separated by the piston. -/
inductive WaterRegion where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Thermodynamic phase classification used by the water-property readout. -/
inductive WaterPhase where
  | liquid
  | liquidVaporMixture
  deriving DecidableEq, Repr

/-- Vertical direction of the gravity arrow in the supplied image. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Text or object labels visibly associated with a region of the figure. -/
inductive FigureRegionLabel where
  | waterH2O
  | piston
  deriving DecidableEq, Repr

/-- The pressure symbol printed at the open upper free surface. -/
inductive FigurePressureLabel where
  | P0
  deriving DecidableEq, Repr

/-- Qualitative information transcribed from the primary bitmap. -/
structure PrimaryOpenCylinderFigure where
  regionLabel : WaterRegion → FigureRegionLabel
  pistonLabel : FigureRegionLabel
  freeSurfacePressureLabel : FigurePressureLabel
  gravityArrowDirection : VerticalDirection
  upperWaterReachesOpenRim : Bool
  pistonSeparatesWaterRegions : Bool

/-- Pressure, volume, temperature, phase, and water properties at an endpoint. -/
structure LowerWaterState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : TemperatureQuantity
  phase : WaterPhase
  specificVolume : SpecificVolumeQuantity
  specificInternalEnergy : SpecificEnergyQuantity

/-!
The complete apparatus and its independent observables.

In particular, `heatAddedToLowerWater`, `boundaryWorkByLowerWater`, and
`lowerWaterInternalEnergyChange` are independent dimensionful energies.  Their
relations and values are not built into this structure.
-/
structure SpillingWaterPistonSetup where
  figure : PrimaryOpenCylinderFigure
  cylinderHeight : LengthQuantity
  cylinderCrossSectionalArea : DimArea
  atmosphericPressureP0 : DimPressure
  gravitationalAcceleration : AccelerationQuantity
  pistonMass : MassQuantity
  lowerWaterMass : MassQuantity
  waterDensityAtTwentyCelsius : MassDensityQuantity
  pistonHeight : ProcessEndpoint → LengthQuantity
  upperWaterMass : ProcessEndpoint → MassQuantity
  lowerWaterState : ProcessEndpoint → LowerWaterState
  upperWaterInitialTemperature : TemperatureQuantity
  pistonIsThin : Bool
  pistonIsInsulated : Bool
  pistonIsFloatingAndFrictionless : Bool
  processIsQuasistatic : Bool
  heatIsAddedOnlyBelowPiston : Bool
  boundaryWorkByLowerWater : DimEnergy
  lowerWaterInternalEnergyChange : DimEnergy
  heatAddedToLowerWater : DimEnergy

/-! ## Source data, reference data, and physical branch -/

/-!
The stated data and qualitative facts visible in image `453.png`.  No field
contains a derived pressure, volume, work, internal-energy change, heat, or
answer choice.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : SpillingWaterPistonSetup) : Prop where
  upperRegionIsWater : setup.figure.regionLabel .upper = .waterH2O
  lowerRegionIsWater : setup.figure.regionLabel .lower = .waterH2O
  centralObjectIsPiston : setup.figure.pistonLabel = .piston
  freeSurfaceIsLabelledP0 :
    setup.figure.freeSurfacePressureLabel = .P0
  gravityPointsDownward :
    setup.figure.gravityArrowDirection = .downward
  waterInitiallyReachesOpenRim :
    setup.figure.upperWaterReachesOpenRim = true
  pistonSeparatesTheWaterRegions :
    setup.figure.pistonSeparatesWaterRegions = true
  cylinderHeightIsTenMeters :
    lengthInMeters setup.cylinderHeight = 10
  crossSectionalAreaIsOneTenthSquareMeter :
    areaInSquareMeters setup.cylinderCrossSectionalArea = 1 / 10
  pistonMassIsOneHundredNinetyEightPointFiveKilograms :
    massInKilograms setup.pistonMass = 397 / 2
  lowerWaterMassIsTwoKilograms :
    massInKilograms setup.lowerWaterMass = 2
  lowerWaterInitiallyAtTwentyCelsius :
    temperatureInDegreesCelsius
      (setup.lowerWaterState .initial).temperature = 20
  upperWaterInitiallyAtTwentyCelsius :
    temperatureInDegreesCelsius setup.upperWaterInitialTemperature = 20
  lowerWaterInitiallyLiquid :
    (setup.lowerWaterState .initial).phase = .liquid
  thinPiston : setup.pistonIsThin = true
  insulatedPiston : setup.pistonIsInsulated = true
  floatingFrictionlessPiston :
    setup.pistonIsFloatingAndFrictionless = true
  quasistaticExpansion : setup.processIsQuasistatic = true
  heatIsSuppliedBelow : setup.heatIsAddedOnlyBelowPiston = true
  finalPistonHeightIsCylinderHeight :
    setup.pistonHeight .final = setup.cylinderHeight

/-!
Standard environmental constants and rounded equilibrium-water property
readouts used by the textbook calculation.

The density `998.2 kg/m³` is the liquid-water density near `20 °C`.
The specific internal energies `83.900 kJ/kg` and `1168.950 kJ/kg` are
rounded property-table readouts at the initial liquid state and the final
two-phase state determined by the derived pressure and specific volume.
These are calibrations of water states, not calibrations of the requested
total heat.
-/
structure UsesStandardEnvironmentAndWaterData
    (setup : SpillingWaterPistonSetup) : Prop where
  standardAtmosphericPressure :
    pressureInPascals setup.atmosphericPressureP0 = 101325
  standardGravity :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 196133 / 20000
  waterDensityAtTwentyCelsius :
    densityInKilogramsPerCubicMeter
      setup.waterDensityAtTwentyCelsius = 4991 / 5
  initialSpecificInternalEnergy :
    specificEnergyInJoulesPerKilogram
      (setup.lowerWaterState .initial).specificInternalEnergy = 83900
  finalStateIsLiquidVaporMixture :
    (setup.lowerWaterState .final).phase = .liquidVaporMixture
  finalSpecificInternalEnergy :
    specificEnergyInJoulesPerKilogram
      (setup.lowerWaterState .final).specificInternalEnergy = 1168950

/-- Positivity conditions selecting physically meaningful states. -/
structure HasPhysicalSpillingWaterParameters
    (setup : SpillingWaterPistonSetup) : Prop where
  cylinderHeightPositive : 0 < lengthInMeters setup.cylinderHeight
  crossSectionalAreaPositive :
    0 < areaInSquareMeters setup.cylinderCrossSectionalArea
  atmosphericPressurePositive :
    0 < pressureInPascals setup.atmosphericPressureP0
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  lowerWaterMassPositive : 0 < massInKilograms setup.lowerWaterMass
  waterDensityPositive :
    0 < densityInKilogramsPerCubicMeter
      setup.waterDensityAtTwentyCelsius
  pistonHeightNonnegative : ∀ endpoint,
    0 ≤ lengthInMeters (setup.pistonHeight endpoint)
  pistonHeightAtMostCylinderHeight : ∀ endpoint,
    lengthInMeters (setup.pistonHeight endpoint) ≤
      lengthInMeters setup.cylinderHeight
  upperWaterMassNonnegative : ∀ endpoint,
    0 ≤ massInKilograms (setup.upperWaterMass endpoint)
  lowerWaterPressurePositive : ∀ endpoint,
    0 < pressureInPascals (setup.lowerWaterState endpoint).pressure
  lowerWaterVolumePositive : ∀ endpoint,
    0 < volumeInCubicMeters (setup.lowerWaterState endpoint).volume
  lowerWaterSpecificVolumePositive : ∀ endpoint,
    0 < specificVolumeInCubicMetersPerKilogram
      (setup.lowerWaterState endpoint).specificVolume

/-! ## Governing geometry, hydrostatics, work, and thermodynamics -/

/-!
The governing laws for a constant-area cylinder with a spilling upper water
column.  While the piston rises, the upper free surface remains at the rim,
so its mass is `ρ A (H - h)`.  Quasistatic piston equilibrium gives the lower
pressure.  The boundary-work identity integrates the atmospheric load, the
piston weight, and the changing hydrostatic load of the spilling upper water.

The last two fields are the mass-specific internal-energy relation and the
closed-system first law with work done by the lower water taken as positive.
All relations are generic in the apparatus fields and contain no numerical
heat, component value, or answer choice.
-/
structure ObeysSpillingPistonCylinderLaws
    (setup : SpillingWaterPistonSetup) : Prop where
  lowerWaterOccupiesCylindricalVolume : ∀ endpoint,
    volumeInCubicMeters (setup.lowerWaterState endpoint).volume =
      areaInSquareMeters setup.cylinderCrossSectionalArea *
        lengthInMeters (setup.pistonHeight endpoint)
  lowerWaterSpecificVolumeDefinition : ∀ endpoint,
    specificVolumeInCubicMetersPerKilogram
        (setup.lowerWaterState endpoint).specificVolume =
      volumeInCubicMeters (setup.lowerWaterState endpoint).volume /
        massInKilograms setup.lowerWaterMass
  initiallyLiquidVolumeFromDensity :
    volumeInCubicMeters (setup.lowerWaterState .initial).volume =
      massInKilograms setup.lowerWaterMass /
        densityInKilogramsPerCubicMeter
          setup.waterDensityAtTwentyCelsius
  spillingUpperWaterMassBalance : ∀ endpoint,
    massInKilograms (setup.upperWaterMass endpoint) =
      densityInKilogramsPerCubicMeter
          setup.waterDensityAtTwentyCelsius *
        areaInSquareMeters setup.cylinderCrossSectionalArea *
        (lengthInMeters setup.cylinderHeight -
          lengthInMeters (setup.pistonHeight endpoint))
  quasistaticPistonMechanicalEquilibrium : ∀ endpoint,
    pressureInPascals (setup.lowerWaterState endpoint).pressure =
      pressureInPascals setup.atmosphericPressureP0 +
        (massInKilograms setup.pistonMass +
            massInKilograms (setup.upperWaterMass endpoint)) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration /
          areaInSquareMeters setup.cylinderCrossSectionalArea
  quasistaticBoundaryWork :
    energyInJoules setup.boundaryWorkByLowerWater =
      pressureInPascals setup.atmosphericPressureP0 *
          (volumeInCubicMeters (setup.lowerWaterState .final).volume -
            volumeInCubicMeters (setup.lowerWaterState .initial).volume) +
        massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (lengthInMeters (setup.pistonHeight .final) -
            lengthInMeters (setup.pistonHeight .initial)) +
        densityInKilogramsPerCubicMeter
            setup.waterDensityAtTwentyCelsius *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          areaInSquareMeters setup.cylinderCrossSectionalArea / 2 *
          ((lengthInMeters setup.cylinderHeight -
              lengthInMeters (setup.pistonHeight .initial)) ^ 2 -
            (lengthInMeters setup.cylinderHeight -
              lengthInMeters (setup.pistonHeight .final)) ^ 2)
  lowerWaterInternalEnergyChange :
    energyInJoules setup.lowerWaterInternalEnergyChange =
      massInKilograms setup.lowerWaterMass *
        (specificEnergyInJoulesPerKilogram
            (setup.lowerWaterState .final).specificInternalEnergy -
          specificEnergyInJoulesPerKilogram
            (setup.lowerWaterState .initial).specificInternalEnergy)
  closedSystemFirstLaw :
    energyInJoules setup.heatAddedToLowerWater =
      energyInJoules setup.lowerWaterInternalEnergyChange +
        energyInJoules setup.boundaryWorkByLowerWater

/-! ## Intermediate physical consequences -/

/-!
The source geometry and the liquid-density relation determine both endpoint
volumes and heights.  The final equilibrium pressure includes atmospheric
pressure and the piston load, while the upper-water mass has fallen to zero.
-/
lemma endpointGeometryAndFinalPressure
    (setup : SpillingWaterPistonSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_reference : UsesStandardEnvironmentAndWaterData setup)
    (_physical : HasPhysicalSpillingWaterParameters setup)
    (_laws : ObeysSpillingPistonCylinderLaws setup) :
    volumeInCubicMeters (setup.lowerWaterState .initial).volume =
        (10 : ℝ) / 4991 ∧
      lengthInMeters (setup.pistonHeight .initial) =
        (100 : ℝ) / 4991 ∧
      volumeInCubicMeters (setup.lowerWaterState .final).volume = 1 ∧
      massInKilograms (setup.upperWaterMass .final) = 0 ∧
      pressureInPascals (setup.lowerWaterState .final).pressure =
        101325 + (397 / 2) * (196133 / 20000) / (1 / 10) := by
  have hVi :
      volumeInCubicMeters (setup.lowerWaterState .initial).volume =
        (10 : ℝ) / 4991 := by
    calc
      volumeInCubicMeters (setup.lowerWaterState .initial).volume =
          massInKilograms setup.lowerWaterMass /
            densityInKilogramsPerCubicMeter setup.waterDensityAtTwentyCelsius :=
        _laws.initiallyLiquidVolumeFromDensity
      _ = (10 : ℝ) / 4991 := by
        rw [_problem.lowerWaterMassIsTwoKilograms,
          _reference.waterDensityAtTwentyCelsius]
        norm_num
  have hHi :
      lengthInMeters (setup.pistonHeight .initial) = (100 : ℝ) / 4991 := by
    have h := _laws.lowerWaterOccupiesCylindricalVolume .initial
    rw [hVi, _problem.crossSectionalAreaIsOneTenthSquareMeter] at h
    nlinarith
  have hVf :
      volumeInCubicMeters (setup.lowerWaterState .final).volume = 1 := by
    calc
      volumeInCubicMeters (setup.lowerWaterState .final).volume =
          areaInSquareMeters setup.cylinderCrossSectionalArea *
            lengthInMeters (setup.pistonHeight .final) :=
        _laws.lowerWaterOccupiesCylindricalVolume .final
      _ = 1 := by
        rw [_problem.crossSectionalAreaIsOneTenthSquareMeter,
          _problem.finalPistonHeightIsCylinderHeight,
          _problem.cylinderHeightIsTenMeters]
        norm_num
  have hMf : massInKilograms (setup.upperWaterMass .final) = 0 := by
    calc
      massInKilograms (setup.upperWaterMass .final) =
          densityInKilogramsPerCubicMeter setup.waterDensityAtTwentyCelsius *
            areaInSquareMeters setup.cylinderCrossSectionalArea *
              (lengthInMeters setup.cylinderHeight -
                lengthInMeters (setup.pistonHeight .final)) :=
        _laws.spillingUpperWaterMassBalance .final
      _ = 0 := by
        rw [_reference.waterDensityAtTwentyCelsius,
          _problem.crossSectionalAreaIsOneTenthSquareMeter,
          _problem.finalPistonHeightIsCylinderHeight,
          _problem.cylinderHeightIsTenMeters]
        norm_num
  have hPf :
      pressureInPascals (setup.lowerWaterState .final).pressure =
        101325 + (397 / 2) * (196133 / 20000) / (1 / 10) := by
    calc
      pressureInPascals (setup.lowerWaterState .final).pressure =
          pressureInPascals setup.atmosphericPressureP0 +
            (massInKilograms setup.pistonMass +
                massInKilograms (setup.upperWaterMass .final)) *
              accelerationInMetersPerSecondSquared setup.gravitationalAcceleration /
                areaInSquareMeters setup.cylinderCrossSectionalArea :=
        _laws.quasistaticPistonMechanicalEquilibrium .final
      _ = 101325 + (397 / 2) * (196133 / 20000) / (1 / 10) := by
        rw [_reference.standardAtmosphericPressure,
          _problem.pistonMassIsOneHundredNinetyEightPointFiveKilograms,
          hMf, _reference.standardGravity,
          _problem.crossSectionalAreaIsOneTenthSquareMeter]
        norm_num
  exact ⟨hVi, hHi, hVf, hMf, hPf⟩

/-- A value rounds to a displayed number of kilojoules to the nearest tenth. -/
def RoundsToNearestTenthKilojoule
    (value displayedValue : ℝ) : Prop :=
  displayedValue - 1 / 20 ≤ value ∧ value < displayedValue + 1 / 20

/-!
Integrating the changing hydrostatic load gives approximately `169.3 kJ` of
boundary work.  This is an intermediate consequence, not a premise.
-/
lemma boundaryWorkDuringSpill
    (setup : SpillingWaterPistonSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_reference : UsesStandardEnvironmentAndWaterData setup)
    (_physical : HasPhysicalSpillingWaterParameters setup)
    (_laws : ObeysSpillingPistonCylinderLaws setup) :
    energyInJoules setup.boundaryWorkByLowerWater =
        (1207096421637 : ℝ) / 7130000 ∧
      RoundsToNearestTenthKilojoule
        (energyInKilojoules setup.boundaryWorkByLowerWater) (1693 / 10) := by
  rcases endpointGeometryAndFinalPressure
      setup _problem _reference _physical _laws with
    ⟨hVi, hHi, hVf, _hMf, _hPf⟩
  have hW := _laws.quasistaticBoundaryWork
  rw [_reference.standardAtmosphericPressure, hVf, hVi,
    _problem.pistonMassIsOneHundredNinetyEightPointFiveKilograms,
    _reference.standardGravity, _problem.finalPistonHeightIsCylinderHeight,
    _problem.cylinderHeightIsTenMeters, hHi,
    _reference.waterDensityAtTwentyCelsius,
    _problem.crossSectionalAreaIsOneTenthSquareMeter] at hW
  norm_num at hW
  refine ⟨hW, ?_⟩
  norm_num [RoundsToNearestTenthKilojoule, energyInKilojoules, hW]

/-!
The two rounded water-property readouts give the lower water's internal-energy
increase `2 kg · (1168.950 - 83.900) kJ/kg = 2170.1 kJ`.
-/
lemma lowerWaterInternalEnergyIncrease
    (setup : SpillingWaterPistonSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_reference : UsesStandardEnvironmentAndWaterData setup)
    (_physical : HasPhysicalSpillingWaterParameters setup)
    (_laws : ObeysSpillingPistonCylinderLaws setup) :
    energyInJoules setup.lowerWaterInternalEnergyChange = 2170100 ∧
      energyInKilojoules setup.lowerWaterInternalEnergyChange = 21701 / 10 := by
  have hΔU := _laws.lowerWaterInternalEnergyChange
  rw [_problem.lowerWaterMassIsTwoKilograms,
    _reference.finalSpecificInternalEnergy,
    _reference.initialSpecificInternalEnergy] at hΔU
  norm_num at hΔU
  refine ⟨hΔU, ?_⟩
  norm_num [energyInKilojoules, hΔU]

/-! ## Displayed answers and requested heat -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilojoule value printed beside each answer label. -/
def AnswerChoice.kilojoules : AnswerChoice → ℝ
  | .A => 21701 / 10
  | .B => 1693 / 10
  | .C => 1420
  | .D => 2340

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A displayed answer is the unique closest choice to a heat readout. -/
def IsUniqueClosestAnswer
    (heatKilojoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    otherChoice ≠ choice →
      |heatKilojoules - choice.kilojoules| <
        |heatKilojoules - otherChoice.kilojoules|

/-- A kilojoule value rounds to a displayed multiple of ten kilojoules. -/
def RoundsToNearestTenKilojoules
    (value displayedValue : ℝ) : Prop :=
  displayedValue - 5 ≤ value ∧ value < displayedValue + 5

/-!
The first law adds the `2170.1 kJ` internal-energy increase to the
approximately `169.3 kJ` boundary work.  The exact rational dictated by the
rounded reference data is about `2339.398 kJ`, which rounds to `2340 kJ` and
has answer D as the unique closest displayed choice.

This formalizes blueprint label `thm:physics:phyx_mini_0453:target`.
-/
theorem heatAddedDuringSpillingProcess
    (setup : SpillingWaterPistonSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_reference : UsesStandardEnvironmentAndWaterData setup)
    (_physical : HasPhysicalSpillingWaterParameters setup)
    (_laws : ObeysSpillingPistonCylinderLaws setup) :
    energyInJoules setup.heatAddedToLowerWater =
        2170100 + (1207096421637 : ℝ) / 7130000 ∧
      RoundsToNearestTenKilojoules
        (energyInKilojoules setup.heatAddedToLowerWater) 2340 ∧
      IsUniqueClosestAnswer
        (energyInKilojoules setup.heatAddedToLowerWater) .D := by
  rcases boundaryWorkDuringSpill
      setup _problem _reference _physical _laws with
    ⟨hW, _hWRounds⟩
  rcases lowerWaterInternalEnergyIncrease
      setup _problem _reference _physical _laws with
    ⟨hΔU, _hΔUkJ⟩
  have hQ := _laws.closedSystemFirstLaw
  rw [hΔU, hW] at hQ
  refine ⟨hQ, ?_, ?_⟩
  · norm_num [RoundsToNearestTenKilojoules, energyInKilojoules, hQ]
  · intro otherChoice hne
    cases otherChoice with
    | A => norm_num [energyInKilojoules, hQ, AnswerChoice.kilojoules]
    | B => norm_num [energyInKilojoules, hQ, AnswerChoice.kilojoules]
    | C => norm_num [energyInKilojoules, hQ, AnswerChoice.kilojoules]
    | D => exact (hne rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0453
