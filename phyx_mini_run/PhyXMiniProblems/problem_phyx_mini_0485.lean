import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0485

open Dimension

/-!
# Initial temperature of a forged horseshoe

A `0.40 kg` iron horseshoe is dropped into `1.25 L` of water in a `0.30 kg`
iron pot.  The water and pot start at `20.0 °C`, and all three bodies reach
thermal equilibrium at `25.0 °C`.  The idealized estimate uses `m = ρV`,
constant-specific-heat calorimetry `Q = mcΔT`, and conservation of energy for
an isolated three-body system.

Mass, volume, density, specific heat capacity, signed heat, and absolute
temperature are represented as physical quantities.  Real numbers occur only
as named unit readouts, affine Celsius coordinates, and displayed answer
values.  In particular, the unknown initial horseshoe temperature is an
independent field of the setup, not a definition of the requested answer.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- The physical dimension of volume, `L³`. -/
def volumeDimension : Dimension := L𝓭 * L𝓭 * L𝓭

/-- The physical dimension of mass density, `M L⁻³`. -/
def massDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension of mass-specific heat capacity, `L² T⁻² Θ⁻¹`. -/
def specificHeatCapacityDimension : Dimension :=
  L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

/-- A nonnegative physical mass, independent of a choice of units. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical volume, independent of a choice of units. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim volumeDimension NNReal)

/-- A nonnegative physical mass density, independent of a choice of units. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim massDensityDimension NNReal)

/-- A nonnegative mass-specific heat capacity, independent of a choice of units. -/
abbrev SpecificHeatCapacityQuantity : Type :=
  Dimensionful (WithDim specificHeatCapacityDimension NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical volume in the cube of a selected length unit. -/
def volumeReadout (unit : LengthUnit) (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read density in selected mass-per-cubic-length units. -/
def massDensityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : MassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Kilogram readout used by the calorimetry law. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  volumeReadout LengthUnit.meters volume

/-- Litre readout, using `1 m³ = 1000 L`. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- SI density readout in kilograms per cubic metre. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  massDensityReadout MassUnit.kilograms LengthUnit.meters density

/-- Kilogram-per-litre density readout, using `1 m³ = 1000 L`. -/
def massDensityInKilogramsPerLiter
    (density : MassDensityQuantity) : ℝ :=
  massDensityInKilogramsPerCubicMeter density / 1000

/-- SI readout of mass-specific heat capacity in joules per kilogram-kelvin. -/
def specificHeatInJoulesPerKilogramKelvin
    (capacity : SpecificHeatCapacityQuantity) : ℝ :=
  ((capacity UnitChoices.SI).val : ℝ)

/-- SI readout of a signed heat transfer in joules. -/
def heatInJoules (heat : DimEnergy) : ℝ :=
  (heat UnitChoices.SI).val

/--
An affine Celsius coordinate attached to a Physlib absolute temperature.
The offset is `273.15 K = 5463/20 K`.
-/
structure CelsiusTemperatureReading where
  absoluteTemperature : Temperature
  degreesCelsius : ℝ
  kelvinCalibration :
    absoluteTemperature.toReal = degreesCelsius + (5463 / 20 : ℝ)

/-! ## Bodies, materials, process roles, and supplied-image vocabulary -/

/-- The three bodies that exchange heat. -/
inductive ThermalBody where
  | horseshoe
  | water
  | pot
  deriving DecidableEq, Fintype, Repr

/-- The two thermal materials named in the problem. -/
inductive ThermalMaterial where
  | iron
  | liquidWater
  deriving DecidableEq, Fintype, Repr

/-- Thermal condition at the boundary of the modeled three-body system. -/
inductive ExteriorBoundaryCondition where
  | isolated
  | exchangesHeatWithSurroundings
  deriving DecidableEq, Repr

/-- Manufacturing and thermal condition of the horseshoe before immersion. -/
inductive HorseshoeCondition where
  | justForgedAndHot
  | ambient
  deriving DecidableEq, Repr

/-- Contact relation between the horseshoe and water. -/
inductive HorseshoeWaterContact where
  | immersed
  | separated
  deriving DecidableEq, Repr

/-- Objects identified in the supplied blacksmithing image and caption. -/
inductive FigureObject where
  | glowingHorseshoe
  | tongs
  | pairOfHands
  | anvil
  deriving DecidableEq, Fintype, Repr

/-- Recorded visible glow color of the hot horseshoe. -/
inductive HorseshoeGlowColor where
  | orange
  | other
  deriving DecidableEq, Repr

/--
Qualitative evidence from the supplied image.  It contains no printed
temperature, mass, volume, material constant, or answer label.
-/
structure SuppliedBlacksmithFigure where
  showsObject : FigureObject → Bool
  horseshoeGlowColor : HorseshoeGlowColor
  tongsHoldHorseshoe : Bool
  horseshoePositionedAgainstAnvil : Bool
  backgroundSoftlyBlurred : Bool
  containsPrintedText : Bool

/--
Independent physical quantities and qualitative roles of the experiment.
Signed body heats are positive into each body; the surroundings heat is
positive into the modeled three-body system.
-/
structure HorseshoeWaterCalorimetrySetup where
  materialAt : ThermalBody → ThermalMaterial
  massAt : ThermalBody → MassQuantity
  waterVolume : VolumeQuantity
  waterMassDensity : MassDensityQuantity
  specificHeatCapacityAt : ThermalMaterial → SpecificHeatCapacityQuantity
  initialTemperatureAt : ThermalBody → CelsiusTemperatureReading
  finalEquilibriumTemperature : CelsiusTemperatureReading
  heatAbsorbedDuringContact : ThermalBody → DimEnergy
  heatTransferredFromSurroundings : DimEnergy
  exteriorBoundary : ExteriorBoundaryCondition
  horseshoeCondition : HorseshoeCondition
  horseshoeWaterContact : HorseshoeWaterContact
  reachesCommonThermalEquilibrium : Bool
  usesConstantSpecificHeatApproximation : Bool
  waterRemainsLiquid : Bool
  figure : SuppliedBlacksmithFigure

/-- The requested Celsius coordinate, exposed without assigning it a value. -/
def initialHorseshoeTemperatureInDegreesCelsius
    (setup : HorseshoeWaterCalorimetrySetup) : ℝ :=
  (setup.initialTemperatureAt .horseshoe).degreesCelsius

/-! ## Assumptions: scenario, source readouts, reference data, and laws -/

/-- Qualitative process conditions stated or selected by the textbook model. -/
structure MatchesHorseshoeWaterScenario
    (setup : HorseshoeWaterCalorimetrySetup) : Prop where
  horseshoeIsIron : setup.materialAt .horseshoe = .iron
  waterIsLiquidWater : setup.materialAt .water = .liquidWater
  potIsIron : setup.materialAt .pot = .iron
  horseshoeWasJustForgedAndHot :
    setup.horseshoeCondition = .justForgedAndHot
  horseshoeIsImmersedInWater : setup.horseshoeWaterContact = .immersed
  modeledBoundaryIsIsolated : setup.exteriorBoundary = .isolated
  commonEquilibriumIsReached : setup.reachesCommonThermalEquilibrium = true
  constantSpecificHeatModel :
    setup.usesConstantSpecificHeatApproximation = true
  noWaterPhaseChange : setup.waterRemainsLiquid = true
  horseshoeStartsHotterThanEquilibrium :
    initialHorseshoeTemperatureInDegreesCelsius setup >
      setup.finalEquilibriumTemperature.degreesCelsius

/--
Numerical data printed in the problem.  The unknown initial horseshoe
temperature and the recorded answer do not occur here.
-/
structure MatchesProblemReadouts
    (setup : HorseshoeWaterCalorimetrySetup) : Prop where
  horseshoeMassKilograms :
    massInKilograms (setup.massAt .horseshoe) = 2 / 5
  waterVolumeLiters : volumeInLiters setup.waterVolume = 5 / 4
  ironPotMassKilograms : massInKilograms (setup.massAt .pot) = 3 / 10
  initialWaterTemperatureCelsius :
    (setup.initialTemperatureAt .water).degreesCelsius = 20
  initialPotTemperatureCelsius :
    (setup.initialTemperatureAt .pot).degreesCelsius = 20
  finalEquilibriumTemperatureCelsius :
    setup.finalEquilibriumTemperature.degreesCelsius = 25

/-- Qualitative facts recorded from the supplied blacksmithing image. -/
structure MatchesSuppliedBlacksmithFigure
    (figure : SuppliedBlacksmithFigure) : Prop where
  everyNamedObjectIsShown : ∀ object, figure.showsObject object = true
  glowingMetalIsOrange : figure.horseshoeGlowColor = .orange
  horseshoeHeldWithTongs : figure.tongsHoldHorseshoe = true
  horseshoeIsAgainstAnvil :
    figure.horseshoePositionedAgainstAnvil = true
  backgroundIsSoftlyBlurred : figure.backgroundSoftlyBlurred = true
  noPrintedText : figure.containsPrintedText = false

/--
Rounded textbook reference data needed for the estimate: water density is
`1 kg/L`, iron specific heat is `450 J/(kg K)`, and water specific heat is
`4186 J/(kg K)`.  These values are not printed in the problem, so they are
kept separate from `MatchesProblemReadouts`.
-/
structure UsesReferenceIronAndWaterThermalData
    (setup : HorseshoeWaterCalorimetrySetup) : Prop where
  waterDensityKilogramsPerLiter :
    massDensityInKilogramsPerLiter setup.waterMassDensity = 1
  ironSpecificHeatJoulesPerKilogramKelvin :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacityAt .iron) = 450
  waterSpecificHeatJoulesPerKilogramKelvin :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacityAt .liquidWater) = 4186

/-- Positivity conditions selecting physically meaningful quantities. -/
structure HasPhysicalHorseshoeWaterParameters
    (setup : HorseshoeWaterCalorimetrySetup) : Prop where
  positiveMasses : ∀ body, 0 < massInKilograms (setup.massAt body)
  positiveWaterVolume : 0 < volumeInLiters setup.waterVolume
  positiveWaterDensity :
    0 < massDensityInKilogramsPerLiter setup.waterMassDensity
  positiveSpecificHeats : ∀ material,
    0 < specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacityAt material)
  positiveInitialAbsoluteTemperatures : ∀ body,
    0 < (setup.initialTemperatureAt body).absoluteTemperature.toReal
  positiveFinalAbsoluteTemperature :
    0 < setup.finalEquilibriumTemperature.absoluteTemperature.toReal

/-- The bulk relation `m = ρV` for the water in compatible unit readouts. -/
structure SatisfiesWaterBulkMassLaw
    (setup : HorseshoeWaterCalorimetrySetup) : Prop where
  waterMassEqualsDensityTimesVolume :
    massInKilograms (setup.massAt .water) =
      massDensityInKilogramsPerLiter setup.waterMassDensity *
        volumeInLiters setup.waterVolume

/--
The governing three-body calorimetry laws: each signed heat is `mc(Tf - Ti)`,
an isolated boundary supplies zero heat, and all four signed transfers sum to
zero.  These are uniform laws and do not encode the requested temperature.
-/
structure SatisfiesIsolatedHorseshoeWaterCalorimetry
    (setup : HorseshoeWaterCalorimetrySetup) : Prop where
  sensibleHeatLaw : ∀ body,
    heatInJoules (setup.heatAbsorbedDuringContact body) =
      massInKilograms (setup.massAt body) *
        specificHeatInJoulesPerKilogramKelvin
          (setup.specificHeatCapacityAt (setup.materialAt body)) *
        (setup.finalEquilibriumTemperature.degreesCelsius -
          (setup.initialTemperatureAt body).degreesCelsius)
  isolatedBoundaryHasZeroHeatTransfer :
    setup.exteriorBoundary = .isolated →
      heatInJoules setup.heatTransferredFromSurroundings = 0
  totalHeatBalance :
    heatInJoules (setup.heatAbsorbedDuringContact .horseshoe) +
          heatInJoules (setup.heatAbsorbedDuringContact .water) +
        heatInJoules (setup.heatAbsorbedDuringContact .pot) +
      heatInJoules setup.heatTransferredFromSurroundings = 0

/-! ## Displayed choices and current conclusions -/

/-- Labels of the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Celsius values printed beside the four answer labels. -/
def displayedTemperatureInDegreesCelsius : AnswerChoice → ℝ
  | .A => 140
  | .B => 150
  | .C => 160
  | .D => 170

/-- The answer label recorded in the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The calculated temperature rounds to the displayed ten-degree value. -/
def RoundsToDisplayedTenDegrees
    (setup : HorseshoeWaterCalorimetrySetup)
    (choice : AnswerChoice) : Prop :=
  |initialHorseshoeTemperatureInDegreesCelsius setup -
      displayedTemperatureInDegreesCelsius choice| < 5

/-- The selected displayed value is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedTemperature
    (setup : HorseshoeWaterCalorimetrySetup)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |initialHorseshoeTemperatureInDegreesCelsius setup -
        displayedTemperatureInDegreesCelsius choice| <
      |initialHorseshoeTemperatureInDegreesCelsius setup -
        displayedTemperatureInDegreesCelsius other|

/-- The density and volume readouts determine the water mass as `5/4 kg`. -/
lemma water_mass_from_density_and_volume
    (setup : HorseshoeWaterCalorimetrySetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hThermalData : UsesReferenceIronAndWaterThermalData setup)
    (hMass : SatisfiesWaterBulkMassLaw setup) :
    massInKilograms (setup.massAt .water) = 5 / 4 := by
  calc
    massInKilograms (setup.massAt .water) =
        massDensityInKilogramsPerLiter setup.waterMassDensity *
          volumeInLiters setup.waterVolume :=
      hMass.waterMassEqualsDensityTimesVolume
    _ = 1 * (5 / 4 : ℝ) := by
      rw [hThermalData.waterDensityKilogramsPerLiter,
        hReadouts.waterVolumeLiters]
    _ = 5 / 4 := by norm_num

/--
Substitution into the isolated heat balance gives `12535/72 °C`, approximately
`174.10 °C`.  The requested temperature remains on the conclusion side.
-/
lemma initial_horseshoe_temperature_exact
    (setup : HorseshoeWaterCalorimetrySetup)
    (hScenario : MatchesHorseshoeWaterScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hThermalData : UsesReferenceIronAndWaterThermalData setup)
    (hMass : SatisfiesWaterBulkMassLaw setup)
    (hCalorimetry : SatisfiesIsolatedHorseshoeWaterCalorimetry setup) :
    initialHorseshoeTemperatureInDegreesCelsius setup =
      (12535 / 72 : ℝ) := by
  have hWaterMass :
      massInKilograms (setup.massAt .water) = (5 / 4 : ℝ) :=
    water_mass_from_density_and_volume setup hReadouts hThermalData hMass
  have hHorseshoeHeat := hCalorimetry.sensibleHeatLaw .horseshoe
  rw [hScenario.horseshoeIsIron, hReadouts.horseshoeMassKilograms,
    hThermalData.ironSpecificHeatJoulesPerKilogramKelvin,
    hReadouts.finalEquilibriumTemperatureCelsius] at hHorseshoeHeat
  change
    heatInJoules (setup.heatAbsorbedDuringContact .horseshoe) =
      (2 / 5 : ℝ) * 450 *
        (25 - initialHorseshoeTemperatureInDegreesCelsius setup)
    at hHorseshoeHeat
  have hWaterHeat := hCalorimetry.sensibleHeatLaw .water
  rw [hScenario.waterIsLiquidWater, hWaterMass,
    hThermalData.waterSpecificHeatJoulesPerKilogramKelvin,
    hReadouts.finalEquilibriumTemperatureCelsius,
    hReadouts.initialWaterTemperatureCelsius] at hWaterHeat
  have hPotHeat := hCalorimetry.sensibleHeatLaw .pot
  rw [hScenario.potIsIron, hReadouts.ironPotMassKilograms,
    hThermalData.ironSpecificHeatJoulesPerKilogramKelvin,
    hReadouts.finalEquilibriumTemperatureCelsius,
    hReadouts.initialPotTemperatureCelsius] at hPotHeat
  have hExteriorHeat :
      heatInJoules setup.heatTransferredFromSurroundings = 0 :=
    hCalorimetry.isolatedBoundaryHasZeroHeatTransfer
      hScenario.modeledBoundaryIsIsolated
  have hBalance := hCalorimetry.totalHeatBalance
  rw [hHorseshoeHeat, hWaterHeat, hPotHeat, hExteriorHeat] at hBalance
  norm_num at hBalance ⊢
  linarith

/--
The model estimate is approximately `174.10 °C`, so the requested estimate is
the displayed `170 °C` choice D.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0485:target`.
-/
theorem problem_phyx_mini_0485
    (setup : HorseshoeWaterCalorimetrySetup)
    (hScenario : MatchesHorseshoeWaterScenario setup)
    (hFigure : MatchesSuppliedBlacksmithFigure setup.figure)
    (hReadouts : MatchesProblemReadouts setup)
    (hThermalData : UsesReferenceIronAndWaterThermalData setup)
    (hPhysical : HasPhysicalHorseshoeWaterParameters setup)
    (hMass : SatisfiesWaterBulkMassLaw setup)
    (hCalorimetry : SatisfiesIsolatedHorseshoeWaterCalorimetry setup) :
    initialHorseshoeTemperatureInDegreesCelsius setup =
        (12535 / 72 : ℝ) ∧
      RoundsToDisplayedTenDegrees setup .D ∧
      IsUniqueClosestDisplayedTemperature setup .D ∧
      recordedDatasetAnswer = .D := by
  have hExact :=
    initial_horseshoe_temperature_exact setup hScenario hReadouts
      hThermalData hMass hCalorimetry
  refine ⟨hExact, ?_, ?_, rfl⟩
  · unfold RoundsToDisplayedTenDegrees
    rw [hExact]
    norm_num [displayedTemperatureInDegreesCelsius]
  · unfold IsUniqueClosestDisplayedTemperature
    intro other hOther
    rw [hExact]
    cases other <;>
      norm_num [displayedTemperatureInDegreesCelsius] at *

end PhyXMiniProblems.ProblemPhyXMini0485
