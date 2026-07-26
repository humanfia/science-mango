import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0455

open Dimension

/-!
# Final temperature of a copper block immersed in an insulated oil bath

A `1 L` copper block initially at `500 °C` is fully submerged in a `200 L`
oil bath initially at `20 °C`.  The copper and oil exchange sensible heat but
the combined system exchanges no heat with its surroundings.

The primary image shows a rectangular region labelled `Copper` completely
inside a larger region labelled `Oil`.  Blue horizontal strokes depict the
oil, a thick grey outline depicts the container, and diagonal hatching depicts
the exterior.  The image supplies no additional numerical scale.

Volume, mass, mass density, specific heat capacity, heat capacity, absolute
temperature, and heat remain dimensionful physical quantities.  Real numbers
below occur only as explicitly named SI or display-unit readouts, calibrated
material-property data, and displayed answer values.

Because the problem gives volumes rather than masses and does not identify the
oil grade or print a property table, the source data do not determine a
numerical final temperature.  The source-supported target below therefore
keeps the four material-property readouts free and gives the symbolic
equilibrium formula.  `UsesRoundedClassroomMaterialData` records a separate,
explicitly non-source calibration under which one can recover the dataset's
recorded `25 °C` estimate; that conditional calculation is not the problem's
physical conclusion.

Assumption/target split:

* governing laws: `m = ρV`, `C = mc`, `Q = C(T_f - T_i)`, and isolated energy
  balance;
* previous-part results: none;
* figure/data readouts: the two volumes, two initial temperatures, insulated
  boundary, and the pictured copper-in-oil immersion geometry;
* current target conclusion: the symbolic equilibrium temperature with the
  unspecified copper and oil density/specific-heat readouts still visible.

The displayed choices and recorded answer D are retained as dataset metadata.
Neither a displayed temperature nor an answer choice is asserted by the main
theorem.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass carrying dimension `M`. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative mass density carrying dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/--
Specific heat capacity, with dimension `L² T⁻² Θ⁻¹`, read in
joules per kilogram-kelvin in coherent SI units.
-/
abbrev SpecificHeatCapacityQuantity : Type :=
  Dimensionful
    (WithDim (L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/--
Heat capacity of a complete body, with dimension `M L² T⁻² Θ⁻¹`, read in
joules per kelvin in coherent SI units.
-/
abbrev HeatCapacityQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- Signed physical heat represented by Physlib's dimensionful energy type. -/
abbrev HeatQuantity : Type := DimEnergy

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in litres, using `1 m³ = 1000 L`. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read a physical mass in coherent SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a mass density in coherent SI kilograms per cubic metre. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Read a specific heat capacity in joules per kilogram-kelvin. -/
def specificHeatInJoulesPerKilogramKelvin
    (specificHeat : SpecificHeatCapacityQuantity) : ℝ :=
  ((specificHeat UnitChoices.SI).val : ℝ)

/-- Read a body's heat capacity in joules per kelvin. -/
def heatCapacityInJoulesPerKelvin
    (heatCapacity : HeatCapacityQuantity) : ℝ :=
  ((heatCapacity UnitChoices.SI).val : ℝ)

/-- Read signed physical heat in joules. -/
def heatInJoules (heat : HeatQuantity) : ℝ :=
  (heat UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read an absolute `Temperature` in kelvins from its storage-unit scale. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Convert an absolute-temperature readout to degrees Celsius. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - (27315 / 100 : ℝ)

/-! ## Bodies, thermal model, and primary-image vocabulary -/

/-- The two finite bodies that exchange heat. -/
inductive ThermalBody where
  | copperBlock
  | oilBath
  deriving DecidableEq, Fintype, Repr

/-- Material identity specified for each body. -/
inductive MaterialKind where
  | copper
  | oil
  deriving DecidableEq, Repr

/-- Thermal character of the combined copper-oil system boundary. -/
inductive SystemBoundaryKind where
  | thermallyIsolatedFromSurroundings
  | exchangesHeatWithSurroundings
  deriving DecidableEq, Repr

/-- Geometric/contact relation between the copper and the oil. -/
inductive ThermalContactKind where
  | copperFullySubmergedInOil
  | bodiesNotInContact
  deriving DecidableEq, Repr

/-- Literal material labels visible in the supplied image. -/
inductive FigureLabel where
  | copper
  | oil
  deriving DecidableEq, Fintype, Repr

/-- Qualitative data transcribed from image `455.png`. -/
structure CopperInOilFigure where
  labelShown : FigureLabel → Bool
  copperDrawnAsRectangle : Bool
  copperRectangleInsideOilRegion : Bool
  oilShownByBlueHorizontalStrokes : Bool
  thickContainerWallShown : Bool
  exteriorDiagonalHatchingShown : Bool

/-!
Independent physical observables for the immersion experiment.  The common
final temperature and the heat received by each body are not defined from an
answer choice; the governing calorimetry laws below constrain them.
-/
structure CopperOilCalorimetrySetup where
  material : ThermalBody → MaterialKind
  volume : ThermalBody → VolumeQuantity
  density : ThermalBody → MassDensityQuantity
  mass : ThermalBody → MassQuantity
  specificHeatCapacity : ThermalBody → SpecificHeatCapacityQuantity
  heatCapacity : ThermalBody → HeatCapacityQuantity
  initialTemperature : ThermalBody → Temperature
  commonFinalTemperature : Temperature
  heatTransferredInto : ThermalBody → HeatQuantity
  temperatureStorageUnit : TemperatureUnit
  systemBoundary : SystemBoundaryKind
  thermalContact : ThermalContactKind
  figure : CopperInOilFigure

/-- Initial-temperature readout of one body in degrees Celsius. -/
def initialTemperatureInDegreesCelsius
    (setup : CopperOilCalorimetrySetup) (body : ThermalBody) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    (setup.initialTemperature body)

/-- Requested common final-temperature readout in degrees Celsius. -/
def finalTemperatureInDegreesCelsius
    (setup : CopperOilCalorimetrySetup) : ℝ :=
  temperatureInDegreesCelsius setup.temperatureStorageUnit
    setup.commonFinalTemperature

/-! ## Problem data, calibrated properties, and governing laws -/

/-!
The prose data and qualitative primary-image readouts.  This premise records
the two stated volumes, the two initial temperatures, the insulated boundary,
and the displayed immersion geometry.  It contains no final-temperature or
answer-choice value.
-/
structure MatchesProblemStatementAndPrimaryFigure
    (setup : CopperOilCalorimetrySetup) : Prop where
  copperBlockMaterial : setup.material .copperBlock = .copper
  oilBathMaterial : setup.material .oilBath = .oil
  copperBlockVolumeLiters : volumeInLiters (setup.volume .copperBlock) = 1
  oilBathVolumeLiters : volumeInLiters (setup.volume .oilBath) = 200
  temperaturesStoredInKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  copperInitialTemperatureCelsius :
    initialTemperatureInDegreesCelsius setup .copperBlock = 500
  oilInitialTemperatureCelsius :
    initialTemperatureInDegreesCelsius setup .oilBath = 20
  noHeatTransferWithSurroundings :
    setup.systemBoundary = .thermallyIsolatedFromSurroundings
  copperIsFullySubmerged :
    setup.thermalContact = .copperFullySubmergedInOil
  everyPrintedLabelShown : ∀ label, setup.figure.labelShown label = true
  copperIsRectangularInFigure : setup.figure.copperDrawnAsRectangle = true
  copperLiesInsideOilRegion :
    setup.figure.copperRectangleInsideOilRegion = true
  oilHasBlueHorizontalStrokes :
    setup.figure.oilShownByBlueHorizontalStrokes = true
  containerWallIsShown : setup.figure.thickContainerWallShown = true
  exteriorHatchingIsShown :
    setup.figure.exteriorDiagonalHatchingShown = true

/-!
Rounded classroom material data required to turn the stated volumes into heat
capacities: copper density `8960 kg/m³`, oil density `800 kg/m³`, copper
specific heat `385 J/(kg K)`, and oil specific heat `2000 J/(kg K)`.

These are independent material-property calibrations, not the requested final
temperature.
-/
structure UsesRoundedClassroomMaterialData
    (setup : CopperOilCalorimetrySetup) : Prop where
  copperDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter (setup.density .copperBlock) = 8960
  oilDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter (setup.density .oilBath) = 800
  copperSpecificHeatJoulesPerKilogramKelvin :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity .copperBlock) = 385
  oilSpecificHeatJoulesPerKilogramKelvin :
    specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity .oilBath) = 2000

/-- Positivity conditions selecting the physical branch of the model. -/
structure HasPhysicalThermalParameters
    (setup : CopperOilCalorimetrySetup) : Prop where
  positiveVolume : ∀ body,
    0 < volumeInCubicMeters (setup.volume body)
  positiveDensity : ∀ body,
    0 < densityInKilogramsPerCubicMeter (setup.density body)
  positiveMass : ∀ body,
    0 < massInKilograms (setup.mass body)
  positiveSpecificHeat : ∀ body,
    0 < specificHeatInJoulesPerKilogramKelvin
      (setup.specificHeatCapacity body)
  positiveHeatCapacity : ∀ body,
    0 < heatCapacityInJoulesPerKelvin (setup.heatCapacity body)
  positiveInitialAbsoluteTemperature : ∀ body,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.initialTemperature body)
  positiveFinalAbsoluteTemperature :
    0 < temperatureInKelvins setup.temperatureStorageUnit
      setup.commonFinalTemperature

/-!
Constant-specific-heat calorimetry for both bodies:

* `m = ρV` converts the given volumes to masses;
* `C = mc` converts masses and specific heats to body heat capacities;
* `Q = C(T_f - T_i)` gives the signed sensible heat into each body; and
* `Q_copper + Q_oil = 0` expresses the isolated-system energy balance.

All four fields are generic laws over the two bodies and contain no numerical
final temperature or answer-choice value.
-/
structure SatisfiesIsolatedConstantSpecificHeatCalorimetry
    (setup : CopperOilCalorimetrySetup) : Prop where
  massFromDensityAndVolume : ∀ body,
    massInKilograms (setup.mass body) =
      densityInKilogramsPerCubicMeter (setup.density body) *
        volumeInCubicMeters (setup.volume body)
  heatCapacityFromMassAndSpecificHeat : ∀ body,
    heatCapacityInJoulesPerKelvin (setup.heatCapacity body) =
      massInKilograms (setup.mass body) *
        specificHeatInJoulesPerKilogramKelvin
          (setup.specificHeatCapacity body)
  sensibleHeatIntoEachBody : ∀ body,
    heatInJoules (setup.heatTransferredInto body) =
      heatCapacityInJoulesPerKelvin (setup.heatCapacity body) *
        (temperatureInKelvins setup.temperatureStorageUnit
            setup.commonFinalTemperature -
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.initialTemperature body))
  isolatedEnergyBalance :
    heatInJoules (setup.heatTransferredInto .copperBlock) +
      heatInJoules (setup.heatTransferredInto .oilBath) = 0

/-!
The source-supplied volumes and initial temperatures determine the equilibrium
temperature only up to the copper and oil material properties.  Cancelling the
common litre-to-cubic-metre scale gives this symbolic Celsius relation.  It
uses no supplemental density or specific-heat calibration and therefore makes
the source's numerical underdetermination explicit in the formal model.
-/
lemma finalTemperatureInDegreesCelsius_fromSourceData
    (setup : CopperOilCalorimetrySetup)
    (_data : MatchesProblemStatementAndPrimaryFigure setup)
    (_physical : HasPhysicalThermalParameters setup)
    (_laws : SatisfiesIsolatedConstantSpecificHeatCalorimetry setup) :
    finalTemperatureInDegreesCelsius setup =
      (densityInKilogramsPerCubicMeter (setup.density .copperBlock) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .copperBlock) * 500 +
          200 * densityInKilogramsPerCubicMeter (setup.density .oilBath) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .oilBath) * 20) /
        (densityInKilogramsPerCubicMeter (setup.density .copperBlock) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .copperBlock) +
          200 * densityInKilogramsPerCubicMeter (setup.density .oilBath) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .oilBath)) := by
  sorry

/-!
Under the explicitly supplemental rounded material calibration, the
heat-balance model has the exact Celsius solution `1269500 / 50539`,
approximately `25.12 °C`.  This conditional diagnostic is not a conclusion
from the supplied problem data.
-/
lemma finalTemperatureInDegreesCelsius_exact
    (setup : CopperOilCalorimetrySetup)
    (_data : MatchesProblemStatementAndPrimaryFigure setup)
    (_calibration : UsesRoundedClassroomMaterialData setup)
    (_physical : HasPhysicalThermalParameters setup)
    (_laws : SatisfiesIsolatedConstantSpecificHeatCalorimetry setup) :
    finalTemperatureInDegreesCelsius setup =
      (1269500 / 50539 : ℝ) := by
  sorry

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Whole-degree Celsius temperature printed beside each answer label. -/
def displayedTemperatureDegreesCelsius : AnswerChoice → ℝ
  | .A => 243
  | .B => 110
  | .C => 56
  | .D => 25

/-- Dataset metadata records answer choice D. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- The modeled final temperature rounds to a displayed whole degree. -/
def RoundsToDisplayedWholeDegree
    (setup : CopperOilCalorimetrySetup) (choice : AnswerChoice) : Prop :=
  |finalTemperatureInDegreesCelsius setup -
      displayedTemperatureDegreesCelsius choice| < (1 / 2 : ℝ)

/-- The selected displayed temperature is closer than every alternative. -/
def IsUniqueClosestDisplayedTemperature
    (setup : CopperOilCalorimetrySetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |finalTemperatureInDegreesCelsius setup -
        displayedTemperatureDegreesCelsius choice| <
      |finalTemperatureInDegreesCelsius setup -
        displayedTemperatureDegreesCelsius other|

/-!
The isolated copper-oil heat balance gives the strongest conclusion supported
by the supplied source: a symbolic weighted-average formula in which the
unreported copper and oil material properties remain free.  In particular,
this theorem does not assume `UsesRoundedClassroomMaterialData` and does not
assert that the final temperature rounds to the recorded `25 °C` choice.

The declaration name for blueprint label
`thm:physics:phyx_mini_0455:target` is retained, while its statement is repaired
according to the final formalization gate's underdetermination finding.
-/
theorem problem_phyx_mini_0455
    (setup : CopperOilCalorimetrySetup)
    (_data : MatchesProblemStatementAndPrimaryFigure setup)
    (_physical : HasPhysicalThermalParameters setup)
    (_laws : SatisfiesIsolatedConstantSpecificHeatCalorimetry setup) :
    finalTemperatureInDegreesCelsius setup =
      (densityInKilogramsPerCubicMeter (setup.density .copperBlock) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .copperBlock) * 500 +
          200 * densityInKilogramsPerCubicMeter (setup.density .oilBath) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .oilBath) * 20) /
        (densityInKilogramsPerCubicMeter (setup.density .copperBlock) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .copperBlock) +
          200 * densityInKilogramsPerCubicMeter (setup.density .oilBath) *
            specificHeatInJoulesPerKilogramKelvin
              (setup.specificHeatCapacity .oilBath)) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0455
