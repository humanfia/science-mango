import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0466

open Dimension

/-!
# Heat conduction into a Styrofoam cooler

The cooler has total wall area (including its lid) `0.80 m²`, wall thickness
`2.0 cm`, contents at `0 °C`, and an outside-wall temperature of `30 °C`.
The supplied image shows three heat arrows directed toward the cooler.  The
dataset records answer `B`, namely `32.4 J/s`, but the supplied source gives no
Styrofoam conductivity or table citation.  Consequently that answer is retained
only as metadata, and the physical conclusion remains symbolic in the unknown
conductivity.

Physical area, thickness, thermal conductivity, and heat-flow rate are modeled
as unit-independent Physlib quantities.  Real numbers occur only as calibrated
unit readouts and displayed answer values.

Assumption/target split:

* governing laws: thermal equilibrium of the contents with the cooler
  interior and steady one-dimensional Fourier conduction through a uniform
  plane wall;
* previous-part results: none;
* data and figure evidence: Styrofoam walls, area including the lid, thickness,
  temperatures, contents, inward arrows, displayed choices, and recorded label
  `B`; no numerical conductivity is supplied;
* target conclusion: the inward rate is `1200` times the unknown Styrofoam
  conductivity when both are expressed in the coherent SI readouts below.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative wall thickness, with physical dimension length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- The physical dimension of power, `mass * length² / time³`. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension of thermal conductivity, `power / (length * temperature)`. -/
def thermalConductivityDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

/-- A nonnegative rate of energy transfer, whose coherent SI unit is the watt. -/
abbrev PowerQuantity : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- A nonnegative thermal conductivity, with SI unit watt per metre-kelvin. -/
abbrev ThermalConductivityQuantity : Type :=
  Dimensionful (WithDim thermalConductivityDimension NNReal)

/-- Read a physical length using a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of the cooler-wall thickness. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the problem statement. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout in watts per metre-kelvin. -/
def thermalConductivityInWattsPerMeterKelvin
    (conductivity : ThermalConductivityQuantity) : ℝ :=
  ((conductivity UnitChoices.SI).val : ℝ)

/-- Coherent-SI watt readout of an energy-transfer rate. -/
def heatFlowRateInWatts (rate : PowerQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-- A watt is one joule per second, the unit printed in the answer list. -/
def heatFlowRateInJoulesPerSecond (rate : PowerQuantity) : ℝ :=
  heatFlowRateInWatts rate

/-- Read absolute temperature in kelvins from its zero-preserving storage unit. -/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Celsius is an affine scalar readout of a physical absolute temperature. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - (5463 / 20 : ℝ)

/-- Conversion between the two length readouts used in the model. -/
lemma lengthInMeters_eq_centimeters_div_hundred
    (length : LengthQuantity) :
    lengthInMeters length = lengthInCentimeters length / 100 := by
  sorry

/-! ## Cooler contents and primary-image vocabulary -/

/-- The wall material named by the problem. -/
inductive CoolerWallMaterial where
  | styrofoam
  | other
  deriving DecidableEq, Repr

/-- The three classes of contents explicitly listed in the prose. -/
inductive CoolerContent where
  | ice
  | water
  | omniColaCan
  deriving DecidableEq, Fintype, Repr

/-- Physical interpretation of the purple arrows in the supplied image. -/
inductive FigureArrowMeaning where
  | heatIntoCooler
  | heatOutOfCooler
  | other
  deriving DecidableEq, Repr

/--
Primary-image evidence.  The picture provides qualitative context and an
arrow count/direction, but no geometric or material numerical readout.
-/
structure CoolerFigure where
  showsCooler : Bool
  showsIceCubes : Bool
  showsBeverageCans : Bool
  heatArrowCount : Nat
  heatArrowMeaning : FigureArrowMeaning
  showsBottleMarked15 : Bool

/-! ## Physical setup and input predicates -/

/-- Independent physical quantities describing the cooler experiment. -/
structure StyrofoamCoolerSetup where
  wallMaterial : CoolerWallMaterial
  totalWallArea : DimArea
  wallThickness : LengthQuantity
  wallAreaIncludesLid : Bool
  contentPresent : CoolerContent → Bool
  interiorTemperature : Temperature
  contentTemperature : CoolerContent → Temperature
  outsideWallTemperature : Temperature
  temperatureStorageUnit : TemperatureUnit
  styrofoamThermalConductivity : ThermalConductivityQuantity
  heatFlowIntoCooler : PowerQuantity
  figure : CoolerFigure

/-- Qualitative setup stated in the prose, independent of the requested rate. -/
structure MatchesStyrofoamCoolerScenario
    (setup : StyrofoamCoolerSetup) : Prop where
  wallIsStyrofoam : setup.wallMaterial = .styrofoam
  statedAreaIncludesLid : setup.wallAreaIncludesLid = true
  everyListedContentIsPresent : ∀ content, setup.contentPresent content = true

/-- Exact scalar measurements printed in the problem statement. -/
structure MatchesCoolerMeasurementData
    (setup : StyrofoamCoolerSetup) : Prop where
  temperatureStoredInKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  totalWallAreaSquareMeters :
    areaInSquareMeters setup.totalWallArea = 4 / 5
  wallThicknessCentimeters :
    lengthInCentimeters setup.wallThickness = 2
  interiorTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      setup.interiorTemperature = 0
  everyContentTemperatureCelsius : ∀ content,
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      (setup.contentTemperature content) = 0
  outsideWallTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      setup.outsideWallTemperature = 30

/-- Qualitative facts read from the supplied cooler image. -/
structure MatchesSuppliedCoolerFigure
    (setup : StyrofoamCoolerSetup) : Prop where
  coolerShown : setup.figure.showsCooler = true
  iceShown : setup.figure.showsIceCubes = true
  beverageCansShown : setup.figure.showsBeverageCans = true
  threeHeatArrowsShown : setup.figure.heatArrowCount = 3
  arrowsIndicateHeatIntoCooler :
    setup.figure.heatArrowMeaning = .heatIntoCooler
  bottleMarked15Shown : setup.figure.showsBottleMarked15 = true

/-- Positivity and hot-outside/cold-inside conditions for inward conduction. -/
structure HasPhysicalCoolerParameters
    (setup : StyrofoamCoolerSetup) : Prop where
  wallAreaPositive : 0 < areaInSquareMeters setup.totalWallArea
  wallThicknessPositive : 0 < lengthInMeters setup.wallThickness
  thermalConductivityPositive :
    0 < thermalConductivityInWattsPerMeterKelvin
      setup.styrofoamThermalConductivity
  interiorAbsoluteTemperaturePositive :
    0 < temperatureInKelvin setup.temperatureStorageUnit
      setup.interiorTemperature
  outsideIsWarmerThanInterior :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
        setup.interiorTemperature <
      temperatureInDegreesCelsius setup.temperatureStorageUnit
        setup.outsideWallTemperature

/-! ## Governing laws -/

/--
The contents are equilibrated with the cooler interior, and the inward heat
rate is the magnitude supplied by Fourier's steady plane-wall law
`Q̇ = k A (T_out - T_in) / L`.  This field is a general physical relation;
it contains no numerical answer or answer-choice label.
-/
structure SatisfiesSteadyPlaneWallConduction
    (setup : StyrofoamCoolerSetup) : Prop where
  contentsInThermalEquilibriumWithInterior : ∀ content,
    setup.contentTemperature content = setup.interiorTemperature
  fourierPlaneWallLaw :
    heatFlowRateInWatts setup.heatFlowIntoCooler =
      thermalConductivityInWattsPerMeterKelvin
          setup.styrofoamThermalConductivity *
        areaInSquareMeters setup.totalWallArea *
        (temperatureInDegreesCelsius setup.temperatureStorageUnit
            setup.outsideWallTemperature -
          temperatureInDegreesCelsius setup.temperatureStorageUnit
            setup.interiorTemperature) /
        lengthInMeters setup.wallThickness

/-! ## Displayed answers and target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Joule-per-second value printed beside each answer label. -/
def displayedHeatFlowInJoulesPerSecond : AnswerChoice → ℝ
  | .A => 67 / 2
  | .B => 162 / 5
  | .C => 174 / 5
  | .D => 186 / 5

/-- Dataset answer-label metadata; it does not determine the physical rate. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
Steady conduction through the cooler walls and the supplied measurements give
`Qdot = k * 0.80 * (30 - 0) / 0.020 = 1200 * k`, where `k` is the unknown
Styrofoam conductivity in watts per metre-kelvin.  The source provides no value
for `k`, so this declaration neither asserts a numerical rate nor selects a
physical answer choice.

This declaration formalizes `thm:physics:phyx_mini_0466:target`.  The requested
symbolic rate occurs only in this conclusion, not in any scenario, measurement,
figure, physicality, or governing-law field.
-/
theorem problem_phyx_mini_0466
    (setup : StyrofoamCoolerSetup)
    (hScenario : MatchesStyrofoamCoolerScenario setup)
    (hData : MatchesCoolerMeasurementData setup)
    (hFigure : MatchesSuppliedCoolerFigure setup)
    (hPhysical : HasPhysicalCoolerParameters setup)
    (hLaws : SatisfiesSteadyPlaneWallConduction setup) :
    heatFlowRateInJoulesPerSecond setup.heatFlowIntoCooler =
      thermalConductivityInWattsPerMeterKelvin
          setup.styrofoamThermalConductivity * 1200 := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0466
