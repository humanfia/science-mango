import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0440

open Dimension

/-!
# Petcock mass for boiling at 120 degrees Celsius

A pressure cooker has a tightly screwed lid and a `5 mm²` opening covered by
a weighted petcock. Saturated steam beneath the petcock pushes upward, while
the outside atmosphere and the petcock's weight act downward. At the desired
`120 °C` boiling point the petcock is at the threshold of lifting.

Pressure, area, mass, acceleration, and absolute temperature retain physical
quantity types. Real numbers occur only as named-unit readouts, calibrated
steam-table data, and displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-!
An absolute temperature and the zero-preserving unit in which its magnitude
is stored. The affine Celsius offset is applied only by the scalar readout
below, rather than treating Celsius as an absolute-temperature unit.
-/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  storageUnit : TemperatureUnit

/-- Read an area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Square-metre readout used in the pressure-force law. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Square-millimetre readout used for the cooker opening. -/
def areaInSquareMillimeters (area : DimArea) : ℝ :=
  areaReadout LengthUnit.millimeters area

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Kilogram readout used in the weight law. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Gram readout used by the displayed choices. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Pascal readout of an absolute physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used by the atmospheric and steam-table data. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Kelvin readout of a measured absolute temperature. -/
def temperatureInKelvin (temperature : MeasuredTemperature) : ℝ :=
  let unitRatio : NNReal :=
    temperature.storageUnit / TemperatureUnit.kelvin
  temperature.absoluteTemperature.toReal * (unitRatio : ℝ)

/-- Celsius readout, with `273.15 K` represented exactly as `5463 / 20`. -/
def temperatureInDegreesCelsius
    (temperature : MeasuredTemperature) : ℝ :=
  temperatureInKelvin temperature - 5463 / 20

/-- Normal force in newtons exerted by a uniform pressure on the opening. -/
def pressureForceInNewtons (pressure : DimPressure) (area : DimArea) : ℝ :=
  pressureInPascals pressure * areaInSquareMeters area

/-- Downward petcock weight in newtons. -/
def weightInNewtons
    (mass : MassQuantity) (acceleration : AccelerationQuantity) : ℝ :=
  massInKilograms mass *
    accelerationInMetersPerSecondSquared acceleration

/-! ## Apparatus, phases, and primary-figure vocabulary -/

/-- The working liquid whose saturated vapor fills the cooker headspace. -/
inductive WorkingFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-- Mechanical state of the weighted vent at the specified boiling point. -/
inductive PetcockState where
  | seated
  | incipientLift
  | freelyVenting
  deriving DecidableEq, Repr

/-- Literal labels visible in the supplied raster. -/
inductive FigureLabel where
  | liquid
  | steamOrVapor
  | escapingSteam
  deriving DecidableEq, Fintype, Repr

/-- Vertically ordered regions distinguished by the supplied raster. -/
inductive FigureRegion where
  | lowerCookerInterior
  | upperCookerInterior
  | aboveLid
  deriving DecidableEq, Repr

/-!
Qualitative and geometric information read from the primary image. This
record contains no numerical mass, pressure, area, or temperature datum.
-/
structure PressureCookerFigure where
  printedText : FigureLabel → String
  labelRegion : FigureLabel → FigureRegion
  showsClosedContainer : Bool
  showsDomedLid : Bool
  showsPetcockAboveOpening : Bool
  showsLiquidBelowVapor : Bool
  showsSteamEscapingPastPetcock : Bool

/-!
Independent physical quantities at the requested operating point. In
particular, `petcockMass` is not defined using a displayed answer, and the
saturation-pressure function represents a steam table independently of the
actual cooker pressure.
-/
structure PressureCookerSetup where
  fluid : WorkingFluid
  lidScrewedTight : Bool
  petcockCoversOpening : Bool
  petcockStateAtBoiling : PetcockState
  openingArea : DimArea
  boilingTemperature : MeasuredTemperature
  outsideAtmosphericPressure : DimPressure
  steamPressureAtBoiling : DimPressure
  saturationPressureAt : MeasuredTemperature → DimPressure
  petcockMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  figure : PressureCookerFigure

/-! ## Scenario, readouts, calibrations, and governing laws -/

/-- Qualitative apparatus assumptions stated in the problem. -/
structure MatchesPressureCookerScenario
    (setup : PressureCookerSetup) : Prop where
  workingFluidIsWater : setup.fluid = .water
  lidIsScrewedTight : setup.lidScrewedTight = true
  petcockClosesOpening : setup.petcockCoversOpening = true
  ventIsAtLiftThreshold : setup.petcockStateAtBoiling = .incipientLift

/-!
Primary-image evidence: liquid occupies the lower region, steam or vapor the
upper region, and escaping steam is drawn above the lid-mounted petcock.
-/
structure MatchesSuppliedPressureCookerFigure
    (setup : PressureCookerSetup) : Prop where
  liquidText : setup.figure.printedText .liquid = "Liquid"
  vaporText : setup.figure.printedText .steamOrVapor = "Steam\nor vapor"
  escapingSteamText : setup.figure.printedText .escapingSteam = "Steam"
  liquidRegion : setup.figure.labelRegion .liquid = .lowerCookerInterior
  vaporRegion : setup.figure.labelRegion .steamOrVapor = .upperCookerInterior
  escapingSteamRegion : setup.figure.labelRegion .escapingSteam = .aboveLid
  closedContainerShown : setup.figure.showsClosedContainer = true
  domedLidShown : setup.figure.showsDomedLid = true
  petcockAboveOpening : setup.figure.showsPetcockAboveOpening = true
  liquidBelowVapor : setup.figure.showsLiquidBelowVapor = true
  escapingSteamShown : setup.figure.showsSteamEscapingPastPetcock = true

/-!
Numerical data stated in the prose. No petcock-mass value or answer label
occurs here.
-/
structure MatchesProblemReadouts (setup : PressureCookerSetup) : Prop where
  openingAreaSquareMillimeters :
    areaInSquareMillimeters setup.openingArea = 5
  boilingTemperatureCelsius :
    temperatureInDegreesCelsius setup.boilingTemperature = 120
  outsidePressureKilopascals :
    pressureInKilopascals setup.outsideAtmosphericPressure = 1013 / 10

/-!
Standard near-Earth gravity used by the recorded numerical choice. It is an
independent environmental calibration rather than the requested mass.
-/
structure UsesStandardNearEarthGravity (setup : PressureCookerSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-!
The saturated-water steam-table readout at the independently specified
`120 °C` operating temperature is `198.5 kPa`. This thermodynamic datum does
not constrain the petcock mass.
-/
structure UsesWaterSaturationTableAt120C
    (setup : PressureCookerSetup) : Prop where
  saturationPressureKilopascals :
    pressureInKilopascals
      (setup.saturationPressureAt setup.boilingTemperature) = 397 / 2

/-!
The governing laws are separate from their numerical calibrations:

* water boils when the headspace steam pressure equals its saturation
  pressure at the water temperature;
* at incipient lift, upward steam-pressure force balances downward
  atmospheric-pressure force and petcock weight.

Neither law asserts a numerical petcock mass or selects an answer choice.
-/
structure SatisfiesBoilingAndPetcockBalanceLaws
    (setup : PressureCookerSetup) : Prop where
  boilingPressureIsSaturationPressure :
    setup.steamPressureAtBoiling =
      setup.saturationPressureAt setup.boilingTemperature
  incipientLiftVerticalForceBalance :
    pressureForceInNewtons setup.steamPressureAtBoiling setup.openingArea =
      pressureForceInNewtons setup.outsideAtmosphericPressure
          setup.openingArea +
        weightInNewtons setup.petcockMass
          setup.gravitationalAcceleration

/-! ## Displayed choices and current target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Gram values printed beside the four labels. This records the candidate list
without asserting which candidate follows from the physical laws.
-/
def displayedMassInGrams : AnswerChoice → ℝ
  | .A => 10
  | .B => 397 / 2
  | .C => 100
  | .D => 50

/-- A displayed mass choice is at least as close as every alternative. -/
def IsNearestDisplayedMass
    (setup : PressureCookerSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |massInGrams setup.petcockMass - displayedMassInGrams choice| ≤
      |massInGrams setup.petcockMass - displayedMassInGrams other|

/-!
The pressure difference and lift-threshold balance give

`m = ((198.5 - 101.3) kPa) (5 mm²) / (9.8 m/s²)`
`  = 243/4900 kg = 2430/49 g`,

approximately `49.59 g`. Hence `50 g`, displayed as choice D, is uniquely
nearest.

This formalizes `thm:physics:phyx_mini_0440:target`.
-/
theorem problem_phyx_mini_0440
    (setup : PressureCookerSetup)
    (hScenario : MatchesPressureCookerScenario setup)
    (hFigure : MatchesSuppliedPressureCookerFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hSteamTable : UsesWaterSaturationTableAt120C setup)
    (hLaws : SatisfiesBoilingAndPetcockBalanceLaws setup) :
    massInKilograms setup.petcockMass = 243 / 4900 ∧
      massInGrams setup.petcockMass = 2430 / 49 ∧
      IsNearestDisplayedMass setup .D ∧
      ∀ choice : AnswerChoice,
        IsNearestDisplayedMass setup choice → choice = .D := by
  have area_millimeters_eq (area : DimArea) :
      areaInSquareMillimeters area =
        1000000 * areaInSquareMeters area := by
    change
      ((area
          {UnitChoices.SI with
            length := LengthUnit.millimeters}).val : ℝ) =
        1000000 * ((area UnitChoices.SI).val : ℝ)
    rw [area.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.millimeters}]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.millimeters}
          (dim (WithDim (L𝓭 * L𝓭) NNReal)) = 1000000 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.millimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      change (((1000 : NNReal) : ℝ) ^ 2 = 1000000)
      norm_num
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have hArea := hReadouts.openingAreaSquareMillimeters
  rw [area_millimeters_eq] at hArea
  have hAreaSI :
      areaInSquareMeters setup.openingArea = 5 / 1000000 := by
    linarith
  have hOutside := hReadouts.outsidePressureKilopascals
  norm_num [pressureInKilopascals] at hOutside
  have hOutsidePa :
      pressureInPascals setup.outsideAtmosphericPressure = 101300 := by
    linarith
  have hSteam := hSteamTable.saturationPressureKilopascals
  norm_num [pressureInKilopascals] at hSteam
  have hSteamPa :
      pressureInPascals setup.steamPressureAtBoiling = 198500 := by
    rw [hLaws.boilingPressureIsSaturationPressure]
    linarith
  have hBalance := hLaws.incipientLiftVerticalForceBalance
  simp only [pressureForceInNewtons, weightInNewtons] at hBalance
  rw [hSteamPa, hOutsidePa, hAreaSI,
    hGravity.gravitationalAccelerationSI] at hBalance
  have hMassKg :
      massInKilograms setup.petcockMass = 243 / 4900 := by
    norm_num at hBalance ⊢
    linarith
  have hMassConversion :
      massInGrams setup.petcockMass =
        1000 * massInKilograms setup.petcockMass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.petcockMass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, massReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hMassGrams :
      massInGrams setup.petcockMass = 2430 / 49 := by
    rw [hMassConversion, hMassKg]
    norm_num
  refine ⟨hMassKg, hMassGrams, ?_, ?_⟩
  · rw [IsNearestDisplayedMass]
    intro other
    rw [hMassGrams]
    cases other <;> norm_num [displayedMassInGrams]
  · intro choice hChoice
    cases choice with
    | A =>
        exfalso
        have h := hChoice .D
        rw [hMassGrams] at h
        norm_num [displayedMassInGrams] at h
    | B =>
        exfalso
        have h := hChoice .D
        rw [hMassGrams] at h
        norm_num [displayedMassInGrams] at h
    | C =>
        exfalso
        have h := hChoice .D
        rw [hMassGrams] at h
        norm_num [displayedMassInGrams] at h
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0440
