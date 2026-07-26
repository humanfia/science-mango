import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0398

open Dimension

/-!
# Petcock mass for a pressure cooker boiling at 120 degrees Celsius

A petcock covers a small opening in a tightly closed pressure-cooker lid.
Water is to boil at `120 °C` while the exterior atmosphere is at `101.3 kPa`.
At the onset of venting, the upward steam-pressure force on the petcock
balances the downward atmospheric-pressure force and the petcock's weight.

Area, mass, acceleration, pressure, and absolute temperature remain physical
quantities. Real numbers occur only as explicitly named unit readouts, as
empirical constant readouts, and as the displayed multiple-choice masses.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude with physical dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in grams using Physlib's gram unit. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.grams}).val : ℝ)

/-- Read the opening area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read the opening area in square millimetres. -/
def areaInSquareMillimeters (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with length := LengthUnit.millimeters}).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read an absolute pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read an absolute pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a Physlib absolute temperature in kelvin. -/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Convert the absolute-temperature readout to degrees Celsius. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvin storageUnit temperature - 27315 / 100

/-! ## Apparatus roles and primary-figure transcription -/

/-- The working fluid whose vapor is labelled as steam in the figure. -/
inductive CookerFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-- How the pressure-cooker lid is attached to the vessel. -/
inductive LidClosure where
  | screwedOnTight
  | notSealed
  deriving DecidableEq, Repr

/-- The device covering the small top opening. -/
inductive OpeningCover where
  | liftablePetcock
  | other
  deriving DecidableEq, Repr

/-- Text labels visibly printed in the supplied pressure-cooker figure. -/
inductive FigureLabel where
  | liquid
  | steamOrVapor
  | escapingSteam
  deriving DecidableEq, Fintype, Repr

/-- Direction in which the petcock can move to uncover the opening. -/
inductive PetcockMotion where
  | liftsVertically
  | fixed
  deriving DecidableEq, Repr

/-!
Qualitative information transcribed from image `398.png`. The bitmap shows
liquid below a steam-or-vapor region, a petcock at the top opening, and steam
escaping above it. It contains no mass, pressure, area, or temperature value.
-/
structure PressureCookerFigure where
  showsLabel : FigureLabel → Bool
  liquidRegionBelowVaporRegion : Bool
  showsClosedContainer : Bool
  showsLid : Bool
  showsTopOpening : Bool
  showsPetcockOverOpening : Bool
  showsSteamEscapingAroundPetcock : Bool

/-!
The pressure cooker and its independent physical observables. In particular,
`petcockMass` is not defined from the recorded answer. The saturation-pressure
function is retained as thermodynamic data rather than replacing pressure by a
bare scalar.
-/
structure PressureCookerSetup where
  figure : PressureCookerFigure
  workingFluid : CookerFluid
  lidClosure : LidClosure
  openingCover : OpeningCover
  petcockMotion : PetcockMotion
  openingArea : DimArea
  petcockMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  outsideAtmosphericPressure : DimPressure
  steamPressureAtBoiling : DimPressure
  boilingTemperature : Temperature
  temperatureStorageUnit : TemperatureUnit
  waterSaturationPressure : Temperature → DimPressure
  pressureUniformOnPetcockFaces : Bool
  pressureActsNormallyOnPetcock : Bool
  guideFrictionNeglected : Bool

/-! ## Figure/data readouts and physical modeling assumptions -/

/-- Qualitative labels and geometry read directly from the primary image. -/
structure MatchesPrimaryFigure (setup : PressureCookerSetup) : Prop where
  everyPrintedLabelShown : ∀ label, setup.figure.showsLabel label = true
  liquidIsBelowVapor : setup.figure.liquidRegionBelowVaporRegion = true
  containerIsShownClosed : setup.figure.showsClosedContainer = true
  lidIsShown : setup.figure.showsLid = true
  topOpeningIsShown : setup.figure.showsTopOpening = true
  petcockCoversOpening : setup.figure.showsPetcockOverOpening = true
  escapingSteamIsShown :
    setup.figure.showsSteamEscapingAroundPetcock = true

/-!
The apparatus description and numerical data stated in the problem. No mass
value or answer-choice label occurs here.
-/
structure MatchesProblemData (setup : PressureCookerSetup) : Prop where
  fluidIsWater : setup.workingFluid = .water
  lidIsScrewedOnTight : setup.lidClosure = .screwedOnTight
  openingIsCoveredByLiftablePetcock :
    setup.openingCover = .liftablePetcock
  petcockLiftsToVent : setup.petcockMotion = .liftsVertically
  openingAreaSquareMillimeters :
    areaInSquareMillimeters setup.openingArea = 5
  requestedBoilingTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      setup.boilingTemperature = 120
  outsideAtmosphericPressureKilopascals :
    pressureInKilopascals setup.outsideAtmosphericPressure = 1013 / 10

/-!
Standard terrestrial gravity and a rounded water steam-table readout at
`120 °C`. The saturation-pressure value is empirical input to the model; it
does not state the requested petcock mass.
-/
structure MatchesStandardWaterData (setup : PressureCookerSetup) : Prop where
  terrestrialGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5
  waterSaturationPressureKilopascalsAtOperatingTemperature :
    pressureInKilopascals
      (setup.waterSaturationPressure setup.boilingTemperature) = 397 / 2

/-- Positivity and pressure ordering for the intended operating state. -/
structure HasPhysicalPetcockParameters
    (setup : PressureCookerSetup) : Prop where
  openingAreaPositive : 0 < areaInSquareMeters setup.openingArea
  petcockMassPositive : 0 < massInGrams setup.petcockMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  outsidePressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressure
  steamPressurePositive :
    0 < pressureInPascals setup.steamPressureAtBoiling
  steamPressureExceedsOutside :
    pressureInPascals setup.outsideAtmosphericPressure <
      pressureInPascals setup.steamPressureAtBoiling

/-- Idealizations used by the one-dimensional petcock force balance. -/
structure MatchesIdealPetcockModel
    (setup : PressureCookerSetup) : Prop where
  pressureUniform : setup.pressureUniformOnPetcockFaces = true
  pressureNormal : setup.pressureActsNormallyOnPetcock = true
  frictionNeglected : setup.guideFrictionNeglected = true

/-! ## Governing boiling and force-balance laws -/

/-!
At equilibrium boiling, the cooker steam pressure equals the water saturation
pressure at the water temperature. This generic law contains no numerical
mass or answer choice.
-/
def SatisfiesWaterBoilingLaw (setup : PressureCookerSetup) : Prop :=
  setup.steamPressureAtBoiling =
    setup.waterSaturationPressure setup.boilingTemperature

/-- Upward steam-pressure force on the underside of the petcock, in newtons. -/
def upwardSteamPressureForceInNewtons
    (setup : PressureCookerSetup) : ℝ :=
  pressureInPascals setup.steamPressureAtBoiling *
    areaInSquareMeters setup.openingArea

/-- Downward outside-atmosphere force on the top face, in newtons. -/
def downwardAtmosphericForceInNewtons
    (setup : PressureCookerSetup) : ℝ :=
  pressureInPascals setup.outsideAtmosphericPressure *
    areaInSquareMeters setup.openingArea

/-- Petcock weight in newtons, using grams for the displayed mass readout. -/
def petcockWeightInNewtons (setup : PressureCookerSetup) : ℝ :=
  (massInGrams setup.petcockMass / 1000) *
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/-!
Vertical force balance at incipient lift: the steam force just balances the
outside atmospheric force together with the petcock weight. It is a generic
governing relation and does not fix the unknown mass.
-/
def AtIncipientVenting (setup : PressureCookerSetup) : Prop :=
  upwardSteamPressureForceInNewtons setup =
    downwardAtmosphericForceInNewtons setup +
      petcockWeightInNewtons setup

/-! ## Multiple-choice display and formalization target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Petcock mass in grams printed beside each answer label. -/
def displayedMassInGrams : AnswerChoice → ℝ
  | .A => 40
  | .B => 50
  | .C => 60
  | .D => 70

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A choice is the unique closest displayed mass to an unrounded result. -/
def IsUniqueClosestDisplayedMass
    (actualMassGrams : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    otherChoice ≠ choice →
      |actualMassGrams - displayedMassInGrams choice| <
        |actualMassGrams - displayedMassInGrams otherChoice|

/-!
Using `p_sat(120 °C) = 198.5 kPa`, the net pressure is `97.2 kPa`.
Across `5 mm²` it produces `0.486 N`; division by `9.8 m/s²` gives the
unrounded mass `2430 / 49 g ≈ 49.59 g`. Thus `50 g`, answer B, is the unique
closest displayed answer.

Blueprint label: `thm:physics:phyx_mini_0398:target`.
-/
theorem problem_phyx_mini_0398
    (setup : PressureCookerSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_standardData : MatchesStandardWaterData setup)
    (_physical : HasPhysicalPetcockParameters setup)
    (_model : MatchesIdealPetcockModel setup)
    (_boilingLaw : SatisfiesWaterBoilingLaw setup)
    (_forceBalance : AtIncipientVenting setup) :
    massInGrams setup.petcockMass = 2430 / 49 ∧
      IsUniqueClosestDisplayedMass
        (massInGrams setup.petcockMass) recordedAnswerChoice := by
  let millimeterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.millimeters}
  have hscale :
      millimeterUnits.dimScale UnitChoices.SI (L𝓭 * L𝓭) =
        (1 / 1000000 : NNReal) := by
    with_reducible_and_instances
      apply NNReal.eq
      norm_num [millimeterUnits, UnitChoices.dimScale, L𝓭, UnitChoices.SI,
        LengthUnit.millimeters, LengthUnit.scale, LengthUnit.div_eq_val]
      simp only [NNReal.toReal]
      norm_num
  have hareaConversion :
      areaInSquareMeters setup.openingArea =
        areaInSquareMillimeters setup.openingArea / 1000000 := by
    have hareaUnits :
        setup.openingArea UnitChoices.SI =
          millimeterUnits.dimScale UnitChoices.SI (L𝓭 * L𝓭) •
            setup.openingArea millimeterUnits := by
      simpa only [WithDim.dim_apply] using
        setup.openingArea.2 millimeterUnits UnitChoices.SI
    rw [hscale] at hareaUnits
    unfold areaInSquareMeters areaInSquareMillimeters
    change ((setup.openingArea UnitChoices.SI).val : ℝ) =
      ((setup.openingArea millimeterUnits).val : ℝ) / 1000000
    have hareaValues :=
      congrArg (fun x => ((x.val : NNReal) : ℝ)) hareaUnits
    simp only [WithDim.smul_val, smul_eq_mul, NNReal.coe_mul,
      NNReal.coe_div, NNReal.coe_one] at hareaValues
    norm_num at hareaValues ⊢
    linarith
  have harea :
      areaInSquareMeters setup.openingArea = 1 / 200000 := by
    rw [hareaConversion, _data.openingAreaSquareMillimeters]
    norm_num
  have houtsidePressure :
      pressureInPascals setup.outsideAtmosphericPressure = 101300 := by
    have h := _data.outsideAtmosphericPressureKilopascals
    unfold pressureInKilopascals at h
    norm_num at h ⊢
    linarith
  have hsteamPressureKilopascals :
      pressureInKilopascals setup.steamPressureAtBoiling = 397 / 2 := by
    rw [_boilingLaw]
    exact
      _standardData.waterSaturationPressureKilopascalsAtOperatingTemperature
  have hsteamPressure :
      pressureInPascals setup.steamPressureAtBoiling = 198500 := by
    unfold pressureInKilopascals at hsteamPressureKilopascals
    norm_num at hsteamPressureKilopascals ⊢
    linarith
  have hmass : massInGrams setup.petcockMass = 2430 / 49 := by
    have hforce := _forceBalance
    unfold AtIncipientVenting upwardSteamPressureForceInNewtons
      downwardAtmosphericForceInNewtons petcockWeightInNewtons at hforce
    rw [hsteamPressure, houtsidePressure, harea,
      _standardData.terrestrialGravityMetersPerSecondSquared] at hforce
    norm_num at hforce ⊢
    linarith
  refine ⟨hmass, ?_⟩
  rw [hmass]
  intro otherChoice hotherChoice
  fin_cases otherChoice <;>
    norm_num [recordedAnswerChoice, displayedMassInGrams] at *

end PhyXMiniProblems.ProblemPhyXMini0398
