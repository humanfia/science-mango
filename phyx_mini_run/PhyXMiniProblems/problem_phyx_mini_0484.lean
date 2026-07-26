import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Vent-weight mass for a pressure cooker at 120 degrees Celsius

The supplied cross section shows water below a steam-filled headspace. A
weight of mass `m` covers a circular vent of diameter `d = 3.0 mm`. At the
desired boiling point, saturated steam pushes the weight upward while the
outside atmosphere and gravity act downward.

Length, area, pressure, mass, acceleration, and absolute temperature retain
physical quantity types. Real numbers occur only as readouts in named units,
steam-table and gravity calibrations, and displayed multiple-choice values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0484

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of its readout unit. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass, independent of its readout unit. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-!
An absolute temperature and its zero-preserving storage unit. Celsius is
handled only by the affine scalar readout below.
-/
structure MeasuredTemperature where
  absoluteTemperature : Temperature
  storageUnit : TemperatureUnit

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Millimetre readout used for the labelled vent diameter. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Metre readout used in the circular-area law. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : DimArea) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Square-metre readout used in the pressure-force balance. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Kilogram readout used in the gravitational force law. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Gram readout used by the displayed choices. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kelvin readout of a measured absolute temperature. -/
def temperatureInKelvin (temperature : MeasuredTemperature) : ℝ :=
  let unitRatio : NNReal :=
    temperature.storageUnit / TemperatureUnit.kelvin
  temperature.absoluteTemperature.toReal * (unitRatio : ℝ)

/-- Celsius readout, with the affine offset `273.15 K = 5463/20 K`. -/
def temperatureInDegreesCelsius
    (temperature : MeasuredTemperature) : ℝ :=
  temperatureInKelvin temperature - 5463 / 20

/-- Upward or downward normal pressure force, read in newtons. -/
def pressureForceInNewtons (pressure : DimPressure) (area : DimArea) : ℝ :=
  pressureInPascals pressure * areaInSquareMeters area

/-- Downward weight, read in newtons. -/
def weightInNewtons
    (mass : MassQuantity) (acceleration : AccelerationQuantity) : ℝ :=
  massInKilograms mass *
    accelerationInMetersPerSecondSquared acceleration

/-! ## Apparatus, phases, and primary-figure vocabulary -/

/-- The liquid whose saturated vapor fills the cooker headspace. -/
inductive WorkingFluid where
  | water
  | other
  deriving DecidableEq, Repr

/-- Mechanical state of the weighted vent at the requested boiling point. -/
inductive VentState where
  | seated
  | incipientLift
  | venting
  deriving DecidableEq, Repr

/-- The five distinct text occurrences visible in the supplied image. -/
inductive FigureLabel where
  | weightMassM
  | diameterD
  | steam
  | waterLeft
  | waterRight
  deriving DecidableEq, Fintype, Repr

/-- Physical objects and regions to which the figure labels refer. -/
inductive FigureObject where
  | ventWeight
  | ventOpening
  | steamHeadspace
  | liquidWater
  deriving DecidableEq, Repr

/-!
Qualitative information from the primary raster. It contains no numerical
mass, pressure, temperature, or diameter value.
-/
structure PressureCookerFigure where
  printedText : FigureLabel → String
  labelPointsTo : FigureLabel → FigureObject
  isCrossSection : Bool
  showsClosedContainer : Bool
  showsWaterBelowSteam : Bool
  showsWeightOverOpening : Bool
  showsSteamEscapingAroundWeight : Bool

/-!
Independent physical quantities at the desired operating point. In
particular, `ventWeightMass` is not defined from an answer choice. The
saturation-pressure function is independent of the actual headspace pressure.
-/
structure PressureCookerSetup where
  fluid : WorkingFluid
  sealedPot : Bool
  weightCoversVent : Bool
  ventStateAtBoiling : VentState
  ventDiameter : LengthQuantity
  ventOpeningArea : DimArea
  cookingTemperature : MeasuredTemperature
  outsideAtmosphericPressure : DimPressure
  steamPressureAtBoiling : DimPressure
  saturationPressureAt : Temperature → DimPressure
  ventWeightMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  figure : PressureCookerFigure

/-! ## Assumptions: scenario, readouts, figure evidence, and laws -/

/-- Qualitative pressure-cooker assumptions stated by the problem. -/
structure MatchesPressureCookerScenario
    (setup : PressureCookerSetup) : Prop where
  workingFluidIsWater : setup.fluid = .water
  potIsSealed : setup.sealedPot = true
  weightClosesVent : setup.weightCoversVent = true
  weightIsAtLiftThreshold : setup.ventStateAtBoiling = .incipientLift

/-!
Facts read from the supplied cross-sectional image. The two visible copies
of `Water` are retained as distinct label occurrences pointing to one region.
-/
structure MatchesSuppliedPressureCookerFigure
    (setup : PressureCookerSetup) : Prop where
  weightText : setup.figure.printedText .weightMassM = "Weight\n(mass m)"
  diameterText : setup.figure.printedText .diameterD = "Diameter d"
  steamText : setup.figure.printedText .steam = "Steam"
  leftWaterText : setup.figure.printedText .waterLeft = "Water"
  rightWaterText : setup.figure.printedText .waterRight = "Water"
  weightLabelTarget :
    setup.figure.labelPointsTo .weightMassM = .ventWeight
  diameterLabelTarget :
    setup.figure.labelPointsTo .diameterD = .ventOpening
  steamLabelTarget :
    setup.figure.labelPointsTo .steam = .steamHeadspace
  leftWaterLabelTarget :
    setup.figure.labelPointsTo .waterLeft = .liquidWater
  rightWaterLabelTarget :
    setup.figure.labelPointsTo .waterRight = .liquidWater
  drawingIsCrossSection : setup.figure.isCrossSection = true
  closedContainerShown : setup.figure.showsClosedContainer = true
  waterBelowSteam : setup.figure.showsWaterBelowSteam = true
  weightAboveVent : setup.figure.showsWeightOverOpening = true
  escapingSteamShown :
    setup.figure.showsSteamEscapingAroundWeight = true

/-!
Numerical data stated in the prose. Neither a vent-mass value nor an answer
label occurs here.
-/
structure MatchesProblemReadouts (setup : PressureCookerSetup) : Prop where
  ventDiameterMillimeters :
    lengthInMillimeters setup.ventDiameter = 3
  cookingTemperatureCelsius :
    temperatureInDegreesCelsius setup.cookingTemperature = 120
  outsideAtmosphericPressurePascals :
    pressureInPascals setup.outsideAtmosphericPressure = 101000

/-!
Standard near-Earth gravity, used as an environmental calibration rather than
as any part of the requested mass.
-/
structure UsesStandardNearEarthGravity
    (setup : PressureCookerSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-!
The saturated-water pressure at `120 °C` is read as `1.99 × 10⁵ Pa`. This is
an independent steam-table calibration and does not constrain the vent mass.
-/
structure UsesWaterSaturationTableAt120C
    (setup : PressureCookerSetup) : Prop where
  saturationPressurePascals :
    pressureInPascals
        (setup.saturationPressureAt
          setup.cookingTemperature.absoluteTemperature) = 199000

/-!
The vent is circular, so its independently represented physical area and
diameter obey `A = πd²/4` when both are read in coherent SI units.
-/
structure HasCircularVentGeometry
    (setup : PressureCookerSetup) : Prop where
  circularOpeningArea :
    areaInSquareMeters setup.ventOpeningArea =
      Real.pi * lengthInMeters setup.ventDiameter ^ 2 / 4

/-! Positivity conditions selecting a physically meaningful apparatus. -/
structure HasPhysicalPressureCookerParameters
    (setup : PressureCookerSetup) : Prop where
  ventDiameterPositive : 0 < lengthInMeters setup.ventDiameter
  ventAreaPositive : 0 < areaInSquareMeters setup.ventOpeningArea
  ventMassPositive : 0 < massInKilograms setup.ventWeightMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  outsidePressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressure
  steamPressurePositive :
    0 < pressureInPascals setup.steamPressureAtBoiling

/-!
The governing relations are kept separate from all numerical calibrations:

* at boiling, the actual steam pressure is the saturation pressure of water;
* at incipient lift, upward steam pressure balances downward atmospheric
  pressure and the weight's gravitational force.

Neither law asserts a numerical vent mass or selects a displayed answer.
-/
structure SatisfiesBoilingAndVentForceLaws
    (setup : PressureCookerSetup) : Prop where
  boilingPressureIsSaturationPressure :
    setup.steamPressureAtBoiling =
      setup.saturationPressureAt
        setup.cookingTemperature.absoluteTemperature
  incipientLiftVerticalForceBalance :
    pressureForceInNewtons
        setup.steamPressureAtBoiling setup.ventOpeningArea =
      pressureForceInNewtons
          setup.outsideAtmosphericPressure setup.ventOpeningArea +
        weightInNewtons
          setup.ventWeightMass setup.gravitationalAcceleration

/-! ## Displayed choices and current target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Gram values printed beside the four labels. This table records the candidate
list without asserting which one follows from the physical laws.
-/
def displayedMassInGrams : AnswerChoice → ℝ
  | .A => 59
  | .B => 63
  | .C => 67
  | .D => 71

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed mass choice is at least as close as every alternative. -/
def IsNearestDisplayedMass
    (setup : PressureCookerSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |massInGrams setup.ventWeightMass - displayedMassInGrams choice| ≤
      |massInGrams setup.ventWeightMass - displayedMassInGrams other|

/-!
The steam-table pressure and atmospheric pressure differ by `98000 Pa`.
Using `d = 3/1000 m`, `A = πd²/4`, and `g = 9.8 m/s²`, the lift-threshold
balance gives

`m = 9π/400 kg = 45π/2 g`,

approximately `70.69 g`. Thus `71 g` is the unique nearest displayed mass,
which is choice D.

Blueprint: `thm:physics:phyx_mini_0484:target`.
-/
theorem problem_phyx_mini_0484
    (setup : PressureCookerSetup)
    (hScenario : MatchesPressureCookerScenario setup)
    (hFigure : MatchesSuppliedPressureCookerFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hSteamTable : UsesWaterSaturationTableAt120C setup)
    (hGeometry : HasCircularVentGeometry setup)
    (hPhysical : HasPhysicalPressureCookerParameters setup)
    (hLaws : SatisfiesBoilingAndVentForceLaws setup) :
    massInKilograms setup.ventWeightMass = 9 * Real.pi / 400 ∧
      massInGrams setup.ventWeightMass = 45 * Real.pi / 2 ∧
      IsNearestDisplayedMass setup .D ∧
      ∀ choice : AnswerChoice,
        IsNearestDisplayedMass setup choice → choice = .D := by
  have hLengthConversion :
      lengthInMillimeters setup.ventDiameter =
        1000 * lengthInMeters setup.ventDiameter := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.ventDiameter.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.millimeters})
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.millimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hDiameterMeters :
      lengthInMeters setup.ventDiameter = 3 / 1000 := by
    rw [hReadouts.ventDiameterMillimeters] at hLengthConversion
    norm_num at hLengthConversion ⊢
    linarith
  have hArea :
      areaInSquareMeters setup.ventOpeningArea =
        9 * Real.pi / 4000000 := by
    rw [hGeometry.circularOpeningArea, hDiameterMeters]
    ring
  have hSteamPressure :
      pressureInPascals setup.steamPressureAtBoiling = 199000 := by
    rw [hLaws.boilingPressureIsSaturationPressure]
    exact hSteamTable.saturationPressurePascals
  have hBalance := hLaws.incipientLiftVerticalForceBalance
  simp only [pressureForceInNewtons, weightInNewtons] at hBalance
  rw [hSteamPressure, hReadouts.outsideAtmosphericPressurePascals,
    hArea, hGravity.gravitationalAccelerationSI] at hBalance
  have hMassKilograms :
      massInKilograms setup.ventWeightMass = 9 * Real.pi / 400 := by
    norm_num at hBalance ⊢
    linarith
  have hMassConversion :
      massInGrams setup.ventWeightMass =
        1000 * massInKilograms setup.ventWeightMass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.ventWeightMass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, massReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hMassGrams :
      massInGrams setup.ventWeightMass = 45 * Real.pi / 2 := by
    rw [hMassConversion, hMassKilograms]
    ring
  have hPiLower : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hPiUpper : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  refine ⟨hMassKilograms, hMassGrams, ?_, ?_⟩
  · rw [IsNearestDisplayedMass]
    intro other
    rw [hMassGrams]
    cases other with
    | A =>
        simp only [displayedMassInGrams]
        rw [abs_of_nonpos (by nlinarith [hPiUpper]),
          abs_of_nonneg (by nlinarith [hPiLower])]
        nlinarith [hPiLower]
    | B =>
        simp only [displayedMassInGrams]
        rw [abs_of_nonpos (by nlinarith [hPiUpper]),
          abs_of_nonneg (by nlinarith [hPiLower])]
        nlinarith [hPiLower]
    | C =>
        simp only [displayedMassInGrams]
        rw [abs_of_nonpos (by nlinarith [hPiUpper]),
          abs_of_nonneg (by nlinarith [hPiLower])]
        nlinarith [hPiLower]
    | D => simp [displayedMassInGrams]
  · intro choice hChoice
    cases choice with
    | A =>
        exfalso
        have h := hChoice .D
        rw [hMassGrams] at h
        simp only [displayedMassInGrams] at h
        rw [abs_of_nonneg (by nlinarith [hPiLower]),
          abs_of_nonpos (by nlinarith [hPiUpper])] at h
        nlinarith [hPiLower]
    | B =>
        exfalso
        have h := hChoice .D
        rw [hMassGrams] at h
        simp only [displayedMassInGrams] at h
        rw [abs_of_nonneg (by nlinarith [hPiLower]),
          abs_of_nonpos (by nlinarith [hPiUpper])] at h
        nlinarith [hPiLower]
    | C =>
        exfalso
        have h := hChoice .D
        rw [hMassGrams] at h
        simp only [displayedMassInGrams] at h
        rw [abs_of_nonneg (by nlinarith [hPiLower]),
          abs_of_nonpos (by nlinarith [hPiUpper])] at h
        nlinarith [hPiLower]
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0484
