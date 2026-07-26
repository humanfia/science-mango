import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0365

open Dimension

/-!
# Freezer temperature from a mercury manometer

A rigid gas cell is joined to the left arm of an open mercury U-tube.  In the
supplied figure the mercury surface on the gas side is below the surface in the
arm open to the atmosphere, so the gas pressure is atmospheric pressure plus
the positive mercury-column head.

The height difference is `120 mm` in an ice-water mixture and `30 mm` in the
industrial freezer.  Pressures, lengths, volumes, and absolute temperatures
remain physical quantities; real numbers occur only as explicit unit readouts.
The standard reference data used by the multiple-choice calculation are
`760 mmHg` for atmospheric pressure and `273.15 K` for the ice point.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Millimetre readout for the height label `h` in the supplied figure. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a dimensionful pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/--
Read pressure in millimetres of mercury by comparison with Physlib's
dimensionful one-millimetre-of-mercury pressure.
-/
def pressureInMillimetersOfMercury (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.millimeterOfMercury

/-- The two thermal environments in which the same apparatus is observed. -/
inductive ThermalEnvironment where
  | iceWaterMixture
  | industrialFreezer
  deriving DecidableEq, Fintype, Repr

/-- The two arms of the U-tube, named by their boundary conditions. -/
inductive ManometerArm where
  | gasCellSide
  | openAtmosphereSide
  deriving DecidableEq, Fintype, Repr

/-- The liquid occupying the lower part of the manometer. -/
inductive ManometerLiquid where
  | mercury
  | other
  deriving DecidableEq, Repr

/-!
Qualitative and labelled geometry visible in the supplied figure.  In
particular, `gasSideSurfaceLowerThanOpenSide` fixes the sign of the gauge
pressure; it does not prescribe its magnitude.
-/
structure SuppliedManometerFigure where
  gasCellConnectedArm : ManometerArm
  armOpenToAtmosphere : ManometerArm
  manometerLiquid : ManometerLiquid
  showsUShapedTube : Bool
  showsGasCellLabel : Bool
  showsVerticalHeightArrow : Bool
  showsHeightLabelH : Bool
  gasSideSurfaceLowerThanOpenSide : Bool

/-!
The physical apparatus and its observables in the two environments.

The pressure and temperature fields are not defined from the desired answer.
The governing manometer and ideal-gas relations are stated separately below.
-/
structure GasCellManometerSetup where
  figure : SuppliedManometerFigure
  gasPressure : ThermalEnvironment → DimPressure
  atmosphericPressure : DimPressure
  gasTemperature : ThermalEnvironment → Temperature
  temperatureStorageUnit : TemperatureUnit
  gasVolume : ThermalEnvironment → VolumeQuantity
  mercuryHeightDifference : ThermalEnvironment → LengthQuantity
  gasCellContainsGas : Bool
  gasCellIsSealed : Bool

/-!
Convert the stored absolute-temperature magnitude to a kelvin readout.  The
explicit storage unit prevents treating an arbitrary numerical temperature
scale as kelvin without a calibration.
-/
def temperatureInKelvin
    (setup : GasCellManometerSetup)
    (environment : ThermalEnvironment) : ℝ :=
  let unitRatio : NNReal :=
    setup.temperatureStorageUnit / TemperatureUnit.kelvin
  (setup.gasTemperature environment).toReal * (unitRatio : ℝ)

/-- Numerical readout of the figure's mercury height difference in mm. -/
def mercuryHeightInMillimeters
    (setup : GasCellManometerSetup)
    (environment : ThermalEnvironment) : ℝ :=
  lengthInMillimeters (setup.mercuryHeightDifference environment)

/-!
The requested freezer-temperature readout in degrees Celsius.  The offset
`273.15` is written exactly as `5463 / 20`.
-/
def freezerTemperatureInCelsius (setup : GasCellManometerSetup) : ℝ :=
  temperatureInKelvin setup .industrialFreezer - 5463 / 20

/-!
Primary-figure evidence: a gas cell joins one arm of a mercury U-tube, the
other arm is open, and the labelled positive height `h` has the orientation
shown in the raster.
-/
def MatchesSuppliedManometerFigure
    (setup : GasCellManometerSetup) : Prop :=
  setup.figure.gasCellConnectedArm = .gasCellSide ∧
    setup.figure.armOpenToAtmosphere = .openAtmosphereSide ∧
    setup.figure.manometerLiquid = .mercury ∧
    setup.figure.showsUShapedTube = true ∧
    setup.figure.showsGasCellLabel = true ∧
    setup.figure.showsVerticalHeightArrow = true ∧
    setup.figure.showsHeightLabelH = true ∧
    setup.figure.gasSideSurfaceLowerThanOpenSide = true

/-!
The two scalar height readouts stated in the problem.  These are observations,
not pressure or temperature conclusions.
-/
def MatchesSuppliedHeightReadouts
    (setup : GasCellManometerSetup) : Prop :=
  mercuryHeightInMillimeters setup .iceWaterMixture = 120 ∧
    mercuryHeightInMillimeters setup .industrialFreezer = 30

/-!
Standard reference conditions used in the multiple-choice calculation:
normal atmospheric pressure is `760 mmHg`, and an ice-water mixture is at
`273.15 K`.  No freezer-temperature value occurs here.
-/
def UsesStandardIcePointAndAtmosphericPressure
    (setup : GasCellManometerSetup) : Prop :=
  pressureInMillimetersOfMercury setup.atmosphericPressure = 760 ∧
    temperatureInKelvin setup .iceWaterMixture = 5463 / 20

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalGasCellManometerParameters
    (setup : GasCellManometerSetup) : Prop where
  gasPressurePositive :
    ∀ environment,
      0 < pressureInMillimetersOfMercury (setup.gasPressure environment)
  atmosphericPressurePositive :
    0 < pressureInMillimetersOfMercury setup.atmosphericPressure
  absoluteTemperaturePositive :
    ∀ environment, 0 < temperatureInKelvin setup environment
  gasVolumePositive :
    ∀ environment, 0 < volumeInCubicMeters (setup.gasVolume environment)
  heightDifferenceNonnegative :
    ∀ environment, 0 ≤ mercuryHeightInMillimeters setup environment

/-!
Governing laws for the apparatus.

* The same sealed gas cell retains a constant volume in both environments.
* Since the gas-side mercury surface is lower, the absolute gas pressure is
  atmospheric pressure plus the positive `h`-column head when both are read
  in compatible mercury units.
* For the fixed amount of ideal gas at constant volume, `P / T` is constant;
  the division-free cross-multiplied relation is used.

All laws are quantified over environments and contain no solved freezer
temperature or answer choice.
-/
structure SatisfiesSealedConstantVolumeGasAndManometerLaws
    (setup : GasCellManometerSetup) : Prop where
  gasCellContainsGas : setup.gasCellContainsGas = true
  gasCellIsSealed : setup.gasCellIsSealed = true
  volumeIsConstant :
    ∀ first second, setup.gasVolume first = setup.gasVolume second
  mercuryColumnPressureLaw :
    ∀ environment,
      pressureInMillimetersOfMercury (setup.gasPressure environment) =
        pressureInMillimetersOfMercury setup.atmosphericPressure +
          mercuryHeightInMillimeters setup environment
  constantVolumeIdealGasLaw :
    ∀ first second,
      pressureInMillimetersOfMercury (setup.gasPressure first) *
          temperatureInKelvin setup second =
        pressureInMillimetersOfMercury (setup.gasPressure second) *
          temperatureInKelvin setup first

/-- The four temperature choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Celsius value printed beside each answer label. -/
def displayedFreezerTemperatureInCelsius : AnswerChoice → ℝ
  | .A => -28
  | .B => -56
  | .C => -36
  | .D => -84

/-!
A displayed integral Celsius answer matches the calculated temperature when
it is the nearest degree (strictly within half a degree).
-/
def MatchesNearestDegreeAnswer
    (setup : GasCellManometerSetup)
    (choice : AnswerChoice) : Prop :=
  |freezerTemperatureInCelsius setup -
      displayedFreezerTemperatureInCelsius choice| < (1 / 2 : ℝ)

/-- A matching answer is unique among the four displayed choices. -/
def IsUniqueMatchingAnswer
    (setup : GasCellManometerSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesNearestDegreeAnswer setup choice ∧
    ∀ other,
      MatchesNearestDegreeAnswer setup other → other = choice

/-!
The two manometer observations and the normal-atmosphere calibration give
absolute gas-pressure readouts of `880 mmHg` and `790 mmHg`.
-/
lemma gasPressureReadouts_eq
    (setup : GasCellManometerSetup)
    (hReadouts : MatchesSuppliedHeightReadouts setup)
    (hReference : UsesStandardIcePointAndAtmosphericPressure setup)
    (hLaws : SatisfiesSealedConstantVolumeGasAndManometerLaws setup) :
    pressureInMillimetersOfMercury
        (setup.gasPressure .iceWaterMixture) = 880 ∧
      pressureInMillimetersOfMercury
        (setup.gasPressure .industrialFreezer) = 790 := by
  constructor
  · rw [hLaws.mercuryColumnPressureLaw .iceWaterMixture,
      hReference.1, hReadouts.1]
    norm_num
  · rw [hLaws.mercuryColumnPressureLaw .industrialFreezer,
      hReference.1, hReadouts.2]
    norm_num

/-!
The unrounded ideal-gas result is
`273.15 K * 790 / 880 = 431577 / 1760 K`.
-/
lemma freezerTemperatureInKelvin_eq
    (setup : GasCellManometerSetup)
    (hReadouts : MatchesSuppliedHeightReadouts setup)
    (hReference : UsesStandardIcePointAndAtmosphericPressure setup)
    (hLaws : SatisfiesSealedConstantVolumeGasAndManometerLaws setup) :
    temperatureInKelvin setup .industrialFreezer = 431577 / 1760 := by
  have hPressures :=
    gasPressureReadouts_eq setup hReadouts hReference hLaws
  have hIdealGas :=
    hLaws.constantVolumeIdealGasLaw
      .iceWaterMixture .industrialFreezer
  rw [hPressures.1, hPressures.2, hReference.2] at hIdealGas
  norm_num at hIdealGas ⊢
  linarith

/-!
Thus the unrounded freezer temperature is `-49167 / 1760 °C`, approximately
`-27.94 °C`.  It rounds uniquely to `-28 °C`, answer A.

This formalizes `thm:physics:phyx_mini_0365:target`.
-/
theorem problem_phyx_mini_0365
    (setup : GasCellManometerSetup)
    (hFigure : MatchesSuppliedManometerFigure setup)
    (hReadouts : MatchesSuppliedHeightReadouts setup)
    (hReference : UsesStandardIcePointAndAtmosphericPressure setup)
    (hPhysical : HasPhysicalGasCellManometerParameters setup)
    (hLaws : SatisfiesSealedConstantVolumeGasAndManometerLaws setup) :
    temperatureInKelvin setup .industrialFreezer = 431577 / 1760 ∧
      freezerTemperatureInCelsius setup = -(49167 / 1760) ∧
      IsUniqueMatchingAnswer setup .A := by
  have hKelvin :=
    freezerTemperatureInKelvin_eq setup hReadouts hReference hLaws
  have hCelsius :
      freezerTemperatureInCelsius setup = -(49167 / 1760) := by
    rw [freezerTemperatureInCelsius, hKelvin]
    norm_num
  refine ⟨hKelvin, hCelsius, ?_⟩
  constructor
  · unfold MatchesNearestDegreeAnswer
    rw [hCelsius]
    norm_num [displayedFreezerTemperatureInCelsius]
  · intro other hOther
    cases other with
    | A => rfl
    | B =>
        exfalso
        unfold MatchesNearestDegreeAnswer at hOther
        rw [hCelsius] at hOther
        norm_num [displayedFreezerTemperatureInCelsius] at hOther
    | C =>
        exfalso
        unfold MatchesNearestDegreeAnswer at hOther
        rw [hCelsius] at hOther
        norm_num [displayedFreezerTemperatureInCelsius] at hOther
    | D =>
        exfalso
        unfold MatchesNearestDegreeAnswer at hOther
        rw [hCelsius] at hOther
        norm_num [displayedFreezerTemperatureInCelsius] at hOther

end PhyXMiniProblems.ProblemPhyXMini0365
