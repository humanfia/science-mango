import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0382

open Dimension

/-!
# Pressure at the bottom of a gasoline storage tank

The tank contains gasoline at `25 °C`.  Its free top surface is exposed to an
absolute atmospheric pressure of `101 kPa`, and the vertical gasoline depth is
`7.5 m`.  The primary bitmap shows a spherical vessel on a braced support
frame, together with a vertical double-headed height arrow labelled `H`.

Pressure, length, mass density, acceleration, and absolute temperature remain
physical quantities.  Real numbers appear only as explicitly named unit
readouts and as the displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the chosen readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass density, with dimension `M L⁻³`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Absolute pressure, represented by Physlib's dimensional pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Absolute thermodynamic temperature. -/
abbrev TemperatureQuantity : Type := Temperature

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read pressure in the coherent unit induced by selected base units. -/
def pressureReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (pressure : PressureQuantity) : ℝ :=
  (pressure {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Read mass density in a selected mass unit per selected length unit cubed. -/
def densityReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (density : MassDensityQuantity) : ℝ :=
  ((density {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read acceleration in selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  pressureReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds pressure

/-- Kilopascal readout of an absolute pressure. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Kilogram-per-cubic-meter readout of a physical mass density. -/
def densityInKilogramsPerCubicMeter (density : MassDensityQuantity) : ℝ :=
  densityReadout MassUnit.kilograms LengthUnit.meters density

/-- Meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Read a stored absolute temperature in kelvins. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : TemperatureQuantity) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Celsius readout, using the exact offset `0 °C = 273.15 K`. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : TemperatureQuantity) : ℝ :=
  temperatureInKelvins storageUnit temperature - 27315 / 100

/-! ## Apparatus, physical roles, and primary-figure labels -/

/-- Shape of the storage vessel visible in the primary bitmap. -/
inductive TankShape where
  | spherical
  | other
  deriving DecidableEq, Repr

/-- Liquid named in the problem statement. -/
inductive TankLiquid where
  | gasoline
  | other
  deriving DecidableEq, Repr

/-- Boundary condition at the upper gasoline surface. -/
inductive TopSurfaceBoundary where
  | exposedToAtmosphere
  | other
  deriving DecidableEq, Repr

/-- Thermal condition used for the tabulated gasoline density. -/
inductive TankThermalCondition where
  | uniform
  | other
  deriving DecidableEq, Repr

/-- The literal quantity label visible beside the height arrow. -/
inductive FigureQuantityLabel where
  | capitalH
  deriving DecidableEq, Fintype, Repr

/-- Physical role assigned to the figure's `H` marker. -/
inductive FigureHeightRole where
  | topSurfaceToTankBottom
  deriving DecidableEq, Repr

/-- Endpoints of the vertical double-headed arrow in the supplied figure. -/
inductive FigureHeightEndpoint where
  | tankTop
  | horizontalBase
  deriving DecidableEq, Repr

/-- Structured transcription of image `382.png`. -/
structure SphericalStorageTankFigure where
  vesselShape : TankShape
  labelShown : FigureQuantityLabel → Bool
  markedHeight : LengthQuantity
  markedHeightRole : FigureHeightRole
  arrowUpperEndpoint : FigureHeightEndpoint
  arrowLowerEndpoint : FigureHeightEndpoint
  heightArrowVertical : Bool
  heightArrowDoubleHeaded : Bool
  verticalSupportColumnsShown : Bool
  diagonalBracesShown : Bool
  horizontalBaseShown : Bool

/-!
Independent physical quantities in the tank problem.  In particular,
`bottomAbsolutePressure` is an observable field rather than a definition made
from the recorded answer or the hydrostatic formula.
-/
structure GasolineStorageTankSetup where
  figure : SphericalStorageTankFigure
  liquid : TankLiquid
  topSurfaceBoundary : TopSurfaceBoundary
  thermalCondition : TankThermalCondition
  tankHeight : LengthQuantity
  fluidDepthFromTopSurfaceToBottom : LengthQuantity
  topSurfaceAbsolutePressure : PressureQuantity
  bottomAbsolutePressure : PressureQuantity
  fluidTemperature : TemperatureQuantity
  temperatureStorageUnit : TemperatureUnit
  gasolineMassDensityAt : TemperatureQuantity → MassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity

/-! ## Figure readouts, stated data, and physical calibrations -/

/--
Qualitative and labelled geometry read directly from the primary bitmap.  The
figure itself supplies no numerical value for `H`.
-/
structure MatchesPrimaryFigure (setup : GasolineStorageTankSetup) : Prop where
  vesselIsSpherical : setup.figure.vesselShape = .spherical
  everyQuantityLabelShown : ∀ label, setup.figure.labelShown label = true
  heightMarkMatchesTankHeight : setup.figure.markedHeight = setup.tankHeight
  heightMarkRole : setup.figure.markedHeightRole = .topSurfaceToTankBottom
  upperEndpointIsTankTop : setup.figure.arrowUpperEndpoint = .tankTop
  lowerEndpointIsHorizontalBase :
    setup.figure.arrowLowerEndpoint = .horizontalBase
  heightArrowIsVertical : setup.figure.heightArrowVertical = true
  heightArrowHasTwoHeads : setup.figure.heightArrowDoubleHeaded = true
  supportColumnsAreShown : setup.figure.verticalSupportColumnsShown = true
  diagonalBracingIsShown : setup.figure.diagonalBracesShown = true
  horizontalBaseIsShown : setup.figure.horizontalBaseShown = true

/--
Quantitative and qualitative information stated in the problem.  The fluid is
filled to its atmospheric top surface, so its hydrostatic depth is the stated
`7.5 m` tank height.  No bottom-pressure value occurs here.
-/
structure MatchesProblemStatement (setup : GasolineStorageTankSetup) : Prop where
  liquidIsGasoline : setup.liquid = .gasoline
  freeSurfaceIsAtmospheric :
    setup.topSurfaceBoundary = .exposedToAtmosphere
  uniformTemperature : setup.thermalCondition = .uniform
  absoluteTemperatureStorageIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  tankHeightMeters : lengthInMeters setup.tankHeight = 15 / 2
  fluidDepthEqualsTankHeight :
    setup.fluidDepthFromTopSurfaceToBottom = setup.tankHeight
  topSurfacePressureKilopascals :
    pressureInKilopascals setup.topSurfaceAbsolutePressure = 101
  gasolineTemperatureCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
      setup.fluidTemperature = 25

/--
Standard reference-property values implicit in the recorded multiple-choice
answer: gasoline at `25 °C` has density `750 kg/m³`, and near-surface Earth
gravity is `9.81 m/s²`.  These calibrations do not mention bottom pressure.
-/
structure UsesReferenceGasolineAndEarthGravity
    (setup : GasolineStorageTankSetup) : Prop where
  gasolineDensityKilogramsPerCubicMeter :
    densityInKilogramsPerCubicMeter
      (setup.gasolineMassDensityAt setup.fluidTemperature) = 750
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      981 / 100

/-- Positivity of the physical parameters and absolute pressures. -/
structure HasPhysicalTankParameters (setup : GasolineStorageTankSetup) : Prop where
  tankHeightPositive : 0 < lengthInMeters setup.tankHeight
  fluidDepthPositive :
    0 < lengthInMeters setup.fluidDepthFromTopSurfaceToBottom
  gasolineDensityPositive :
    0 < densityInKilogramsPerCubicMeter
      (setup.gasolineMassDensityAt setup.fluidTemperature)
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  topSurfaceAbsolutePressurePositive :
    0 < pressureInPascals setup.topSurfaceAbsolutePressure
  bottomAbsolutePressurePositive :
    0 < pressureInPascals setup.bottomAbsolutePressure

/-! ## Governing hydrostatic law -/

/--
For a stationary uniform-density liquid column, the absolute pressure gain
from the free surface to the bottom is `ρ g h`.  The equation is stated for
every coherent choice of mass, length, and time units.  It contains no
numerical bottom-pressure answer.
-/
structure SatisfiesHydrostaticPressureLaw
    (setup : GasolineStorageTankSetup) : Prop where
  bottomPressureLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      pressureReadout massUnit lengthUnit timeUnit
          setup.bottomAbsolutePressure =
        pressureReadout massUnit lengthUnit timeUnit
            setup.topSurfaceAbsolutePressure +
          densityReadout massUnit lengthUnit
              (setup.gasolineMassDensityAt setup.fluidTemperature) *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit
              setup.fluidDepthFromTopSurfaceToBottom

/-! ## Displayed choices and target conclusions -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilopascal value printed beside each answer label. -/
def displayedPressureKilopascals : AnswerChoice → ℝ
  | .A => 731 / 5
  | .B => 781 / 5
  | .C => 1281 / 5
  | .D => 831 / 5

/-- Dataset answer metadata, deliberately not used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A physical pressure rounds to a displayed tenth of a kilopascal. -/
def RoundsToNearestTenthKilopascal
    (pressure : PressureQuantity) (displayedKilopascals : ℝ) : Prop :=
  |pressureInKilopascals pressure - displayedKilopascals| < 1 / 20

/-- A displayed choice agrees with the modeled bottom pressure. -/
def MatchesDisplayedBottomPressure
    (setup : GasolineStorageTankSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenthKilopascal setup.bottomAbsolutePressure
    (displayedPressureKilopascals choice)

/-- Exactly one displayed answer agrees with the modeled bottom pressure. -/
def IsUniqueMatchingDisplayedPressure
    (setup : GasolineStorageTankSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedBottomPressure setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedBottomPressure setup other → other = choice

/-!
The hydrostatic law and the calibrated data give the unrounded bottom pressure
`156.18125 kPa = 124945 / 800 kPa`.  This derived value is not a premise.
-/
lemma bottom_pressure_in_kilopascals
    (setup : GasolineStorageTankSetup)
    (hProblem : MatchesProblemStatement setup)
    (hCalibration : UsesReferenceGasolineAndEarthGravity setup)
    (hLaws : SatisfiesHydrostaticPressureLaw setup) :
    pressureInKilopascals setup.bottomAbsolutePressure = 124945 / 800 := by
  have hLaw :=
    hLaws.bottomPressureLaw
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    pressureInPascals setup.bottomAbsolutePressure =
      pressureInPascals setup.topSurfaceAbsolutePressure +
        densityInKilogramsPerCubicMeter
            (setup.gasolineMassDensityAt setup.fluidTemperature) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.fluidDepthFromTopSurfaceToBottom at hLaw
  rw [hProblem.fluidDepthEqualsTankHeight,
    hCalibration.gasolineDensityKilogramsPerCubicMeter,
    hCalibration.gravitationalAccelerationMetersPerSecondSquared,
    hProblem.tankHeightMeters] at hLaw
  have hTop := hProblem.topSurfacePressureKilopascals
  change pressureInPascals setup.topSurfaceAbsolutePressure / 1000 = 101 at hTop
  change pressureInPascals setup.bottomAbsolutePressure / 1000 = 124945 / 800
  norm_num at hLaw hTop ⊢
  linarith

/-!
The exact modeled pressure rounds to `156.2 kPa`, and this uniquely selects
choice B among the four displayed values.

This formalizes blueprint label `thm:physics:phyx_mini_0382:target`.
-/
theorem problem_phyx_mini_0382
    (setup : GasolineStorageTankSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hProblem : MatchesProblemStatement setup)
    (hCalibration : UsesReferenceGasolineAndEarthGravity setup)
    (hPhysical : HasPhysicalTankParameters setup)
    (hLaws : SatisfiesHydrostaticPressureLaw setup) :
    pressureInKilopascals setup.bottomAbsolutePressure = 124945 / 800 ∧
      MatchesDisplayedBottomPressure setup .B ∧
      IsUniqueMatchingDisplayedPressure setup .B := by
  have hPressure :=
    bottom_pressure_in_kilopascals setup hProblem hCalibration hLaws
  have hMatchB : MatchesDisplayedBottomPressure setup .B := by
    norm_num [MatchesDisplayedBottomPressure,
      RoundsToNearestTenthKilopascal, displayedPressureKilopascals, hPressure]
  refine ⟨hPressure, hMatchB, hMatchB, ?_⟩
  intro other hOther
  fin_cases other
  · norm_num [MatchesDisplayedBottomPressure,
      RoundsToNearestTenthKilopascal, displayedPressureKilopascals,
      hPressure] at hOther
  · rfl
  · norm_num [MatchesDisplayedBottomPressure,
      RoundsToNearestTenthKilopascal, displayedPressureKilopascals,
      hPressure] at hOther
  · norm_num [MatchesDisplayedBottomPressure,
      RoundsToNearestTenthKilopascal, displayedPressureKilopascals,
      hPressure] at hOther

end PhyXMiniProblems.ProblemPhyXMini0382
