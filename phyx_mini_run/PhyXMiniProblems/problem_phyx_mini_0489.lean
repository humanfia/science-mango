import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0489

open Dimension

/-!
# Solar irradiance at Earth from a perfect emitter

The Sun is modeled as a spherical perfect blackbody at `5500 K`, with radius
`7.0 × 10^8 m`.  The primary figure places Earth to the right of the Sun and
labels their separation by `r = 1.5 × 10^11 m`.  Stefan--Boltzmann emission
and isotropic spherical dilution determine the arriving power per unit area.

Length, radiant power, irradiance, and the Stefan--Boltzmann constant are
represented by Physlib dimensionful quantities.  Absolute temperature uses
Physlib's `Temperature`.  Real numbers below are used only for named SI
readouts and the numerical values printed in the problem and answer choices.

Assumption/target split:

* `MatchesProblemStatement` records the perfect-emitter model, temperature,
  and solar radius;
* `MatchesPrimarySunEarthFigure` records the body labels, connector lines, and
  the displayed Sun--Earth distance;
* `UsesTextbookStefanBoltzmannConstant` calibrates the governing constant;
* `SatisfiesPerfectEmitterRadiationLaws` states blackbody emission, spherical
  luminosity, and inverse-square propagation; and
* `powerPerUnitArea_arrivingAtEarth_matches_answer_D` concludes the requested
  Earth irradiance and answer choice.  Its numerical conclusion occurs in no
  premise or setup field.
-/

/-! ## Dimensionful quantities and named SI readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative radiant power, with SI unit watt. -/
abbrev RadiantPowerQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹)
      NNReal)

/-- A nonnegative irradiance (radiant power per area), with SI unit `W / m²`. -/
abbrev IrradianceQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-!
The Stefan--Boltzmann constant has SI unit `W / (m² K⁴)`, hence physical
dimension `mass * time⁻³ * temperature⁻⁴`.
-/
abbrev StefanBoltzmannConstantQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹ *
        Θ𝓭⁻¹ * Θ𝓭⁻¹ * Θ𝓭⁻¹ * Θ𝓭⁻¹)
      NNReal)

/-- Read a physical length in SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a radiant power in SI watts. -/
def radiantPowerInWatts (power : RadiantPowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Read an irradiance in SI watts per square metre. -/
def irradianceInWattsPerSquareMeter (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- Read the Stefan--Boltzmann constant in SI `W / (m² K⁴)`. -/
def stefanBoltzmannConstantInSI
    (constant : StefanBoltzmannConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-!
Read a Physlib absolute temperature in kelvins.  The explicit storage unit is
needed because `Temperature` stores a nonnegative magnitude in an arbitrary
zero-preserving temperature unit.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Physical source, observation, and primary-figure vocabulary -/

/-- Radiation model assigned to the Sun by the problem statement. -/
inductive ThermalEmitterModel where
  | perfectBlackbody
  deriving DecidableEq, Repr

/-- The two named celestial bodies shown in the primary figure. -/
inductive CelestialBodyLabel where
  | sun
  | earth
  deriving DecidableEq, Fintype, Repr

/-- The separation symbol printed above the connector lines in the figure. -/
inductive FigureDistanceSymbol where
  | r
  deriving DecidableEq, Repr

/-!
Raw information represented by the primary bitmap.  Its two yellow boundary
lines connect the left-hand Sun to the right-hand Earth, and the displayed
distance carries the label `r`.
-/
structure SunEarthFigure where
  leftBody : CelestialBodyLabel
  rightBody : CelestialBodyLabel
  bodyNameShown : CelestialBodyLabel → Bool
  distanceSymbol : FigureDistanceSymbol
  displayedDistance : LengthQuantity
  yellowConnectorLineCount : ℕ

/-!
The spherical stellar emitter.  Surface radiant exitance, total luminosity,
and temperature are independent physical quantities; their relations are
supplied only by the governing-law structure below.
-/
structure SphericalStellarEmitter where
  model : ThermalEmitterModel
  temperatureStorageUnit : TemperatureUnit
  surfaceTemperature : Temperature
  radius : LengthQuantity
  surfaceRadiantExitance : IrradianceQuantity
  luminosity : RadiantPowerQuantity

/-!
All physical quantities in the Sun--Earth setup.  In particular,
`irradianceAtEarth` is an independent observable, not a definition involving
an answer choice or the requested numerical value.
-/
structure SolarIrradianceSetup where
  sun : SphericalStellarEmitter
  sunEarthDistance : LengthQuantity
  irradianceAtEarth : IrradianceQuantity
  stefanBoltzmannConstant : StefanBoltzmannConstantQuantity
  figure : SunEarthFigure

/-! ## Problem data, figure readouts, and governing laws -/

/-- The perfect-emitter model and numerical source data stated in the prose. -/
structure MatchesProblemStatement (setup : SolarIrradianceSetup) : Prop where
  sunIsPerfectEmitter : setup.sun.model = .perfectBlackbody
  temperatureStoredInKelvins :
    setup.sun.temperatureStorageUnit = TemperatureUnit.kelvin
  sunTemperatureKelvins :
    temperatureInKelvins setup.sun.temperatureStorageUnit
      setup.sun.surfaceTemperature = 5500
  sunRadiusMeters :
    lengthInMeters setup.sun.radius = 7 * 10 ^ 8

/-!
Primary-image readout: Sun is on the left, Earth is on the right, both names
are shown, two yellow connector lines are drawn, and their displayed
separation is `r = 1.5 × 10^11 m`.
-/
structure MatchesPrimarySunEarthFigure
    (setup : SolarIrradianceSetup) : Prop where
  sunOnLeft : setup.figure.leftBody = .sun
  earthOnRight : setup.figure.rightBody = .earth
  sunNameShown : setup.figure.bodyNameShown .sun = true
  earthNameShown : setup.figure.bodyNameShown .earth = true
  separationLabeledR : setup.figure.distanceSymbol = .r
  displayedDistanceIsSetupDistance :
    setup.figure.displayedDistance = setup.sunEarthDistance
  displayedDistanceMeters :
    lengthInMeters setup.figure.displayedDistance = 15 * 10 ^ 10
  twoYellowConnectorLines : setup.figure.yellowConnectorLineCount = 2

/-!
The standard textbook calibration `σ = 5.67 × 10⁻⁸ W/(m² K⁴)`.  This is an
input constant for the Stefan--Boltzmann law, not the requested irradiance.
-/
structure UsesTextbookStefanBoltzmannConstant
    (setup : SolarIrradianceSetup) : Prop where
  constantValueInSI :
    stefanBoltzmannConstantInSI setup.stefanBoltzmannConstant =
      567 / 10 ^ 10

/-- Positivity of the physical source, geometry, and radiation constant. -/
structure HasPhysicalSolarIrradianceParameters
    (setup : SolarIrradianceSetup) : Prop where
  absoluteTemperaturePositive :
    0 < temperatureInKelvins setup.sun.temperatureStorageUnit
      setup.sun.surfaceTemperature
  sunRadiusPositive : 0 < lengthInMeters setup.sun.radius
  sunEarthDistancePositive : 0 < lengthInMeters setup.sunEarthDistance
  stefanBoltzmannConstantPositive :
    0 < stefanBoltzmannConstantInSI setup.stefanBoltzmannConstant

/-!
The governing radiation laws.  A perfect blackbody has surface radiant
exitance `σ T⁴`; its spherical surface produces luminosity
`4 π R² M`; and isotropic propagation spreads that luminosity across the
sphere of radius equal to the Sun--Earth separation.  None of these fields
contains the recorded `1100 W/m²` answer.
-/
structure SatisfiesPerfectEmitterRadiationLaws
    (setup : SolarIrradianceSetup) : Prop where
  stefanBoltzmannSurfaceLaw :
    irradianceInWattsPerSquareMeter setup.sun.surfaceRadiantExitance =
      stefanBoltzmannConstantInSI setup.stefanBoltzmannConstant *
        temperatureInKelvins setup.sun.temperatureStorageUnit
          setup.sun.surfaceTemperature ^ 4
  sphericalSurfaceLuminosity :
    radiantPowerInWatts setup.sun.luminosity =
      4 * Real.pi * lengthInMeters setup.sun.radius ^ 2 *
        irradianceInWattsPerSquareMeter setup.sun.surfaceRadiantExitance
  isotropicSphericalPropagation :
    irradianceInWattsPerSquareMeter setup.irradianceAtEarth *
        (4 * Real.pi * lengthInMeters setup.sunEarthDistance ^ 2) =
      radiantPowerInWatts setup.sun.luminosity

/-! ## Derived irradiance and displayed answer -/

/-!
Combining blackbody emission with spherical dilution gives the usual solar
irradiance formula.  This is a derived relation, not one of the law fields.
-/
lemma earthIrradiance_eq_stefanBoltzmann_times_radiusRatioSq
    (setup : SolarIrradianceSetup)
    (_physical : HasPhysicalSolarIrradianceParameters setup)
    (_laws : SatisfiesPerfectEmitterRadiationLaws setup) :
    irradianceInWattsPerSquareMeter setup.irradianceAtEarth =
      stefanBoltzmannConstantInSI setup.stefanBoltzmannConstant *
        temperatureInKelvins setup.sun.temperatureStorageUnit
            setup.sun.surfaceTemperature ^ 4 *
          (lengthInMeters setup.sun.radius /
            lengthInMeters setup.sunEarthDistance) ^ 2 := by
  have hd : lengthInMeters setup.sunEarthDistance ≠ 0 :=
    ne_of_gt _physical.sunEarthDistancePositive
  have h := _laws.isotropicSphericalPropagation
  rw [_laws.sphericalSurfaceLuminosity,
    _laws.stefanBoltzmannSurfaceLaw] at h
  field_simp [hd]
  nlinarith [Real.pi_pos]

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Irradiance readout in `W/m²` printed beside each answer label. -/
def answerIrradianceInWattsPerSquareMeter : AnswerChoice → ℝ
  | .A => 1050
  | .B => 1200
  | .C => 1000
  | .D => 1100

/-!
The arriving irradiance lies within `50 W/m²` of `1100 W/m²`, so it rounds to
`1100 W/m²` to the nearest hundred; moreover D is at least as close as every
displayed alternative.  Thus the recorded answer is D.  The tolerance is
needed because the supplied physical data and `σ` are rounded measurements.
-/
theorem powerPerUnitArea_arrivingAtEarth_matches_answer_D
    (setup : SolarIrradianceSetup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimarySunEarthFigure setup)
    (_constant : UsesTextbookStefanBoltzmannConstant setup)
    (_physical : HasPhysicalSolarIrradianceParameters setup)
    (_laws : SatisfiesPerfectEmitterRadiationLaws setup) :
    |irradianceInWattsPerSquareMeter setup.irradianceAtEarth -
        answerIrradianceInWattsPerSquareMeter .D| ≤ 50 ∧
      answerIrradianceInWattsPerSquareMeter .D = 1100 ∧
      ∀ alternative : AnswerChoice,
        |irradianceInWattsPerSquareMeter setup.irradianceAtEarth -
            answerIrradianceInWattsPerSquareMeter .D| ≤
          |irradianceInWattsPerSquareMeter setup.irradianceAtEarth -
            answerIrradianceInWattsPerSquareMeter alternative| := by
  have hdistance :
      lengthInMeters setup.sunEarthDistance = 15 * 10 ^ 10 := by
    rw [← _figure.displayedDistanceIsSetupDistance]
    exact _figure.displayedDistanceMeters
  rw [earthIrradiance_eq_stefanBoltzmann_times_radiusRatioSq
      setup _physical _laws,
    _constant.constantValueInSI, _problem.sunTemperatureKelvins,
    _problem.sunRadiusMeters, hdistance]
  constructor
  · norm_num [answerIrradianceInWattsPerSquareMeter]
  constructor
  · rfl
  intro alternative
  cases alternative <;>
    norm_num [answerIrradianceInWattsPerSquareMeter]

end PhyXMiniProblems.ProblemPhyXMini0489
