import Mathlib.Analysis.Calculus.Deriv.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0156

open Dimension

/-!
# Temperature rate for an extremely slow thermally driven source

A radioactive source is fastened to one end of an aluminum rod, whose other
end is fixed by a clamp.  An electric heater controls the temperature of an
effective central segment of length `d`.  Expansion of that segment moves the
source along the rod axis.

The problem asks for the constant temperature-change rate when `d = 2.00 cm`
and the source speed is `100 nm/s`.  Physical quantities below use Physlib's
unit-independent `Dimensionful (WithDim ...)` representation; real numbers
occur only as readouts in explicitly named units and as dimensionless angles.

The supplied image file is inconsistent with the problem and auxiliary
caption: it shows laser refraction through a prism, with angles `30 degrees`,
`60 degrees`, and `22.6 degrees`.  Both the image readouts and the narrated rod
diagram are retained, but the laser image contributes no thermal premise.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed position along the clamp-to-source rod axis. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent physical time coordinate. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A signed thermodynamic temperature readout. -/
abbrev TemperatureQuantity : Type := Dimensionful (WithDim Θ𝓭 ℝ)

/-- Temperature change per time, with dimension `temperature / time`. -/
abbrev TemperatureRateQuantity : Type :=
  Dimensionful (WithDim (Θ𝓭 * T𝓭⁻¹) ℝ)

/-- A linear thermal-expansion coefficient, with inverse-temperature dimension. -/
abbrev LinearExpansionCoefficientQuantity : Type :=
  Dimensionful (WithDim Θ𝓭⁻¹ ℝ)

/-- The nonnegative physical speed type supplied by Physlib. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a signed physical position in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (position : SignedLengthQuantity) : ℝ :=
  (position { UnitChoices.SI with length := unit }).val

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed { UnitChoices.SI with
    length := lengthUnit, time := timeUnit }).val : ℝ)

/-- Read a temperature in a selected temperature unit. -/
def temperatureReadout
    (unit : TemperatureUnit) (temperature : TemperatureQuantity) : ℝ :=
  (temperature { UnitChoices.SI with temperature := unit }).val

/-- Read a temperature rate in selected temperature and time units. -/
def temperatureRateReadout
    (temperatureUnit : TemperatureUnit) (timeUnit : TimeUnit)
    (rate : TemperatureRateQuantity) : ℝ :=
  (rate { UnitChoices.SI with
    temperature := temperatureUnit, time := timeUnit }).val

/-- Read a linear expansion coefficient in the inverse of a temperature unit. -/
def expansionCoefficientReadout
    (temperatureUnit : TemperatureUnit)
    (coefficient : LinearExpansionCoefficientQuantity) : ℝ :=
  (coefficient { UnitChoices.SI with temperature := temperatureUnit }).val

/-- The metre readout used by the SI expansion law. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The centimetre readout in which the effective heater length is stated. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The SI speed readout in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- The source-speed readout in nanometres per second used in the question. -/
def speedInNanometersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.nanometers TimeUnit.seconds speed

/-- The SI temperature-rate readout in kelvins per second. -/
def temperatureRateInKelvinsPerSecond
    (rate : TemperatureRateQuantity) : ℝ :=
  temperatureRateReadout TemperatureUnit.kelvin TimeUnit.seconds rate

/-- The aluminum expansion-coefficient readout in inverse kelvins. -/
def expansionCoefficientPerKelvin
    (coefficient : LinearExpansionCoefficientQuantity) : ℝ :=
  expansionCoefficientReadout TemperatureUnit.kelvin coefficient

/-- Embed a real number of seconds as a dimensionful time. -/
def timeOfSeconds (seconds : ℝ) : TimeQuantity :=
  CarriesDimension.toDimensionful UnitChoices.SI
    (show WithDim T𝓭 ℝ from ⟨seconds⟩)

/-! ## Physical roles and figure provenance -/

/-- The material named for the rod. -/
inductive RodMaterial where
  | aluminum
  deriving DecidableEq, Repr

/-- Labeled apparatus components in the narrated thermal-expansion diagram. -/
inductive RodComponent where
  | radioactiveSource
  | electricHeater
  | clamp
  deriving DecidableEq, Repr

/-- Qualitative regions along the rod, ordered as narrated from left to right. -/
inductive RodRegion where
  | sourceEnd
  | centralSection
  | clampEnd
  deriving DecidableEq, Repr

/-- The clamp condition used to turn expansion into source displacement. -/
inductive ClampCondition where
  | fixed
  deriving DecidableEq, Repr

/-- How the heater temperature is controlled. -/
inductive HeaterControl where
  | constantTemperatureRate
  deriving DecidableEq, Repr

/-- Positive axial direction, chosen to point outward from clamp to source. -/
inductive RodAxisOrientation where
  | clampTowardSource
  deriving DecidableEq, Repr

/-- The two incompatible scenes represented by the source materials. -/
inductive FigureScene where
  | heatedRodApparatus
  | laserPrismRefraction
  deriving DecidableEq, Repr

/-- The chapter's explicit policy for resolving figure/caption evidence. -/
inductive FigureEvidencePolicy where
  | imagePrimary
  deriving DecidableEq, Repr

/-- Angle labels visible only in the supplied laser/prism image. -/
inductive PrimaryImageAngle where
  | upperPrismInterior
  | lowerPrismInterior
  | outgoingRayBelowHorizontal
  deriving DecidableEq, Repr

/-!
The experiment state and its dimensionful histories.

`sourceOutwardPosition` is measured along the positive axis from the fixed
clamp toward the source, so heating an aluminum segment gives a positive
position derivative.  No numerical value is built into `temperatureRate`.
-/
structure ThermalExpansionSetup where
  rodMaterial : RodMaterial
  componentRegion : RodComponent → RodRegion
  clampCondition : ClampCondition
  heaterControl : HeaterControl
  positiveAxis : RodAxisOrientation
  effectiveHeatedLengthD : LengthQuantity
  linearExpansionCoefficientAlpha : LinearExpansionCoefficientQuantity
  sourceSpeedMagnitude : SpeedQuantity
  temperatureRate : TemperatureRateQuantity
  sourceOutwardPosition : TimeQuantity → SignedLengthQuantity
  rodTemperature : TimeQuantity → TemperatureQuantity
  primaryImageScene : FigureScene
  auxiliaryCaptionScene : FigureScene
  evidencePolicy : FigureEvidencePolicy
  primaryImageAngleDegrees : PrimaryImageAngle → ℝ

/-- The source-position metre readout as a function of seconds. -/
def sourcePositionInMetersAtSeconds
    (setup : ThermalExpansionSetup) (seconds : ℝ) : ℝ :=
  signedLengthReadout LengthUnit.meters
    (setup.sourceOutwardPosition (timeOfSeconds seconds))

/-- The rod-temperature kelvin readout as a function of seconds. -/
def rodTemperatureInKelvinsAtSeconds
    (setup : ThermalExpansionSetup) (seconds : ℝ) : ℝ :=
  temperatureReadout TemperatureUnit.kelvin
    (setup.rodTemperature (timeOfSeconds seconds))

/-!
Problem-text information: an aluminum rod is fixed at the clamp, and the
heater is controlled at a constant temperature-change rate.  These are setup
facts, not a value for that rate.
-/
structure MatchesProblemDescription (setup : ThermalExpansionSetup) : Prop where
  aluminum_rod : setup.rodMaterial = .aluminum
  clamp_is_fixed : setup.clampCondition = .fixed
  heater_is_rate_controlled : setup.heaterControl = .constantTemperatureRate
  outward_axis : setup.positiveAxis = .clampTowardSource

/-!
Spatial labels from the narrated rod diagram and auxiliary caption.  They are
kept separate from the conflicting primary image readout.
-/
structure MatchesNarratedRodDiagram (setup : ThermalExpansionSetup) : Prop where
  source_at_left_end :
    setup.componentRegion .radioactiveSource = .sourceEnd
  heater_on_central_section :
    setup.componentRegion .electricHeater = .centralSection
  clamp_at_right_end : setup.componentRegion .clamp = .clampEnd

/-!
Audit of the actual supplied image.  The image shows a laser/prism scene rather
than the narrated thermal apparatus.  Its three printed angles are retained
as dimensionless degree readouts but are not used in the expansion law.
-/
structure RecordsProvidedFigureMismatch (setup : ThermalExpansionSetup) : Prop where
  primary_is_laser_prism : setup.primaryImageScene = .laserPrismRefraction
  caption_is_heated_rod : setup.auxiliaryCaptionScene = .heatedRodApparatus
  image_is_primary_evidence : setup.evidencePolicy = .imagePrimary
  upper_angle : setup.primaryImageAngleDegrees .upperPrismInterior = 30
  lower_angle : setup.primaryImageAngleDegrees .lowerPrismInterior = 60
  outgoing_angle :
    setup.primaryImageAngleDegrees .outgoingRayBelowHorizontal = 113 / 5

/-!
The two numerical data readouts in the question.  The effective heated length
is `2.00 cm`; the source speed magnitude is `100 nm/s`.
-/
structure HasStatedLengthAndSpeed (setup : ThermalExpansionSetup) : Prop where
  effective_length_cm : lengthInCentimeters setup.effectiveHeatedLengthD = 2
  source_speed_nm_per_s :
    speedInNanometersPerSecond setup.sourceSpeedMagnitude = 100

/-!
Standard linear-expansion calibration for aluminum used by the exercise:
`alpha = 23 * 10^-6 K^-1`.  This is a material property, not the requested
temperature rate.
-/
structure UsesAluminumExpansionCalibration
    (setup : ThermalExpansionSetup) : Prop where
  coefficient_per_kelvin :
    expansionCoefficientPerKelvin setup.linearExpansionCoefficientAlpha =
      23 / 1000000

/-!
The stated speed and requested temperature change are constant in time.  The
derivatives are taken after reading time in seconds, position in metres, and
temperature in kelvins.
-/
structure HasConstantReadoutRates (setup : ThermalExpansionSetup) : Prop where
  source_motion : ∀ seconds : ℝ,
    HasDerivAt (sourcePositionInMetersAtSeconds setup)
      (speedInMetersPerSecond setup.sourceSpeedMagnitude) seconds
  temperature_change : ∀ seconds : ℝ,
    HasDerivAt (rodTemperatureInKelvinsAtSeconds setup)
      (temperatureRateInKelvinsPerSecond setup.temperatureRate) seconds

/-!
The governing one-dimensional linear thermal-expansion rate law

`v = alpha * d * dT/dt`.

It relates the unknown rate to independent material, geometry, and speed
parameters; it does not state any numerical answer to the question.
-/
structure ObeysLinearThermalExpansionRateLaw
    (setup : ThermalExpansionSetup) : Prop where
  rate_law :
    speedInMetersPerSecond setup.sourceSpeedMagnitude =
      expansionCoefficientPerKelvin setup.linearExpansionCoefficientAlpha *
        lengthInMeters setup.effectiveHeatedLengthD *
          temperatureRateInKelvinsPerSecond setup.temperatureRate

/-- Convert the two stated readouts to the SI values used in the rate law. -/
lemma stated_length_and_speed_in_si
    (setup : ThermalExpansionSetup)
    (_data : HasStatedLengthAndSpeed setup) :
    lengthInMeters setup.effectiveHeatedLengthD = 1 / 50 ∧
      speedInMetersPerSecond setup.sourceSpeedMagnitude = 1 / 10000000 := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h_units := length.2 UnitChoices.SI
      ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
    have h_units_real := congrArg
      (fun reading : WithDim L𝓭 NNReal => (reading.val : ℝ)) h_units
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val] at h_units_real ⊢
    exact h_units_real
  have speed_nanometers_eq (speed : SpeedQuantity) :
      speedInNanometersPerSecond speed =
        1000000000 * speedInMetersPerSecond speed := by
    have h_units := speed.2 UnitChoices.SI
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    have h_units_real := congrArg
      (fun reading : WithDim (L𝓭 * T𝓭⁻¹) NNReal => (reading.val : ℝ)) h_units
    norm_num [speedInNanometersPerSecond, speedInMetersPerSecond, speedReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, TimeUnit.seconds,
      TimeUnit.div_eq_val] at h_units_real ⊢
    exact h_units_real
  rcases _data with ⟨h_length_cm, h_speed_nm⟩
  rw [length_centimeters_eq] at h_length_cm
  rw [speed_nanometers_eq] at h_speed_nm
  constructor <;> norm_num at h_length_cm h_speed_nm ⊢ <;> nlinarith

/-! ## Multiple-choice readouts and target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Temperature-rate readout in kelvins per second printed by each choice. -/
def answerTemperatureRateKelvinPerSecond : AnswerChoice → ℝ
  | .A => 195 / 1000
  | .B => 204 / 1000
  | .C => 212 / 1000
  | .D => 217 / 1000

/-- Dataset metadata recording answer D; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
A physical rate matches a three-decimal-place answer when its SI readout is
within half of `0.001 K/s` of the displayed number.
-/
def MatchesAnswerToNearestThousandthKelvinPerSecond
    (rate : TemperatureRateQuantity) (choice : AnswerChoice) : Prop :=
  |temperatureRateInKelvinsPerSecond rate -
      answerTemperatureRateKelvinPerSecond choice| < 1 / 2000

/-!
With `d = 2.00 cm`, `v = 100 nm/s`, and
`alpha = 23 * 10^-6 K^-1`, the governing law gives the exact rate
`5/23 K/s`.  Its nearest-thousandth readout is `0.217 K/s`, answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0156:target`.
-/
theorem problem_phyx_mini_0156
    (setup : ThermalExpansionSetup)
    (_problem : MatchesProblemDescription setup)
    (_diagram : MatchesNarratedRodDiagram setup)
    (_figureAudit : RecordsProvidedFigureMismatch setup)
    (_data : HasStatedLengthAndSpeed setup)
    (_aluminum : UsesAluminumExpansionCalibration setup)
    (_constantRates : HasConstantReadoutRates setup)
    (_expansion : ObeysLinearThermalExpansionRateLaw setup) :
    temperatureRateInKelvinsPerSecond setup.temperatureRate = 5 / 23 ∧
      MatchesAnswerToNearestThousandthKelvinPerSecond
        setup.temperatureRate .D := by
  have h_si := stated_length_and_speed_in_si setup _data
  have h_rate := _expansion.rate_law
  rw [h_si.1, h_si.2, _aluminum.coefficient_per_kelvin] at h_rate
  have h_temperature_rate :
      temperatureRateInKelvinsPerSecond setup.temperatureRate = 5 / 23 := by
    norm_num at h_rate ⊢
    linarith
  refine ⟨h_temperature_rate, ?_⟩
  unfold MatchesAnswerToNearestThousandthKelvinPerSecond
  rw [h_temperature_rate]
  norm_num [answerTemperatureRateKelvinPerSecond, abs_lt]

end PhyXMiniProblems.ProblemPhyXMini0156
