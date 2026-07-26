import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0123

open Dimension

/-!
# Smallest resolvable detail in quasar 3C 405

The orbiting radio telescope and the ground-based VLBA are modeled as an
interferometer whose effective circular-aperture diameter is the projected
space-to-Earth baseline. The radio wavelength is determined by `c = λ f`.
Rayleigh's circular-aperture criterion gives the angular resolution, and the
small-angle relation converts that angle to a physical length at the quasar.

Lengths, frequencies, and speeds are genuine dimensionful Physlib quantities.
The scalar real values below are explicit readouts in named units,
dimensionless radian angles, and answer-choice values.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Scalar readout of a physical frequency in inverse selected time units. -/
def frequencyReadout (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Meter readout used for positivity and the SI wave relation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Kilometer readout used by the telescope baseline and answer choices. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Light-year readout used for the source distance and one requested answer. -/
def lengthInLightYears (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.lightYears length

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Physlib's exact vacuum speed of light in selected length and time units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- The astronomical source named in the problem. -/
inductive AstronomicalSourceLabel where
  | threeC405
  deriving DecidableEq, Repr

/-- Physical class assigned to the source in the scenario. -/
inductive AstronomicalSourceClass where
  | quasar
  deriving DecidableEq, Repr

/-- Leading qualitative model for the quasar's radiation source. -/
inductive QuasarEmissionModel where
  | accretionAroundSupermassiveBlackHole
  deriving DecidableEq, Repr

/-- Qualitative scale stated for the compact emitting region. -/
inductive EmissionRegionScale where
  | fewLightYearsAcross
  deriving DecidableEq, Repr

/-- Radio-instrument configuration used for the observation. -/
inductive RadioArrayConfiguration where
  | orbitingTelescopeCombinedWithVLBA
  deriving DecidableEq, Repr

/-- Optical regime used to estimate the smallest resolvable detail. -/
inductive ResolutionRegime where
  | circularApertureRayleighParaxial
  deriving DecidableEq, Repr

/-- Distinct qualitative objects visible in the supplied astronomical image. -/
inductive FigureFeature where
  | brightCompactQuasar
  | diffuseHostGalaxyGlow
  | elongatedNormalGalaxies
  deriving DecidableEq, Repr

/-- Qualitative locations distinguished by the astronomical photograph. -/
inductive ImageLocation where
  | belowAndLeftOfCenter
  | surroundingBrightQuasar
  | distributedAcrossField
  deriving DecidableEq, Repr

/-!
All physical quantities and qualitative labels in the problem.

`smallestResolvableDetail` is an unknown physical length. No field gives it a
numerical value or identifies an answer choice.
-/
structure QuasarResolutionSetup where
  source : AstronomicalSourceLabel
  sourceClass : AstronomicalSourceClass
  emissionModel : QuasarEmissionModel
  emissionRegionScale : EmissionRegionScale
  arrayConfiguration : RadioArrayConfiguration
  resolutionRegime : ResolutionRegime
  imageShows : FigureFeature → Prop
  featureLocation : FigureFeature → ImageLocation
  emissionRegionDiameter : LengthQuantity
  spaceTelescopeEarthSeparation : LengthQuantity
  effectiveApertureDiameter : LengthQuantity
  sourceDistance : LengthQuantity
  radioFrequency : FrequencyQuantity
  vacuumWavelength : LengthQuantity
  angularResolutionRad : ℝ
  smallestResolvableDetail : LengthQuantity

/-!
Qualitative scenario and primary-image readouts. The image contains the bright
compact quasar, diffuse host-galaxy glow, and elongated normal galaxies; it
supplies no numerical length scale.
-/
def MatchesScenarioAndFigure (setup : QuasarResolutionSetup) : Prop :=
  setup.source = .threeC405 ∧
    setup.sourceClass = .quasar ∧
    setup.emissionModel = .accretionAroundSupermassiveBlackHole ∧
    setup.emissionRegionScale = .fewLightYearsAcross ∧
    setup.arrayConfiguration = .orbitingTelescopeCombinedWithVLBA ∧
    setup.resolutionRegime = .circularApertureRayleighParaxial ∧
    setup.imageShows .brightCompactQuasar ∧
    setup.imageShows .diffuseHostGalaxyGlow ∧
    setup.imageShows .elongatedNormalGalaxies ∧
    setup.featureLocation .brightCompactQuasar = .belowAndLeftOfCenter ∧
    setup.featureLocation .diffuseHostGalaxyGlow = .surroundingBrightQuasar ∧
    setup.featureLocation .elongatedNormalGalaxies = .distributedAcrossField

/-!
Numerical data explicitly stated in the problem: a `77,000 km` space-to-Earth
baseline, distance `7.2 * 10^8` light-years, and radio frequency `1665 MHz`.
The latter is recorded as `1665 * 10^6 Hz`.
-/
def MatchesProblemReadouts (setup : QuasarResolutionSetup) : Prop :=
  lengthInKilometers setup.spaceTelescopeEarthSeparation = 77000 ∧
    lengthInLightYears setup.sourceDistance = (36 / 5 : ℝ) * 10 ^ 8 ∧
    frequencyInHertz setup.radioFrequency = 1665 * 10 ^ 6

/-- Positivity and angular-range conditions for the physical configuration. -/
def HasPhysicalParameters (setup : QuasarResolutionSetup) : Prop :=
  0 < lengthInMeters setup.emissionRegionDiameter ∧
    0 < lengthInMeters setup.spaceTelescopeEarthSeparation ∧
    0 < lengthInMeters setup.effectiveApertureDiameter ∧
    0 < lengthInMeters setup.sourceDistance ∧
    0 < frequencyInHertz setup.radioFrequency ∧
    0 < lengthInMeters setup.vacuumWavelength ∧
    0 < setup.angularResolutionRad ∧
    setup.angularResolutionRad < 1 ∧
    0 < lengthInMeters setup.smallestResolvableDetail

/-!
The problem's interferometric idealization: combining the orbiting receiver
with the VLBA gives the resolution of one circular aperture whose diameter is
the space-to-Earth baseline. This is required in every length unit.
-/
structure SatisfiesInterferometricApertureModel
    (setup : QuasarResolutionSetup) : Prop where
  effectiveDiameterEqualsBaseline :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.effectiveApertureDiameter =
        lengthReadout unit setup.spaceTelescopeEarthSeparation

/-!
Vacuum electromagnetic-wave dispersion, `c = λ f`, in every compatible
choice of length and time units. This determines the wavelength but not the
requested resolvable size.
-/
structure SatisfiesVacuumWaveLaw (setup : QuasarResolutionSetup) : Prop where
  speedEqualsWavelengthTimesFrequency :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      vacuumSpeedOfLightReadout lengthUnit timeUnit =
        lengthReadout lengthUnit setup.vacuumWavelength *
          frequencyReadout timeUnit setup.radioFrequency

/-!
Rayleigh's circular-aperture criterion `θ = 1.22 λ / D`, with the radian
angle dimensionless. The factor `1.22` is represented exactly by `61 / 50`.
-/
structure SatisfiesRayleighCriterion (setup : QuasarResolutionSetup) : Prop where
  angularResolutionLaw :
    ∀ unit : LengthUnit,
      setup.angularResolutionRad =
        (61 / 50 : ℝ) * lengthReadout unit setup.vacuumWavelength /
          lengthReadout unit setup.effectiveApertureDiameter

/-!
Small-angle geometry at the source: the physical linear detail is the source
distance times the angular resolution. This is a governing relation, not a
numerical assignment of the unknown detail.
-/
structure SatisfiesParaxialResolutionGeometry
    (setup : QuasarResolutionSetup) : Prop where
  linearResolutionLaw :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.smallestResolvableDetail =
        lengthReadout unit setup.sourceDistance * setup.angularResolutionRad

/-- Labels of the four kilometer-valued choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Kilometer readout displayed beside each answer choice. -/
def displayedDetailKilometers : AnswerChoice → ℝ
  | .A => 194 * 10 ^ 11
  | .B => 193 * 10 ^ 10
  | .C => 195 * 10 ^ 12
  | .D => 192 * 10 ^ 9

/-- Place value of the last displayed significant digit, in kilometers. -/
def displayedPrecisionKilometers : AnswerChoice → ℝ
  | .A => 10 ^ 11
  | .B => 10 ^ 10
  | .C => 10 ^ 12
  | .D => 10 ^ 9

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Agreement of the derived detail with a displayed kilometer answer. -/
def MatchesDisplayedKilometerChoice
    (setup : QuasarResolutionSetup) (choice : AnswerChoice) : Prop :=
  |lengthInKilometers setup.smallestResolvableDetail -
      displayedDetailKilometers choice| ≤
    displayedPrecisionKilometers choice / 2

/-- The light-year answer rounds to `2.05 ly` at the stated precision. -/
def RoundsToLightYearAnswer (setup : QuasarResolutionSetup) : Prop :=
  |lengthInLightYears setup.smallestResolvableDetail - (41 / 20 : ℝ)| ≤
    1 / 200

/-!
For 3C 405 at `7.2 * 10^8 ly`, observed at `1665 MHz` with the effective
`77,000 km` aperture, the Rayleigh and paraxial laws give a smallest detail of
approximately `2.05 ly`, or `1.94 * 10^13 km`, which is answer A.

This formalizes `thm:physics:phyx_mini_0123:target`.
-/
theorem problem_phyx_mini_0123
    (setup : QuasarResolutionSetup)
    (h_scenario : MatchesScenarioAndFigure setup)
    (h_data : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_interferometry : SatisfiesInterferometricApertureModel setup)
    (h_wave : SatisfiesVacuumWaveLaw setup)
    (h_rayleigh : SatisfiesRayleighCriterion setup)
    (h_geometry : SatisfiesParaxialResolutionGeometry setup) :
    RoundsToLightYearAnswer setup ∧
      MatchesDisplayedKilometerChoice setup .A := by
  rcases h_data with ⟨h_baseline_km, h_distance_ly, h_frequency_hz⟩
  have h_effective_km :=
    h_interferometry.effectiveDiameterEqualsBaseline LengthUnit.kilometers
  change
    lengthInKilometers setup.effectiveApertureDiameter =
      lengthInKilometers setup.spaceTelescopeEarthSeparation at h_effective_km
  have h_effective_km_value :
      lengthInKilometers setup.effectiveApertureDiameter = 77000 := by
    exact h_effective_km.trans h_baseline_km
  have h_c_km :
      vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds =
        (299792458 / 1000 : ℝ) := by
    norm_num [vacuumSpeedOfLightReadout, DimSpeed.speedOfLight,
      CarriesDimension.toDimensionful_apply_apply, UnitChoices.dimScale,
      LengthUnit.kilometers, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val, TimeUnit.seconds, TimeUnit.div_eq_val,
      WithDim.smul_val, NNReal.smul_def]
    change (1 / 1000 : ℝ) * 299792458 = 149896229 / 500
    norm_num
  have h_wave_km :=
    h_wave.speedEqualsWavelengthTimesFrequency
      LengthUnit.kilometers TimeUnit.seconds
  change
    vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds =
      lengthInKilometers setup.vacuumWavelength *
        frequencyInHertz setup.radioFrequency at h_wave_km
  rw [h_c_km, h_frequency_hz] at h_wave_km
  have h_wavelength_km :
      lengthInKilometers setup.vacuumWavelength =
        (299792458 : ℝ) / (1000 * (1665 * 10 ^ 6)) := by
    norm_num at h_wave_km ⊢
    linarith
  have h_angle :=
    h_rayleigh.angularResolutionLaw LengthUnit.kilometers
  change
    setup.angularResolutionRad =
      (61 / 50 : ℝ) * lengthInKilometers setup.vacuumWavelength /
        lengthInKilometers setup.effectiveApertureDiameter at h_angle
  rw [h_wavelength_km, h_effective_km_value] at h_angle
  have h_angle_value :
      setup.angularResolutionRad =
        (1306238567 : ℝ) / 457875000000000000 := by
    norm_num at h_angle ⊢
    exact h_angle
  have h_detail_ly_law :=
    h_geometry.linearResolutionLaw LengthUnit.lightYears
  change
    lengthInLightYears setup.smallestResolvableDetail =
      lengthInLightYears setup.sourceDistance *
        setup.angularResolutionRad at h_detail_ly_law
  rw [h_distance_ly, h_angle_value] at h_detail_ly_law
  have h_detail_ly :
      lengthInLightYears setup.smallestResolvableDetail =
        (1306238567 : ℝ) / 635937500 := by
    norm_num at h_detail_ly_law ⊢
    exact h_detail_ly_law
  have h_detail_km_conversion :
      lengthInKilometers setup.smallestResolvableDetail =
        (9460730472580800 / 1000 : ℝ) *
          lengthInLightYears setup.smallestResolvableDetail := by
    have h := congrArg (fun x : NNReal => (x : ℝ)) <|
      congrArg WithDim.val <|
        setup.smallestResolvableDetail.2
          ({UnitChoices.SI with length := LengthUnit.lightYears} : UnitChoices)
          ({UnitChoices.SI with length := LengthUnit.kilometers} : UnitChoices)
    change
      lengthInKilometers setup.smallestResolvableDetail =
        _ * lengthInLightYears setup.smallestResolvableDetail at h
    norm_num [lengthInKilometers, lengthInLightYears, lengthReadout,
      UnitChoices.dimScale, LengthUnit.lightYears, LengthUnit.kilometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.smul_def] at h ⊢
    exact h
  have h_detail_km :
      lengthInKilometers setup.smallestResolvableDetail =
        (15447463769096471229642 : ℝ) / 794921875 := by
    rw [h_detail_km_conversion, h_detail_ly]
    norm_num
  constructor
  · change
      |lengthInLightYears setup.smallestResolvableDetail - (41 / 20 : ℝ)| ≤
        1 / 200
    rw [h_detail_ly]
    norm_num [abs_le]
  · change
      |lengthInKilometers setup.smallestResolvableDetail - 194 * 10 ^ 11| ≤
        10 ^ 11 / 2
    rw [h_detail_km]
    norm_num [abs_le]

end PhyXMiniProblems.ProblemPhyXMini0123
