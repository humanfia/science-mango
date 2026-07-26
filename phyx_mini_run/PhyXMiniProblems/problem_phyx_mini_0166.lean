import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0166

open Dimension

/-!
# Mass of a vibrating string from stroboscopic standing-wave data

The string's length, tension, mass, linear mass density, time scales,
frequencies, wavelength, wave speed, amplitude, and transverse displacements
are stored as unit-covariant physical quantities.  Real numbers occur only as
readouts in explicitly chosen units, natural-number mode data, and displayed
answer values.

The primary figure has fixed endpoints, a node at the midpoint, and two
antinodes.  Point `P` labels the left antinode.  Flashes 1 and 5 show opposite
extrema, with flashes 2--4 strictly inside the extremal displacement.
-/

/-- A nonnegative physical length, independent of the selected length unit. -/
abbrev PhysicalLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed transverse displacement, independent of the selected length unit. -/
abbrev TransverseDisplacement : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical time interval. -/
abbrev PhysicalTime : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical frequency. -/
abbrev PhysicalFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical mass. -/
abbrev PhysicalMass : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative force; its SI scalar readout is measured in newtons. -/
abbrev PhysicalForce : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Mass per unit length of the uniform string. -/
abbrev LinearMassDensity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- SI base units with grams selected as the mass unit. -/
noncomputable def gramUnitChoices : UnitChoices :=
  { UnitChoices.SI with mass := MassUnit.grams }

/-- SI base units with minutes selected as the time unit. -/
noncomputable def minuteUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.minutes }

/-- Scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : PhysicalLength) : ℝ :=
  ((length centimeterUnitChoices).val : ℝ)

/-- Scalar readout of a physical length in meters. -/
def lengthInMeters (length : PhysicalLength) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Scalar readout of a signed transverse displacement in centimeters. -/
def displacementInCentimeters (displacement : TransverseDisplacement) : ℝ :=
  (displacement centimeterUnitChoices).val

/-- Scalar readout of a physical time in seconds. -/
def timeInSeconds (time : PhysicalTime) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Scalar readout of a physical frequency in hertz. -/
def frequencyInHertz (frequency : PhysicalFrequency) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Scalar readout of a physical frequency per minute. -/
def frequencyPerMinute (frequency : PhysicalFrequency) : ℝ :=
  ((frequency minuteUnitChoices).val : ℝ)

/-- Scalar SI readout of a force in newtons. -/
def forceInNewtons (force : PhysicalForce) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Scalar readout of a mass in grams. -/
def massInGrams (mass : PhysicalMass) : ℝ :=
  ((mass gramUnitChoices).val : ℝ)

/-- The labels printed beside the five successive stroboscopic profiles. -/
inductive FlashLabel where
  | one
  | two
  | three
  | four
  | five
  deriving DecidableEq, Repr

/-- The one-based ordinal printed next to a stroboscopic profile. -/
def FlashLabel.ordinal : FlashLabel → ℕ
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5

/-- Geometrically distinguished points in the primary standing-wave figure. -/
inductive FigurePoint where
  | leftEndpoint
  | pointP
  | midpointNode
  | rightAntinode
  | rightEndpoint
  deriving DecidableEq, Repr

/-!
All physical quantities required by the calculation and all labeled profile
readouts from the primary figure.  `modeNumber` is the number of half
wavelengths along the fixed string.
-/
structure VibratingStringSetup where
  stringLength : PhysicalLength
  tension : PhysicalForce
  stringMass : PhysicalMass
  linearMassDensity : LinearMassDensity
  waveSpeed : DimSpeed
  wavelength : PhysicalLength
  oscillationPeriod : PhysicalTime
  oscillationFrequency : PhysicalFrequency
  strobeInterval : PhysicalTime
  strobeRate : PhysicalFrequency
  antinodeAmplitude : PhysicalLength
  modeNumber : ℕ
  transverseDisplacement : FlashLabel → FigurePoint → TransverseDisplacement

/-!
Numerical measurements stated in the text and printed on the figure.  In
particular, no mass, density, wave speed, wavelength, period, or oscillation
frequency is specified here.
-/
structure MatchesProblemReadouts (setup : VibratingStringSetup) : Prop where
  string_length_cm : lengthInCentimeters setup.stringLength = 50
  tension_N : forceInNewtons setup.tension = 1
  strobe_flashes_per_minute : frequencyPerMinute setup.strobeRate = 5000
  antinode_amplitude_cm : lengthInCentimeters setup.antinodeAmplitude = 3 / 2

/-!
Readouts and qualitative geometry taken from the primary figure.  The two
lobes have opposite transverse displacements at every flash.  Flashes 1 and 5
are opposite extrema at `P`, and none of the intervening flashes is extremal.
-/
structure MatchesPrimaryFigure (setup : VibratingStringSetup) : Prop where
  second_harmonic : setup.modeNumber = 2
  fixed_left_endpoint :
    ∀ flash,
      displacementInCentimeters
          (setup.transverseDisplacement flash .leftEndpoint) = 0
  fixed_right_endpoint :
    ∀ flash,
      displacementInCentimeters
          (setup.transverseDisplacement flash .rightEndpoint) = 0
  midpoint_is_node :
    ∀ flash,
      displacementInCentimeters
          (setup.transverseDisplacement flash .midpointNode) = 0
  lobes_have_opposite_displacement :
    ∀ flash,
      displacementInCentimeters
          (setup.transverseDisplacement flash .rightAntinode) =
        -displacementInCentimeters
          (setup.transverseDisplacement flash .pointP)
  flash_one_positive_extremum :
    displacementInCentimeters
        (setup.transverseDisplacement .one .pointP) =
      lengthInCentimeters setup.antinodeAmplitude
  flash_five_negative_extremum :
    displacementInCentimeters
        (setup.transverseDisplacement .five .pointP) =
      -lengthInCentimeters setup.antinodeAmplitude
  flash_two_not_extremal :
    |displacementInCentimeters
        (setup.transverseDisplacement .two .pointP)| <
      lengthInCentimeters setup.antinodeAmplitude
  flash_three_not_extremal :
    |displacementInCentimeters
        (setup.transverseDisplacement .three .pointP)| <
      lengthInCentimeters setup.antinodeAmplitude
  flash_four_not_extremal :
    |displacementInCentimeters
        (setup.transverseDisplacement .four .pointP)| <
      lengthInCentimeters setup.antinodeAmplitude

/-- Strict positivity of the physical magnitudes used in the wave laws. -/
structure HasPositiveStringQuantities (setup : VibratingStringSetup) : Prop where
  string_length_positive : 0 < lengthInMeters setup.stringLength
  tension_positive : 0 < forceInNewtons setup.tension
  mass_positive : 0 < massInGrams setup.stringMass
  linear_density_positive :
    0 < ((setup.linearMassDensity UnitChoices.SI).val : ℝ)
  wave_speed_positive : 0 < ((setup.waveSpeed UnitChoices.SI).val : ℝ)
  wavelength_positive : 0 < lengthInMeters setup.wavelength
  period_positive : 0 < timeInSeconds setup.oscillationPeriod
  frequency_positive : 0 < frequencyInHertz setup.oscillationFrequency
  strobe_interval_positive : 0 < timeInSeconds setup.strobeInterval
  strobe_rate_positive : 0 < frequencyInHertz setup.strobeRate
  amplitude_positive : 0 < lengthInCentimeters setup.antinodeAmplitude
  mode_number_positive : 0 < setup.modeNumber

/-!
The physical laws used in the calculation, stated in every coherent choice of
units:

* flash rate and flash interval are reciprocal;
* consecutive opposite extrema are separated by half a period (four flash
  intervals in this observation);
* oscillation frequency and period are reciprocal;
* a fixed-string mode contains `modeNumber` half wavelengths;
* wave speed is wavelength times frequency;
* the stretched-string law is `v² μ = tension`;
* the string is uniform, so `mass = μ length`.

None of these fields specifies the requested numerical mass or an answer
choice.
-/
structure ObeysStandingStringLaws (setup : VibratingStringSetup) : Prop where
  strobe_rate_interval_reciprocal :
    ∀ units : UnitChoices,
      ((setup.strobeRate units).val : ℝ) *
          ((setup.strobeInterval units).val : ℝ) = 1
  consecutive_opposite_extrema_timing :
    ∀ units : UnitChoices,
      ((setup.oscillationPeriod units).val : ℝ) / 2 =
        ((FlashLabel.five.ordinal : ℝ) -
            (FlashLabel.one.ordinal : ℝ)) *
          ((setup.strobeInterval units).val : ℝ)
  frequency_period_reciprocal :
    ∀ units : UnitChoices,
      ((setup.oscillationFrequency units).val : ℝ) *
          ((setup.oscillationPeriod units).val : ℝ) = 1
  fixed_string_mode_geometry :
    ∀ units : UnitChoices,
      (setup.modeNumber : ℝ) * ((setup.wavelength units).val : ℝ) =
        2 * ((setup.stringLength units).val : ℝ)
  wave_speed_eq_wavelength_mul_frequency :
    ∀ units : UnitChoices,
      ((setup.waveSpeed units).val : ℝ) =
        ((setup.wavelength units).val : ℝ) *
          ((setup.oscillationFrequency units).val : ℝ)
  stretched_string_wave_law :
    ∀ units : UnitChoices,
      ((setup.waveSpeed units).val : ℝ) ^ 2 *
          ((setup.linearMassDensity units).val : ℝ) =
        ((setup.tension units).val : ℝ)
  uniform_string_mass_law :
    ∀ units : UnitChoices,
      ((setup.stringMass units).val : ℝ) =
        ((setup.linearMassDensity units).val : ℝ) *
          ((setup.stringLength units).val : ℝ)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The mass readout in grams printed beside an answer choice. -/
def AnswerChoice.massInGrams : AnswerChoice → ℝ
  | .A => 185 / 10
  | .B => 165 / 10
  | .C => 195 / 10
  | .D => 485 / 10

/-- A displayed choice is at least as close as every other displayed mass. -/
def IsClosestDisplayedMass
    (setup : VibratingStringSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |massInGrams setup.stringMass - choice.massInGrams| ≤
      |massInGrams setup.stringMass - other.massInGrams|

/-!
The four flash intervals from flash 1 to the opposite extremum at flash 5
constitute half a cycle.  At 5000 flashes per minute, the full period is
`12/125 s`.
-/
lemma oscillationPeriodInSeconds_eq_twelve_div_oneHundredTwentyFive
    (setup : VibratingStringSetup)
    (_data : MatchesProblemReadouts setup)
    (_positive : HasPositiveStringQuantities setup)
    (_laws : ObeysStandingStringLaws setup) :
    timeInSeconds setup.oscillationPeriod = 12 / 125 := by
  have frequency_per_minute_eq
      (frequency : PhysicalFrequency) :
      frequencyPerMinute frequency =
        60 * frequencyInHertz frequency := by
    have h_units := frequency.2 UnitChoices.SI minuteUnitChoices
    have h_units_real := congrArg
      (fun reading : WithDim T𝓭⁻¹ NNReal => (reading.val : ℝ)) h_units
    norm_num [frequencyPerMinute, frequencyInHertz, minuteUnitChoices,
      UnitChoices.dimScale, TimeUnit.minutes, TimeUnit.seconds,
      TimeUnit.scale, TimeUnit.div_eq_val, NNReal.rpow_neg_one] at h_units_real ⊢
    convert h_units_real using 1
    apply congrArg
      (fun x : ℝ => x * ((frequency UnitChoices.SI).val : ℝ))
    change (60 : ℝ) = (1 / 60)⁻¹
    norm_num
  have h_strobe_rate :
      frequencyInHertz setup.strobeRate = 250 / 3 := by
    have h := _data.strobe_flashes_per_minute
    rw [frequency_per_minute_eq] at h
    norm_num at h ⊢
    linarith
  have h_strobe_interval :
      timeInSeconds setup.strobeInterval = 3 / 250 := by
    have h := _laws.strobe_rate_interval_reciprocal UnitChoices.SI
    change frequencyInHertz setup.strobeRate *
        timeInSeconds setup.strobeInterval = 1 at h
    rw [h_strobe_rate] at h
    norm_num at h ⊢
    linarith
  have h_timing :=
    _laws.consecutive_opposite_extrema_timing UnitChoices.SI
  change timeInSeconds setup.oscillationPeriod / 2 =
      ((FlashLabel.five.ordinal : ℝ) -
        (FlashLabel.one.ordinal : ℝ)) *
        timeInSeconds setup.strobeInterval at h_timing
  rw [h_strobe_interval] at h_timing
  norm_num [FlashLabel.ordinal] at h_timing ⊢
  linarith

/-- The corresponding oscillation frequency is `125/12 Hz`. -/
lemma oscillationFrequencyInHertz_eq_oneHundredTwentyFive_div_twelve
    (setup : VibratingStringSetup)
    (_data : MatchesProblemReadouts setup)
    (_positive : HasPositiveStringQuantities setup)
    (_laws : ObeysStandingStringLaws setup) :
    frequencyInHertz setup.oscillationFrequency = 125 / 12 := by
  have h_period :=
    oscillationPeriodInSeconds_eq_twelve_div_oneHundredTwentyFive
      setup _data _positive _laws
  have h_reciprocal :=
    _laws.frequency_period_reciprocal UnitChoices.SI
  change frequencyInHertz setup.oscillationFrequency *
      timeInSeconds setup.oscillationPeriod = 1 at h_reciprocal
  rw [h_period] at h_reciprocal
  norm_num at h_reciprocal ⊢
  linarith

/-- The pictured second harmonic has wavelength equal to the `0.500 m` string length. -/
lemma wavelengthInMeters_eq_oneHalf
    (setup : VibratingStringSetup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_positive : HasPositiveStringQuantities setup)
    (_laws : ObeysStandingStringLaws setup) :
    lengthInMeters setup.wavelength = 1 / 2 := by
  have length_centimeters_eq
      (length : PhysicalLength) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h_units := length.2 UnitChoices.SI centimeterUnitChoices
    have h_units_real := congrArg
      (fun reading : WithDim L𝓭 NNReal => (reading.val : ℝ)) h_units
    norm_num [lengthInCentimeters, lengthInMeters, centimeterUnitChoices,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val] at h_units_real ⊢
    exact h_units_real
  have h_length :
      lengthInMeters setup.stringLength = 1 / 2 := by
    have h := _data.string_length_cm
    rw [length_centimeters_eq] at h
    norm_num at h ⊢
    linarith
  have h_geometry :=
    _laws.fixed_string_mode_geometry UnitChoices.SI
  change (setup.modeNumber : ℝ) * lengthInMeters setup.wavelength =
      2 * lengthInMeters setup.stringLength at h_geometry
  rw [_figure.second_harmonic, h_length] at h_geometry
  norm_num at h_geometry ⊢
  linarith

/-!
The idealized exact inputs give `2304/125 g = 18.432 g`.  This exposes the
unrounded physical calculation separately from selection among the displayed
choices.
-/
lemma stringMassInGrams_eq_twoThousandThreeHundredFour_div_oneHundredTwentyFive
    (setup : VibratingStringSetup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_positive : HasPositiveStringQuantities setup)
    (_laws : ObeysStandingStringLaws setup) :
    massInGrams setup.stringMass = 2304 / 125 := by
  have length_centimeters_eq
      (length : PhysicalLength) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h_units := length.2 UnitChoices.SI centimeterUnitChoices
    have h_units_real := congrArg
      (fun reading : WithDim L𝓭 NNReal => (reading.val : ℝ)) h_units
    norm_num [lengthInCentimeters, lengthInMeters, centimeterUnitChoices,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val] at h_units_real ⊢
    exact h_units_real
  have mass_grams_eq
      (mass : PhysicalMass) :
      massInGrams mass =
        1000 * (((mass UnitChoices.SI).val : NNReal) : ℝ) := by
    have h_units := mass.2 UnitChoices.SI gramUnitChoices
    have h_units_real := congrArg
      (fun reading : WithDim M𝓭 NNReal => (reading.val : ℝ)) h_units
    norm_num [massInGrams, gramUnitChoices, UnitChoices.dimScale,
      M𝓭, MassUnit.grams, MassUnit.kilograms, MassUnit.scale,
      MassUnit.div_eq_val] at h_units_real ⊢
    exact h_units_real
  have h_length :
      lengthInMeters setup.stringLength = 1 / 2 := by
    have h := _data.string_length_cm
    rw [length_centimeters_eq] at h
    norm_num at h ⊢
    linarith
  have h_frequency :=
    oscillationFrequencyInHertz_eq_oneHundredTwentyFive_div_twelve
      setup _data _positive _laws
  have h_wavelength :=
    wavelengthInMeters_eq_oneHalf
      setup _data _figure _positive _laws
  have h_speed_law :=
    _laws.wave_speed_eq_wavelength_mul_frequency UnitChoices.SI
  change (((setup.waveSpeed UnitChoices.SI).val : NNReal) : ℝ) =
      lengthInMeters setup.wavelength *
        frequencyInHertz setup.oscillationFrequency at h_speed_law
  rw [h_wavelength, h_frequency] at h_speed_law
  have h_speed :
      (((setup.waveSpeed UnitChoices.SI).val : NNReal) : ℝ) =
        125 / 24 := by
    norm_num at h_speed_law ⊢
    linarith
  have h_density_law :=
    _laws.stretched_string_wave_law UnitChoices.SI
  change (((setup.waveSpeed UnitChoices.SI).val : NNReal) : ℝ) ^ 2 *
      (((setup.linearMassDensity UnitChoices.SI).val : NNReal) : ℝ) =
        forceInNewtons setup.tension at h_density_law
  rw [h_speed, _data.tension_N] at h_density_law
  have h_density :
      (((setup.linearMassDensity UnitChoices.SI).val : NNReal) : ℝ) =
        576 / 15625 := by
    norm_num at h_density_law ⊢
    linarith
  have h_mass_law :=
    _laws.uniform_string_mass_law UnitChoices.SI
  change (((setup.stringMass UnitChoices.SI).val : NNReal) : ℝ) =
      (((setup.linearMassDensity UnitChoices.SI).val : NNReal) : ℝ) *
        lengthInMeters setup.stringLength at h_mass_law
  rw [h_density, h_length] at h_mass_law
  rw [mass_grams_eq, h_mass_law]
  norm_num

/-!
A 50.0 cm string under 1.00 N tension, pictured in its second harmonic and
strobed at 5000 flashes per minute, has ideal-model mass `18.432 g`.  Of the
four displayed masses, `18.5 g` (choice A) is the closest.

This formalizes `thm:physics:phyx_mini_0166:target`.
-/
theorem problem_phyx_mini_0166
    (setup : VibratingStringSetup)
    (_data : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_positive : HasPositiveStringQuantities setup)
    (_laws : ObeysStandingStringLaws setup) :
    massInGrams setup.stringMass = 2304 / 125 ∧
      IsClosestDisplayedMass setup .A := by
  have h_mass :=
    stringMassInGrams_eq_twoThousandThreeHundredFour_div_oneHundredTwentyFive
      setup _data _figure _positive _laws
  constructor
  · exact h_mass
  · intro other
    rw [h_mass]
    cases other <;>
      norm_num [AnswerChoice.massInGrams, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0166
