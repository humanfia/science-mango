import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

/-!
# First acoustic diffraction minimum at an auditorium wall

This file models problem `phyx_mini_0175`. A speaker cabinet has a rectangular
opening of horizontal width `30.0 cm`. A `3000 Hz` sound wave travelling at
`343 m/s` diffracts through that opening toward a wall `100 m` away along the
central axis. Reflections are neglected.

Lengths, frequency, and speed are represented by Physlib dimensionful
quantities. Real numbers below are explicit readouts in named units or
dimensionless trigonometric values. The finite-distance diffraction model has
an explicit Fresnel-number remainder bound; the Fraunhofer leading term is not
asserted as a globally exact law.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0175

open Dimension

/-! ## Dimensionful acoustic quantities and unit readouts -/

/-- A signed physical length, independent of the unit used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical propagation speed, carrying the length-per-time dimension. -/
abbrev AcousticSpeed : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Read a physical frequency in inverse selected time units. -/
def frequencyReadout (unit : TimeUnit) (frequency : AcousticFrequency) : ℝ :=
  (frequency ({ UnitChoices.SI with time := unit } : UnitChoices)).val

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : AcousticSpeed) : ℝ :=
  (speed ({ UnitChoices.SI with
    length := lengthUnit, time := timeUnit } : UnitChoices)).val

/-- Metre readout used for the wall geometry and answer choices. -/
def metersValue (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used for the stated opening width. -/
def centimetersValue (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Hertz readout used for the stated tone frequency. -/
def hertzValue (frequency : AcousticFrequency) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Metres-per-second readout used for the stated sound speed. -/
def metersPerSecondValue (speed : AcousticSpeed) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical apparatus and figure labels -/

/-- The shape assigned to the speaker-cabinet opening. -/
inductive OpeningGeometry where
  | rectangular
  deriving DecidableEq, Repr

/-- The alignment of the cabinet opening, central axis, and far wall. -/
inductive CabinetAlignment where
  | openingFacesWallAlongHorizontalCentralAxis
  deriving DecidableEq, Repr

/-- The propagation approximation stipulated in the question. -/
inductive PropagationApproximation where
  | directDiffractionWithReflectionsNeglected
  deriving DecidableEq, Repr

/-- Text labels and geometric features visible in the supplied figure. -/
inductive FigureFeature where
  | speakerCabinet
  | centralAxis
  | distanceD
  | farWall
  deriving DecidableEq, Repr

/--
The acoustic wave, speaker opening, auditorium geometry, and unknown first
minimum location. The opening height is not included because the problem gives
only the horizontal width relevant to diffraction along the wall.
-/
structure SpeakerDiffractionSetup where
  openingGeometry : OpeningGeometry
  cabinetAlignment : CabinetAlignment
  propagationApproximation : PropagationApproximation
  figureShows : FigureFeature → Prop
  /-- Frequency `f` of the emitted sound. -/
  toneFrequency : AcousticFrequency
  /-- Propagation speed `c` of sound in the auditorium. -/
  soundSpeed : AcousticSpeed
  /-- Wavelength `λ` of the tone in the auditorium. -/
  wavelength : AcousticLength
  /-- Horizontal aperture width `a` of the rectangular cabinet opening. -/
  openingHorizontalWidth : AcousticLength
  /-- Auditorium length `d` stated in the problem. -/
  auditoriumLengthD : AcousticLength
  /-- Distance from the cabinet to the wall along the central axis. -/
  wallDistanceAlongAxis : AcousticLength
  /-- Positive first-minimum diffraction angle measured from the central axis. -/
  firstMinimumAngle : Real.Angle
  /-- Requested perpendicular listener distance from the central axis at the wall. -/
  listenerDistanceFromAxis : AcousticLength

/--
The scalar data and qualitative information supplied by the problem and its
figure. In particular, this predicate contains no numerical readout of the
requested listener distance and no answer-choice selection.
-/
def MatchesProblemAndFigureReadouts (setup : SpeakerDiffractionSetup) : Prop :=
  setup.openingGeometry = .rectangular ∧
    setup.cabinetAlignment = .openingFacesWallAlongHorizontalCentralAxis ∧
    setup.propagationApproximation =
      .directDiffractionWithReflectionsNeglected ∧
    setup.figureShows .speakerCabinet ∧
    setup.figureShows .centralAxis ∧
    setup.figureShows .distanceD ∧
    setup.figureShows .farWall ∧
    hertzValue setup.toneFrequency = 3000 ∧
    metersPerSecondValue setup.soundSpeed = 343 ∧
    centimetersValue setup.openingHorizontalWidth = 30 ∧
    metersValue setup.auditoriumLengthD = 100 ∧
    metersValue setup.wallDistanceAlongAxis = 100

/-- Positivity conditions for the physical scalar readouts in the setup. -/
def HasPhysicalParameters (setup : SpeakerDiffractionSetup) : Prop :=
  0 < hertzValue setup.toneFrequency ∧
    0 < metersPerSecondValue setup.soundSpeed ∧
    0 < metersValue setup.wavelength ∧
    0 < metersValue setup.openingHorizontalWidth ∧
    0 < metersValue setup.auditoriumLengthD ∧
    0 < metersValue setup.wallDistanceAlongAxis ∧
    0 < metersValue setup.listenerDistanceFromAxis

/--
An angle is on the positive acute branch when it has a radian representative
strictly between `0` and `π/2`. This selects the first-minimum ray on one side
of the central axis and removes the periodic ambiguity of sine and tangent.
-/
def IsPositiveAcuteAngle (angle : Real.Angle) : Prop :=
  ∃ radians : ℝ,
    0 < radians ∧ radians < Real.pi / 2 ∧
      angle = (radians : Real.Angle)

/-!
## Assumption/target split

`MatchesProblemAndFigureReadouts` contains only the numerical source data and
the labels visible in the primary figure. `HasPhysicalParameters` supplies
positivity and `SatisfiesAcousticWaveLaw` gives the nondispersive relation
`c = λ f`. `SatisfiesControlledFirstMinimumDiffractionLaw` supplies a
finite-distance remainder bound for the first-minimum Fraunhofer leading term,
and `SatisfiesWallGeometry` gives the exact planar-wall intersection geometry.

No premise fixes the listener distance, mentions `41.2 m`, or selects answer C.
Those statements occur only in `listenerDistance_matches_recordedAnswerC`.
-/

/-! ## Governing physical laws -/

/--
The nondispersive acoustic-wave relation `c = λ f`, stated in every compatible
choice of length and time units. It determines the wavelength from the given
speed and frequency but does not prescribe the listener's position.
-/
structure SatisfiesAcousticWaveLaw (setup : SpeakerDiffractionSetup) : Prop where
  speed_eq_wavelength_mul_frequency :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeed =
        lengthReadout lengthUnit setup.wavelength *
          frequencyReadout timeUnit setup.toneFrequency

/--
The dimensionless aperture Fresnel number `a² / (λ d)` in metre readouts.
It measures the finite-distance correction to the far-field diffraction
pattern. Absolute values make the expression meaningful independently of the
positivity assumptions used by the main theorem.
-/
def apertureFresnelNumber (setup : SpeakerDiffractionSetup) : ℝ :=
  |metersValue setup.openingHorizontalWidth| ^ 2 /
    (|metersValue setup.wavelength| *
      |metersValue setup.wallDistanceAlongAxis|)

/--
A controlled finite-distance form of the first single-slit diffraction law.
The Fraunhofer leading term is `sin θ₁ = λ / a`; rather than imposing it as an
exact identity at the finite wall distance, the actual first-minimum sine has
an explicit residual bounded by the square of the aperture Fresnel number.
For a centered rectangular aperture the first correction to the location is
second order in that number. The opening's horizontal width is the relevant
aperture dimension because the requested displacement is along the wall.
-/
structure SatisfiesControlledFirstMinimumDiffractionLaw
    (setup : SpeakerDiffractionSetup) : Prop where
  first_minimum_angle_is_positive_acute :
    IsPositiveAcuteAngle setup.firstMinimumAngle
  first_minimum_sine_residual_bound :
    |Real.Angle.sin setup.firstMinimumAngle -
        metersValue setup.wavelength /
          metersValue setup.openingHorizontalWidth| ≤
      apertureFresnelNumber setup ^ 2

/--
The right-triangle wall geometry `y = d tan θ₁`, where `d` is measured along
the labelled central axis and `y` is the perpendicular distance along the wall.
-/
structure SatisfiesWallGeometry (setup : SpeakerDiffractionSetup) : Prop where
  auditorium_length_is_wall_distance :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.auditoriumLengthD =
        lengthReadout unit setup.wallDistanceAlongAxis
  lateral_offset_relation :
    ∀ unit : LengthUnit,
      lengthReadout unit setup.listenerDistanceFromAxis =
        lengthReadout unit setup.wallDistanceAlongAxis *
          Real.Angle.tan setup.firstMinimumAngle

/-! ## Derived relations and displayed answer -/

/-- The given acoustic data imply `λ = 343/3000 m`. -/
lemma wavelengthInMeters_eq_speed_div_frequency
    (setup : SpeakerDiffractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_wave : SatisfiesAcousticWaveLaw setup) :
    metersValue setup.wavelength = (343 / 3000 : ℝ) := by
  rcases h_readouts with
    ⟨_, _, _, _, _, _, _, h_frequency, h_speed, _, _, _⟩
  have h_wave_meters_seconds :=
    h_wave.speed_eq_wavelength_mul_frequency
      LengthUnit.meters TimeUnit.seconds
  change metersPerSecondValue setup.soundSpeed =
      metersValue setup.wavelength * hertzValue setup.toneFrequency at h_wave_meters_seconds
  rw [h_speed, h_frequency] at h_wave_meters_seconds
  norm_num at h_wave_meters_seconds ⊢
  linarith

/--
The controlled diffraction law puts the actual first-minimum sine within the
finite-distance remainder of the Fraunhofer value `343/900`.
-/
lemma firstMinimumSine_has_controlled_error
    (setup : SpeakerDiffractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_wave : SatisfiesAcousticWaveLaw setup)
    (h_diffraction : SatisfiesControlledFirstMinimumDiffractionLaw setup) :
    |Real.Angle.sin setup.firstMinimumAngle - (343 / 900 : ℝ)| ≤
      (((3 / 10 : ℝ) ^ 2) /
        ((343 / 3000 : ℝ) * 100)) ^ 2 := by
  have h_wavelength :=
    wavelengthInMeters_eq_speed_div_frequency setup h_readouts h_wave
  rcases h_readouts with
    ⟨_, _, _, _, _, _, _, _, _, h_width_cm, _, h_wall⟩
  have h_width_scaling :=
    setup.openingHorizontalWidth.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
  have h_width_meters :
      metersValue setup.openingHorizontalWidth = (3 / 10 : ℝ) := by
    have h_width_scaling_val := congrArg WithDim.val h_width_scaling
    change centimetersValue setup.openingHorizontalWidth =
        _ * metersValue setup.openingHorizontalWidth at h_width_scaling_val
    rw [h_width_cm] at h_width_scaling_val
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters] at h_width_scaling_val
    change (30 : ℝ) = 100 * metersValue setup.openingHorizontalWidth at h_width_scaling_val
    norm_num
    linarith
  have h_bound := h_diffraction.first_minimum_sine_residual_bound
  simp only [apertureFresnelNumber] at h_bound
  rw [h_wavelength, h_width_meters, h_wall] at h_bound
  norm_num at h_bound ⊢
  exact h_bound

/-- Labels of the four distance answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre value printed beside each answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 178 / 5
  | .B => 487 / 10
  | .C => 206 / 5
  | .D => 59 / 2

/--
Agreement with a distance displayed to the nearest tenth of a metre. The
half-unit in the last displayed place is `0.05 m = 1/20 m`.
-/
def MatchesDisplayedDistance
    (distance : AcousticLength) (choice : AnswerChoice) : Prop :=
  |metersValue distance - choice.meters| ≤ 1 / 20

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/--
The first diffraction minimum reaches the wall approximately `41.2 m` from
the central axis, matching recorded answer choice C. The conclusion concerns
the actual first minimum constrained by the explicit finite-distance residual,
not a globally exact Fraunhofer identity.

This formalizes `thm:physics:phyx_mini_0175:target`.
-/
theorem listenerDistance_matches_recordedAnswerC
    (setup : SpeakerDiffractionSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_wave : SatisfiesAcousticWaveLaw setup)
    (h_diffraction : SatisfiesControlledFirstMinimumDiffractionLaw setup)
    (h_geometry : SatisfiesWallGeometry setup) :
    MatchesDisplayedDistance
      setup.listenerDistanceFromAxis recordedAnswerChoice := by
  have h_sine_error :=
    firstMinimumSine_has_controlled_error setup h_readouts h_wave h_diffraction
  have h_listener_pos :
      0 < metersValue setup.listenerDistanceFromAxis :=
    h_physical.2.2.2.2.2.2
  have h_offset :=
    h_geometry.lateral_offset_relation LengthUnit.meters
  rcases h_readouts with
    ⟨_, _, _, _, _, _, _, _, _, _, _, h_wall⟩
  rcases h_diffraction.first_minimum_angle_is_positive_acute with
    ⟨theta, htheta_pos, htheta_lt, h_angle⟩
  simp only [h_angle, Real.Angle.sin_coe] at h_sine_error
  have hsin_pos : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta_pos (by linarith [Real.pi_pos])
  have hcos_pos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htheta_lt⟩
  rw [abs_le] at h_sine_error
  norm_num at h_sine_error
  have hsin_lower : (381 / 1000 : ℝ) ≤ Real.sin theta := by
    linarith [h_sine_error.1]
  have hsin_upper : Real.sin theta ≤ (953 / 2500 : ℝ) := by
    linarith [h_sine_error.2]
  have hsin_sq_lower : (381 / 1000 : ℝ) ^ 2 ≤ Real.sin theta ^ 2 :=
    (sq_le_sq₀ (by norm_num) hsin_pos.le).2 hsin_lower
  have hsin_sq_upper : Real.sin theta ^ 2 ≤ (953 / 2500 : ℝ) ^ 2 :=
    (sq_le_sq₀ hsin_pos.le (by norm_num)).2 hsin_upper
  have h_pythagorean := Real.sin_sq_add_cos_sq theta
  have htan_lower : (823 / 2000 : ℝ) ≤ Real.tan theta := by
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos_pos]
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) hcos_pos.le) hsin_pos.le).1
    nlinarith [hsin_sq_lower]
  have htan_upper : Real.tan theta ≤ (33 / 80 : ℝ) := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos_pos]
    apply (sq_le_sq₀ hsin_pos.le (mul_nonneg (by norm_num) hcos_pos.le)).1
    nlinarith [hsin_sq_upper]
  change metersValue setup.listenerDistanceFromAxis =
      metersValue setup.wallDistanceAlongAxis *
        Real.Angle.tan setup.firstMinimumAngle at h_offset
  rw [h_wall, h_angle, Real.Angle.tan_coe] at h_offset
  rw [MatchesDisplayedDistance, recordedAnswerChoice]
  simp only [AnswerChoice.meters]
  rw [h_offset] at h_listener_pos
  rw [h_offset, abs_le]
  constructor <;> norm_num <;> linarith [h_listener_pos]

end PhyXMiniProblems.ProblemPhyXMini0175
