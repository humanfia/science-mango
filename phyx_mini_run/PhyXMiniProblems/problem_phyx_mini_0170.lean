import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/-!
# Lowest destructive-interference frequency for two in-phase loudspeakers

The primary figure places loudspeaker `B` two metres to the right of
loudspeaker `A`, and the observation point `Q` one further metre to the right.
The auxiliary point `P` is between the speakers, at the distance labelled `x`
from `A`.  Both speakers are connected to one amplifier, emit sinusoidal waves
in phase, and send direct acoustic paths to `Q`.

Lengths, frequencies, and propagation speeds are represented by Physlib
dimensionful quantities.  Real numbers below are only SI readouts,
dimensionless interference orders, or answer-table values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0170

open Dimension

/-! ## Dimensionful acoustic quantities and named SI readouts -/

/-- A unit-independent physical length. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent physical frequency, with inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A unit-independent physical propagation speed. -/
abbrev AcousticSpeed : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in metres. -/
def metersValue (length : AcousticLength) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical frequency in hertz. -/
def hertzValue (frequency : AcousticFrequency) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read a physical speed in metres per second. -/
def metersPerSecondValue (speed : AcousticSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-- Construct a physical frequency from an arbitrary hertz readout. -/
noncomputable def frequencyInHertz (value : ℝ) : AcousticFrequency :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-! ## Apparatus and primary-figure labels -/

/-- The four labeled collinear locations in the primary figure. -/
inductive FigurePoint where
  | A
  | P
  | B
  | Q
  deriving DecidableEq, Repr

/-- The two physical loudspeakers. -/
inductive SpeakerLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The point in the figure occupied by a speaker. -/
def SpeakerLabel.figurePoint : SpeakerLabel → FigurePoint
  | .A => .A
  | .B => .B

/-- The common audio amplifier depicted above the two speakers. -/
inductive AmplifierLabel where
  | common
  deriving DecidableEq, Repr

/-- The waveform distinction relevant to the problem statement. -/
inductive WaveformKind where
  | sinusoidal
  deriving DecidableEq, Repr

/-- Whether an acoustic path travels directly or reflects before arrival. -/
inductive PropagationKind where
  | direct
  | reflected
  deriving DecidableEq, Repr

/-- One physical propagation path from a speaker to a labeled point. -/
structure AcousticPath where
  source : SpeakerLabel
  destination : FigurePoint
  propagationKind : PropagationKind
  length : AcousticLength

/-!
The tunable two-speaker experiment and its physical observables.

`destructiveInterferenceAtQ frequency` is an observable predicate, not a
definition in terms of an answer value.  Its relation to wavelength and path
difference is supplied only by the general governing law below.
-/
structure TwoLoudspeakerInterferenceSetup where
  drivingAmplifier : SpeakerLabel → AmplifierLabel
  emittedWaveform : SpeakerLabel → WaveformKind
  emissionPhase : SpeakerLabel → AcousticFrequency → Real.Angle
  propagationSpeed : AcousticSpeed
  wavelengthAt : AcousticFrequency → AcousticLength
  axialCoordinate : FigurePoint → AcousticLength
  /-- The distance labeled `x` from `A` to the auxiliary point `P`. -/
  pointPDistanceX : AcousticLength
  directPathToQ : SpeakerLabel → AcousticPath
  destructiveInterferenceAtQ : AcousticFrequency → Prop

/-- A positive physical frequency, expressed through its hertz readout. -/
def IsPositiveFrequency (frequency : AcousticFrequency) : Prop :=
  0 < hertzValue frequency

/-!
Both speakers are driven by the depicted common amplifier.  At every positive
test frequency they emit sinusoidal waves with the same source phase.
-/
structure HasCommonSinusoidalInPhaseDrive
    (setup : TwoLoudspeakerInterferenceSetup) : Prop where
  speakerA_uses_common_amplifier :
    setup.drivingAmplifier .A = .common
  speakerB_uses_common_amplifier :
    setup.drivingAmplifier .B = .common
  speakerA_emits_sinusoid : setup.emittedWaveform .A = .sinusoidal
  speakerB_emits_sinusoid : setup.emittedWaveform .B = .sinusoidal
  sources_are_in_phase : ∀ frequency : AcousticFrequency,
    IsPositiveFrequency frequency →
      setup.emissionPhase .A frequency = setup.emissionPhase .B frequency

/-!
Geometry and metric readouts taken from the primary figure.

`A`, `P`, `B`, and `Q` occur from left to right; `AB = 2 m`, `BQ = 1 m`,
and `AP = x`.  The two acoustic paths end at `Q` and have the direct collinear
lengths shown by this coordinate chart.  No frequency or interference answer
appears in these figure premises.
-/
structure MatchesDepictedLineGeometry
    (setup : TwoLoudspeakerInterferenceSetup) : Prop where
  speakerA_at_origin : metersValue (setup.axialCoordinate .A) = 0
  speakerB_two_meters_right_of_A :
    metersValue (setup.axialCoordinate .B) -
        metersValue (setup.axialCoordinate .A) = 2
  pointQ_one_meter_right_of_B :
    metersValue (setup.axialCoordinate .Q) -
        metersValue (setup.axialCoordinate .B) = 1
  pointP_distance_is_x :
    metersValue (setup.axialCoordinate .P) -
        metersValue (setup.axialCoordinate .A) =
      metersValue setup.pointPDistanceX
  pointP_is_right_of_A :
    metersValue (setup.axialCoordinate .A) <
      metersValue (setup.axialCoordinate .P)
  pointP_is_left_of_B :
    metersValue (setup.axialCoordinate .P) <
      metersValue (setup.axialCoordinate .B)
  speakerA_path_has_source : (setup.directPathToQ .A).source = .A
  speakerB_path_has_source : (setup.directPathToQ .B).source = .B
  both_paths_end_at_Q : ∀ speaker : SpeakerLabel,
    (setup.directPathToQ speaker).destination = .Q
  both_paths_are_direct : ∀ speaker : SpeakerLabel,
    (setup.directPathToQ speaker).propagationKind = .direct
  direct_path_length : ∀ speaker : SpeakerLabel,
    metersValue (setup.directPathToQ speaker).length =
      metersValue (setup.axialCoordinate .Q) -
        metersValue (setup.axialCoordinate speaker.figurePoint)

/-- Positivity conditions selecting the physical branch of the model. -/
structure HasPhysicalAcousticParameters
    (setup : TwoLoudspeakerInterferenceSetup) : Prop where
  propagation_speed_positive :
    0 < metersPerSecondValue setup.propagationSpeed
  wavelength_positive : ∀ frequency : AcousticFrequency,
    IsPositiveFrequency frequency →
      0 < metersValue (setup.wavelengthAt frequency)
  direct_path_lengths_nonnegative : ∀ speaker : SpeakerLabel,
    0 ≤ metersValue (setup.directPathToQ speaker).length

/-!
The conventional room-temperature sound-speed calibration used to obtain the
recorded numerical answer.  The printed source omits a speed readout; making
the `344 m/s` modeling convention explicit prevents it from being hidden in
the requested frequency or in the interference law.
-/
structure UsesStandardAirSoundSpeed
    (setup : TwoLoudspeakerInterferenceSetup) : Prop where
  sound_speed_meters_per_second :
    metersPerSecondValue setup.propagationSpeed = 344

/-- The absolute difference of the two direct path lengths to `Q`, in metres. -/
def pathDifferenceAtQInMeters
    (setup : TwoLoudspeakerInterferenceSetup) : ℝ :=
  |metersValue (setup.directPathToQ .A).length -
    metersValue (setup.directPathToQ .B).length|

/-!
The governing acoustic laws, uniform over every positive test frequency:

* propagation speed equals wavelength times frequency, `c = λ f`;
* for sources which are in phase, destructive interference at `Q` occurs
  exactly when the path difference is an odd half-wavelength,
  `Δr = (n + 1/2) λ` for some natural order `n`.

Neither law identifies a least order, a numerical frequency, or an answer
choice.
-/
structure SatisfiesTwoSourceAcousticLaws
    (setup : TwoLoudspeakerInterferenceSetup) : Prop where
  wave_speed_relation : ∀ frequency : AcousticFrequency,
    IsPositiveFrequency frequency →
      metersPerSecondValue setup.propagationSpeed =
        metersValue (setup.wavelengthAt frequency) * hertzValue frequency
  destructive_interference_iff : ∀ frequency : AcousticFrequency,
    IsPositiveFrequency frequency →
      setup.emissionPhase .A frequency = setup.emissionPhase .B frequency →
        (setup.destructiveInterferenceAtQ frequency ↔
          ∃ order : ℕ,
            pathDifferenceAtQInMeters setup =
              ((order : ℝ) + 1 / 2) *
                metersValue (setup.wavelengthAt frequency))

/-! ## Least-frequency predicate and displayed answers -/

/-!
`frequency` is the lowest positive frequency producing destructive
interference at `Q`.  The comparison is made in hertz because Physlib's
unit-independent quantities deliberately do not have a global order.
-/
def IsLowestDestructiveFrequency
    (setup : TwoLoudspeakerInterferenceSetup)
    (frequency : AcousticFrequency) : Prop :=
  IsPositiveFrequency frequency ∧
    setup.destructiveInterferenceAtQ frequency ∧
    ∀ otherFrequency : AcousticFrequency,
      IsPositiveFrequency otherFrequency →
        setup.destructiveInterferenceAtQ otherFrequency →
          hertzValue frequency ≤ hertzValue otherFrequency

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The hertz readout printed beside each answer label. -/
def AnswerChoice.frequencyHertz : AnswerChoice → ℝ
  | .A => 86
  | .B => 80
  | .C => 896
  | .D => 85

/-- A physical frequency has the readout printed beside an answer choice. -/
def MatchesDisplayedFrequency
    (frequency : AcousticFrequency) (choice : AnswerChoice) : Prop :=
  hertzValue frequency = choice.frequencyHertz

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
The depicted direct paths differ by `2 m`: `AQ = 3 m` and `BQ = 1 m`.
This is a derived geometric intermediate and contains no frequency claim.
-/
lemma pathDifferenceAtQ_eq_two_meters
    (setup : TwoLoudspeakerInterferenceSetup)
    (_geometry : MatchesDepictedLineGeometry setup) :
    pathDifferenceAtQInMeters setup = 2 := by
  unfold pathDifferenceAtQInMeters
  rw [_geometry.direct_path_length .A, _geometry.direct_path_length .B]
  simp only [SpeakerLabel.figurePoint]
  have hpath_difference :
      (metersValue (setup.axialCoordinate .Q) -
          metersValue (setup.axialCoordinate .A)) -
        (metersValue (setup.axialCoordinate .Q) -
          metersValue (setup.axialCoordinate .B)) = 2 := by
    linarith [_geometry.speakerB_two_meters_right_of_A]
  rw [hpath_difference]
  norm_num

/-!
With `Δr = 2 m`, the largest destructive wavelength is `4 m` (order zero).
At the conventional `344 m/s` sound speed, `f = c / λ = 86 Hz`.
Thus the physical frequency constructed from the `86 Hz` readout is the least
positive destructive frequency and agrees with recorded answer A.

This formalizes `thm:physics:phyx_mini_0170:target`.
-/
theorem problem_phyx_mini_0170
    (setup : TwoLoudspeakerInterferenceSetup)
    (_drive : HasCommonSinusoidalInPhaseDrive setup)
    (_geometry : MatchesDepictedLineGeometry setup)
    (_physical : HasPhysicalAcousticParameters setup)
    (_speed : UsesStandardAirSoundSpeed setup)
    (_laws : SatisfiesTwoSourceAcousticLaws setup) :
    IsLowestDestructiveFrequency setup (frequencyInHertz 86) ∧
      MatchesDisplayedFrequency
        (frequencyInHertz 86) recordedDatasetAnswer := by
  have hfrequency_value :
      hertzValue (frequencyInHertz 86) = 86 := by
    simp [hertzValue, frequencyInHertz,
      CarriesDimension.toDimensionful_apply_apply]
  have hfrequency_positive :
      IsPositiveFrequency (frequencyInHertz 86) := by
    norm_num [IsPositiveFrequency, hfrequency_value]
  have hpath_difference : pathDifferenceAtQInMeters setup = 2 :=
    pathDifferenceAtQ_eq_two_meters setup _geometry
  have hwavelength :
      metersValue (setup.wavelengthAt (frequencyInHertz 86)) = 4 := by
    have hwave_speed :=
      _laws.wave_speed_relation (frequencyInHertz 86) hfrequency_positive
    rw [_speed.sound_speed_meters_per_second, hfrequency_value] at hwave_speed
    nlinarith
  constructor
  · refine ⟨hfrequency_positive, ?_, ?_⟩
    · apply (_laws.destructive_interference_iff
        (frequencyInHertz 86) hfrequency_positive
        (_drive.sources_are_in_phase
          (frequencyInHertz 86) hfrequency_positive)).2
      refine ⟨0, ?_⟩
      rw [hpath_difference, hwavelength]
      norm_num
    · intro otherFrequency hother_positive hother_destructive
      have hother_phase :=
        _drive.sources_are_in_phase otherFrequency hother_positive
      obtain ⟨order, horder⟩ :=
        (_laws.destructive_interference_iff
          otherFrequency hother_positive hother_phase).1 hother_destructive
      rw [hpath_difference] at horder
      have hother_wave_speed :=
        _laws.wave_speed_relation otherFrequency hother_positive
      rw [_speed.sound_speed_meters_per_second] at hother_wave_speed
      have hother_hertz_positive : 0 < hertzValue otherFrequency := by
        simpa [IsPositiveFrequency] using hother_positive
      have hother_wavelength_positive :
          0 < metersValue (setup.wavelengthAt otherFrequency) :=
        _physical.wavelength_positive otherFrequency hother_positive
      have horder_nonnegative : 0 ≤ (order : ℝ) := Nat.cast_nonneg order
      have horder_term_nonnegative :
          0 ≤ (order : ℝ) *
            metersValue (setup.wavelengthAt otherFrequency) :=
        mul_nonneg horder_nonnegative (le_of_lt hother_wavelength_positive)
      have hwavelength_le :
          metersValue (setup.wavelengthAt otherFrequency) ≤ 4 := by
        nlinarith [horder, horder_term_nonnegative]
      have hproduct_le :
          metersValue (setup.wavelengthAt otherFrequency) *
              hertzValue otherFrequency ≤
            4 * hertzValue otherFrequency :=
        mul_le_mul_of_nonneg_right hwavelength_le
          (le_of_lt hother_hertz_positive)
      rw [hfrequency_value]
      nlinarith [hother_wave_speed, hproduct_le]
  · simpa [MatchesDisplayedFrequency, recordedDatasetAnswer,
      AnswerChoice.frequencyHertz] using hfrequency_value

end PhyXMiniProblems.ProblemPhyXMini0170
