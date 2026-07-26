import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.Basic
import Physlib.Units.WithDim.Speed

/-!
# Moving the middle loudspeaker for constructive interference

This file models problem `phyx_mini_0186`.  Three identical loudspeakers are
labelled 1, 2, and 3 from top to bottom.  In the primary figure their vertical
coordinates are respectively `3 m`, `0 m`, and `-3 m`, while the listener is
`4 m` directly in front of speaker 2.  Speaker 2 is moved horizontally to the
left, away from the listener.

Lengths, frequency, and sound speed are Physlib dimensionful quantities.
Coordinates in `Space 2` and distances computed from them are explicitly
metre readouts.  The type of wave amplitudes remains abstract because the
problem names a common amplitude `a` but supplies no amplitude unit.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0186

open Dimension

/-! ## Dimensionful acoustic quantities and SI readouts -/

/-- A physical length, independent of the unit system used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical acoustic frequency, carrying the inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical sound speed, carrying the length-per-time dimension. -/
abbrev AcousticSpeed : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a dimensionful length in metres. -/
def metersValue (length : AcousticLength) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a dimensionful acoustic frequency in hertz. -/
def hertzValue (frequency : AcousticFrequency) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read a dimensionful sound speed in metres per second. -/
def metersPerSecondValue (speed : AcousticSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-- Construct a physical length from its metre readout. -/
def lengthOfMeters (value : ℝ) : AcousticLength :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-! ## Loudspeakers, figure labels, and supplied data -/

/-- The loudspeaker numbers printed in the primary figure. -/
inductive SpeakerLabel where
  | speaker1
  | speaker2
  | speaker3
  deriving DecidableEq, Repr

/-!
The physical objects and named quantities in the three-speaker experiment.

The coordinates of `speakerPosition` and `listenerPosition` are metre
readouts in the axes of the primary figure: positive `x` points toward the
listener and positive `y` points toward speaker 1.  The common individual
wave amplitude at the listener is the quantity denoted by `a` in the problem.
-/
structure ThreeSpeakerInterferenceSetup (Amplitude : Type) where
  sourcePosition : SpeakerLabel → Space 2
  listenerPosition : Space 2
  adjacentSpeakerSeparation : AcousticLength
  listenerDistanceInFront : AcousticLength
  toneFrequency : AcousticFrequency
  soundSpeed : AcousticSpeed
  wavelength : AcousticLength
  emissionPhase : SpeakerLabel → Real.Angle
  individualAmplitudeAtListener : SpeakerLabel → Amplitude
  amplitudeA : Amplitude

/-!
The scalar data printed in the problem and figure: adjacent speakers are
`3 m` apart, the listener is `4 m` in front of speaker 2, the common tone is
`170 Hz`, and sound travels at `340 m/s`.  This predicate contains neither a
leftward displacement nor a maximum-interference answer.
-/
def MatchesProblemReadouts {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude) : Prop :=
  metersValue setup.adjacentSpeakerSeparation = 3 ∧
    metersValue setup.listenerDistanceInFront = 4 ∧
    hertzValue setup.toneFrequency = 170 ∧
    metersPerSecondValue setup.soundSpeed = 340

/-!
The coordinate layout read from the primary image.  Speaker 2 is the origin;
speakers 1 and 3 lie respectively `3 m` above and below it, and the listener
lies on the positive horizontal axis.
-/
def HasDepictedLayout {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude) : Prop :=
  setup.sourcePosition .speaker1 0 = 0 ∧
    setup.sourcePosition .speaker1 1 =
      metersValue setup.adjacentSpeakerSeparation ∧
    setup.sourcePosition .speaker2 0 = 0 ∧
    setup.sourcePosition .speaker2 1 = 0 ∧
    setup.sourcePosition .speaker3 0 = 0 ∧
    setup.sourcePosition .speaker3 1 =
      -metersValue setup.adjacentSpeakerSeparation ∧
    setup.listenerPosition 0 = metersValue setup.listenerDistanceInFront ∧
    setup.listenerPosition 1 = 0

/-!
The identical-source assumptions used by the interference model.  All three
sources emit with one initial phase, and the wave arriving from each source
has the named common amplitude `a`, as stated in the problem.  Their frequency
is already common because it is represented by the single field
`toneFrequency`.
-/
def EmitsCoherentlyWithCommonAmplitude {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude) : Prop :=
  (∀ speaker,
      setup.emissionPhase speaker = setup.emissionPhase .speaker2) ∧
    ∀ speaker,
      setup.individualAmplitudeAtListener speaker = setup.amplitudeA

/-- Positivity conditions for the physical wavelength and supplied data. -/
def HasPhysicalParameters {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude) : Prop :=
  0 < metersValue setup.adjacentSpeakerSeparation ∧
    0 < metersValue setup.listenerDistanceInFront ∧
    0 < hertzValue setup.toneFrequency ∧
    0 < metersPerSecondValue setup.soundSpeed ∧
    0 < metersValue setup.wavelength

/-!
The acoustic propagation law `c = λ f`.  It is a governing law relating
speed, wavelength, and frequency, not a statement about the requested motion
of speaker 2.
-/
structure SatisfiesSoundWaveLaw {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude) : Prop where
  speed_eq_wavelength_mul_frequency :
    metersPerSecondValue setup.soundSpeed =
      metersValue setup.wavelength * hertzValue setup.toneFrequency

/-! ## Moving speaker 2 and the maximum-amplitude condition -/

/-!
The position obtained by moving speaker 2 left by `displacement`.  Since the
listener lies on the positive horizontal axis, a leftward movement subtracts
the positive metre readout from speaker 2's `x` coordinate and leaves its
vertical coordinate fixed.
-/
def movedMiddleSpeakerPosition {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (displacement : AcousticLength) : Space 2 :=
  ⟨fun i =>
    if i = 0 then
      setup.sourcePosition .speaker2 i - metersValue displacement
    else
      setup.sourcePosition .speaker2 i⟩

/-- Source positions after moving only speaker 2 to the left. -/
def sourcePositionAfterMove {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (displacement : AcousticLength) : SpeakerLabel → Space 2
  | .speaker1 => setup.sourcePosition .speaker1
  | .speaker2 => movedMiddleSpeakerPosition setup displacement
  | .speaker3 => setup.sourcePosition .speaker3

/-!
The propagation distance from one speaker to the listener after the move,
read in metres through the metric on Physlib's planar `Space 2`.
-/
def pathLengthMetersAfterMove {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (displacement : AcousticLength) (speaker : SpeakerLabel) : ℝ :=
  dist (sourcePositionAfterMove setup displacement speaker)
    setup.listenerPosition

/-!
For coherent monochromatic sources of equal individual amplitude, their sum
has maximum amplitude precisely when every pairwise path difference is an
integer multiple of the common wavelength.  This predicate records that
standard constructive-interference condition for a proposed displacement; it
does not specify which displacement satisfies it.
-/
def ProducesMaximumAmplitudeAtListener {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (displacement : AcousticLength) : Prop :=
  ∀ first second : SpeakerLabel,
    ∃ order : ℤ,
      pathLengthMetersAfterMove setup displacement first -
          pathLengthMetersAfterMove setup displacement second =
        (order : ℝ) * metersValue setup.wavelength

/-!
A displacement is the requested move when it is positive, produces a
constructive maximum, and is no larger than any other positive displacement
that produces a maximum.  This makes the textbook question's intended
"first maximum" explicit and rules out later maxima one or more wavelengths
farther to the left.
-/
def IsLeastPositiveMaximumDisplacement {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (displacement : AcousticLength) : Prop :=
  0 < metersValue displacement ∧
    ProducesMaximumAmplitudeAtListener setup displacement ∧
    ∀ other : AcousticLength,
      0 < metersValue other →
      ProducesMaximumAmplitudeAtListener setup other →
      metersValue displacement ≤ metersValue other

/-! ## Derived geometry and displayed answer -/

/-!
The numerical sound data and `c = λf` imply a wavelength of `2 m`.
-/
lemma wavelength_in_meters_eq_two {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_wave : SatisfiesSoundWaveLaw setup) :
    metersValue setup.wavelength = 2 := by
  unfold MatchesProblemReadouts at h_readouts
  rcases h_readouts with ⟨_, _, h_frequency, h_speed⟩
  nlinarith [h_wave.speed_eq_wavelength_mul_frequency]

/-!
Before speaker 2 moves, the 3-4-5 triangles in the figure give path lengths
`5 m`, `4 m`, and `5 m` from speakers 1, 2, and 3 respectively.
-/
lemma initial_path_lengths_are_five_four_five {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (h_readouts : MatchesProblemReadouts setup)
    (h_layout : HasDepictedLayout setup) :
    pathLengthMetersAfterMove setup (lengthOfMeters 0) .speaker1 = 5 ∧
      pathLengthMetersAfterMove setup (lengthOfMeters 0) .speaker2 = 4 ∧
      pathLengthMetersAfterMove setup (lengthOfMeters 0) .speaker3 = 5 := by
  rcases h_readouts with ⟨h_separation, h_front, _, _⟩
  rcases h_layout with
    ⟨h_speaker1_x, h_speaker1_y, h_speaker2_x, h_speaker2_y,
      h_speaker3_x, h_speaker3_y, h_listener_x, h_listener_y⟩
  have h_zero_length : metersValue (lengthOfMeters 0) = 0 := by
    simp [metersValue, lengthOfMeters,
      CarriesDimension.toDimensionful_apply_apply]
  have h_sqrt_twenty_five : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have h_sqrt_sixteen : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  norm_num [pathLengthMetersAfterMove, sourcePositionAfterMove,
    movedMiddleSpeakerPosition, Space.dist_eq, Fin.sum_univ_two,
    h_speaker1_x, h_speaker1_y, h_speaker2_x, h_speaker2_y,
    h_speaker3_x, h_speaker3_y, h_listener_x, h_listener_y,
    h_separation, h_front, h_zero_length, h_sqrt_twenty_five,
    h_sqrt_sixteen]

/-!
Moving speaker 2 one metre left puts it five metres from the listener, equal
to the two unchanged outer-speaker path lengths.
-/
lemma one_meter_move_equalizes_path_lengths {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (h_readouts : MatchesProblemReadouts setup)
    (h_layout : HasDepictedLayout setup) :
    ∀ speaker,
      pathLengthMetersAfterMove setup (lengthOfMeters 1) speaker = 5 := by
  rcases h_readouts with ⟨h_separation, h_front, _, _⟩
  rcases h_layout with
    ⟨h_speaker1_x, h_speaker1_y, h_speaker2_x, h_speaker2_y,
      h_speaker3_x, h_speaker3_y, h_listener_x, h_listener_y⟩
  have h_one_length : metersValue (lengthOfMeters 1) = 1 := by
    simp [metersValue, lengthOfMeters,
      CarriesDimension.toDimensionful_apply_apply]
  have h_sqrt_twenty_five : Real.sqrt (25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  intro speaker
  cases speaker <;>
    norm_num [pathLengthMetersAfterMove, sourcePositionAfterMove,
      movedMiddleSpeakerPosition, Space.dist_eq, Fin.sum_univ_two,
      h_speaker1_x, h_speaker1_y, h_speaker2_x, h_speaker2_y,
      h_speaker3_x, h_speaker3_y, h_listener_x, h_listener_y,
      h_separation, h_front, h_one_length, h_sqrt_twenty_five]

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displacement in metres printed beside each answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 1 / 2
  | .B => 2
  | .C => 1 / 4
  | .D => 1

/-- A displayed choice is correct when it gives the least positive maximum. -/
def IsCorrectAnswer {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (choice : AnswerChoice) : Prop :=
  ∃ displacement : AcousticLength,
    IsLeastPositiveMaximumDisplacement setup displacement ∧
      metersValue displacement = choice.meters

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The least positive move of speaker 2 is one metre to the left, which is the
displayed answer D.  Later constructive maxima are farther left by whole
wavelengths and therefore do not satisfy the least-positive condition.

This formalizes blueprint label `thm:physics:phyx_mini_0186:target`.
-/
theorem problem_phyx_mini_0186 {Amplitude : Type}
    (setup : ThreeSpeakerInterferenceSetup Amplitude)
    (h_readouts : MatchesProblemReadouts setup)
    (h_layout : HasDepictedLayout setup)
    (h_sources : EmitsCoherentlyWithCommonAmplitude setup)
    (h_physical : HasPhysicalParameters setup)
    (h_wave : SatisfiesSoundWaveLaw setup) :
    IsLeastPositiveMaximumDisplacement setup (lengthOfMeters 1) ∧
      IsCorrectAnswer setup recordedAnswerChoice := by
  have h_one_length : metersValue (lengthOfMeters 1) = 1 := by
    simp [metersValue, lengthOfMeters,
      CarriesDimension.toDimensionful_apply_apply]
  have h_wavelength :=
    wavelength_in_meters_eq_two setup h_readouts h_physical h_wave
  have h_equal_paths :=
    one_meter_move_equalizes_path_lengths setup h_readouts h_layout
  have h_maximum :
      ProducesMaximumAmplitudeAtListener setup (lengthOfMeters 1) := by
    intro first second
    refine ⟨0, ?_⟩
    rw [h_equal_paths first, h_equal_paths second, h_wavelength]
    norm_num
  have h_initial_paths :=
    initial_path_lengths_are_five_four_five setup h_readouts h_layout
  have h_least :
      IsLeastPositiveMaximumDisplacement setup (lengthOfMeters 1) := by
    refine ⟨?_, h_maximum, ?_⟩
    · rw [h_one_length]
      norm_num
    · intro other h_other_positive h_other_maximum
      have h_outer_path :
          pathLengthMetersAfterMove setup other .speaker1 = 5 := by
        simpa [pathLengthMetersAfterMove, sourcePositionAfterMove] using
          h_initial_paths.1
      rcases h_readouts with ⟨h_separation, h_front, h_frequency, h_speed⟩
      rcases h_layout with
        ⟨h_speaker1_x, h_speaker1_y, h_speaker2_x, h_speaker2_y,
          h_speaker3_x, h_speaker3_y, h_listener_x, h_listener_y⟩
      have h_middle_path :
          pathLengthMetersAfterMove setup other .speaker2 =
            4 + metersValue other := by
        simp only [pathLengthMetersAfterMove, sourcePositionAfterMove,
          movedMiddleSpeakerPosition, Space.dist_eq, Fin.sum_univ_two,
          h_speaker2_x, h_speaker2_y, h_listener_x, h_listener_y, h_front]
        norm_num
        rw [Real.sqrt_sq_eq_abs, abs_of_nonpos]
        · ring
        · linarith
      rcases h_other_maximum .speaker1 .speaker2 with ⟨order, h_order⟩
      rw [h_outer_path, h_middle_path, h_wavelength] at h_order
      by_cases h_order_nonpositive : order ≤ 0
      · have h_order_nonpositive_real : (order : ℝ) ≤ 0 := by
          exact_mod_cast h_order_nonpositive
        rw [h_one_length]
        linarith
      · have h_order_positive : 1 ≤ order := by omega
        have h_order_positive_real : (1 : ℝ) ≤ order := by
          exact_mod_cast h_order_positive
        exfalso
        linarith
  constructor
  · exact h_least
  · refine ⟨lengthOfMeters 1, h_least, ?_⟩
    simpa [recordedAnswerChoice, AnswerChoice.meters] using h_one_length

end PhyXMiniProblems.ProblemPhyXMini0186
