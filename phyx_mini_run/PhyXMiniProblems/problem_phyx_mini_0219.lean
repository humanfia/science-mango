import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0219

open Dimension

/-!
# First intensity minimum to the right of two in-phase loudspeakers

Two coherent loudspeakers emit a common `474 Hz` tone in phase. The primary
image places them `3.00 m` apart on a horizontal line and places the
microphone `3.20 m` below their midpoint, where an intensity maximum is
recorded. The microphone is then translated horizontally to the right.

Physical lengths, frequencies, speeds, and acoustic intensities are
unit-independent Physlib quantities. Real numbers below are used only for
signed Cartesian-coordinate readouts, phase measured in cycles, and scalar
readouts in explicitly selected units.
-/

/-! ## Dimensionful acoustic quantities and readouts -/

/-- A nonnegative physical length independent of a chosen readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length used for Cartesian figure coordinates. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical frequency carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical sound speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-!
Acoustic intensity has dimension mass per time cubed, equivalently power per
area. It is kept as a physical quantity even though only extrema, rather than
numerical intensity readouts, are used by this problem.
-/
abbrev AcousticIntensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed Cartesian coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read frequency in inverse units of a selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Meter readout of a signed figure coordinate. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters length

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical objects, labels, and figure geometry -/

/-- The left and right loudspeakers visible in the primary image. -/
inductive SpeakerLabel where
  | left
  | right
  deriving DecidableEq, Repr

/-- The two dashed source-to-microphone paths labelled in the image. -/
inductive PathLabel where
  | d₁
  | d₂
  deriving DecidableEq, Repr

/-- The image labels `d₁` from the right speaker and `d₂` from the left. -/
def speakerForPath : PathLabel → SpeakerLabel
  | .d₁ => .right
  | .d₂ => .left

/-- The propagation medium implicit in the classroom sound problem. -/
inductive AcousticMedium where
  | roomAir
  | other
  deriving DecidableEq, Repr

/-- The kind of coherent acoustic source drawn in the figure. -/
inductive AcousticSourceKind where
  | loudspeaker
  | other
  deriving DecidableEq, Repr

/-!
The multiple-choice calculation uses the standard path-difference-only model
of two-source interference; distance-dependent amplitude variation is not
used to shift the locations of the extrema.
-/
inductive InterferenceApproximation where
  | pathDifferenceOnly
  | includesAmplitudeGradient
  deriving DecidableEq, Repr

/-- A Cartesian point whose coordinates are dimensionful signed lengths. -/
structure PlanePoint where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-!
Independent physical data and observables for the pictured experiment.

The path lengths `d₁` and `d₂`, the wavelength, and the locations of
intensity minima are related only by the governing-law structures below.
In particular, no field assigns the requested movement a numerical value.
-/
structure TwoSpeakerInterferenceSetup where
  propagationMedium : AcousticMedium
  sourceKind : SpeakerLabel → AcousticSourceKind
  sourcesMutuallyCoherent : Prop
  emissionPhaseCycles : SpeakerLabel → ℝ
  interferenceApproximation : InterferenceApproximation
  toneFrequency : FrequencyQuantity
  soundSpeed : SpeedQuantity
  soundWavelength : LengthQuantity
  speakerSeparation : LengthQuantity
  initialMicrophoneDistanceFromMidpoint : LengthQuantity
  speakerPosition : SpeakerLabel → PlanePoint
  speakerMidpoint : PlanePoint
  initialMicrophonePosition : PlanePoint
  microphonePositionAfterRightMove : LengthQuantity → PlanePoint
  pathLengthAfterRightMove : LengthQuantity → PathLabel → LengthQuantity
  acousticIntensityAt : PlanePoint → AcousticIntensityQuantity
  isIntensityMaximumAt : PlanePoint → Prop
  isIntensityMinimumAt : PlanePoint → Prop

/-!
Both sources are loudspeakers, mutually coherent, and emitted in phase. The
common phase origin is chosen as zero cycles. This contains no microphone
movement or answer-choice information.
-/
def MatchesCoherentInPhaseSourceScenario
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  setup.propagationMedium = .roomAir ∧
    (∀ speaker : SpeakerLabel,
      setup.sourceKind speaker = .loudspeaker) ∧
    setup.sourcesMutuallyCoherent ∧
    (∀ speaker : SpeakerLabel, setup.emissionPhaseCycles speaker = 0) ∧
    setup.interferenceApproximation = .pathDifferenceOnly

/-!
Numerical data explicitly stated in the problem: the speakers are `3.00 m`
apart, their tone is `474 Hz`, and the microphone starts `3.20 m` from the
speaker midpoint. The initial intensity maximum is a recorded observation.
-/
def MatchesProblemReadouts
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  lengthInMeters setup.speakerSeparation = 3 ∧
    frequencyInHertz setup.toneFrequency = 474 ∧
    lengthInMeters setup.initialMicrophoneDistanceFromMidpoint = 16 / 5 ∧
    setup.isIntensityMaximumAt setup.initialMicrophonePosition

/-!
Coordinates read from the primary image, in meters. The speaker midpoint is
the origin, the speakers are at horizontal coordinates `-1.50` and `1.50`,
and the initial microphone lies `3.20 m` vertically below the midpoint.
-/
def MatchesSuppliedFigure
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  signedLengthInMeters (setup.speakerPosition .left).horizontal = -3 / 2 ∧
    signedLengthInMeters (setup.speakerPosition .left).vertical = 0 ∧
    signedLengthInMeters (setup.speakerPosition .right).horizontal = 3 / 2 ∧
    signedLengthInMeters (setup.speakerPosition .right).vertical = 0 ∧
    signedLengthInMeters setup.speakerMidpoint.horizontal = 0 ∧
    signedLengthInMeters setup.speakerMidpoint.vertical = 0 ∧
    signedLengthInMeters setup.initialMicrophonePosition.horizontal = 0 ∧
    signedLengthInMeters setup.initialMicrophonePosition.vertical = -16 / 5

/-!
The source does not state the air temperature or sound speed. The recorded
choice `0.429 m` uses the conventional room-temperature still-air calibration
`343 m/s`; it is therefore exposed as a separate model input rather than
misattributed to the prose or figure.
-/
def UsesStandardRoomAirSoundSpeed
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  speedInMetersPerSecond setup.soundSpeed = 343

/-- Positive, nondegenerate acoustic and geometric quantities. -/
def HasPhysicalParameters (setup : TwoSpeakerInterferenceSetup) : Prop :=
  0 < frequencyInHertz setup.toneFrequency ∧
    0 < speedInMetersPerSecond setup.soundSpeed ∧
    0 < lengthInMeters setup.soundWavelength ∧
    0 < lengthInMeters setup.speakerSeparation ∧
    0 < lengthInMeters setup.initialMicrophoneDistanceFromMidpoint ∧
    ∀ displacement : LengthQuantity, ∀ path : PathLabel,
      0 < lengthInMeters (setup.pathLengthAfterRightMove displacement path)

/-! ## Governing wave, geometry, and interference laws -/

/-!
The nondispersive acoustic-wave relation `v = λ f`, stated for every
compatible selection of length and time units. This determines wavelength
from the calibration and tone frequency but says nothing about a minimum.
-/
structure SatisfiesAcousticWaveLaw
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  speedEqualsWavelengthTimesFrequency :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeed =
        lengthReadout lengthUnit setup.soundWavelength *
          frequencyReadout timeUnit setup.toneFrequency

/-!
General rightward-translation and Euclidean propagation geometry.

A nonnegative displacement adds to the microphone's horizontal coordinate
and leaves its vertical coordinate fixed. The speaker separation, initial
midpoint offset, and each labelled path are Euclidean distances. These laws
hold for arbitrary displacements and contain no distinguished `0.429 m`
case.
-/
structure SatisfiesRightMoveAndPathGeometry
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  speakerSeparationGeometry : ∀ unit : LengthUnit,
    lengthReadout unit setup.speakerSeparation =
      |signedLengthReadout unit (setup.speakerPosition .right).horizontal -
        signedLengthReadout unit (setup.speakerPosition .left).horizontal|
  initialMidpointDistanceGeometry : ∀ unit : LengthUnit,
    lengthReadout unit setup.initialMicrophoneDistanceFromMidpoint =
      Real.sqrt
        ((signedLengthReadout unit setup.initialMicrophonePosition.horizontal -
            signedLengthReadout unit setup.speakerMidpoint.horizontal) ^ 2 +
          (signedLengthReadout unit setup.initialMicrophonePosition.vertical -
            signedLengthReadout unit setup.speakerMidpoint.vertical) ^ 2)
  microphoneMovesRight : ∀ (displacement : LengthQuantity)
      (unit : LengthUnit),
    signedLengthReadout unit
        (setup.microphonePositionAfterRightMove displacement).horizontal =
      signedLengthReadout unit setup.initialMicrophonePosition.horizontal +
        lengthReadout unit displacement
  microphoneKeepsVerticalCoordinate : ∀ (displacement : LengthQuantity)
      (unit : LengthUnit),
    signedLengthReadout unit
        (setup.microphonePositionAfterRightMove displacement).vertical =
      signedLengthReadout unit setup.initialMicrophonePosition.vertical
  euclideanPathLength : ∀ (displacement : LengthQuantity)
      (path : PathLabel) (unit : LengthUnit),
    lengthReadout unit (setup.pathLengthAfterRightMove displacement path) =
      Real.sqrt
        ((signedLengthReadout unit
              (setup.microphonePositionAfterRightMove displacement).horizontal -
            signedLengthReadout unit
              (setup.speakerPosition (speakerForPath path)).horizontal) ^ 2 +
          (signedLengthReadout unit
              (setup.microphonePositionAfterRightMove displacement).vertical -
            signedLengthReadout unit
              (setup.speakerPosition (speakerForPath path)).vertical) ^ 2)

/-!
For two mutually coherent, in-phase sources in the path-difference-only
model, an intensity minimum occurs exactly when the magnitude of the path
difference is an odd half-integral number of wavelengths. The natural order
`0` is the first destructive order. This is a general governing law and does
not select a displacement or an answer value.
-/
structure SatisfiesInPhaseDestructiveInterferenceLaw
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  minimumIffOddHalfWavelengthPathDifference :
    ∀ displacement : LengthQuantity,
      setup.isIntensityMinimumAt
          (setup.microphonePositionAfterRightMove displacement) ↔
        ∃ order : ℕ, ∀ unit : LengthUnit,
          |lengthReadout unit
                (setup.pathLengthAfterRightMove displacement .d₂) -
              lengthReadout unit
                (setup.pathLengthAfterRightMove displacement .d₁)| =
            ((order : ℝ) + 1 / 2) *
              lengthReadout unit setup.soundWavelength

/-! ## The first minimum and displayed answer -/

/-- A strictly positive rightward movement reaching an intensity minimum. -/
def IsPositiveRightMoveToMinimum
    (setup : TwoSpeakerInterferenceSetup)
    (displacement : LengthQuantity) : Prop :=
  0 < lengthInMeters displacement ∧
    setup.isIntensityMinimumAt
      (setup.microphonePositionAfterRightMove displacement)

/-!
The first positive movement reaching a minimum: it reaches a minimum and no
other positive minimum-producing movement has a smaller physical length.
This semantic predicate contains no numerical movement or answer label.
-/
def IsFirstPositiveRightMoveToMinimum
    (setup : TwoSpeakerInterferenceSetup)
    (displacement : LengthQuantity) : Prop :=
  IsPositiveRightMoveToMinimum setup displacement ∧
    ∀ other : LengthQuantity,
      IsPositiveRightMoveToMinimum setup other →
        lengthInMeters displacement ≤ lengthInMeters other

/-!
The calibrated speed and the stated frequency determine the sound wavelength
as `343 / 474` meters. This is an intermediate wave-law consequence, not the
requested microphone movement.
-/
lemma soundWavelengthInMeters_eq
    (setup : TwoSpeakerInterferenceSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_calibration : UsesStandardRoomAirSoundSpeed setup)
    (h_wave : SatisfiesAcousticWaveLaw setup) :
    lengthInMeters setup.soundWavelength = (343 / 474 : ℝ) := by
  rcases h_readouts with ⟨_, h_frequency, _⟩
  have h_wave_meters :=
    h_wave.speedEqualsWavelengthTimesFrequency
      LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.soundSpeed =
      lengthInMeters setup.soundWavelength *
        frequencyInHertz setup.toneFrequency at h_wave_meters
  rw [h_calibration, h_frequency] at h_wave_meters
  norm_num at h_wave_meters ⊢
  linarith

/-- Labels of the four movement distances printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Movement distance in meters printed beside each answer label. -/
def displayedMoveInMeters : AnswerChoice → ℝ
  | .A => 729 / 1000
  | .B => 629 / 1000
  | .C => 529 / 1000
  | .D => 429 / 1000

/-- Answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A derived movement rounds to a displayed three-decimal meter value when it is
within half of `0.001 m` of that value.
-/
def RoundsToDisplayedMove
    (displacement : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters displacement - displayedMoveInMeters choice| < 1 / 2000

/-- Exactly one displayed value agrees with the derived movement. -/
def IsUniqueMatchingAnswer
    (displacement : LengthQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedMove displacement choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedMove displacement other → other = choice

/-!
Euclidean geometry and the first destructive order give a rightward movement
of approximately `0.428803 m`, which rounds to `0.429 m`. The numerical
conclusion appears only here, not in any setup, readout, or governing law.
-/
lemma firstMinimumRoundsTo429Meters
    (setup : TwoSpeakerInterferenceSetup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_calibration : UsesStandardRoomAirSoundSpeed setup)
    (h_physical : HasPhysicalParameters setup)
    (h_wave : SatisfiesAcousticWaveLaw setup)
    (h_geometry : SatisfiesRightMoveAndPathGeometry setup)
    (h_interference : SatisfiesInPhaseDestructiveInterferenceLaw setup)
    (displacement : LengthQuantity)
    (h_first : IsFirstPositiveRightMoveToMinimum setup displacement) :
    RoundsToDisplayedMove displacement .D := by
  rcases h_readouts with
    ⟨_, h_frequency, _, _⟩
  rcases h_figure with
    ⟨h_left_x, h_left_y, h_right_x, h_right_y, _,
      _, h_initial_x, h_initial_y⟩
  have h_wavelength :
      lengthInMeters setup.soundWavelength = (343 / 474 : ℝ) :=
    soundWavelengthInMeters_eq setup
      ⟨by assumption, h_frequency, by assumption, by assumption⟩
      h_calibration h_wave
  have h_path_formulas (move : LengthQuantity) :
      lengthInMeters (setup.pathLengthAfterRightMove move .d₂) =
          Real.sqrt
            ((lengthInMeters move + 3 / 2) ^ 2 + (16 / 5) ^ 2) ∧
        lengthInMeters (setup.pathLengthAfterRightMove move .d₁) =
          Real.sqrt
            ((lengthInMeters move - 3 / 2) ^ 2 + (16 / 5) ^ 2) := by
    have h_move_x :=
      h_geometry.microphoneMovesRight move LengthUnit.meters
    have h_move_y :=
      h_geometry.microphoneKeepsVerticalCoordinate
        move LengthUnit.meters
    change
      signedLengthInMeters
          (setup.microphonePositionAfterRightMove move).horizontal =
        signedLengthInMeters setup.initialMicrophonePosition.horizontal +
          lengthInMeters move at h_move_x
    change
      signedLengthInMeters
          (setup.microphonePositionAfterRightMove move).vertical =
        signedLengthInMeters setup.initialMicrophonePosition.vertical at h_move_y
    rw [h_initial_x, zero_add] at h_move_x
    rw [h_initial_y] at h_move_y
    constructor
    · have h_path :=
        h_geometry.euclideanPathLength
          move .d₂ LengthUnit.meters
      change
        lengthInMeters (setup.pathLengthAfterRightMove move .d₂) =
          Real.sqrt
            ((signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).horizontal -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₂)).horizontal) ^ 2 +
              (signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).vertical -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₂)).vertical) ^ 2)
          at h_path
      rw [speakerForPath, h_move_x, h_move_y, h_left_x, h_left_y] at h_path
      convert h_path using 1 <;> ring
    · have h_path :=
        h_geometry.euclideanPathLength
          move .d₁ LengthUnit.meters
      change
        lengthInMeters (setup.pathLengthAfterRightMove move .d₁) =
          Real.sqrt
            ((signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).horizontal -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₁)).horizontal) ^ 2 +
              (signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).vertical -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₁)).vertical) ^ 2)
          at h_path
      rw [speakerForPath, h_move_x, h_move_y, h_right_x, h_right_y] at h_path
      convert h_path using 1 <;> ring
  let s : ℝ := 343 / 948
  let r : ℝ :=
    s ^ 2 * (1249 / 25 - s ^ 2) / (4 * (9 - s ^ 2))
  let x : ℝ := Real.sqrt r
  have h_s_pos : 0 < s := by
    dsimp [s]
    norm_num
  have h_r_pos : 0 < r := by
    dsimp [r, s]
    norm_num
  have h_x_pos : 0 < x := Real.sqrt_pos.2 h_r_pos
  have h_x_sq : x ^ 2 = r := by
    dsimp [x]
    rw [Real.sq_sqrt h_r_pos.le]
  have h_x_lower : (857 / 2000 : ℝ) < x := by
    have h_x_sq' := h_x_sq
    dsimp [r, s] at h_x_sq'
    norm_num at h_x_sq'
    by_contra h_not
    have h_x_le : x ≤ 857 / 2000 := le_of_not_gt h_not
    nlinarith only [h_x_sq', h_x_le, h_x_pos]
  have h_x_upper : x < (859 / 2000 : ℝ) := by
    have h_x_sq' := h_x_sq
    dsimp [r, s] at h_x_sq'
    norm_num at h_x_sq'
    by_contra h_not
    have h_upper_le : (859 / 2000 : ℝ) ≤ x :=
      le_of_not_gt h_not
    nlinarith only [h_x_sq', h_upper_le, h_x_pos]
  have h_minus_pos : 0 < 3 * x / s - s / 2 := by
    have h_s_value : s = 343 / 948 := by rfl
    rw [h_s_value]
    norm_num at h_x_lower ⊢
    nlinarith only [h_x_lower]
  have h_plus_pos : 0 < 3 * x / s + s / 2 := by
    exact add_pos
      (div_pos (mul_pos (by norm_num) h_x_pos) h_s_pos)
      (div_pos h_s_pos (by norm_num))
  have h_sq_plus :
      (x + 3 / 2) ^ 2 + (16 / 5) ^ 2 =
        (3 * x / s + s / 2) ^ 2 := by
    have h_x_sq' := h_x_sq
    dsimp [r, s] at h_x_sq' ⊢
    norm_num at h_x_sq' ⊢
    nlinarith only [h_x_sq']
  have h_sq_minus :
      (x - 3 / 2) ^ 2 + (16 / 5) ^ 2 =
        (3 * x / s - s / 2) ^ 2 := by
    have h_x_sq' := h_x_sq
    dsimp [r, s] at h_x_sq' ⊢
    norm_num at h_x_sq' ⊢
    nlinarith only [h_x_sq']
  have h_model_path_difference :
      Real.sqrt ((x + 3 / 2) ^ 2 + (16 / 5) ^ 2) -
          Real.sqrt ((x - 3 / 2) ^ 2 + (16 / 5) ^ 2) =
        s := by
    rw [h_sq_plus, h_sq_minus, Real.sqrt_sq_eq_abs,
      Real.sqrt_sq_eq_abs, abs_of_pos h_plus_pos,
      abs_of_pos h_minus_pos]
    ring
  let candidate : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨⟨x, h_x_pos.le⟩⟩ : WithDim L𝓭 NNReal)
  have h_candidate_meters : lengthInMeters candidate = x := by
    unfold lengthInMeters lengthReadout
    rw [CarriesDimension.toDimensionful_apply_apply]
    norm_num [UnitChoices.dimScale, LengthUnit.meters,
      LengthUnit.div_eq_val]
    rfl
  have h_candidate_paths :=
    h_path_formulas candidate
  have h_candidate_path_difference_meters :
      |lengthInMeters
            (setup.pathLengthAfterRightMove candidate .d₂) -
          lengthInMeters
            (setup.pathLengthAfterRightMove candidate .d₁)| =
        s := by
    rw [h_candidate_paths.1, h_candidate_paths.2, h_candidate_meters,
      h_model_path_difference, abs_of_pos h_s_pos]
  have h_length_scale (length : LengthQuantity) (unit : LengthUnit) :
      lengthReadout unit length =
        ((UnitChoices.SI.dimScale
            {UnitChoices.SI with length := unit} L𝓭 : NNReal) : ℝ) *
          lengthInMeters length := by
    unfold lengthReadout lengthInMeters
    change
      (((length
          {UnitChoices.SI with length := unit}).val : NNReal) : ℝ) = _
    rw [length.property UnitChoices.SI
      {UnitChoices.SI with length := unit}]
    simp only [WithDim.smul_val]
    rfl
  have h_candidate_minimum :
      setup.isIntensityMinimumAt
        (setup.microphonePositionAfterRightMove candidate) := by
    apply
      (h_interference.minimumIffOddHalfWavelengthPathDifference
        candidate).2
    refine ⟨0, ?_⟩
    intro unit
    rw [h_length_scale, h_length_scale, h_length_scale, ← mul_sub,
      abs_mul, abs_of_nonneg (NNReal.coe_nonneg _),
      h_candidate_path_difference_meters, h_wavelength]
    dsimp [s]
    ring
  have h_lower_bound (move : LengthQuantity)
      (h_move_pos : 0 < lengthInMeters move)
      (h_move_minimum :
        setup.isIntensityMinimumAt
          (setup.microphonePositionAfterRightMove move)) :
      x ≤ lengthInMeters move := by
    obtain ⟨order, h_order⟩ :=
      (h_interference.minimumIffOddHalfWavelengthPathDifference
        move).1 h_move_minimum
    have h_path := h_order LengthUnit.meters
    rcases h_path_formulas move with ⟨h_d₂, h_d₁⟩
    change
      |lengthInMeters
            (setup.pathLengthAfterRightMove move .d₂) -
          lengthInMeters
            (setup.pathLengthAfterRightMove move .d₁)| =
        ((order : ℝ) + 1 / 2) *
          lengthInMeters setup.soundWavelength at h_path
    rw [h_d₂, h_d₁, h_wavelength] at h_path
    let y : ℝ := lengthInMeters move
    let A : ℝ :=
      Real.sqrt ((y + 3 / 2) ^ 2 + (16 / 5) ^ 2)
    let B : ℝ :=
      Real.sqrt ((y - 3 / 2) ^ 2 + (16 / 5) ^ 2)
    let delta : ℝ :=
      ((order : ℝ) + 1 / 2) * (343 / 474)
    change |A - B| = delta at h_path
    have h_delta_ge : s ≤ delta := by
      dsimp [s, delta]
      have h_order_nonneg : 0 ≤ (order : ℝ) :=
        Nat.cast_nonneg order
      norm_num at h_order_nonneg ⊢
      nlinarith only [h_order_nonneg]
    have h_delta_pos : 0 < delta :=
      lt_of_lt_of_le h_s_pos h_delta_ge
    have h_A_nonneg : 0 ≤ A := Real.sqrt_nonneg _
    have h_B_nonneg : 0 ≤ B := Real.sqrt_nonneg _
    have h_A_sq :
        A ^ 2 = (y + 3 / 2) ^ 2 + (16 / 5) ^ 2 := by
      dsimp [A]
      rw [Real.sq_sqrt (by positivity)]
    have h_B_sq :
        B ^ 2 = (y - 3 / 2) ^ 2 + (16 / 5) ^ 2 := by
      dsimp [B]
      rw [Real.sq_sqrt (by positivity)]
    have h_y_pos : 0 < y := h_move_pos
    have h_B_lt_A : B < A := by
      nlinarith only [h_A_sq, h_B_sq, h_A_nonneg,
        h_B_nonneg, h_y_pos]
    have h_difference : A - B = delta := by
      rw [abs_of_pos (sub_pos.mpr h_B_lt_A)] at h_path
      exact h_path
    have h_sum_large : 2 * y < A + B := by
      by_cases h_y_large : 3 / 2 ≤ y
      · have h_A_linear : y + 3 / 2 < A := by
          nlinarith only [h_A_sq, h_A_nonneg, h_y_pos]
        have h_B_linear : y - 3 / 2 < B := by
          nlinarith only [h_B_sq, h_B_nonneg, h_y_large]
        linarith
      · have h_y_small : y < 3 / 2 := lt_of_not_ge h_y_large
        have h_A_linear : y + 3 / 2 < A := by
          nlinarith only [h_A_sq, h_A_nonneg, h_y_pos]
        nlinarith only [h_A_linear, h_B_nonneg, h_y_small]
    have h_product : delta * (A + B) = 6 * y := by
      calc
        _ = (A - B) * (A + B) := by rw [h_difference]
        _ = A ^ 2 - B ^ 2 := by ring
        _ = 6 * y := by rw [h_A_sq, h_B_sq]; ring
    have h_delta_lt_three : delta < 3 := by
      by_contra h_not
      have h_three_le : 3 ≤ delta := le_of_not_gt h_not
      have h_sum_nonneg : 0 ≤ A + B :=
        add_nonneg h_A_nonneg h_B_nonneg
      have h_mul :=
        mul_le_mul_of_nonneg_right h_three_le h_sum_nonneg
      rw [h_product] at h_mul
      nlinarith only [h_mul, h_sum_large]
    have h_sum_sq :
        (A + B) ^ 2 =
          4 * y ^ 2 + 1249 / 25 - delta ^ 2 := by
      calc
        _ = 2 * (A ^ 2 + B ^ 2) - (A - B) ^ 2 := by ring
        _ = _ := by rw [h_A_sq, h_B_sq, h_difference]; ring
    have h_product_sq :=
      congrArg (fun z : ℝ => z ^ 2) h_product
    have h_polynomial :
        4 * y ^ 2 * (9 - delta ^ 2) =
          delta ^ 2 * (1249 / 25 - delta ^ 2) := by
      rw [mul_pow, h_sum_sq] at h_product_sq
      ring_nf at h_product_sq ⊢
      linarith only [h_product_sq]
    have h_r_polynomial :
        4 * r * (9 - s ^ 2) =
          s ^ 2 * (1249 / 25 - s ^ 2) := by
      dsimp [r, s]
      norm_num
    have h_s_sq_lt : s ^ 2 < 9 := by
      dsimp [s]
      norm_num
    have h_delta_sq_ge : s ^ 2 ≤ delta ^ 2 := by
      nlinarith only [h_delta_ge, h_s_pos, h_delta_pos]
    have h_delta_sq_lt : delta ^ 2 < 9 := by
      nlinarith only [h_delta_lt_three, h_delta_pos]
    have h_factor_pos :
        0 <
          36 * (1249 / 100 : ℝ) -
            9 * (delta ^ 2 + s ^ 2) + delta ^ 2 * s ^ 2 := by
      have h_s_sq_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
      have h_delta_sq_nonneg : 0 ≤ delta ^ 2 :=
        sq_nonneg delta
      nlinarith only [h_s_sq_lt, h_delta_sq_lt,
        h_s_sq_nonneg, h_delta_sq_nonneg]
    have h_comparison :
        4 * (9 - delta ^ 2) * (9 - s ^ 2) * (y ^ 2 - r) =
          (delta ^ 2 - s ^ 2) *
            (36 * (1249 / 100 : ℝ) -
              9 * (delta ^ 2 + s ^ 2) +
                delta ^ 2 * s ^ 2) := by
      calc
        _ =
            (9 - s ^ 2) *
                (4 * y ^ 2 * (9 - delta ^ 2)) -
              (9 - delta ^ 2) *
                (4 * r * (9 - s ^ 2)) := by ring
        _ =
            (9 - s ^ 2) *
                (delta ^ 2 * (1249 / 25 - delta ^ 2)) -
              (9 - delta ^ 2) *
                (s ^ 2 * (1249 / 25 - s ^ 2)) := by
                  rw [h_polynomial, h_r_polynomial]
        _ = _ := by ring
    have h_denominator_pos :
        0 < 4 * (9 - delta ^ 2) * (9 - s ^ 2) := by
      positivity
    have h_rhs_nonneg :
        0 ≤
          (delta ^ 2 - s ^ 2) *
            (36 * (1249 / 100 : ℝ) -
              9 * (delta ^ 2 + s ^ 2) +
                delta ^ 2 * s ^ 2) :=
      mul_nonneg (sub_nonneg.mpr h_delta_sq_ge) h_factor_pos.le
    have h_lhs_nonneg :
        0 ≤
          4 * (9 - delta ^ 2) * (9 - s ^ 2) *
            (y ^ 2 - r) := by
      rw [h_comparison]
      exact h_rhs_nonneg
    have h_r_le_y_sq : r ≤ y ^ 2 := by
      have h_nonneg :=
        nonneg_of_mul_nonneg_right
          h_lhs_nonneg h_denominator_pos
      linarith
    change x ≤ y
    nlinarith only [h_x_sq, h_x_pos, h_y_pos, h_r_le_y_sq]
  have h_displacement_lower :
      x ≤ lengthInMeters displacement :=
    h_lower_bound displacement h_first.1.1 h_first.1.2
  have h_displacement_upper :
      lengthInMeters displacement ≤ x := by
    have h_le :=
      h_first.2 candidate
        ⟨by simpa [h_candidate_meters] using h_x_pos,
          h_candidate_minimum⟩
    simpa [h_candidate_meters] using h_le
  have h_displacement_eq :
      lengthInMeters displacement = x :=
    le_antisymm h_displacement_upper h_displacement_lower
  unfold RoundsToDisplayedMove displayedMoveInMeters
  rw [h_displacement_eq, abs_lt]
  constructor <;> nlinarith only [h_x_lower, h_x_upper]

/-!
The first positive rightward movement to an intensity minimum rounds to
`0.429 m`, and this uniquely selects the recorded answer D.

This formalizes `thm:physics:phyx_mini_0219:target`.
-/
theorem problem_phyx_mini_0219
    (setup : TwoSpeakerInterferenceSetup)
    (h_sources : MatchesCoherentInPhaseSourceScenario setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_calibration : UsesStandardRoomAirSoundSpeed setup)
    (h_physical : HasPhysicalParameters setup)
    (h_wave : SatisfiesAcousticWaveLaw setup)
    (h_geometry : SatisfiesRightMoveAndPathGeometry setup)
    (h_interference : SatisfiesInPhaseDestructiveInterferenceLaw setup) :
    ∃ displacement : LengthQuantity,
      IsFirstPositiveRightMoveToMinimum setup displacement ∧
        RoundsToDisplayedMove displacement recordedDatasetAnswer ∧
        IsUniqueMatchingAnswer displacement recordedDatasetAnswer ∧
        recordedDatasetAnswer = .D := by
  have h_readouts_components := h_readouts
  rcases h_readouts_components with
    ⟨_, h_frequency, _, _⟩
  have h_figure_components := h_figure
  rcases h_figure_components with
    ⟨h_left_x, h_left_y, h_right_x, h_right_y, _,
      _, h_initial_x, h_initial_y⟩
  have h_wavelength :
      lengthInMeters setup.soundWavelength = (343 / 474 : ℝ) :=
    soundWavelengthInMeters_eq setup h_readouts
      h_calibration h_wave
  have h_path_formulas (move : LengthQuantity) :
      lengthInMeters (setup.pathLengthAfterRightMove move .d₂) =
          Real.sqrt
            ((lengthInMeters move + 3 / 2) ^ 2 + (16 / 5) ^ 2) ∧
        lengthInMeters (setup.pathLengthAfterRightMove move .d₁) =
          Real.sqrt
            ((lengthInMeters move - 3 / 2) ^ 2 + (16 / 5) ^ 2) := by
    have h_move_x :=
      h_geometry.microphoneMovesRight move LengthUnit.meters
    have h_move_y :=
      h_geometry.microphoneKeepsVerticalCoordinate
        move LengthUnit.meters
    change
      signedLengthInMeters
          (setup.microphonePositionAfterRightMove move).horizontal =
        signedLengthInMeters setup.initialMicrophonePosition.horizontal +
          lengthInMeters move at h_move_x
    change
      signedLengthInMeters
          (setup.microphonePositionAfterRightMove move).vertical =
        signedLengthInMeters setup.initialMicrophonePosition.vertical at h_move_y
    rw [h_initial_x, zero_add] at h_move_x
    rw [h_initial_y] at h_move_y
    constructor
    · have h_path :=
        h_geometry.euclideanPathLength
          move .d₂ LengthUnit.meters
      change
        lengthInMeters (setup.pathLengthAfterRightMove move .d₂) =
          Real.sqrt
            ((signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).horizontal -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₂)).horizontal) ^ 2 +
              (signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).vertical -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₂)).vertical) ^ 2)
          at h_path
      rw [speakerForPath, h_move_x, h_move_y, h_left_x, h_left_y] at h_path
      convert h_path using 1 <;> ring
    · have h_path :=
        h_geometry.euclideanPathLength
          move .d₁ LengthUnit.meters
      change
        lengthInMeters (setup.pathLengthAfterRightMove move .d₁) =
          Real.sqrt
            ((signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).horizontal -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₁)).horizontal) ^ 2 +
              (signedLengthInMeters
                  (setup.microphonePositionAfterRightMove move).vertical -
                signedLengthInMeters
                  (setup.speakerPosition (speakerForPath .d₁)).vertical) ^ 2)
          at h_path
      rw [speakerForPath, h_move_x, h_move_y, h_right_x, h_right_y] at h_path
      convert h_path using 1 <;> ring
  let s : ℝ := 343 / 948
  let r : ℝ :=
    s ^ 2 * (1249 / 25 - s ^ 2) / (4 * (9 - s ^ 2))
  let x : ℝ := Real.sqrt r
  have h_s_pos : 0 < s := by
    dsimp [s]
    norm_num
  have h_r_pos : 0 < r := by
    dsimp [r, s]
    norm_num
  have h_x_pos : 0 < x := Real.sqrt_pos.2 h_r_pos
  have h_x_sq : x ^ 2 = r := by
    dsimp [x]
    rw [Real.sq_sqrt h_r_pos.le]
  have h_x_lower : (857 / 2000 : ℝ) < x := by
    have h_x_sq' := h_x_sq
    dsimp [r, s] at h_x_sq'
    norm_num at h_x_sq'
    by_contra h_not
    have h_x_le : x ≤ 857 / 2000 := le_of_not_gt h_not
    nlinarith only [h_x_sq', h_x_le, h_x_pos]
  have h_minus_pos : 0 < 3 * x / s - s / 2 := by
    have h_s_value : s = 343 / 948 := by rfl
    rw [h_s_value]
    norm_num at h_x_lower ⊢
    nlinarith only [h_x_lower]
  have h_plus_pos : 0 < 3 * x / s + s / 2 := by
    exact add_pos
      (div_pos (mul_pos (by norm_num) h_x_pos) h_s_pos)
      (div_pos h_s_pos (by norm_num))
  have h_sq_plus :
      (x + 3 / 2) ^ 2 + (16 / 5) ^ 2 =
        (3 * x / s + s / 2) ^ 2 := by
    have h_x_sq' := h_x_sq
    dsimp [r, s] at h_x_sq' ⊢
    norm_num at h_x_sq' ⊢
    nlinarith only [h_x_sq']
  have h_sq_minus :
      (x - 3 / 2) ^ 2 + (16 / 5) ^ 2 =
        (3 * x / s - s / 2) ^ 2 := by
    have h_x_sq' := h_x_sq
    dsimp [r, s] at h_x_sq' ⊢
    norm_num at h_x_sq' ⊢
    nlinarith only [h_x_sq']
  have h_model_path_difference :
      Real.sqrt ((x + 3 / 2) ^ 2 + (16 / 5) ^ 2) -
          Real.sqrt ((x - 3 / 2) ^ 2 + (16 / 5) ^ 2) =
        s := by
    rw [h_sq_plus, h_sq_minus, Real.sqrt_sq_eq_abs,
      Real.sqrt_sq_eq_abs, abs_of_pos h_plus_pos,
      abs_of_pos h_minus_pos]
    ring
  let candidate : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨⟨x, h_x_pos.le⟩⟩ : WithDim L𝓭 NNReal)
  have h_candidate_meters : lengthInMeters candidate = x := by
    unfold lengthInMeters lengthReadout
    rw [CarriesDimension.toDimensionful_apply_apply]
    norm_num [UnitChoices.dimScale, LengthUnit.meters,
      LengthUnit.div_eq_val]
    rfl
  have h_candidate_paths :=
    h_path_formulas candidate
  have h_candidate_path_difference_meters :
      |lengthInMeters
            (setup.pathLengthAfterRightMove candidate .d₂) -
          lengthInMeters
            (setup.pathLengthAfterRightMove candidate .d₁)| =
        s := by
    rw [h_candidate_paths.1, h_candidate_paths.2, h_candidate_meters,
      h_model_path_difference, abs_of_pos h_s_pos]
  have h_length_scale (length : LengthQuantity) (unit : LengthUnit) :
      lengthReadout unit length =
        ((UnitChoices.SI.dimScale
            {UnitChoices.SI with length := unit} L𝓭 : NNReal) : ℝ) *
          lengthInMeters length := by
    unfold lengthReadout lengthInMeters
    change
      (((length
          {UnitChoices.SI with length := unit}).val : NNReal) : ℝ) = _
    rw [length.property UnitChoices.SI
      {UnitChoices.SI with length := unit}]
    simp only [WithDim.smul_val]
    rfl
  have h_candidate_minimum :
      setup.isIntensityMinimumAt
        (setup.microphonePositionAfterRightMove candidate) := by
    apply
      (h_interference.minimumIffOddHalfWavelengthPathDifference
        candidate).2
    refine ⟨0, ?_⟩
    intro unit
    rw [h_length_scale, h_length_scale, h_length_scale, ← mul_sub,
      abs_mul, abs_of_nonneg (NNReal.coe_nonneg _),
      h_candidate_path_difference_meters, h_wavelength]
    dsimp [s]
    ring
  have h_lower_bound (move : LengthQuantity)
      (h_move_pos : 0 < lengthInMeters move)
      (h_move_minimum :
        setup.isIntensityMinimumAt
          (setup.microphonePositionAfterRightMove move)) :
      x ≤ lengthInMeters move := by
    obtain ⟨order, h_order⟩ :=
      (h_interference.minimumIffOddHalfWavelengthPathDifference
        move).1 h_move_minimum
    have h_path := h_order LengthUnit.meters
    rcases h_path_formulas move with ⟨h_d₂, h_d₁⟩
    change
      |lengthInMeters
            (setup.pathLengthAfterRightMove move .d₂) -
          lengthInMeters
            (setup.pathLengthAfterRightMove move .d₁)| =
        ((order : ℝ) + 1 / 2) *
          lengthInMeters setup.soundWavelength at h_path
    rw [h_d₂, h_d₁, h_wavelength] at h_path
    let y : ℝ := lengthInMeters move
    let A : ℝ :=
      Real.sqrt ((y + 3 / 2) ^ 2 + (16 / 5) ^ 2)
    let B : ℝ :=
      Real.sqrt ((y - 3 / 2) ^ 2 + (16 / 5) ^ 2)
    let delta : ℝ :=
      ((order : ℝ) + 1 / 2) * (343 / 474)
    change |A - B| = delta at h_path
    have h_delta_ge : s ≤ delta := by
      dsimp [s, delta]
      have h_order_nonneg : 0 ≤ (order : ℝ) :=
        Nat.cast_nonneg order
      norm_num at h_order_nonneg ⊢
      nlinarith only [h_order_nonneg]
    have h_delta_pos : 0 < delta :=
      lt_of_lt_of_le h_s_pos h_delta_ge
    have h_A_nonneg : 0 ≤ A := Real.sqrt_nonneg _
    have h_B_nonneg : 0 ≤ B := Real.sqrt_nonneg _
    have h_A_sq :
        A ^ 2 = (y + 3 / 2) ^ 2 + (16 / 5) ^ 2 := by
      dsimp [A]
      rw [Real.sq_sqrt (by positivity)]
    have h_B_sq :
        B ^ 2 = (y - 3 / 2) ^ 2 + (16 / 5) ^ 2 := by
      dsimp [B]
      rw [Real.sq_sqrt (by positivity)]
    have h_y_pos : 0 < y := h_move_pos
    have h_B_lt_A : B < A := by
      nlinarith only [h_A_sq, h_B_sq, h_A_nonneg,
        h_B_nonneg, h_y_pos]
    have h_difference : A - B = delta := by
      rw [abs_of_pos (sub_pos.mpr h_B_lt_A)] at h_path
      exact h_path
    have h_sum_large : 2 * y < A + B := by
      by_cases h_y_large : 3 / 2 ≤ y
      · have h_A_linear : y + 3 / 2 < A := by
          nlinarith only [h_A_sq, h_A_nonneg, h_y_pos]
        have h_B_linear : y - 3 / 2 < B := by
          nlinarith only [h_B_sq, h_B_nonneg, h_y_large]
        linarith
      · have h_y_small : y < 3 / 2 := lt_of_not_ge h_y_large
        have h_A_linear : y + 3 / 2 < A := by
          nlinarith only [h_A_sq, h_A_nonneg, h_y_pos]
        nlinarith only [h_A_linear, h_B_nonneg, h_y_small]
    have h_product : delta * (A + B) = 6 * y := by
      calc
        _ = (A - B) * (A + B) := by rw [h_difference]
        _ = A ^ 2 - B ^ 2 := by ring
        _ = 6 * y := by rw [h_A_sq, h_B_sq]; ring
    have h_delta_lt_three : delta < 3 := by
      by_contra h_not
      have h_three_le : 3 ≤ delta := le_of_not_gt h_not
      have h_sum_nonneg : 0 ≤ A + B :=
        add_nonneg h_A_nonneg h_B_nonneg
      have h_mul :=
        mul_le_mul_of_nonneg_right h_three_le h_sum_nonneg
      rw [h_product] at h_mul
      nlinarith only [h_mul, h_sum_large]
    have h_sum_sq :
        (A + B) ^ 2 =
          4 * y ^ 2 + 1249 / 25 - delta ^ 2 := by
      calc
        _ = 2 * (A ^ 2 + B ^ 2) - (A - B) ^ 2 := by ring
        _ = _ := by rw [h_A_sq, h_B_sq, h_difference]; ring
    have h_product_sq :=
      congrArg (fun z : ℝ => z ^ 2) h_product
    have h_polynomial :
        4 * y ^ 2 * (9 - delta ^ 2) =
          delta ^ 2 * (1249 / 25 - delta ^ 2) := by
      rw [mul_pow, h_sum_sq] at h_product_sq
      ring_nf at h_product_sq ⊢
      linarith only [h_product_sq]
    have h_r_polynomial :
        4 * r * (9 - s ^ 2) =
          s ^ 2 * (1249 / 25 - s ^ 2) := by
      dsimp [r, s]
      norm_num
    have h_s_sq_lt : s ^ 2 < 9 := by
      dsimp [s]
      norm_num
    have h_delta_sq_ge : s ^ 2 ≤ delta ^ 2 := by
      nlinarith only [h_delta_ge, h_s_pos, h_delta_pos]
    have h_delta_sq_lt : delta ^ 2 < 9 := by
      nlinarith only [h_delta_lt_three, h_delta_pos]
    have h_factor_pos :
        0 <
          36 * (1249 / 100 : ℝ) -
            9 * (delta ^ 2 + s ^ 2) + delta ^ 2 * s ^ 2 := by
      have h_s_sq_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
      have h_delta_sq_nonneg : 0 ≤ delta ^ 2 :=
        sq_nonneg delta
      nlinarith only [h_s_sq_lt, h_delta_sq_lt,
        h_s_sq_nonneg, h_delta_sq_nonneg]
    have h_comparison :
        4 * (9 - delta ^ 2) * (9 - s ^ 2) * (y ^ 2 - r) =
          (delta ^ 2 - s ^ 2) *
            (36 * (1249 / 100 : ℝ) -
              9 * (delta ^ 2 + s ^ 2) +
                delta ^ 2 * s ^ 2) := by
      calc
        _ =
            (9 - s ^ 2) *
                (4 * y ^ 2 * (9 - delta ^ 2)) -
              (9 - delta ^ 2) *
                (4 * r * (9 - s ^ 2)) := by ring
        _ =
            (9 - s ^ 2) *
                (delta ^ 2 * (1249 / 25 - delta ^ 2)) -
              (9 - delta ^ 2) *
                (s ^ 2 * (1249 / 25 - s ^ 2)) := by
                  rw [h_polynomial, h_r_polynomial]
        _ = _ := by ring
    have h_denominator_pos :
        0 < 4 * (9 - delta ^ 2) * (9 - s ^ 2) := by
      positivity
    have h_rhs_nonneg :
        0 ≤
          (delta ^ 2 - s ^ 2) *
            (36 * (1249 / 100 : ℝ) -
              9 * (delta ^ 2 + s ^ 2) +
                delta ^ 2 * s ^ 2) :=
      mul_nonneg (sub_nonneg.mpr h_delta_sq_ge) h_factor_pos.le
    have h_lhs_nonneg :
        0 ≤
          4 * (9 - delta ^ 2) * (9 - s ^ 2) *
            (y ^ 2 - r) := by
      rw [h_comparison]
      exact h_rhs_nonneg
    have h_r_le_y_sq : r ≤ y ^ 2 := by
      have h_nonneg :=
        nonneg_of_mul_nonneg_right
          h_lhs_nonneg h_denominator_pos
      linarith
    change x ≤ y
    nlinarith only [h_x_sq, h_x_pos, h_y_pos, h_r_le_y_sq]
  have h_first : IsFirstPositiveRightMoveToMinimum setup candidate := by
    refine ⟨⟨?_, h_candidate_minimum⟩, ?_⟩
    · simpa [h_candidate_meters] using h_x_pos
    · intro other h_other
      have h_bound :=
        h_lower_bound other h_other.1 h_other.2
      simpa [h_candidate_meters] using h_bound
  have h_rounds_D :
      RoundsToDisplayedMove candidate .D :=
    firstMinimumRoundsTo429Meters setup h_readouts h_figure
      h_calibration h_physical h_wave h_geometry
      h_interference candidate h_first
  have h_unique_D : IsUniqueMatchingAnswer candidate .D := by
    refine ⟨h_rounds_D, ?_⟩
    intro other h_other
    cases other with
    | D => rfl
    | A =>
        exfalso
        unfold RoundsToDisplayedMove displayedMoveInMeters at h_rounds_D h_other
        rw [abs_lt] at h_rounds_D h_other
        nlinarith only [h_rounds_D.1, h_rounds_D.2,
          h_other.1, h_other.2]
    | B =>
        exfalso
        unfold RoundsToDisplayedMove displayedMoveInMeters at h_rounds_D h_other
        rw [abs_lt] at h_rounds_D h_other
        nlinarith only [h_rounds_D.1, h_rounds_D.2,
          h_other.1, h_other.2]
    | C =>
        exfalso
        unfold RoundsToDisplayedMove displayedMoveInMeters at h_rounds_D h_other
        rw [abs_lt] at h_rounds_D h_other
        nlinarith only [h_rounds_D.1, h_rounds_D.2,
          h_other.1, h_other.2]
  refine ⟨candidate, h_first, ?_, ?_, rfl⟩
  · exact h_rounds_D
  · exact h_unique_D

end PhyXMiniProblems.ProblemPhyXMini0219
