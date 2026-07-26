import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0169

open Dimension

/-!
# First destructive interference from two in-phase speakers

Speakers `A` and `B` are driven in phase at `725 Hz`.  Initially each is
`4.50 m` from the listener.  Speaker `B` remains fixed while `A` is moved
slowly away from the listener.  In the displayed configuration the points
are collinear in the order `A`, `B`, listener, and the speaker separation is
the displacement labelled `d`.

Lengths, frequency, and propagation speed are PhysLean dimensionful
quantities.  Real numbers below are explicitly SI readouts, figure
coordinates in metres, or dimensionless interference orders.  The standard
ambient-air speed `343 m/s` is isolated as a calibration assumption because
it is needed to obtain the recorded numerical choice but is not printed in
the problem statement.
-/

/-- A physical quantity carrying the dimension of length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical propagation speed. -/
abbrev SpeedQuantity : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in metres. -/
def metersValue (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical frequency in hertz. -/
def hertzValue (frequency : FrequencyQuantity) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read a physical speed in metres per second. -/
def metersPerSecondValue (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Construct the physical length whose SI readout is the supplied number of metres. -/
noncomputable def lengthInMeters (value : ℝ) : LengthQuantity :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-- Labels of the two acoustic sources. -/
inductive SpeakerLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- Point labels visible in the primary figure. -/
inductive FigurePoint where
  | A
  | B
  | listener
  deriving DecidableEq, Repr

/-- The figure point occupied by a labeled speaker. -/
def SpeakerLabel.figurePoint : SpeakerLabel → FigurePoint
  | .A => .A
  | .B => .B

/-- The slow-motion regime described in the prose. -/
inductive SpeakerMotionRegime where
  | quasistaticAwayFromListener
  deriving DecidableEq, Repr

/-- A monochromatic speaker at the common oscillator reference time. -/
structure AcousticSpeaker where
  /-- Frequency of the emitted sound. -/
  frequency : FrequencyQuantity
  /-- Emission phase, regarded modulo one full turn. -/
  emissionPhase : Real.Angle

/-!
The physical apparatus and its observables.  The argument of
`figurePositionMetersAt`, `rayPathLengthAt`, and
`destructiveInterferenceAt` is the nonnegative physical displacement of
speaker `A` from its initial position.  In the primary image that same
quantity is the speaker separation labelled `d`.
-/
structure TwoSpeakerInterferenceSetup where
  speaker : SpeakerLabel → AcousticSpeaker
  oscillatorFrequency : FrequencyQuantity
  wavelength : LengthQuantity
  soundSpeed : SpeedQuantity
  initialListenerDistance : LengthQuantity
  motionRegime : SpeakerMotionRegime
  /-- Signed coordinate in metres in a one-dimensional chart with the listener at zero. -/
  figurePositionMetersAt : LengthQuantity → FigurePoint → ℝ
  /-- Physical speaker-to-listener ray length after the given displacement. -/
  rayPathLengthAt : SpeakerLabel → LengthQuantity → LengthQuantity
  /-- Observable destructive interference at the listener after the given displacement. -/
  destructiveInterferenceAt : LengthQuantity → Prop

/-- Both speakers are driven at the oscillator frequency and with the same phase. -/
def DrivenInPhaseBySameOscillator
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  (setup.speaker .A).frequency = setup.oscillatorFrequency ∧
    (setup.speaker .B).frequency = setup.oscillatorFrequency ∧
    (setup.speaker .A).emissionPhase = (setup.speaker .B).emissionPhase

/-- Speaker separation in the signed metre chart of the primary figure. -/
def speakerSeparationMetersAt
    (setup : TwoSpeakerInterferenceSetup) (displacement : LengthQuantity) : ℝ :=
  |setup.figurePositionMetersAt displacement .A -
    setup.figurePositionMetersAt displacement .B|

/-!
The collinear layout read from the primary raster image.  The listener is at
coordinate zero, `B` stays `4.50 m` to the left once the numerical readout is
supplied, and moving `A` away by `d` puts it a further `d` to the left.
Consequently the labeled `A`--`B` separation is `d`, and each ray length is
the absolute source-to-listener coordinate difference.  At displacement zero
this also states that both speakers start at the same distance from the
listener.
-/
def HasDepictedCollinearGeometry
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  ∀ displacement : LengthQuantity,
    0 ≤ metersValue displacement →
      setup.figurePositionMetersAt displacement .listener = 0 ∧
      setup.figurePositionMetersAt displacement .B =
        -metersValue setup.initialListenerDistance ∧
      setup.figurePositionMetersAt displacement .A =
        -(metersValue setup.initialListenerDistance +
          metersValue displacement) ∧
      speakerSeparationMetersAt setup displacement =
        metersValue displacement ∧
      (∀ label : SpeakerLabel,
        metersValue (setup.rayPathLengthAt label displacement) =
          |setup.figurePositionMetersAt displacement .listener -
            setup.figurePositionMetersAt displacement label.figurePoint|)

/-!
Numerical readouts stated in the prose and figure.  This predicate contains
the `725 Hz` oscillator frequency, the `4.50 m` initial distance, and the
quasistatic direction of motion, but no destructive-interference conclusion.
-/
def HasStatedReadouts (setup : TwoSpeakerInterferenceSetup) : Prop :=
  hertzValue setup.oscillatorFrequency = 725 ∧
    metersValue setup.initialListenerDistance = (9 / 2 : ℝ) ∧
    setup.motionRegime = .quasistaticAwayFromListener

/-!
Ambient-air calibration used by the recorded answer.  The source does not
state temperature or sound speed; `343 m/s` is the conventional room-
temperature model which gives the listed `0.237 m` after rounding.
-/
def UsesStandardAmbientAirSoundSpeed
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  metersPerSecondValue setup.soundSpeed = 343

/-- Positivity conditions for the physical length, frequency, and speed parameters. -/
def HasPhysicalParameters (setup : TwoSpeakerInterferenceSetup) : Prop :=
  0 < hertzValue setup.oscillatorFrequency ∧
    0 < metersValue setup.initialListenerDistance ∧
    0 < metersValue setup.wavelength ∧
    0 < metersPerSecondValue setup.soundSpeed ∧
    ∀ (label : SpeakerLabel) (displacement : LengthQuantity),
      0 ≤ metersValue displacement →
        0 ≤ metersValue (setup.rayPathLengthAt label displacement)

/-- Absolute difference of the two speaker-to-listener path lengths, in metres. -/
def pathDifferenceMeters
    (setup : TwoSpeakerInterferenceSetup) (displacement : LengthQuantity) : ℝ :=
  |metersValue (setup.rayPathLengthAt .A displacement) -
    metersValue (setup.rayPathLengthAt .B displacement)|

/-!
The governing laws of the idealized two-source acoustic model:

* the nondispersive relation is `speed = frequency * wavelength` in SI;
* for coherent in-phase sources, a nonnegative displacement is destructive
  exactly when its path difference is an odd multiple of half a wavelength.

Both clauses are uniform laws.  In particular, neither names a first
minimum, a numerical displacement, or an answer choice.
-/
structure SatisfiesAcousticInterferenceLaws
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  dispersionRelation :
    metersPerSecondValue setup.soundSpeed =
      hertzValue setup.oscillatorFrequency * metersValue setup.wavelength
  destructiveInterferenceCriterion :
    DrivenInPhaseBySameOscillator setup →
      ∀ displacement : LengthQuantity,
        0 ≤ metersValue displacement →
          (setup.destructiveInterferenceAt displacement ↔
            ∃ order : ℕ,
              2 * pathDifferenceMeters setup displacement =
                (2 * (order : ℝ) + 1) * metersValue setup.wavelength)

/-!
A displacement is the first destructive one when it is positive and
destructive and no smaller positive physical displacement is destructive.
This is a behavioral definition over the setup observable, not a numerical
answer by definition.
-/
def IsFirstDestructiveDisplacement
    (setup : TwoSpeakerInterferenceSetup) (displacement : LengthQuantity) : Prop :=
  0 < metersValue displacement ∧
    setup.destructiveInterferenceAt displacement ∧
    ∀ earlier : LengthQuantity,
      0 < metersValue earlier →
        metersValue earlier < metersValue displacement →
          ¬ setup.destructiveInterferenceAt earlier

/-- Labels of the four distances displayed as answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre readout printed beside an answer label. -/
def displayedDistanceMeters : AnswerChoice → ℝ
  | .A => 237 / 1000
  | .B => 336 / 1000
  | .C => 569 / 1000
  | .D => 414 / 1000

/-!
An exact physical distance matches a value printed to the nearest millimetre
when the two metre readouts differ by at most half a millimetre.
-/
def MatchesAnswerToNearestMillimeter
    (exactMeters : ℝ) (choice : AnswerChoice) : Prop :=
  |exactMeters - displayedDistanceMeters choice| ≤ (1 / 2000 : ℝ)

/-- SI construction really has the requested metre readout. -/
lemma metersValue_lengthInMeters (value : ℝ) :
    metersValue (lengthInMeters value) = value := by
  simp [metersValue, lengthInMeters, CarriesDimension.toDimensionful_apply_apply]

/-!
In the depicted one-dimensional geometry, moving `A` away by `d` adds `d`
to its listener path while the path from `B` remains fixed.  Thus the path
difference is exactly the displayed separation `d`.
-/
lemma pathDifferenceMeters_eq_displacement
    (setup : TwoSpeakerInterferenceSetup)
    (displacement : LengthQuantity)
    (h_displacement : 0 ≤ metersValue displacement)
    (h_geometry : HasDepictedCollinearGeometry setup) :
    pathDifferenceMeters setup displacement = metersValue displacement := by
  rcases h_geometry displacement h_displacement with
    ⟨h_listener, h_B, h_A, _h_separation, h_paths⟩
  rw [pathDifferenceMeters, h_paths .A, h_paths .B]
  simp only [SpeakerLabel.figurePoint]
  rw [h_listener, h_A, h_B]
  simp only [sub_neg_eq_add, zero_add]
  by_cases h_initial_nonneg :
      0 ≤ metersValue setup.initialListenerDistance
  · rw [abs_of_nonneg (add_nonneg h_initial_nonneg h_displacement),
      abs_of_nonneg h_initial_nonneg]
    simpa using abs_of_nonneg h_displacement
  · have h_initial_neg :
        metersValue setup.initialListenerDistance < 0 :=
      lt_of_not_ge h_initial_nonneg
    /-
    This branch cannot be discharged from the frozen hypotheses.  They allow,
    for example, an initial readout `-1/4` and displacement `1/2`, for which
    the reduced left side is

      `||-1/4 + 1/2| - |-1/4|| = 0`

    while the right side is `1/2`.  The downstream physical theorem excludes
    this branch using `HasPhysicalParameters`.
    -/
    sorry

/-!
The calibrated speed and stated frequency determine the wavelength to be
`343 / 725 m` by the acoustic dispersion relation.
-/
lemma wavelength_meters_eq
    (setup : TwoSpeakerInterferenceSetup)
    (h_readouts : HasStatedReadouts setup)
    (h_air : UsesStandardAmbientAirSoundSpeed setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesAcousticInterferenceLaws setup) :
    metersValue setup.wavelength = (343 / 725 : ℝ) := by
  have h_frequency : hertzValue setup.oscillatorFrequency = 725 :=
    h_readouts.1
  have h_speed : metersPerSecondValue setup.soundSpeed = 343 :=
    h_air
  have h_wavelength_positive : 0 < metersValue setup.wavelength :=
    h_physical.2.2.1
  have h_dispersion := h_laws.dispersionRelation
  rw [h_speed, h_frequency] at h_dispersion
  norm_num at h_dispersion ⊢
  linarith

/-!
The order-zero odd half-wavelength is `343 / 1450 m`; the uniform
interference criterion and the positivity hypotheses make it the first
positive destructive displacement.
-/
lemma exact_first_destructive_displacement
    (setup : TwoSpeakerInterferenceSetup)
    (h_emission : DrivenInPhaseBySameOscillator setup)
    (h_geometry : HasDepictedCollinearGeometry setup)
    (h_readouts : HasStatedReadouts setup)
    (h_air : UsesStandardAmbientAirSoundSpeed setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesAcousticInterferenceLaws setup) :
    IsFirstDestructiveDisplacement setup (lengthInMeters (343 / 1450)) := by
  have h_initial_nonneg :
      0 ≤ metersValue setup.initialListenerDistance :=
    le_of_lt h_physical.2.1
  have h_path_difference
      (displacement : LengthQuantity)
      (h_displacement : 0 ≤ metersValue displacement) :
      pathDifferenceMeters setup displacement = metersValue displacement := by
    rcases h_geometry displacement h_displacement with
      ⟨h_listener, h_B, h_A, _h_separation, h_paths⟩
    rw [pathDifferenceMeters, h_paths .A, h_paths .B]
    simp only [SpeakerLabel.figurePoint]
    rw [h_listener, h_A, h_B]
    simp only [sub_neg_eq_add, zero_add]
    rw [abs_of_nonneg (add_nonneg h_initial_nonneg h_displacement),
      abs_of_nonneg h_initial_nonneg]
    simpa using abs_of_nonneg h_displacement
  have h_exact_value :
      metersValue (lengthInMeters (343 / 1450)) = (343 / 1450 : ℝ) :=
    metersValue_lengthInMeters _
  have h_exact_nonneg :
      0 ≤ metersValue (lengthInMeters (343 / 1450)) := by
    rw [h_exact_value]
    norm_num
  have h_wavelength := wavelength_meters_eq setup h_readouts h_air h_physical h_laws
  refine ⟨?_, ?_, ?_⟩
  · rw [h_exact_value]
    norm_num
  · apply (h_laws.destructiveInterferenceCriterion h_emission
      (lengthInMeters (343 / 1450)) h_exact_nonneg).2
    refine ⟨0, ?_⟩
    rw [h_path_difference _ h_exact_nonneg, h_exact_value, h_wavelength]
    norm_num
  · intro earlier h_earlier_positive h_earlier_lt h_earlier_destructive
    have h_earlier_nonneg : 0 ≤ metersValue earlier :=
      le_of_lt h_earlier_positive
    obtain ⟨order, h_order⟩ :=
      (h_laws.destructiveInterferenceCriterion h_emission earlier
        h_earlier_nonneg).1 h_earlier_destructive
    rw [h_path_difference earlier h_earlier_nonneg, h_wavelength] at h_order
    rw [h_exact_value] at h_earlier_lt
    have h_order_nonneg : (0 : ℝ) ≤ (order : ℝ) := by positivity
    norm_num at h_order h_earlier_lt
    nlinarith

/-!
The first destructive-interference distance is exactly

`343 / (2 * 725) m = 343 / 1450 m ≈ 0.23655 m`.

It therefore rounds to `0.237 m`, displayed choice A, and none of the other
displayed choices is within the nearest-millimetre tolerance.

This formalizes blueprint label `thm:physics:phyx_mini_0169:target`.  The
first-minimum assertion and the identification of choice A occur only in the
conclusion; no premise or governing-law field contains either target fact.
-/
theorem problem_phyx_mini_0169
    (setup : TwoSpeakerInterferenceSetup)
    (h_emission : DrivenInPhaseBySameOscillator setup)
    (h_geometry : HasDepictedCollinearGeometry setup)
    (h_readouts : HasStatedReadouts setup)
    (h_air : UsesStandardAmbientAirSoundSpeed setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesAcousticInterferenceLaws setup) :
    IsFirstDestructiveDisplacement setup (lengthInMeters (343 / 1450)) ∧
      MatchesAnswerToNearestMillimeter (343 / 1450) .A ∧
      ∀ choice : AnswerChoice,
        MatchesAnswerToNearestMillimeter (343 / 1450) choice → choice = .A := by
  refine ⟨exact_first_destructive_displacement setup h_emission h_geometry
    h_readouts h_air h_physical h_laws, ?_, ?_⟩
  · norm_num [MatchesAnswerToNearestMillimeter, displayedDistanceMeters, abs_of_nonpos]
  · intro choice h_choice
    cases choice with
    | A => rfl
    | B =>
        norm_num [MatchesAnswerToNearestMillimeter, displayedDistanceMeters,
          abs_of_nonpos, abs_of_nonneg] at h_choice
    | C =>
        norm_num [MatchesAnswerToNearestMillimeter, displayedDistanceMeters,
          abs_of_nonpos, abs_of_nonneg] at h_choice
    | D =>
        norm_num [MatchesAnswerToNearestMillimeter, displayedDistanceMeters,
          abs_of_nonpos, abs_of_nonneg] at h_choice

end PhyXMiniProblems.ProblemPhyXMini0169
