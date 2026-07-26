import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Destructive-interference cutoff for two coherent loudspeakers

The primary figure places identical loudspeakers at `A` and `B`, with `A`
two metres vertically above `B`.  A microphone moves from `B` along the
horizontal ray `BC`, perpendicular to `AB`.  The two speakers are driven by
the same amplifier and therefore emit coherently.

Lengths, frequencies, and the speed of sound are Physlib dimensionful
quantities.  Coordinates in `EuclideanSpace ℝ (Fin 2)` are explicitly metre
readouts.  The physical cutoff is characterized by interference behavior on
the open ray beyond `B`; it is not stored as a field or assumed by any law.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0173

open Dimension

/-- A signed physical length represented coherently in every unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Read a physical length in metres. -/
def metersValue (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical frequency in hertz. -/
def hertzValue (frequency : FrequencyQuantity) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read a Physlib speed in metres per second. -/
def metersPerSecondValue (speed : DimSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-- The three point labels printed in the primary figure. -/
inductive FigurePoint where
  | A
  | B
  | C
  deriving DecidableEq, Repr

/-- The two loudspeakers displayed at `A` and `B`. -/
inductive SpeakerLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The figure point occupied by each loudspeaker. -/
def SpeakerLabel.figurePoint : SpeakerLabel → FigurePoint
  | .A => .A
  | .B => .B

/-- Amplifier identities used to state that both speakers share one drive. -/
inductive AmplifierLabel where
  | common
  | auxiliary
  deriving DecidableEq, Repr

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The frequency readout, in hertz, printed beside each answer label. -/
def answerFrequencyHertz : AnswerChoice → ℝ
  | .A => 86
  | .B => 38
  | .C => 448 / 5
  | .D => 77 / 2

/-- The answer label recorded by the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
The complete apparatus and the quantities needed by the two-source model.
`frequencyResponse` is a dimensionless response readout and lets the premise
state that the two physical loudspeakers are identical without identifying a
loudspeaker with a scalar.  The microphone observable depends on both the
chosen frequency and its positive displacement from `B`.
-/
structure TwoSpeakerInterferenceSetup where
  speakerFrequency : SpeakerLabel → FrequencyQuantity
  speakerEmissionPhase : SpeakerLabel → Real.Angle
  frequencyResponse : SpeakerLabel → FrequencyQuantity → ℝ
  drivingAmplifier : SpeakerLabel → AmplifierLabel
  referenceFrequency : FrequencyQuantity
  speedOfSound : DimSpeed
  speakerSeparation : LengthQuantity
  figurePosition : FigurePoint → EuclideanSpace ℝ (Fin 2)
  microphonePositionAt : LengthQuantity → EuclideanSpace ℝ (Fin 2)
  rayPathLength : SpeakerLabel → LengthQuantity → LengthQuantity
  wavelengthAt : FrequencyQuantity → LengthQuantity
  displayedFrequency : AnswerChoice → FrequencyQuantity
  destructiveInterferenceAt : FrequencyQuantity → LengthQuantity → Prop

/--
The speakers have the same frequency response, share an amplifier, and emit
at the stated common frequency with equal phase.
-/
def CoherentlyDrivenIdenticalSpeakers
    (setup : TwoSpeakerInterferenceSetup) : Prop :=
  (∀ frequency,
      setup.frequencyResponse .A frequency =
        setup.frequencyResponse .B frequency) ∧
    setup.drivingAmplifier .A = setup.drivingAmplifier .B ∧
    setup.speakerFrequency .A = setup.referenceFrequency ∧
    setup.speakerFrequency .B = setup.referenceFrequency ∧
    setup.speakerEmissionPhase .A = setup.speakerEmissionPhase .B

/-!
The coordinate chart is measured in metres.  The clauses put `B` at the
origin, `A` on the positive vertical axis, and `C` on the positive horizontal
axis.  Hence ray `BC` is perpendicular to segment `AB`.  A nonnegative
physical displacement `x` places the microphone at coordinate `(x, 0)`.
-/
def HasDepictedGeometry (setup : TwoSpeakerInterferenceSetup) : Prop :=
  setup.figurePosition .B 0 = 0 ∧
    setup.figurePosition .B 1 = 0 ∧
    setup.figurePosition .A 0 = 0 ∧
    setup.figurePosition .A 1 = metersValue setup.speakerSeparation ∧
    setup.figurePosition .C 1 = 0 ∧
    0 < setup.figurePosition .C 0 ∧
    dist (setup.figurePosition .A) (setup.figurePosition .B) =
      metersValue setup.speakerSeparation ∧
    ∀ displacement : LengthQuantity,
      0 ≤ metersValue displacement →
        setup.microphonePositionAt displacement 0 =
            metersValue displacement ∧
          setup.microphonePositionAt displacement 1 = 0

/-!
The numerical text and answer-table readouts: separation `2.00 m`, reference
frequency `784 Hz`, speed of sound `344 m/s`, and the four displayed choices.
No cutoff or interference outcome occurs in this predicate.
-/
def HasStatedReadouts (setup : TwoSpeakerInterferenceSetup) : Prop :=
  metersValue setup.speakerSeparation = 2 ∧
    hertzValue setup.referenceFrequency = 784 ∧
    metersPerSecondValue setup.speedOfSound = 344 ∧
    ∀ choice : AnswerChoice,
      hertzValue (setup.displayedFrequency choice) =
        answerFrequencyHertz choice

/-- Positivity and nonnegativity conditions selecting the physical branch. -/
def HasPhysicalParameters (setup : TwoSpeakerInterferenceSetup) : Prop :=
  0 < metersValue setup.speakerSeparation ∧
    0 < hertzValue setup.referenceFrequency ∧
    0 < metersPerSecondValue setup.speedOfSound ∧
    (∀ choice : AnswerChoice,
      0 < hertzValue (setup.displayedFrequency choice)) ∧
    (∀ frequency : FrequencyQuantity,
      0 < hertzValue frequency →
        0 < metersValue (setup.wavelengthAt frequency)) ∧
    ∀ (speaker : SpeakerLabel) (displacement : LengthQuantity),
      0 ≤ metersValue displacement →
        0 ≤ metersValue (setup.rayPathLength speaker displacement)

/-- The magnitude of the two source-to-microphone path difference in metres. -/
def pathDifferenceMeters
    (setup : TwoSpeakerInterferenceSetup)
    (displacement : LengthQuantity) : ℝ :=
  |metersValue (setup.rayPathLength .A displacement) -
    metersValue (setup.rayPathLength .B displacement)|

/-!
The governing acoustic laws, uniformly stated for every positive frequency
and microphone displacement:

* `c = f λ` in SI readouts;
* each ray length is the Euclidean source-to-microphone distance;
* equal-phase sources cancel exactly at odd half-wavelength path differences.

These laws do not identify any answer choice as a cutoff.
-/
structure SatisfiesTwoSourceAcousticLaws
    (setup : TwoSpeakerInterferenceSetup) : Prop where
  dispersion_relation :
    ∀ frequency : FrequencyQuantity,
      0 < hertzValue frequency →
        metersPerSecondValue setup.speedOfSound =
          hertzValue frequency *
            metersValue (setup.wavelengthAt frequency)
  geometric_ray_path :
    ∀ (speaker : SpeakerLabel) (displacement : LengthQuantity),
      0 ≤ metersValue displacement →
        metersValue (setup.rayPathLength speaker displacement) =
          dist (setup.figurePosition speaker.figurePoint)
            (setup.microphonePositionAt displacement)
  destructive_interference_law :
    CoherentlyDrivenIdenticalSpeakers setup →
      ∀ (frequency : FrequencyQuantity) (displacement : LengthQuantity),
        0 < hertzValue frequency →
          0 < metersValue displacement →
            (setup.destructiveInterferenceAt frequency displacement ↔
              ∃ order : ℕ,
                2 * pathDifferenceMeters setup displacement =
                  (2 * (order : ℝ) + 1) *
                    metersValue (setup.wavelengthAt frequency))

/-- There is no destructive-interference point on the open ray beyond `B`. -/
def HasNoDestructivePositionOnBC
    (setup : TwoSpeakerInterferenceSetup)
    (frequency : FrequencyQuantity) : Prop :=
  ∀ displacement : LengthQuantity,
    0 < metersValue displacement →
      ¬ setup.destructiveInterferenceAt frequency displacement

/-!
`cutoff` is the exact upper frequency having no destructive point: every
positive frequency at or below it is safe, while every larger frequency has
at least one destructive position on the open ray.  Excluding displacement
zero reflects the wording that the microphone is moved *out from* `B` and
makes the boundary frequency itself part of the no-interference regime.
-/
def IsNoDestructiveInterferenceCutoff
    (setup : TwoSpeakerInterferenceSetup)
    (cutoff : FrequencyQuantity) : Prop :=
  0 < hertzValue cutoff ∧
    (∀ frequency : FrequencyQuantity,
      0 < hertzValue frequency →
        hertzValue frequency ≤ hertzValue cutoff →
          HasNoDestructivePositionOnBC setup frequency) ∧
    ∀ frequency : FrequencyQuantity,
      hertzValue cutoff < hertzValue frequency →
        ∃ displacement : LengthQuantity,
          0 < metersValue displacement ∧
            setup.destructiveInterferenceAt frequency displacement

/-- The dispersion relation determines the wavelength at any positive frequency. -/
lemma wavelength_meters_eq_speed_div_frequency
    (setup : TwoSpeakerInterferenceSetup)
    (frequency : FrequencyQuantity)
    (h_frequency : 0 < hertzValue frequency)
    (h_laws : SatisfiesTwoSourceAcousticLaws setup) :
    metersValue (setup.wavelengthAt frequency) =
      metersPerSecondValue setup.speedOfSound / hertzValue frequency := by
  rw [h_laws.dispersion_relation frequency h_frequency]
  field_simp

/-!
At a microphone displacement `x`, the upper path is
`sqrt(separation² + x²)` and the lower path is `x`.
-/
lemma pathDifferenceMeters_eq
    (setup : TwoSpeakerInterferenceSetup)
    (displacement : LengthQuantity)
    (h_displacement : 0 ≤ metersValue displacement)
    (h_geometry : HasDepictedGeometry setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesTwoSourceAcousticLaws setup) :
    pathDifferenceMeters setup displacement =
      Real.sqrt
          (metersValue setup.speakerSeparation ^ 2 +
            metersValue displacement ^ 2) -
        metersValue displacement := by
  unfold pathDifferenceMeters
  rw [h_laws.geometric_ray_path .A displacement h_displacement,
    h_laws.geometric_ray_path .B displacement h_displacement]
  rcases h_geometry with
    ⟨hB0, hB1, hA0, hA1, _, _, _, h_microphone⟩
  obtain ⟨hM0, hM1⟩ := h_microphone displacement h_displacement
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, SpeakerLabel.figurePoint]
  rw [hA0, hA1, hB0, hB1, hM0, hM1]
  have hsqrt :
      metersValue displacement ≤
        Real.sqrt
          (metersValue displacement ^ 2 +
            metersValue setup.speakerSeparation ^ 2) := by
    nlinarith [
      Real.sq_sqrt
        (by positivity :
          0 ≤ metersValue displacement ^ 2 +
            metersValue setup.speakerSeparation ^ 2),
      Real.sqrt_nonneg
        (metersValue displacement ^ 2 +
          metersValue setup.speakerSeparation ^ 2)]
  simp [Real.dist_eq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg h_displacement, abs_of_nonneg h_physical.1.le,
    abs_of_nonneg (sub_nonneg.mpr hsqrt), add_comm]

/-!
The general geometric boundary `c / (2 d)` evaluates to `86 Hz` for the
stated sound speed and speaker separation.  This is derived from data and is
not a premise field.
-/
lemma geometric_cutoff_hertz_eq_answerA
    (setup : TwoSpeakerInterferenceSetup)
    (h_readouts : HasStatedReadouts setup) :
    metersPerSecondValue setup.speedOfSound /
        (2 * metersValue setup.speakerSeparation) =
      answerFrequencyHertz .A := by
  rcases h_readouts with ⟨h_separation, _, h_speed, _⟩
  rw [h_speed, h_separation]
  norm_num [answerFrequencyHertz]

/-!
Choice A (`86 Hz`) is the exact upper frequency for which there are no
destructive-interference positions after the microphone leaves `B`.

This formalizes blueprint label `thm:physics:phyx_mini_0173:target`.
The cutoff assertion appears only in this conclusion, never in the setup,
readout, geometry, or governing-law premises.
-/
theorem problem_phyx_mini_0173
    (setup : TwoSpeakerInterferenceSetup)
    (h_sources : CoherentlyDrivenIdenticalSpeakers setup)
    (h_geometry : HasDepictedGeometry setup)
    (h_readouts : HasStatedReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesTwoSourceAcousticLaws setup) :
    IsNoDestructiveInterferenceCutoff setup
      (setup.displayedFrequency recordedDatasetAnswer) := by
  have h_separation : metersValue setup.speakerSeparation = 2 :=
    h_readouts.1
  have h_speed : metersPerSecondValue setup.speedOfSound = 344 :=
    h_readouts.2.2.1
  have h_cutoff :
      hertzValue (setup.displayedFrequency recordedDatasetAnswer) = 86 := by
    simpa [recordedDatasetAnswer, answerFrequencyHertz] using
      h_readouts.2.2.2 AnswerChoice.A
  refine ⟨?_, ?_, ?_⟩
  · rw [h_cutoff]
    norm_num
  · intro frequency h_frequency h_frequency_le displacement
      h_displacement h_destructive
    have h_path := pathDifferenceMeters_eq setup displacement
      h_displacement.le h_geometry h_physical h_laws
    rw [h_separation] at h_path
    have h_sqrt_sq :
        (Real.sqrt ((2 : ℝ) ^ 2 + metersValue displacement ^ 2)) ^ 2 =
          (2 : ℝ) ^ 2 + metersValue displacement ^ 2 :=
      Real.sq_sqrt (by positivity)
    have h_sqrt_nonneg :=
      Real.sqrt_nonneg ((2 : ℝ) ^ 2 + metersValue displacement ^ 2)
    have h_path_lt : pathDifferenceMeters setup displacement < 2 := by
      nlinarith
    have h_frequency_le_86 : hertzValue frequency ≤ 86 := by
      rw [h_cutoff] at h_frequency_le
      exact h_frequency_le
    have h_wavelength_positive :
        0 < metersValue (setup.wavelengthAt frequency) :=
      h_physical.2.2.2.2.1 frequency h_frequency
    have h_dispersion :=
      h_laws.dispersion_relation frequency h_frequency
    rw [h_speed] at h_dispersion
    have h_product_nonnegative :
        0 ≤ (86 - hertzValue frequency) *
          metersValue (setup.wavelengthAt frequency) :=
      mul_nonneg (sub_nonneg.mpr h_frequency_le_86)
        h_wavelength_positive.le
    have h_wavelength_ge_four :
        4 ≤ metersValue (setup.wavelengthAt frequency) := by
      nlinarith
    obtain ⟨order, h_order⟩ :=
      (h_laws.destructive_interference_law h_sources frequency displacement
        h_frequency h_displacement).1 h_destructive
    have h_extra_nonnegative :
        0 ≤ 2 * (order : ℝ) *
          metersValue (setup.wavelengthAt frequency) :=
      mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg order))
        h_wavelength_positive.le
    nlinarith
  · intro frequency h_above_cutoff
    have h_above_86 : 86 < hertzValue frequency := by
      rw [h_cutoff] at h_above_cutoff
      exact h_above_cutoff
    have h_frequency : 0 < hertzValue frequency := by
      linarith
    have h_wavelength_positive :
        0 < metersValue (setup.wavelengthAt frequency) :=
      h_physical.2.2.2.2.1 frequency h_frequency
    have h_dispersion :=
      h_laws.dispersion_relation frequency h_frequency
    rw [h_speed] at h_dispersion
    have h_product_positive :
        0 < (hertzValue frequency - 86) *
          metersValue (setup.wavelengthAt frequency) :=
      mul_pos (sub_pos.mpr h_above_86) h_wavelength_positive
    have h_wavelength_lt_four :
        metersValue (setup.wavelengthAt frequency) < 4 := by
      nlinarith
    let y := metersValue (setup.wavelengthAt frequency) / 2
    have hy : 0 < y := by
      dsimp [y]
      positivity
    have hy_lt_two : y < 2 := by
      dsimp [y]
      linarith
    let x := ((2 : ℝ) ^ 2 - y ^ 2) / (2 * y)
    have h_numerator : 0 < (2 : ℝ) ^ 2 - y ^ 2 := by
      nlinarith
    have hx : 0 < x := by
      dsimp [x]
      exact div_pos h_numerator (mul_pos (by norm_num) hy)
    let displacement : LengthQuantity :=
      CarriesDimension.toDimensionful UnitChoices.SI
        (⟨x⟩ : WithDim L𝓭 ℝ)
    have h_displacement_value : metersValue displacement = x := by
      simp [displacement, metersValue,
        CarriesDimension.toDimensionful_apply_apply]
    have h_two_xy : 2 * x * y = (2 : ℝ) ^ 2 - y ^ 2 := by
      dsimp [x]
      field_simp [hy.ne']
    have h_sum_sq : (x + y) ^ 2 = (2 : ℝ) ^ 2 + x ^ 2 := by
      nlinarith
    have h_sqrt :
        Real.sqrt ((2 : ℝ) ^ 2 + x ^ 2) = x + y := by
      calc
        Real.sqrt ((2 : ℝ) ^ 2 + x ^ 2) =
            Real.sqrt ((x + y) ^ 2) := by rw [h_sum_sq]
        _ = |x + y| := Real.sqrt_sq_eq_abs (x + y)
        _ = x + y := abs_of_pos (add_pos hx hy)
    have h_displacement_nonnegative :
        0 ≤ metersValue displacement := by
      rw [h_displacement_value]
      exact hx.le
    have h_path := pathDifferenceMeters_eq setup displacement
      h_displacement_nonnegative h_geometry h_physical h_laws
    rw [h_separation, h_displacement_value, h_sqrt] at h_path
    have h_path_eq : pathDifferenceMeters setup displacement = y := by
      nlinarith
    refine ⟨displacement, ?_, ?_⟩
    · rw [h_displacement_value]
      exact hx
    · apply
        (h_laws.destructive_interference_law h_sources frequency displacement
          h_frequency (by simpa [h_displacement_value] using hx)).2
      refine ⟨0, ?_⟩
      rw [h_path_eq]
      dsimp [y]
      ring

end PhyXMiniProblems.ProblemPhyXMini0173
