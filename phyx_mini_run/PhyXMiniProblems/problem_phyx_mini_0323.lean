import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

/-!
# Reflected sound arriving in phase with direct sound

This file models problem `phyx_mini_0323`.  An isotropic point source `S` and
detector `D` are separated by `L = 10.0 m`.  Ray 1 goes directly from `S` to
`D`; ray 2 reflects from a flat surface at the point on the perpendicular
bisector of `SD` whose distance from the line `SD` is `d`.  The wavelength is
`0.850 m`, and reflection contributes a phase shift of one half-cycle.

Lengths are genuine unit-independent Physlib quantities.  Real numbers occur
only as explicitly named metre readouts, dimensionless phase-cycle counts, or
displayed numerical answers.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0323

open Dimension

/-! ## Dimensionful acoustic lengths and metre readouts -/

/-- A signed, unit-independent physical quantity carrying length dimension. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The coherent-SI metre readout of an acoustic length. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Construct a physical length from a prescribed metre readout. -/
def lengthOfMeters (value : ℝ) : AcousticLength :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-! ## Physical roles and primary-figure labels -/

/-- The three geometrically distinguished points in the primary figure. -/
inductive FigurePoint where
  | sourceS
  | reflectionPoint
  | detectorD
  deriving DecidableEq, Repr

/-- The two red acoustic-ray labels printed in the primary figure. -/
inductive SoundRay where
  | directRay1
  | reflectedRay2
  deriving DecidableEq, Repr

/-- Physical kind of source specified in the scenario. -/
inductive SoundSourceKind where
  | isotropicPointSource
  deriving DecidableEq, Repr

/-- Physical kind of receiving object specified in the scenario. -/
inductive ReceiverKind where
  | soundDetector
  deriving DecidableEq, Repr

/-- Physical kind of boundary at which ray 2 bounces. -/
inductive ReflectorKind where
  | flatSurface
  deriving DecidableEq, Repr

/-- Qualitative labels and relations visible in the primary figure. -/
inductive FigureFeature where
  | directHorizontalSegmentSD
  | flatReflectingSurface
  | perpendicularBisectorOfSD
  | rightAngleMarker
  | leftHalfLabelLOverTwo
  | rightHalfLabelLOverTwo
  | offsetLabelD
  deriving DecidableEq, Repr

/-- Ordered route through the labelled points followed by each sound ray. -/
def rayRoute : SoundRay → List FigurePoint
  | .directRay1 => [.sourceS, .detectorD]
  | .reflectedRay2 => [.sourceS, .reflectionPoint, .detectorD]

/-!
The independent physical data and observable behavior of the interference
experiment.  The argument of `rayPathLengthInMetersAtOffset` is a physical
candidate offset `d`.  `arriveExactlyInPhaseAtOffset` remains an abstract
acoustic observation here and is related to path and reflection phase by the
governing-law structure below.

No field assigns the requested least positive value of `d`.
-/
structure ReflectedSoundInterferenceSetup where
  sourceKind : SoundSourceKind
  receiverKind : ReceiverKind
  reflectorKind : ReflectorKind
  figureShows : FigureFeature → Prop
  /-- Wavelength `lambda` of the monochromatic sound. -/
  wavelength : AcousticLength
  /-- Direct source-to-detector separation `L`. -/
  sourceDetectorDistanceL : AcousticLength
  /-- Reflection phase shift measured as a dimensionless fraction of a cycle. -/
  reflectionPhaseShiftInCycles : ℝ
  /-- Path length of either labelled ray at a proposed reflector offset. -/
  rayPathLengthInMetersAtOffset : SoundRay → AcousticLength → ℝ
  /-- Physical observation that the two arrivals have equal phase. -/
  arriveExactlyInPhaseAtOffset : AcousticLength → Prop

/-!
Scenario and primary-image data.  The wavelength is `0.850 m = 17/20 m`, the
source-detector distance is `10.0 m`, and reflection shifts the wave by
`0.500 lambda`, equivalently one half-cycle.  This predicate does not select
any value of the unknown offset `d`.
-/
structure MatchesProblemAndFigureData
    (setup : ReflectedSoundInterferenceSetup) : Prop where
  source_is_isotropic_point_source :
    setup.sourceKind = .isotropicPointSource
  receiver_is_sound_detector : setup.receiverKind = .soundDetector
  reflector_is_flat_surface : setup.reflectorKind = .flatSurface
  shows_direct_horizontal_segment :
    setup.figureShows .directHorizontalSegmentSD
  shows_flat_reflecting_surface : setup.figureShows .flatReflectingSurface
  shows_perpendicular_bisector : setup.figureShows .perpendicularBisectorOfSD
  shows_right_angle : setup.figureShows .rightAngleMarker
  shows_left_half_L_over_two : setup.figureShows .leftHalfLabelLOverTwo
  shows_right_half_L_over_two : setup.figureShows .rightHalfLabelLOverTwo
  shows_offset_d : setup.figureShows .offsetLabelD
  wavelength_readout : lengthInMeters setup.wavelength = 17 / 20
  source_detector_distance_readout :
    lengthInMeters setup.sourceDetectorDistanceL = 10
  half_cycle_reflection_shift : setup.reflectionPhaseShiftInCycles = 1 / 2

/-- Positivity assumptions for the independently supplied physical lengths. -/
structure HasPhysicalParameters
    (setup : ReflectedSoundInterferenceSetup) : Prop where
  wavelength_positive : 0 < lengthInMeters setup.wavelength
  source_detector_distance_positive :
    0 < lengthInMeters setup.sourceDetectorDistanceL

/-! ## Governing geometry and acoustic phase laws -/

/-!
The two path-length laws read from the symmetric figure.  Ray 1 has length
`L`.  Ray 2 consists of two congruent right-triangle hypotenuses with legs
`L/2` and `d`, giving `2 * sqrt ((L/2)^2 + d^2)`.

These equations apply to every nonnegative proposed offset and do not state
which offset yields the first in-phase arrival.
-/
structure SatisfiesDepictedRayGeometry
    (setup : ReflectedSoundInterferenceSetup) : Prop where
  direct_ray_path_length :
    ∀ offset : AcousticLength,
      0 ≤ lengthInMeters offset →
      setup.rayPathLengthInMetersAtOffset .directRay1 offset =
        lengthInMeters setup.sourceDetectorDistanceL
  reflected_ray_path_length :
    ∀ offset : AcousticLength,
      0 ≤ lengthInMeters offset →
      setup.rayPathLengthInMetersAtOffset .reflectedRay2 offset =
        2 * Real.sqrt
          ((lengthInMeters setup.sourceDetectorDistanceL / 2) ^ 2 +
            (lengthInMeters offset) ^ 2)

/-!
For monochromatic propagation, path excess divided by wavelength is a phase
difference measured in cycles.  Reflection adds its half-cycle shift.  The
arrivals are exactly in phase precisely when the total cycle difference is an
integer.  This is a general governing law for every nonnegative offset, not a
premise asserting the requested answer.
-/
structure SatisfiesPropagationAndReflectionPhaseLaw
    (setup : ReflectedSoundInterferenceSetup) : Prop where
  in_phase_iff_integer_total_cycle_difference :
    ∀ offset : AcousticLength,
      0 ≤ lengthInMeters offset →
      setup.arriveExactlyInPhaseAtOffset offset ↔
        ∃ order : ℤ,
          (setup.rayPathLengthInMetersAtOffset .reflectedRay2 offset -
                setup.rayPathLengthInMetersAtOffset .directRay1 offset) /
                lengthInMeters setup.wavelength +
              setup.reflectionPhaseShiftInCycles =
            (order : ℝ)

/-! ## Least-positive condition and displayed answer -/

/-!
An offset answers the question when it is strictly positive, produces exactly
in-phase arrivals, and is no larger than any other strictly positive offset
with that property.  The explicit minimality clause formalizes "least value
other than zero".
-/
def IsLeastPositiveInPhaseOffset
    (setup : ReflectedSoundInterferenceSetup)
    (offset : AcousticLength) : Prop :=
  0 < lengthInMeters offset ∧
    setup.arriveExactlyInPhaseAtOffset offset ∧
    ∀ other : AcousticLength,
      0 < lengthInMeters other →
      setup.arriveExactlyInPhaseAtOffset other →
      lengthInMeters offset ≤ lengthInMeters other

/-!
Solving the first constructive condition, whose path excess is `lambda/2`,
gives the exact metre expression

`d = sqrt (lambda * (4 * L + lambda)) / 4`.

This definition only names the candidate expression; proving that it is the
least positive in-phase offset remains the substantive conclusion below.
-/
def exactLeastOffsetInMeters
    (setup : ReflectedSoundInterferenceSetup) : ℝ :=
  Real.sqrt
      (lengthInMeters setup.wavelength *
        (4 * lengthInMeters setup.sourceDetectorDistanceL +
          lengthInMeters setup.wavelength)) /
    4

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre value printed beside each answer label. -/
def displayedOffsetInMeters : AnswerChoice → ℝ
  | .A => 59 / 50
  | .B => 123 / 100
  | .C => 27 / 20
  | .D => 147 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Round a metre readout to the nearest hundredth of a metre. -/
def roundedToNearestHundredth (value : ℝ) : ℝ :=
  (round (100 * value) : ℝ) / 100

/-- A choice matches the least positive offset at the displayed precision. -/
def MatchesDisplayedAnswer
    (setup : ReflectedSoundInterferenceSetup)
    (choice : AnswerChoice) : Prop :=
  roundedToNearestHundredth (exactLeastOffsetInMeters setup) =
    displayedOffsetInMeters choice

/-- The selected label is the unique displayed choice matching the result. -/
def IsUniqueMatchingDisplayedAnswer
    (setup : ReflectedSoundInterferenceSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedAnswer setup choice ∧
    ∀ other : AnswerChoice, MatchesDisplayedAnswer setup other → other = choice

/-!
The ray geometry and phase law imply that the exact square-root expression is
the least positive offset for which the two arrivals are in phase.
-/
lemma exact_offset_is_least_positive_in_phase
    (setup : ReflectedSoundInterferenceSetup)
    (h_data : MatchesProblemAndFigureData setup)
    (h_physical : HasPhysicalParameters setup)
    (h_geometry : SatisfiesDepictedRayGeometry setup)
    (h_phase : SatisfiesPropagationAndReflectionPhaseLaw setup) :
    IsLeastPositiveInPhaseOffset setup
      (lengthOfMeters (exactLeastOffsetInMeters setup)) := by
  have h_readout (x : ℝ) : lengthInMeters (lengthOfMeters x) = x := by
    change
      ((UnitChoices.SI.dimScale UnitChoices.SI L𝓭) •
          (⟨x⟩ : WithDim L𝓭 ℝ)).val = x
    simp
  have hd0 : 0 < exactLeastOffsetInMeters setup := by
    rw [exactLeastOffsetInMeters, h_data.wavelength_readout,
      h_data.source_detector_distance_readout]
    positivity
  have hd0_sq :
      (exactLeastOffsetInMeters setup) ^ 2 = (13889 : ℝ) / 6400 := by
    rw [exactLeastOffsetInMeters, h_data.wavelength_readout,
      h_data.source_detector_distance_readout]
    have hs := Real.sq_sqrt
      (show 0 ≤ (17 / 20 : ℝ) * (4 * 10 + 17 / 20) by norm_num)
    nlinarith
  have hd0_nonneg :
      0 ≤ lengthInMeters
        (lengthOfMeters (exactLeastOffsetInMeters setup)) := by
    rw [h_readout]
    exact hd0.le
  unfold IsLeastPositiveInPhaseOffset
  rw [h_readout]
  refine ⟨hd0, ?_, ?_⟩
  · refine
      ((h_phase.in_phase_iff_integer_total_cycle_difference _).mpr ?_)
        hd0_nonneg
    refine ⟨1, ?_⟩
    rw [h_geometry.direct_ray_path_length _ hd0_nonneg,
      h_geometry.reflected_ray_path_length _ hd0_nonneg, h_readout,
      h_data.wavelength_readout, h_data.source_detector_distance_readout,
      h_data.half_cycle_reflection_shift, hd0_sq]
    have hsqrt :
        Real.sqrt ((10 / 2 : ℝ) ^ 2 + 13889 / 6400) = 417 / 80 := by
      rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by norm_num)]
      norm_num
    rw [hsqrt]
    norm_num
  · intro other hother hother_phase
    have hother_nonneg : 0 ≤ lengthInMeters other := hother.le
    obtain ⟨order, horder⟩ :=
      (h_phase.in_phase_iff_integer_total_cycle_difference other).mp
        (fun _ => hother_phase)
    rw [h_geometry.direct_ray_path_length other hother_nonneg,
      h_geometry.reflected_ray_path_length other hother_nonneg,
      h_data.wavelength_readout, h_data.source_detector_distance_readout,
      h_data.half_cycle_reflection_shift] at horder
    norm_num at horder
    have hs_sq :
        (Real.sqrt (25 + (lengthInMeters other) ^ 2)) ^ 2 =
          25 + (lengthInMeters other) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have hs_nonneg :
        0 ≤ Real.sqrt (25 + (lengthInMeters other) ^ 2) :=
      Real.sqrt_nonneg _
    have hx_sq_pos : 0 < (lengthInMeters other) ^ 2 :=
      sq_pos_of_pos hother
    have hs_gt :
        5 < Real.sqrt (25 + (lengthInMeters other) ^ 2) := by
      nlinarith
    have horder_pos_real : (0 : ℝ) < (order : ℝ) := by
      nlinarith
    have horder_pos : (0 : ℤ) < order :=
      Int.cast_pos.mp horder_pos_real
    have horder_ge : (1 : ℤ) ≤ order := by
      omega
    have horder_ge_real : (1 : ℝ) ≤ (order : ℝ) := by
      exact_mod_cast horder_ge
    have hs_ge :
        (417 / 80 : ℝ) ≤
          Real.sqrt (25 + (lengthInMeters other) ^ 2) := by
      nlinarith
    have hsq_lower :
        (417 / 80 : ℝ) ^ 2 ≤
          (Real.sqrt (25 + (lengthInMeters other) ^ 2)) ^ 2 :=
      (sq_le_sq₀ (by norm_num) hs_nonneg).2 hs_ge
    have hother_sq :
        (13889 : ℝ) / 6400 ≤ (lengthInMeters other) ^ 2 := by
      nlinarith
    apply (sq_le_sq₀ hd0.le hother.le).mp
    rw [hd0_sq]
    exact hother_sq

/-!
With `lambda = 0.850 m` and `L = 10.0 m`, the least positive offset is

`sqrt (lambda * (4 L + lambda)) / 4`,

which rounds to `1.47 m`.  Thus displayed answer D is the unique matching
choice.

This formalizes blueprint label `thm:physics:phyx_mini_0323:target`.
-/
theorem problem_phyx_mini_0323
    (setup : ReflectedSoundInterferenceSetup)
    (h_data : MatchesProblemAndFigureData setup)
    (h_physical : HasPhysicalParameters setup)
    (h_geometry : SatisfiesDepictedRayGeometry setup)
    (h_phase : SatisfiesPropagationAndReflectionPhaseLaw setup) :
    IsLeastPositiveInPhaseOffset setup
        (lengthOfMeters (exactLeastOffsetInMeters setup)) ∧
      lengthInMeters (lengthOfMeters (exactLeastOffsetInMeters setup)) =
        exactLeastOffsetInMeters setup ∧
      roundedToNearestHundredth (exactLeastOffsetInMeters setup) = 147 / 100 ∧
      IsUniqueMatchingDisplayedAnswer setup recordedDatasetAnswer := by
  have h_readout (x : ℝ) : lengthInMeters (lengthOfMeters x) = x := by
    change
      ((UnitChoices.SI.dimScale UnitChoices.SI L𝓭) •
          (⟨x⟩ : WithDim L𝓭 ℝ)).val = x
    simp
  have hd0 : 0 < exactLeastOffsetInMeters setup := by
    rw [exactLeastOffsetInMeters, h_data.wavelength_readout,
      h_data.source_detector_distance_readout]
    positivity
  have hd0_sq :
      (exactLeastOffsetInMeters setup) ^ 2 = (13889 : ℝ) / 6400 := by
    rw [exactLeastOffsetInMeters, h_data.wavelength_readout,
      h_data.source_detector_distance_readout]
    have hs := Real.sq_sqrt
      (show 0 ≤ (17 / 20 : ℝ) * (4 * 10 + 17 / 20) by norm_num)
    nlinarith
  have hd0_lower :
      (293 / 200 : ℝ) < exactLeastOffsetInMeters setup := by
    apply (sq_lt_sq₀ (by norm_num) hd0.le).mp
    rw [hd0_sq]
    norm_num
  have hd0_upper :
      exactLeastOffsetInMeters setup < (59 / 40 : ℝ) := by
    apply (sq_lt_sq₀ hd0.le (by norm_num)).mp
    rw [hd0_sq]
    norm_num
  have hround :
      round (100 * exactLeastOffsetInMeters setup) = (147 : ℤ) := by
    rw [round_eq_iff]
    constructor <;> norm_num <;> nlinarith
  have hrounded :
      roundedToNearestHundredth (exactLeastOffsetInMeters setup) =
        (147 : ℝ) / 100 := by
    rw [roundedToNearestHundredth, hround]
    norm_num
  refine
    ⟨exact_offset_is_least_positive_in_phase setup h_data h_physical
        h_geometry h_phase,
      h_readout _, hrounded, ?_⟩
  constructor
  · simpa [MatchesDisplayedAnswer, recordedDatasetAnswer,
      displayedOffsetInMeters] using hrounded
  · intro other hmatch
    unfold MatchesDisplayedAnswer at hmatch
    rw [hrounded] at hmatch
    cases other with
    | A => norm_num [displayedOffsetInMeters] at hmatch
    | B => norm_num [displayedOffsetInMeters] at hmatch
    | C => norm_num [displayedOffsetInMeters] at hmatch
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0323
