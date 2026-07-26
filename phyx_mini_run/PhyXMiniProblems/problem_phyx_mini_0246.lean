import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0246

open Dimension

/-!
# Intensity at point B from two in-phase loudspeakers

Two equal-amplitude loudspeakers are separated by `6 m`. Point `B` is `10 m`
directly in front of the upper speaker, while point `A` is `10 m` in front of
the midpoint of the source plane. Both sources have wavelength `1 m` and zero
initial phase difference.

Lengths and acoustic intensities are represented as unit-independent Physlib
quantities. Real numbers are used only for readouts in named units, phase
angles in radians, dimensionless ratios, and the displayed answer coefficients.
-/

/-- A nonnegative physical length, independent of its readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length used for planar coordinates. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-!
Acoustic intensity has SI unit watt per square metre and physical dimension
`mass / time^3`.
-/
abbrev AcousticIntensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative physical length in a chosen length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a signed physical coordinate in a chosen length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- Read an acoustic intensity in a coherent system of units. -/
def acousticIntensityReadout
    (units : UnitChoices) (intensity : AcousticIntensityQuantity) : ℝ :=
  ((intensity units).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre readout of a signed planar coordinate. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters length

/-- SI watt-per-square-metre readout of an acoustic intensity. -/
def acousticIntensityInWattsPerSquareMeter
    (intensity : AcousticIntensityQuantity) : ℝ :=
  acousticIntensityReadout UnitChoices.SI intensity

/-- The two loudspeakers shown on the left of the supplied figure. -/
inductive SpeakerLabel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The four physical points distinguished in the planar model. -/
inductive FigurePoint where
  | upperSpeaker
  | lowerSpeaker
  | observerA
  | observerB
  deriving DecidableEq, Repr

/-- The ray labels printed on the source-to-`B` segments. -/
inductive RayLabel where
  | r₁
  | r₂
  deriving DecidableEq, Repr

/-- The physical role of a source in the scenario. -/
inductive AcousticSourceKind where
  | loudspeaker
  | other
  deriving DecidableEq, Repr

/-- A point in the source-observer plane with physical length coordinates. -/
structure PlanarPosition where
  forward : SignedLengthQuantity
  transverse : SignedLengthQuantity

/-!
Qualitative labels and placements read from the primary image. Metric readouts
are supplied by `MatchesSuppliedFigure`; no ray length, phase at `B`, or total
intensity is encoded in this structure.
-/
structure LoudspeakerInterferenceFigure where
  position : FigurePoint → PlanarPosition
  pointShown : FigurePoint → Bool
  rayToBShown : SpeakerLabel → Bool
  rayLabel : SpeakerLabel → RayLabel
  separationLabelShown : Bool
  forwardDistanceLabelShown : Bool
  wavelengthLabelShown : SpeakerLabel → Bool
  initialPhaseDifferenceLabelShown : Bool

/-!
The independent physical quantities and observables. `AcousticAmplitude` stays
abstract because the problem asserts equal amplitudes without giving a unit or
amplitude scale. The total intensity is an observable constrained only by the
general interference law below.
-/
structure TwoLoudspeakerSetup (AcousticAmplitude : Type) where
  sourceKind : SpeakerLabel → AcousticSourceKind
  commonWavelength : LengthQuantity
  sourceWavelength : SpeakerLabel → LengthQuantity
  sourceAmplitude : SpeakerLabel → AcousticAmplitude
  initialPhaseRadians : SpeakerLabel → ℝ
  speakerSeparation : LengthQuantity
  observerForwardDistance : LengthQuantity
  rayPathLengthToB : SpeakerLabel → LengthQuantity
  pathDifferenceAtB : LengthQuantity
  receivedPhaseDifferenceAtB : ℝ
  singleSourceIntensityAtB : SpeakerLabel → AcousticIntensityQuantity
  referenceIntensityI₀ : AcousticIntensityQuantity
  totalIntensityAtB : AcousticIntensityQuantity
  figure : LoudspeakerInterferenceFigure

/-!
Source data from the prose and the `Δφ₀ = 0 rad` label: both objects are
loudspeakers, have the common wavelength and equal amplitudes, start in phase,
and each acting alone contributes the physical intensity denoted by `I₀` at
`B`. This contains no combined-intensity conclusion.
-/
def MatchesSourceDescription {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop :=
  (∀ source, setup.sourceKind source = .loudspeaker) ∧
    (∀ source, setup.sourceWavelength source = setup.commonWavelength) ∧
    setup.sourceAmplitude .upper = setup.sourceAmplitude .lower ∧
    setup.initialPhaseRadians .lower - setup.initialPhaseRadians .upper = 0 ∧
    (∀ source, setup.singleSourceIntensityAtB source = setup.referenceIntensityI₀)

/-- The wavelength, separation, and forward-distance readouts in metres. -/
structure MatchesProblemReadouts {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop where
  wavelengthMeters : lengthInMeters setup.commonWavelength = 1
  separationMeters : lengthInMeters setup.speakerSeparation = 6
  forwardDistanceMeters : lengthInMeters setup.observerForwardDistance = 10

/-!
Primary-image geometry in metre coordinates. The source plane is `forward = 0`;
the speakers are at transverse coordinates `±3`; `A` is at `(10, 0)` and `B`
is at `(10, 3)`, directly in front of the upper source. The horizontal and
diagonal source-to-`B` rays are respectively labeled `r₁` and `r₂`.
-/
def MatchesSuppliedFigure {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop :=
  let xy (point : FigurePoint) : ℝ × ℝ :=
    (signedLengthInMeters (setup.figure.position point).forward,
      signedLengthInMeters (setup.figure.position point).transverse)
  (∀ point, setup.figure.pointShown point = true) ∧
    xy .upperSpeaker = (0, 3) ∧
    xy .lowerSpeaker = (0, -3) ∧
    xy .observerA = (10, 0) ∧
    xy .observerB = (10, 3) ∧
    setup.figure.rayToBShown .upper = true ∧
    setup.figure.rayToBShown .lower = true ∧
    setup.figure.rayLabel .upper = .r₁ ∧
    setup.figure.rayLabel .lower = .r₂ ∧
    setup.figure.separationLabelShown = true ∧
    setup.figure.forwardDistanceLabelShown = true ∧
    (∀ source, setup.figure.wavelengthLabelShown source = true) ∧
    setup.figure.initialPhaseDifferenceLabelShown = true

/-- Positivity and nondegeneracy of the physical quantities in the model. -/
structure HasPhysicalAcousticParameters {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop where
  wavelength_pos : ∀ unit,
    0 < lengthReadout unit setup.commonWavelength
  separation_pos : ∀ unit,
    0 < lengthReadout unit setup.speakerSeparation
  forwardDistance_pos : ∀ unit,
    0 < lengthReadout unit setup.observerForwardDistance
  rayPath_pos : ∀ unit source,
    0 < lengthReadout unit (setup.rayPathLengthToB source)
  referenceIntensity_pos : ∀ units,
    0 < acousticIntensityReadout units setup.referenceIntensityI₀
  totalIntensity_nonneg : ∀ units,
    0 ≤ acousticIntensityReadout units setup.totalIntensityAtB

/-!
Straight-line geometry for the two drawn rays. The upper source is aligned
with `B`; the lower ray is the hypotenuse with legs equal to the forward
distance and source separation. These are general relations, not numerical
answers.
-/
structure SatisfiesStraightLineRayGeometry {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop where
  upperRay : ∀ unit : LengthUnit,
    lengthReadout unit (setup.rayPathLengthToB .upper) =
      lengthReadout unit setup.observerForwardDistance
  lowerRayPythagorean : ∀ unit : LengthUnit,
    lengthReadout unit (setup.rayPathLengthToB .lower) ^ 2 =
      lengthReadout unit setup.observerForwardDistance ^ 2 +
        lengthReadout unit setup.speakerSeparation ^ 2

/-- The path difference is the magnitude of the two ray-length difference. -/
structure SatisfiesPathDifferenceLaw {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop where
  pathDifference : ∀ unit : LengthUnit,
    lengthReadout unit setup.pathDifferenceAtB =
      |lengthReadout unit (setup.rayPathLengthToB .lower) -
        lengthReadout unit (setup.rayPathLengthToB .upper)|

/-!
Propagation converts path difference to phase by `2π Δr / λ`, in addition to
the sources' initial phase difference. Radians are dimensionless.
-/
structure SatisfiesPropagationPhaseLaw {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop where
  receivedPhase :
    setup.receivedPhaseDifferenceAtB =
      (setup.initialPhaseRadians .lower - setup.initialPhaseRadians .upper) +
        2 * Real.pi *
          (lengthInMeters setup.pathDifferenceAtB /
            lengthInMeters setup.commonWavelength)

/-!
The general coherent two-source intensity law. In any coherent unit system,
contributions `I₁` and `I₂` with received phase difference `Δφ` combine as
`I₁ + I₂ + 2 sqrt(I₁ I₂) cos(Δφ)`. No problem-specific path or answer
coefficient occurs in this law.
-/
structure SatisfiesCoherentTwoSourceInterferenceLaw
    {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : Prop where
  coherentIntensity : ∀ units : UnitChoices,
    acousticIntensityReadout units setup.totalIntensityAtB =
      acousticIntensityReadout units (setup.singleSourceIntensityAtB .upper) +
        acousticIntensityReadout units (setup.singleSourceIntensityAtB .lower) +
        2 * Real.sqrt
          (acousticIntensityReadout units
              (setup.singleSourceIntensityAtB .upper) *
            acousticIntensityReadout units
              (setup.singleSourceIntensityAtB .lower)) *
          Real.cos setup.receivedPhaseDifferenceAtB

/-- The total intensity at `B` as a dimensionless multiple of `I₀`. -/
def intensityRatioAtB {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude) : ℝ :=
  acousticIntensityInWattsPerSquareMeter setup.totalIntensityAtB /
    acousticIntensityInWattsPerSquareMeter setup.referenceIntensityI₀

/-- Round a dimensionless scalar to the nearest hundredth. -/
def roundedToNearestHundredth (value : ℝ) : ℝ :=
  ((round (100 * value) : ℤ) : ℝ) / 100

/-- The answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed coefficient multiplying `I₀` for each answer choice. -/
def displayedIntensityMultiple : AnswerChoice → ℝ
  | .A => 19 / 20
  | .B => 21 / 20
  | .C => 17 / 20
  | .D => 3 / 4

/-- A choice agrees with the derived intensity ratio to the nearest hundredth. -/
def MatchesDisplayedIntensityChoice {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude)
    (choice : AnswerChoice) : Prop :=
  roundedToNearestHundredth (intensityRatioAtB setup) =
    displayedIntensityMultiple choice

/-- Exactly one displayed coefficient matches the rounded derived ratio. -/
def IsUniqueMatchingDisplayedIntensityChoice {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedIntensityChoice setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedIntensityChoice setup other → other = choice

/-!
The ray geometry gives `r₁ = 10 m`, `r₂ = sqrt 136 m`, path difference
`sqrt 136 - 10 m`, and the displayed received phase. All four statements are
derived conclusions rather than setup assumptions.
-/
lemma ray_lengths_path_difference_and_phase_at_B
    {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude)
    (h_source : MatchesSourceDescription setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_geometry : SatisfiesStraightLineRayGeometry setup)
    (h_path : SatisfiesPathDifferenceLaw setup)
    (h_phase : SatisfiesPropagationPhaseLaw setup) :
    lengthInMeters (setup.rayPathLengthToB .upper) = 10 ∧
      lengthInMeters (setup.rayPathLengthToB .lower) = Real.sqrt 136 ∧
      lengthInMeters setup.pathDifferenceAtB = Real.sqrt 136 - 10 ∧
      setup.receivedPhaseDifferenceAtB =
        2 * Real.pi * (Real.sqrt 136 - 10) := by
  have h_upper :
      lengthInMeters (setup.rayPathLengthToB .upper) = 10 := by
    calc
      lengthInMeters (setup.rayPathLengthToB .upper) =
          lengthInMeters setup.observerForwardDistance :=
        h_geometry.upperRay LengthUnit.meters
      _ = 10 := h_readouts.forwardDistanceMeters
  have h_lower_sq :
      lengthInMeters (setup.rayPathLengthToB .lower) ^ 2 = 136 := by
    calc
      lengthInMeters (setup.rayPathLengthToB .lower) ^ 2 =
          lengthInMeters setup.observerForwardDistance ^ 2 +
            lengthInMeters setup.speakerSeparation ^ 2 :=
        h_geometry.lowerRayPythagorean LengthUnit.meters
      _ = 136 := by
        rw [h_readouts.forwardDistanceMeters, h_readouts.separationMeters]
        norm_num
  have h_lower_pos :
      0 < lengthInMeters (setup.rayPathLengthToB .lower) :=
    h_physical.rayPath_pos LengthUnit.meters .lower
  have h_sqrt_sq : Real.sqrt 136 ^ 2 = 136 :=
    Real.sq_sqrt (by norm_num)
  have h_lower :
      lengthInMeters (setup.rayPathLengthToB .lower) = Real.sqrt 136 := by
    nlinarith [Real.sqrt_nonneg 136]
  have h_sqrt_gt_ten : 10 < Real.sqrt 136 := by
    nlinarith [Real.sqrt_nonneg 136]
  have h_path_difference :
      lengthInMeters setup.pathDifferenceAtB = Real.sqrt 136 - 10 := by
    change lengthReadout LengthUnit.meters setup.pathDifferenceAtB =
      Real.sqrt 136 - 10
    rw [h_path.pathDifference LengthUnit.meters, ← lengthInMeters,
      ← lengthInMeters, h_lower, h_upper,
      abs_of_pos (sub_pos.mpr h_sqrt_gt_ten)]
  refine ⟨h_upper, h_lower, h_path_difference, ?_⟩
  rw [h_phase.receivedPhase, h_source.2.2.2.1, h_path_difference,
    h_readouts.wavelengthMeters]
  ring

/-!
Substitution of the equal single-source intensities into the coherent-source
law yields the exact, unrounded intensity factor in every coherent unit system.
-/
lemma exact_intensity_at_B
    {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude)
    (h_source : MatchesSourceDescription setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_geometry : SatisfiesStraightLineRayGeometry setup)
    (h_path : SatisfiesPathDifferenceLaw setup)
    (h_phase : SatisfiesPropagationPhaseLaw setup)
    (h_interference : SatisfiesCoherentTwoSourceInterferenceLaw setup) :
    ∀ units : UnitChoices,
      acousticIntensityReadout units setup.totalIntensityAtB =
      acousticIntensityReadout units setup.referenceIntensityI₀ *
          (2 * (1 +
            Real.cos (2 * Real.pi * (Real.sqrt 136 - 10)))) := by
  intro units
  have h_phase_at_B :=
    (ray_lengths_path_difference_and_phase_at_B setup h_source h_readouts
      h_physical h_geometry h_path h_phase).2.2.2
  have h_reference_pos :
      0 < acousticIntensityReadout units setup.referenceIntensityI₀ :=
    h_physical.referenceIntensity_pos units
  have h_sqrt :
      Real.sqrt
          (acousticIntensityReadout units setup.referenceIntensityI₀ *
            acousticIntensityReadout units setup.referenceIntensityI₀) =
        acousticIntensityReadout units setup.referenceIntensityI₀ := by
    rw [← pow_two, Real.sqrt_sq h_reference_pos.le]
  rw [h_interference.coherentIntensity units, h_source.2.2.2.2 .upper,
    h_source.2.2.2.2 .lower, h_sqrt, h_phase_at_B]
  ring

/-- The exact dimensionless intensity ratio at point `B`. -/
lemma intensity_ratio_at_B_exact
    {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude)
    (h_source : MatchesSourceDescription setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_geometry : SatisfiesStraightLineRayGeometry setup)
    (h_path : SatisfiesPathDifferenceLaw setup)
    (h_phase : SatisfiesPropagationPhaseLaw setup)
    (h_interference : SatisfiesCoherentTwoSourceInterferenceLaw setup) :
    intensityRatioAtB setup =
      2 * (1 + Real.cos (2 * Real.pi * (Real.sqrt 136 - 10))) := by
  have h_exact :=
    exact_intensity_at_B setup h_source h_readouts h_physical h_geometry
      h_path h_phase h_interference UnitChoices.SI
  have h_reference_ne :
      acousticIntensityInWattsPerSquareMeter setup.referenceIntensityI₀ ≠ 0 :=
    ne_of_gt (h_physical.referenceIntensity_pos UnitChoices.SI)
  rw [intensityRatioAtB, acousticIntensityInWattsPerSquareMeter,
    acousticIntensityInWattsPerSquareMeter, h_exact]
  exact mul_div_cancel_left₀ _ h_reference_ne

/-!
At point `B`, the coherent interference result is

`I_B = 2 I₀ (1 + cos (2π (sqrt 136 - 10)))`.

Its dimensionless coefficient rounds to `0.95`, uniquely selecting answer A.
Neither this exact factor, its rounded value, nor answer A occurs in a setup
field, figure/readout predicate, or governing-law premise.

This formalizes `thm:physics:phyx_mini_0246:target`.
-/
theorem problem_phyx_mini_0246
    {AcousticAmplitude : Type}
    (setup : TwoLoudspeakerSetup AcousticAmplitude)
    (h_source : MatchesSourceDescription setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_geometry : SatisfiesStraightLineRayGeometry setup)
    (h_path : SatisfiesPathDifferenceLaw setup)
    (h_phase : SatisfiesPropagationPhaseLaw setup)
    (h_interference : SatisfiesCoherentTwoSourceInterferenceLaw setup) :
    (∀ units : UnitChoices,
      acousticIntensityReadout units setup.totalIntensityAtB =
        acousticIntensityReadout units setup.referenceIntensityI₀ *
          (2 * (1 +
            Real.cos (2 * Real.pi * (Real.sqrt 136 - 10))))) ∧
      roundedToNearestHundredth (intensityRatioAtB setup) = 19 / 20 ∧
      IsUniqueMatchingDisplayedIntensityChoice
        setup .A := by
  have h_exact :=
    exact_intensity_at_B setup h_source h_readouts h_physical h_geometry
      h_path h_phase h_interference
  have h_ratio :=
    intensity_ratio_at_B_exact setup h_source h_readouts h_physical h_geometry
      h_path h_phase h_interference

  /-
  `Trigonometric.Basic` supplies the complex exponential series estimate but not
  the later decimal bounds for `π`.  Applying that estimate at the two rational
  half-angles proves exactly the precision needed below.
  -/
  have h_pi_lower : (31415 / 10000 : ℝ) < Real.pi := by
    have h_cos : 0 < Real.cos (31415 / 20000 : ℝ) := by
      have h_exp := Complex.exp_bound'
        (x := ((31415 / 20000 : ℝ) : ℂ) * Complex.I) (n := 14)
        (by norm_num [Complex.norm_mul])
      have h_re := (Complex.abs_re_le_norm
        (Complex.exp (((31415 / 20000 : ℝ) : ℂ) * Complex.I) -
          ∑ m ∈ Finset.range 14,
            (((31415 / 20000 : ℝ) : ℂ) * Complex.I) ^ m /
              m.factorial)).trans h_exp
      rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re] at h_re
      norm_num [Complex.re_sum, Finset.sum_range_succ,
        Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.norm_mul, pow_succ] at h_re
      rw [abs_le] at h_re
      norm_num at h_re ⊢
      linarith
    by_contra h
    have h_order : Real.pi / 2 ≤ (31415 / 20000 : ℝ) := by
      norm_num at h ⊢
      linarith
    have h_cos_le :
        Real.cos (31415 / 20000 : ℝ) ≤ Real.cos (Real.pi / 2) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · nlinarith [Real.two_le_pi]
      · exact h_order
    simp only [Real.cos_pi_div_two] at h_cos_le
    linarith
  have h_pi_upper : Real.pi < (31416 / 10000 : ℝ) := by
    have h_cos : Real.cos (31416 / 20000 : ℝ) < 0 := by
      have h_exp := Complex.exp_bound'
        (x := ((31416 / 20000 : ℝ) : ℂ) * Complex.I) (n := 14)
        (by norm_num [Complex.norm_mul])
      have h_re := (Complex.abs_re_le_norm
        (Complex.exp (((31416 / 20000 : ℝ) : ℂ) * Complex.I) -
          ∑ m ∈ Finset.range 14,
            (((31416 / 20000 : ℝ) : ℂ) * Complex.I) ^ m /
              m.factorial)).trans h_exp
      rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re] at h_re
      norm_num [Complex.re_sum, Finset.sum_range_succ,
        Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.norm_mul, pow_succ] at h_re
      rw [abs_le] at h_re
      norm_num at h_re ⊢
      linarith
    by_contra h
    have h_order : (31416 / 20000 : ℝ) ≤ Real.pi / 2 := by
      norm_num at h ⊢
      linarith
    have h_cos_le :
        Real.cos (Real.pi / 2) ≤ Real.cos (31416 / 20000 : ℝ) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · positivity
      · nlinarith [Real.pi_pos]
      · exact h_order
    simp only [Real.cos_pi_div_two] at h_cos_le
    linarith

  have h_sqrt_136_sq : Real.sqrt 136 ^ 2 = 136 :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_136_lower : (116619 / 10000 : ℝ) < Real.sqrt 136 := by
    nlinarith only [h_sqrt_136_sq, Real.sqrt_nonneg 136]
  have h_sqrt_136_upper : Real.sqrt 136 < (5831 / 500 : ℝ) := by
    nlinarith only [h_sqrt_136_sq, Real.sqrt_nonneg 136]

  let y : ℝ := 2 * Real.pi * (12 - Real.sqrt 136)
  let δ : ℝ := y - 2 * Real.pi / 3
  have h_delta_factor :
      δ = 2 * Real.pi * (35 / 3 - Real.sqrt 136) := by
    dsimp [δ, y]
    ring
  have h_factor_pos : 0 < 35 / 3 - Real.sqrt 136 := by
    nlinarith only [h_sqrt_136_upper]
  have h_factor_lower :
      (7 / 1500 : ℝ) < 35 / 3 - Real.sqrt 136 := by
    nlinarith only [h_sqrt_136_upper]
  have h_factor_upper :
      35 / 3 - Real.sqrt 136 < (143 / 30000 : ℝ) := by
    nlinarith only [h_sqrt_136_lower]
  have h_product_lower :
      (31415 / 10000 : ℝ) * (7 / 1500) <
        Real.pi * (35 / 3 - Real.sqrt 136) := by
    calc
      (31415 / 10000 : ℝ) * (7 / 1500) <
          Real.pi * (7 / 1500) :=
        mul_lt_mul_of_pos_right h_pi_lower (by norm_num)
      _ < Real.pi * (35 / 3 - Real.sqrt 136) :=
        mul_lt_mul_of_pos_left h_factor_lower Real.pi_pos
  have h_product_upper :
      Real.pi * (35 / 3 - Real.sqrt 136) <
        (31416 / 10000 : ℝ) * (143 / 30000) := by
    calc
      Real.pi * (35 / 3 - Real.sqrt 136) <
          (31416 / 10000 : ℝ) * (35 / 3 - Real.sqrt 136) :=
        mul_lt_mul_of_pos_right h_pi_upper h_factor_pos
      _ < (31416 / 10000 : ℝ) * (143 / 30000) :=
        mul_lt_mul_of_pos_left h_factor_upper (by norm_num)
  have h_delta_lower : (293 / 10000 : ℝ) < δ := by
    rw [h_delta_factor]
    norm_num at h_product_lower ⊢
    nlinarith only [h_product_lower]
  have h_delta_upper : δ < (3 / 100 : ℝ) := by
    rw [h_delta_factor]
    norm_num at h_product_upper ⊢
    nlinarith only [h_product_upper]
  have h_delta_pos : 0 < δ := by
    norm_num at h_delta_lower ⊢
    linarith only [h_delta_lower]

  /-
  The reduced angle differs from `2π/3` by only `δ`.  The degree-three
  complex exponential polynomial has a fourth-order norm remainder, giving
  simultaneous certified approximations for `cos δ` and `sin δ`.
  -/
  have h_small_exp := Complex.exp_bound'
    (x := (δ : ℂ) * Complex.I) (n := 4) (by
      norm_num [Complex.norm_mul, abs_of_pos h_delta_pos]
      linarith only [h_delta_upper])
  have h_small_re := (Complex.abs_re_le_norm
    (Complex.exp ((δ : ℂ) * Complex.I) -
      ∑ m ∈ Finset.range 4,
        ((δ : ℂ) * Complex.I) ^ m / m.factorial)).trans h_small_exp
  have h_small_im := (Complex.abs_im_le_norm
    (Complex.exp ((δ : ℂ) * Complex.I) -
      ∑ m ∈ Finset.range 4,
        ((δ : ℂ) * Complex.I) ^ m / m.factorial)).trans h_small_exp
  rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re] at h_small_re
  rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im] at h_small_im
  norm_num [Complex.re_sum, Complex.im_sum, Finset.sum_range_succ,
    Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.norm_mul, pow_succ, abs_of_pos h_delta_pos]
    at h_small_re h_small_im
  have h_delta_pow_four : δ ^ 4 ≤ (3 / 100 : ℝ) ^ 4 := by
    gcongr
  have h_error : δ ^ 4 / 12 ≤ (1 / 1000000 : ℝ) := by
    norm_num
    nlinarith only [h_delta_pow_four]
  have h_cos_approx :
      |Real.cos δ - (1 - δ ^ 2 / 2)| ≤ (1 / 1000000 : ℝ) := by
    apply le_trans (b := δ ^ 4 / 12)
    · convert h_small_re using 1 <;> ring_nf
    · exact h_error
  have h_sin_approx :
      |Real.sin δ - (δ - δ ^ 3 / 6)| ≤ (1 / 1000000 : ℝ) := by
    apply le_trans (b := δ ^ 4 / 12)
    · convert h_small_im using 1 <;> ring_nf
    · exact h_error
  rw [abs_le] at h_cos_approx h_sin_approx
  have h_delta_cube_upper : δ ^ 3 ≤ (3 / 100 : ℝ) ^ 3 := by
    gcongr
  have h_delta_cube_nonneg : 0 ≤ δ ^ 3 := pow_nonneg h_delta_pos.le 3
  have h_delta_square_upper : δ ^ 2 ≤ (3 / 100 : ℝ) ^ 2 := by
    gcongr
  have h_sin_lower : (292 / 10000 : ℝ) < Real.sin δ := by
    norm_num at h_sin_approx h_delta_lower h_delta_cube_upper ⊢
    nlinarith only [h_sin_approx.1, h_delta_lower, h_delta_cube_upper]
  have h_sin_upper : Real.sin δ < (301 / 10000 : ℝ) := by
    norm_num at h_sin_approx h_delta_upper h_delta_cube_nonneg ⊢
    nlinarith only [h_sin_approx.2, h_delta_upper, h_delta_cube_nonneg]
  have h_cos_lower : (999 / 1000 : ℝ) < Real.cos δ := by
    norm_num at h_cos_approx h_delta_square_upper ⊢
    nlinarith only [h_cos_approx.1, h_delta_square_upper]

  have h_sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have h_sqrt_three_lower : (1732 / 1000 : ℝ) < Real.sqrt 3 := by
    nlinarith only [h_sqrt_three_sq, Real.sqrt_nonneg 3]
  have h_sqrt_three_upper : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
    nlinarith only [h_sqrt_three_sq, Real.sqrt_nonneg 3]
  have h_sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h_sin_pos : 0 < Real.sin δ := by
    norm_num at h_sin_lower ⊢
    linarith only [h_sin_lower]
  have h_product_sin_lower :
      (1732 / 1000 : ℝ) * (292 / 10000) <
        Real.sqrt 3 * Real.sin δ := by
    calc
      (1732 / 1000 : ℝ) * (292 / 10000) <
          Real.sqrt 3 * (292 / 10000) :=
        mul_lt_mul_of_pos_right h_sqrt_three_lower (by norm_num)
      _ < Real.sqrt 3 * Real.sin δ :=
        mul_lt_mul_of_pos_left h_sin_lower h_sqrt_three_pos
  have h_product_sin_upper :
      Real.sqrt 3 * Real.sin δ <
        (1733 / 1000 : ℝ) * (301 / 10000) := by
    calc
      Real.sqrt 3 * Real.sin δ < (1733 / 1000 : ℝ) * Real.sin δ :=
        mul_lt_mul_of_pos_right h_sqrt_three_upper h_sin_pos
      _ < (1733 / 1000 : ℝ) * (301 / 10000) :=
        mul_lt_mul_of_pos_left h_sin_upper (by norm_num)

  have h_cos_y :
      Real.cos y =
        -1 / 2 * Real.cos δ - Real.sqrt 3 / 2 * Real.sin δ := by
    have hy : y = 2 * Real.pi / 3 + δ := by
      dsimp [δ]
      ring
    rw [hy, Real.cos_add]
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
    ring
  have h_cos_y_lower : (-211 / 400 : ℝ) ≤ Real.cos y := by
    rw [h_cos_y]
    nlinarith only [Real.cos_le_one δ, h_product_sin_upper]
  have h_cos_y_upper : Real.cos y < (-209 / 400 : ℝ) := by
    rw [h_cos_y]
    nlinarith only [h_cos_lower, h_product_sin_lower]
  have h_period :
      Real.cos (2 * Real.pi * (Real.sqrt 136 - 10)) = Real.cos y := by
    calc
      Real.cos (2 * Real.pi * (Real.sqrt 136 - 10)) =
          Real.cos ((2 : ℕ) * (2 * Real.pi) - y) := by
        congr 1
        dsimp [y]
        ring
      _ = Real.cos y := Real.cos_nat_mul_two_pi_sub y 2
  have h_phase_cos_lower :
      (-211 / 400 : ℝ) ≤
        Real.cos (2 * Real.pi * (Real.sqrt 136 - 10)) := by
    rwa [h_period]
  have h_phase_cos_upper :
      Real.cos (2 * Real.pi * (Real.sqrt 136 - 10)) <
        (-209 / 400 : ℝ) := by
    rwa [h_period]

  have h_rounded :
      roundedToNearestHundredth (intensityRatioAtB setup) = 19 / 20 := by
    rw [roundedToNearestHundredth, h_ratio]
    have h_round :
        round
            (100 *
              (2 * (1 +
                Real.cos (2 * Real.pi * (Real.sqrt 136 - 10))))) =
          (95 : ℤ) := by
      rw [round_eq_iff]
      constructor
      · change (95 : ℝ) - 1 / 2 ≤
          100 * (2 * (1 +
            Real.cos (2 * Real.pi * (Real.sqrt 136 - 10))))
        nlinarith only [h_phase_cos_lower]
      · change
          100 * (2 * (1 +
            Real.cos (2 * Real.pi * (Real.sqrt 136 - 10)))) <
            (95 : ℝ) + 1 / 2
        nlinarith only [h_phase_cos_upper]
    rw [h_round]
    norm_num
  have h_unique : IsUniqueMatchingDisplayedIntensityChoice setup .A := by
    unfold IsUniqueMatchingDisplayedIntensityChoice
    constructor
    · simpa [MatchesDisplayedIntensityChoice, displayedIntensityMultiple] using
        h_rounded
    · intro other h_other
      unfold MatchesDisplayedIntensityChoice at h_other
      rw [h_rounded] at h_other
      cases other with
      | A => rfl
      | B => norm_num [displayedIntensityMultiple] at h_other
      | C => norm_num [displayedIntensityMultiple] at h_other
      | D => norm_num [displayedIntensityMultiple] at h_other
  exact ⟨h_exact, h_rounded, h_unique⟩

end PhyXMiniProblems.ProblemPhyXMini0246
