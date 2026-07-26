import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Fringe spacing in a Fresnel biprism interferometer

The primary figure contains the actual source `S₀`, its two virtual images
`S₁` and `S₂`, a thin biprism whose two small apex angles are both labelled
`A`, and screen points `O` and `P`.  Its length labels are the source--prism
distance `a`, prism--screen distance `b`, and virtual-source separation `d`.

All wavelengths and geometric distances are unit-aware physical lengths.
The prism angle uses Mathlib's physical angle type `Real.Angle`; refractive
indices and unit readouts are dimensionless real numbers.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0121

open Dimension

/-- A signed physical length represented independently of a chosen unit system. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthValueIn (unit : LengthUnit) (length : DimLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The metre readout used in the biprism geometry and interference laws. -/
def metersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.meters length

/-- The nanometre readout used for the stated green-light wavelength. -/
def nanometersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- The scalar milliradian readout of a physical angle. -/
def milliradiansValue (angle : Real.Angle) : ℝ :=
  1000 * angle.toReal

/-- The three source labels in the primary figure. -/
inductive SourceLabel where
  /-- The actual monochromatic source at the centre of the source plane. -/
  | S0
  /-- The upper virtual image formed by the biprism. -/
  | S1
  /-- The lower virtual image formed by the biprism. -/
  | S2
  deriving DecidableEq, Repr

/-- Whether a labelled source is actual or is a virtual biprism image. -/
inductive SourceRole where
  | actual
  | virtual
  deriving DecidableEq, Repr

/-- The optical role assigned to each source label by the ray diagram. -/
def SourceLabel.role : SourceLabel → SourceRole
  | .S0 => .actual
  | .S1 => .virtual
  | .S2 => .virtual

/-- The two explicitly marked points on the observation screen. -/
inductive ScreenPoint where
  /-- The point `O` on the central optical axis. -/
  | O
  /-- The off-axis observation point `P`. -/
  | P
  deriving DecidableEq, Repr

/-- The two homogeneous optical media relevant to the thin-prism deviation. -/
inductive OpticalMedium where
  | ambientAir
  | biprismGlass
  deriving DecidableEq, Repr

/--
The monochromatic source, Fresnel biprism, virtual images, and screen.

`sourceToBiprismDistance`, `biprismToScreenDistance`, and
`virtualSourceSeparation` are the figure labels `a`, `b`, and `d`.
`prismAngle` is the common magnitude `A` displayed at both halves of the
biprism.  `adjacentFringeSpacing` is the physical quantity requested by the
problem; it is stored independently and constrained only by the controlled
approximation law below.
-/
structure FresnelBiprismInterferometer where
  lightWavelength : DimLength
  sourceToBiprismDistance : DimLength
  biprismToScreenDistance : DimLength
  prismAngle : Real.Angle
  refractiveIndex : OpticalMedium → ℝ
  virtualSourceSeparation : DimLength
  adjacentFringeSpacing : DimLength

/-!
## Assumption/target split

`HasStatedProblemReadouts` contains only numerical source and figure data.
`HasPhysicalParameters` supplies positivity and the small physical angle
branch.  `SatisfiesControlledThinBiprismImageLaw` and
`SatisfiesControlledAdjacentFringeLaw` state the two governing optical
approximations together with explicit higher-order remainder bounds.  Neither
the requested spacing, its rounding interval, nor answer A occurs in any of
those premises.
-/

/--
The numerical readouts given by the problem and primary figure: green light
of wavelength `500 nm`, `a = 0.200 m`, `b = 2.00 m`, common prism angle
`A = 3.50 mrad`, air index one, and glass index `n = 1.50`.
-/
def HasStatedProblemReadouts
    (setup : FresnelBiprismInterferometer) : Prop :=
  nanometersValue setup.lightWavelength = 500 ∧
    metersValue setup.sourceToBiprismDistance = 1 / 5 ∧
    metersValue setup.biprismToScreenDistance = 2 ∧
    milliradiansValue setup.prismAngle = 7 / 2 ∧
    setup.refractiveIndex .ambientAir = 1 ∧
    setup.refractiveIndex .biprismGlass = 3 / 2

/-- Positivity, optical-index ordering, and the small acute prism-angle branch. -/
def HasPhysicalParameters
    (setup : FresnelBiprismInterferometer) : Prop :=
  0 < metersValue setup.lightWavelength ∧
    0 < metersValue setup.sourceToBiprismDistance ∧
    0 < metersValue setup.biprismToScreenDistance ∧
    0 < metersValue setup.virtualSourceSeparation ∧
    0 < metersValue setup.adjacentFringeSpacing ∧
    0 < setup.prismAngle.toReal ∧
    setup.prismAngle.toReal < Real.pi / 2 ∧
    0 < setup.refractiveIndex .ambientAir ∧
    setup.refractiveIndex .ambientAir < setup.refractiveIndex .biprismGlass

/--
A quantitative small-angle contract for the virtual-image separation.

The leading term is the usual thin-prism prediction
`2 a (n_glass / n_air - 1) A`.  Instead of globalizing that first-order
formula as an exact optical law, this predicate exposes a metre-valued
higher-order remainder and bounds it at cubic order in the dimensionless
angle `A`.  The bound is a modeling contract for the stated thin biprism, not
the answer to the fringe-spacing question.
-/
def SatisfiesControlledThinBiprismImageLaw
    (setup : FresnelBiprismInterferometer) : Prop :=
  ∃ separationRemainderMeters : ℝ,
    metersValue setup.virtualSourceSeparation =
        2 * metersValue setup.sourceToBiprismDistance *
            (setup.refractiveIndex .biprismGlass /
                setup.refractiveIndex .ambientAir - 1) *
              setup.prismAngle.toReal +
          separationRemainderMeters ∧
      |separationRemainderMeters| ≤
        2 * metersValue setup.sourceToBiprismDistance *
          |setup.prismAngle.toReal| ^ 3

/--
A controlled near-axis interference contract for the coherent virtual sources
`S₁` and `S₂`.

The leading term is `λ (a + b) / d`.  The exact observed central adjacent
spacing may differ by `fringeRemainderMeters`.  Its relative error is bounded
by the squared aperture ratio `d / (2 (a + b))` plus the squared wavelength
ratio `λ / d`, making the paraxial and many-fringe approximations explicit
rather than asserting their leading term globally as an exact equality.
-/
def SatisfiesControlledAdjacentFringeLaw
    (setup : FresnelBiprismInterferometer) : Prop :=
  ∃ fringeRemainderMeters : ℝ,
    metersValue setup.adjacentFringeSpacing =
        metersValue setup.lightWavelength *
              (metersValue setup.sourceToBiprismDistance +
                metersValue setup.biprismToScreenDistance) /
            metersValue setup.virtualSourceSeparation +
          fringeRemainderMeters ∧
      |fringeRemainderMeters| ≤
        |metersValue setup.lightWavelength *
              (metersValue setup.sourceToBiprismDistance +
                metersValue setup.biprismToScreenDistance) /
            metersValue setup.virtualSourceSeparation| *
          ((|metersValue setup.virtualSourceSeparation| /
                (2 * |metersValue setup.sourceToBiprismDistance +
                  metersValue setup.biprismToScreenDistance|)) ^ 2 +
            (|metersValue setup.lightWavelength| /
                |metersValue setup.virtualSourceSeparation|) ^ 2)

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre readout printed beside each displayed answer choice. -/
def answerFringeSpacingMeters : AnswerChoice → ℝ
  | .A => 157 / 100000
  | .B => 157 / 10000
  | .C => 157 / 1000000
  | .D => 157 / 10000000

/-- Half a unit in the final displayed digit of each three-significant-figure choice. -/
def answerRoundingToleranceMeters : AnswerChoice → ℝ
  | .A => 1 / 200000
  | .B => 1 / 20000
  | .C => 1 / 2000000
  | .D => 1 / 20000000

/-- A physical spacing agrees with a displayed choice to its printed precision. -/
def MatchesDisplayedPrecision
    (spacing : DimLength) (choice : AnswerChoice) : Prop :=
  |metersValue spacing - answerFringeSpacingMeters choice| ≤
    answerRoundingToleranceMeters choice

/--
For the stated Fresnel biprism, the controlled optical model puts the central
adjacent-fringe spacing in the printed rounding interval around
`1.57 × 10⁻³ m`.  No other displayed choice lies in that interval, so the
recorded answer A is unique.

Blueprint: `thm:physics:phyx_mini_0121:target`.
-/
theorem fringeSpacing_matches_recordedAnswerA
    (setup : FresnelBiprismInterferometer)
    (h_readouts : HasStatedProblemReadouts setup)
    (h_physical : HasPhysicalParameters setup)
    (h_biprism : SatisfiesControlledThinBiprismImageLaw setup)
    (h_interference : SatisfiesControlledAdjacentFringeLaw setup) :
    MatchesDisplayedPrecision setup.adjacentFringeSpacing .A ∧
      ∀ choice,
        MatchesDisplayedPrecision setup.adjacentFringeSpacing choice →
          choice = .A := by
  rcases h_readouts with
    ⟨h_wavelength_nm, h_source_distance, h_screen_distance, h_angle_mrad,
      h_air_index, h_glass_index⟩
  rcases h_physical with
    ⟨h_wavelength_pos, _, _, h_separation_pos, h_spacing_pos, h_angle_pos,
      _, _, _⟩
  have h_wavelength_units :
      nanometersValue setup.lightWavelength =
        1000000000 * metersValue setup.lightWavelength := by
    have h := congrArg WithDim.val <| setup.lightWavelength.property
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    norm_num [nanometersValue, metersValue, lengthValueIn,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.toReal] at h ⊢
    exact h
  have h_wavelength_m :
      metersValue setup.lightWavelength = (1 / 2000000 : ℝ) := by
    nlinarith only [h_wavelength_nm, h_wavelength_units]
  have h_angle :
      setup.prismAngle.toReal = (7 / 2000 : ℝ) := by
    unfold milliradiansValue at h_angle_mrad
    norm_num at h_angle_mrad ⊢
    linarith
  rcases h_biprism with ⟨separationRemainder, h_separation, h_separation_error⟩
  rw [h_source_distance, h_air_index, h_glass_index, h_angle] at h_separation
  rw [h_source_distance, h_angle] at h_separation_error
  norm_num at h_separation h_separation_error
  have h_remainder_bounds := abs_le.mp h_separation_error
  have h_separation_lower :
      (1 / 2000 : ℝ) < metersValue setup.virtualSourceSeparation := by
    nlinarith only [h_separation, h_remainder_bounds.1]
  have h_separation_upper :
      metersValue setup.virtualSourceSeparation < (1 / 1000 : ℝ) := by
    nlinarith only [h_separation, h_remainder_bounds.2]
  rcases h_interference with
    ⟨fringeRemainder, h_spacing, h_fringe_error⟩
  rw [h_wavelength_m, h_source_distance, h_screen_distance] at h_spacing h_fringe_error
  norm_num at h_spacing h_fringe_error
  have h_separation_lower_strong :
      (699 / 1000000 : ℝ) < metersValue setup.virtualSourceSeparation := by
    nlinarith only [h_separation, h_remainder_bounds.1]
  have h_separation_upper_strong :
      metersValue setup.virtualSourceSeparation < (701 / 1000000 : ℝ) := by
    nlinarith only [h_separation, h_remainder_bounds.2]
  have h_leading_pos :
      0 <
        (11 / 10000000 : ℝ) /
          metersValue setup.virtualSourceSeparation :=
    div_pos (by norm_num) h_separation_pos
  have h_leading_lower :
      (783 / 500000 : ℝ) <
        (11 / 10000000 : ℝ) /
          metersValue setup.virtualSourceSeparation := by
    apply (lt_div_iff₀ h_separation_pos).2
    nlinarith only [h_separation_upper_strong]
  have h_leading_upper :
      (11 / 10000000 : ℝ) /
          metersValue setup.virtualSourceSeparation <
        (787 / 500000 : ℝ) := by
    apply (div_lt_iff₀ h_separation_pos).2
    nlinarith only [h_separation_lower_strong]
  have h_leading_coarse_upper :
      (11 / 10000000 : ℝ) /
          metersValue setup.virtualSourceSeparation <
        (1 / 500 : ℝ) := by
    nlinarith only [h_leading_upper]
  have h_aperture_ratio_pos :
      0 <
        metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ) :=
    div_pos h_separation_pos (by norm_num)
  have h_aperture_ratio_upper :
      metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ) <
        (1 / 1000 : ℝ) := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 22 / 5)).2
    nlinarith only [h_separation_upper]
  have h_wavelength_ratio_pos :
      0 <
        (1 / 2000000 : ℝ) /
          metersValue setup.virtualSourceSeparation :=
    div_pos (by norm_num) h_separation_pos
  have h_wavelength_ratio_upper :
      (1 / 2000000 : ℝ) /
          metersValue setup.virtualSourceSeparation <
        (1 / 1000 : ℝ) := by
    apply (div_lt_iff₀ h_separation_pos).2
    nlinarith only [h_separation_lower]
  have h_aperture_sq_upper :
      (metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ)) ^ 2 <
        (1 / 1000 : ℝ) ^ 2 := by
    nlinarith only [h_aperture_ratio_pos, h_aperture_ratio_upper]
  have h_wavelength_sq_upper :
      ((1 / 2000000 : ℝ) /
          metersValue setup.virtualSourceSeparation) ^ 2 <
        (1 / 1000 : ℝ) ^ 2 := by
    nlinarith only [h_wavelength_ratio_pos, h_wavelength_ratio_upper]
  have h_relative_error_pos :
      0 <
        (metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ)) ^ 2 +
          ((1 / 2000000 : ℝ) /
            metersValue setup.virtualSourceSeparation) ^ 2 := by
    positivity
  have h_relative_error_upper :
      (metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ)) ^ 2 +
          ((1 / 2000000 : ℝ) /
            metersValue setup.virtualSourceSeparation) ^ 2 <
        (1 / 500000 : ℝ) := by
    nlinarith only [h_aperture_sq_upper, h_wavelength_sq_upper]
  rw [abs_of_pos h_separation_pos, abs_of_pos h_leading_pos] at h_fringe_error
  have h_fringe_product_upper :
      (11 / 10000000 : ℝ) /
            metersValue setup.virtualSourceSeparation *
          ((metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ)) ^ 2 +
            ((1 / 2000000 : ℝ) /
              metersValue setup.virtualSourceSeparation) ^ 2) <
        (1 / 1000000 : ℝ) := by
    calc
      (11 / 10000000 : ℝ) /
              metersValue setup.virtualSourceSeparation *
            ((metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ)) ^ 2 +
              ((1 / 2000000 : ℝ) /
                metersValue setup.virtualSourceSeparation) ^ 2) <
          (1 / 500 : ℝ) *
            ((metersValue setup.virtualSourceSeparation / (22 / 5 : ℝ)) ^ 2 +
              ((1 / 2000000 : ℝ) /
                metersValue setup.virtualSourceSeparation) ^ 2) :=
        mul_lt_mul_of_pos_right h_leading_coarse_upper h_relative_error_pos
      _ < (1 / 500 : ℝ) * (1 / 500000 : ℝ) :=
        mul_lt_mul_of_pos_left h_relative_error_upper (by norm_num)
      _ < (1 / 1000000 : ℝ) := by norm_num
  have h_fringe_remainder_small :
      |fringeRemainder| < (1 / 1000000 : ℝ) :=
    lt_of_le_of_lt h_fringe_error h_fringe_product_upper
  have h_fringe_remainder_bounds := abs_lt.mp h_fringe_remainder_small
  have h_spacing_lower :
      (313 / 200000 : ℝ) <
        metersValue setup.adjacentFringeSpacing := by
    nlinarith only [h_spacing, h_leading_lower, h_fringe_remainder_bounds.1]
  have h_spacing_upper :
      metersValue setup.adjacentFringeSpacing <
        (63 / 40000 : ℝ) := by
    nlinarith only [h_spacing, h_leading_upper, h_fringe_remainder_bounds.2]
  have h_matches_A :
      MatchesDisplayedPrecision setup.adjacentFringeSpacing .A := by
    change
      |metersValue setup.adjacentFringeSpacing - (157 / 100000 : ℝ)| ≤
        (1 / 200000 : ℝ)
    apply abs_le.mpr
    constructor
    · nlinarith only [h_spacing_lower]
    · nlinarith only [h_spacing_upper]
  refine ⟨h_matches_A, ?_⟩
  intro choice h_choice
  cases choice with
  | A => rfl
  | B =>
      exfalso
      change
        |metersValue setup.adjacentFringeSpacing - (157 / 10000 : ℝ)| ≤
          (1 / 20000 : ℝ) at h_choice
      have h_choice_lower := (abs_le.mp h_choice).1
      nlinarith only [h_spacing_upper, h_choice_lower]
  | C =>
      exfalso
      change
        |metersValue setup.adjacentFringeSpacing - (157 / 1000000 : ℝ)| ≤
          (1 / 2000000 : ℝ) at h_choice
      have h_choice_upper := (abs_le.mp h_choice).2
      nlinarith only [h_spacing_lower, h_choice_upper]
  | D =>
      exfalso
      change
        |metersValue setup.adjacentFringeSpacing - (157 / 10000000 : ℝ)| ≤
          (1 / 20000000 : ℝ) at h_choice
      have h_choice_upper := (abs_le.mp h_choice).2
      nlinarith only [h_spacing_lower, h_choice_upper]

end PhyXMiniProblems.ProblemPhyXMini0121
