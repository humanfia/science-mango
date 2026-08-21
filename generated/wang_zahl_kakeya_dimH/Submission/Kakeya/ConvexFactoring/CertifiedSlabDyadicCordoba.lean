import Submission.Kakeya.ConvexFactoring.CertifiedSlabDyadicAngle
import Submission.Kakeya.ConvexFactoring.CordobaAnalytic

/-!
# Certified slab dyadic angle to Córdoba consequences

This module connects the genuine certified-slab sine-bucket geometry to
the division-free Córdoba conclusions.  Pairwise overlap, row bounds, and
second-moment bounds are derived by the imported certified dyadic theorem;
none of them is an input below.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

namespace CertifiedSlabDyadicCordoba

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]
variable {F : ConvexFamily ι} {Y : Shading F}
variable {C θ : ℝ≥0}

/-- The explicit Córdoba factor produced by the exceptional level together
with all genuine sine levels. -/
def certifiedSlabDyadicFactor
    (levels : Finset κ) (D A : ℝ≥0∞) : ℝ≥0∞ :=
  ((slabAngleLevels levels).card : ℝ≥0∞) * D * A

/-- Certified slab geometry, dyadic angle summation, and Katz--Tao
nonconcentration give the required second-moment estimate. -/
theorem certifiedSlabDyadicSecondMoment_le
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (levels : Finset κ)
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (container : ι → Option κ → ConvexBody Space)
    (D A : ℝ≥0∞)
    (hlevel : ∀ i j, level i j ∈ slabAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ slabAngleLevels levels →
      certifiedSlabAngleScale C θ inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i)) :
    (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) ≤
      certifiedSlabDyadicFactor levels D A * Y.shadingMass := by
  simpa [certifiedSlabDyadicFactor] using
    certifiedSlabDyadicOverlap_secondMoment_le
      cert levels level inverseSineWeight container D A
      hlevel htransverse hinverse hcontained hKT hscale

/-- End-to-end division-free union estimate from the actual certified slab
geometry and dyadic row summation. -/
theorem certifiedSlabDyadic_shadingMass_le
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (levels : Finset κ)
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (container : ι → Option κ → ConvexBody Space)
    (D A : ℝ≥0∞)
    (hlevel : ∀ i j, level i j ∈ slabAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ slabAngleLevels levels →
      certifiedSlabAngleScale C θ inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i)) :
    Y.shadingMass ≤ certifiedSlabDyadicFactor levels D A *
      volume Y.shadedUnion := by
  apply shadingMass_le_factor_mul_volume_shadedUnion_of_secondMoment_le
  exact certifiedSlabDyadicSecondMoment_le
    cert levels level inverseSineWeight container D A
    hlevel htransverse hinverse hcontained hKT hscale

/-- The same genuine geometric inputs bound average multiplicity, including
zero shaded-union volume and infinite factor cases. -/
theorem certifiedSlabDyadic_averageMultiplicity_le
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (levels : Finset κ)
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (container : ι → Option κ → ConvexBody Space)
    (D A : ℝ≥0∞)
    (hlevel : ∀ i j, level i j ∈ slabAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ slabAngleLevels levels →
      certifiedSlabAngleScale C θ inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i)) :
    Y.averageMultiplicity ≤ certifiedSlabDyadicFactor levels D A := by
  apply averageMultiplicity_le_factor_of_secondMoment_le
  exact certifiedSlabDyadicSecondMoment_le
    cert levels level inverseSineWeight container D A
    hlevel htransverse hinverse hcontained hKT hscale

/-- Safe quotient-form lower bound for the shaded union. -/
theorem certifiedSlabDyadic_shadingMass_div_factor_le_volume
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (levels : Finset κ)
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (container : ι → Option κ → ConvexBody Space)
    (D A : ℝ≥0∞)
    (hlevel : ∀ i j, level i j ∈ slabAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ slabAngleLevels levels →
      certifiedSlabAngleScale C θ inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i)) :
    Y.shadingMass / certifiedSlabDyadicFactor levels D A ≤
      volume Y.shadedUnion := by
  apply shadingMass_div_factor_le_volume_shadedUnion_of_secondMoment_le
  exact certifiedSlabDyadicSecondMoment_le
    cert levels level inverseSineWeight container D A
    hlevel htransverse hinverse hcontained hKT hscale

/-- Density bridge with no division side conditions. -/
theorem certifiedSlabDyadic_shadingDensity_le
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (levels : Finset κ)
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (container : ι → Option κ → ConvexBody Space)
    (D A : ℝ≥0∞)
    (hlevel : ∀ i j, level i j ∈ slabAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ slabAngleLevels levels →
      certifiedSlabAngleScale C θ inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i)) :
    Y.shadingDensity ≤ certifiedSlabDyadicFactor levels D A *
      (volume Y.shadedUnion / familyVolume F) := by
  apply shadingDensity_le_factor_mul_unionRatio_of_secondMoment_le
  exact certifiedSlabDyadicSecondMoment_le
    cert levels level inverseSineWeight container D A
    hlevel htransverse hinverse hcontained hKT hscale

end CertifiedSlabDyadicCordoba

end

end Submission.Kakeya.ConvexFactoring
