import Submission.Kakeya.ConvexFactoring.CertifiedInducedThickeningLower
import Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity

/-!
# Certified slab weak-scale induced-density bridge

This module composes the valid certificate-only `theta / 8` local-inner-box
estimate with the fiber multiplicity and induced-density algebra.  For every
active coarse index it applies the certified thickening theorem to the actual
fiber shaded union inside the actual coarse body.  Thus the set-growth and
fiber-covering-growth predicates are derived intermediate facts, not inputs.

The resulting scale is of order `theta^4 C^{-3}`.  This is the strongest
uniform scale supplied by the current global slab certificate; no
`theta^3` local-capture estimate is claimed.  The only remaining analytic
input in the density conclusions is the displayed coarse-family
normalization inequality.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open InducedShadingDensityAlgebra
open FiberCoveringGrowthFromMultiplicity

noncomputable section

namespace CertifiedSlabWeakScaleDensity

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
variable {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- The explicit local-inner volume furnished by the `theta / 8`
contraction of a certified `theta × 1 × 1` slab. -/
def slabThetaEighthScale (C θ : ℝ≥0) : ℝ≥0∞ :=
  (((θ / 8 : ℝ≥0) : ℝ≥0∞) ^ 3) *
    (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3) * (θ : ℝ≥0∞)

/-- The explicit coarse local-ball cap at radius `3 * theta`. -/
def slabThetaGrowth (θ : ℝ≥0) : ℝ≥0∞ :=
  (θ : ℝ≥0∞) * (6 * (θ : ℝ≥0∞)) ^ 2

/-- The certified weak scale is nonzero under the scalar conditions already
encoded by any nonvacuous slab certificate family. -/
theorem slabThetaEighthScale_ne_zero
    {C θ : ℝ≥0} (hC : 1 ≤ C) (hθ : 0 < θ) :
    slabThetaEighthScale C θ ≠ 0 := by
  have hC0 : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC)
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  simp [slabThetaEighthScale, hC0, hθ0]

/-- The certified weak scale is always finite. -/
theorem slabThetaEighthScale_ne_top (C θ : ℝ≥0) :
    slabThetaEighthScale C θ ≠ ∞ := by
  unfold slabThetaEighthScale
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    ENNReal.coe_ne_top

omit [Fintype ι] [Fintype κ] in
/-- Applying the formal certified-slab thickening theorem fiber by fiber
produces the exact set-growth predicate for neighborhood-induced shading. -/
theorem hasFiberSetGrowth_of_slabCertificates
    (P : ConvexFactorization F W) (Z : Shading F)
    (C θ : ℝ≥0)
    (cert : ∀ k ∈ P.index.coarse,
      SlabDimensionsCertificate C θ (W k)) :
    HasFiberSetGrowth P Z (θ : ℝ)
      (slabThetaEighthScale C θ) (slabThetaGrowth θ) := by
  intro k hk
  obtain ⟨_packing, _hlow, hgrowth⟩ :=
    (cert k hk).exists_packingCertificate_with_explicit_bodyIntersectionGrowth
      (P.fiberShadedUnion_subset_coarseBody Z k)
  simpa [slabThetaEighthScale, slabThetaGrowth,
    ConvexFactorization.neighborhoodInducedShading_carrier] using hgrowth

/-- Genuine active-fiber pointwise multiplicity together with certified slab
geometry yields the full fiber-covering-growth input used downstream. -/
theorem hasFiberCoveringGrowth_of_slabCertificates
    (P : ConvexFactorization F W) (Z : Shading F)
    (m : ℕ) (C θ : ℝ≥0)
    (cert : ∀ k ∈ P.index.coarse,
      SlabDimensionsCertificate C θ (W k))
    (hmult : HasActiveFiberMultiplicityBound P Z m) :
    HasFiberCoveringGrowth P Z (θ : ℝ)
      (slabThetaEighthScale C θ)
      ((m : ℝ≥0∞) * slabThetaGrowth θ) :=
  hasFiberCoveringGrowth_of_multiplicity_of_setGrowth
    P Z m (θ : ℝ) (slabThetaEighthScale C θ) (slabThetaGrowth θ)
      hmult (hasFiberSetGrowth_of_slabCertificates P Z C θ cert)

/-- End-to-end cross-multiplied mass conclusion at the certified weak scale.
Neither set growth nor fiber covering growth is assumed. -/
theorem sourceMass_sq_mul_coarseVolume_le_of_slabCertificates
    (P : ConvexFactorization F W) (Y : Shading F)
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (loss : ℕ) (m : ℕ) (C θ : ℝ≥0) (normalization : ℝ≥0∞)
    (hC : 1 ≤ C) (hθ : 0 < θ)
    (cert : ∀ k ∈ P.index.coarse,
      SlabDimensionsCertificate C θ (W k))
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass)
    (hmult : HasActiveFiberMultiplicityBound P R.shading m)
    (hnormalize :
      ((m : ℝ≥0∞) * slabThetaGrowth θ) * familyVolume W *
          Y.shadingDensity ≤
        normalization * slabThetaEighthScale C θ * familyVolume F) :
    Y.shadingMass ^ 2 * familyVolume W ≤
      ((loss : ℝ≥0∞) * normalization) * familyVolume F ^ 2 *
        (P.neighborhoodInducedShading R.shading (θ : ℝ)).shadingMass := by
  apply InducedShadingDensityAlgebra.sourceMass_sq_mul_coarseVolume_le
    P Y R hindices loss (θ : ℝ)
      (slabThetaEighthScale C θ)
      ((m : ℝ≥0∞) * slabThetaGrowth θ) normalization
      (slabThetaEighthScale_ne_zero hC hθ)
      (slabThetaEighthScale_ne_top C θ)
      hretained
      (hasFiberCoveringGrowth_of_slabCertificates P R.shading m C θ cert hmult)
      hnormalize

/-- The actual source density squared is controlled by the density of the
actual neighborhood-induced shading at radius `theta`. -/
theorem sourceDensity_sq_le_mul_inducedDensity_of_slabCertificates
    (P : ConvexFactorization F W) (Y : Shading F)
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (loss : ℕ) (m : ℕ) (C θ : ℝ≥0) (normalization : ℝ≥0∞)
    (hC : 1 ≤ C) (hθ : 0 < θ)
    (hcoarse_zero : familyVolume W ≠ 0)
    (cert : ∀ k ∈ P.index.coarse,
      SlabDimensionsCertificate C θ (W k))
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass)
    (hmult : HasActiveFiberMultiplicityBound P R.shading m)
    (hnormalize :
      ((m : ℝ≥0∞) * slabThetaGrowth θ) * familyVolume W *
          Y.shadingDensity ≤
        normalization * slabThetaEighthScale C θ * familyVolume F) :
    Y.shadingDensity ^ 2 ≤
      ((loss : ℝ≥0∞) * normalization) *
        (P.neighborhoodInducedShading R.shading (θ : ℝ)).shadingDensity := by
  apply InducedShadingDensityAlgebra.sourceDensity_sq_le_mul_inducedDensity
    P Y R hindices loss (θ : ℝ)
      (slabThetaEighthScale C θ)
      ((m : ℝ≥0∞) * slabThetaGrowth θ) normalization
      (slabThetaEighthScale_ne_zero hC hθ)
      (slabThetaEighthScale_ne_top C θ)
      hcoarse_zero hretained
      (hasFiberCoveringGrowth_of_slabCertificates P R.shading m C θ cert hmult)
      hnormalize

/-- Safe quotient form of the induced-density lower bound.  No nonzero or
finite assumption is imposed on the explicit loss/normalization factor. -/
theorem sourceDensity_sq_div_loss_le_inducedDensity_of_slabCertificates
    (P : ConvexFactorization F W) (Y : Shading F)
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (loss : ℕ) (m : ℕ) (C θ : ℝ≥0) (normalization : ℝ≥0∞)
    (hC : 1 ≤ C) (hθ : 0 < θ)
    (hcoarse_zero : familyVolume W ≠ 0)
    (cert : ∀ k ∈ P.index.coarse,
      SlabDimensionsCertificate C θ (W k))
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass)
    (hmult : HasActiveFiberMultiplicityBound P R.shading m)
    (hnormalize :
      ((m : ℝ≥0∞) * slabThetaGrowth θ) * familyVolume W *
          Y.shadingDensity ≤
        normalization * slabThetaEighthScale C θ * familyVolume F) :
    Y.shadingDensity ^ 2 / ((loss : ℝ≥0∞) * normalization) ≤
      (P.neighborhoodInducedShading R.shading (θ : ℝ)).shadingDensity := by
  apply ENNReal.div_le_of_le_mul'
  exact sourceDensity_sq_le_mul_inducedDensity_of_slabCertificates
    P Y R hindices loss m C θ normalization hC hθ hcoarse_zero
      cert hretained hmult hnormalize

end CertifiedSlabWeakScaleDensity

end

end Submission.Kakeya.ConvexFactoring
