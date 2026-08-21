import Submission.Kakeya.ConvexFactoring.NeighborhoodInducedShading
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement

/-!
# Algebraic induced-shading density bridge

This module isolates the measure algebra behind the induced-shading
density step.  The only geometric input is a cross-multiplied covering-growth
estimate on every active fiber.  Its derivation from the existing set-level
packing theorem still requires a fiberwise union/multiplicity estimate and
the comparison between the full thickening and its intersection with the
coarse body.

All summation and density conclusions below are derived from that local
input, an actual `WithinFactor` refinement, and an explicit coarse-family
normalization.  No induced-density conclusion is stored as a hypothesis.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

namespace InducedShadingDensityAlgebra

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
variable {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- Multiplicity-counted shaded mass inside one actual factorization fiber. -/
def fiberShadingMass (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) : ℝ≥0∞ :=
  ∑ i ∈ P.index.fiber k, volume (Y.carrier i)

/-- Total volume of the active coarse bodies.  The density denominator
`familyVolume W` may be larger because it also counts inactive indices. -/
def activeCoarseVolume (P : ConvexFactorization F W) : ℝ≥0∞ :=
  ∑ k ∈ P.index.coarse, volume (W k : Set Space)

omit [DecidableEq ι] in
/-- Shading density multiplied by its finite family-volume denominator
recovers shading mass, including when the family volume is zero. -/
theorem shadingDensity_mul_familyVolume (Y : Shading F) :
    Y.shadingDensity * familyVolume F = Y.shadingMass := by
  by_cases hzero : familyVolume F = 0
  · have hmass : Y.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp (Y.shadingMass_le_familyVolume.trans_eq hzero)
    simp [Shading.shadingDensity, hzero, hmass]
  · unfold Shading.shadingDensity
    exact ENNReal.div_mul_cancel hzero (familyVolume_ne_top F)

omit [Fintype κ] in
/-- If a genuine indexed refinement is supported on the active fine set, its
total mass is exactly the sum of the actual fiber masses. -/
theorem refinement_shadingMass_eq_sum_fiberShadingMass
    (P : ConvexFactorization F W) {Y : Shading F}
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine) :
    R.shading.shadingMass =
      ∑ k ∈ P.index.coarse, fiberShadingMass P R.shading k := by
  classical
  unfold Shading.shadingMass
  calc
    (∑ i, volume (R.shading.carrier i)) =
        ∑ i ∈ P.index.fine, volume (R.shading.carrier i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _hi hifine
      have hiR : i ∉ R.indices := fun hi => hifine (hindices hi)
      rw [R.carrier_eq_empty_of_not_mem i hiR]
      simp
    _ = ∑ k ∈ P.index.coarse,
        fiberShadingMass P R.shading k := by
      simpa [fiberShadingMass] using
        P.index.sum_fiberwise
          (fun i => volume (R.shading.carrier i))

/-- The minimal geometric input left by the current library: each active
fiber's multiplicity-counted mass satisfies a division-free covering-growth
estimate into the actual neighborhood-induced carrier. -/
def HasFiberCoveringGrowth
    (P : ConvexFactorization F W) (Y : Shading F)
    (r : ℝ) (scale growth : ℝ≥0∞) : Prop :=
  ∀ k ∈ P.index.coarse,
    fiberShadingMass P Y k * scale ≤
      growth * volume ((P.neighborhoodInducedShading Y r).carrier k)

/-- Summing actual fiber covering growth bounds the refined mass by the
actual neighborhood-induced shading mass. -/
theorem refinement_shadingMass_mul_scale_le_inducedMass
    (P : ConvexFactorization F W) {Y : Shading F}
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (r : ℝ) (scale growth : ℝ≥0∞)
    (hgrowth : HasFiberCoveringGrowth P R.shading r scale growth) :
    R.shading.shadingMass * scale ≤
      growth * (P.neighborhoodInducedShading R.shading r).shadingMass := by
  rw [refinement_shadingMass_eq_sum_fiberShadingMass P R hindices]
  calc
    (∑ k ∈ P.index.coarse, fiberShadingMass P R.shading k) * scale =
        ∑ k ∈ P.index.coarse,
          fiberShadingMass P R.shading k * scale := by
      rw [Finset.sum_mul]
    _ ≤ ∑ k ∈ P.index.coarse,
        growth *
          volume ((P.neighborhoodInducedShading R.shading r).carrier k) := by
      exact Finset.sum_le_sum fun k hk => hgrowth k hk
    _ = growth * ∑ k ∈ P.index.coarse,
        volume ((P.neighborhoodInducedShading R.shading r).carrier k) := by
      rw [Finset.mul_sum]
    _ ≤ growth *
        (P.neighborhoodInducedShading R.shading r).shadingMass := by
      exact mul_le_mul' le_rfl (by
        unfold Shading.shadingMass
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _))

/-- Actual retained mass and fiber covering growth combine without any
division or cancellation. -/
theorem source_shadingMass_mul_scale_le_inducedMass
    (P : ConvexFactorization F W) (Y : Shading F)
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (loss : ℕ) (r : ℝ) (scale growth : ℝ≥0∞)
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass)
    (hgrowth : HasFiberCoveringGrowth P R.shading r scale growth) :
    Y.shadingMass * scale ≤
      (loss : ℝ≥0∞) * growth *
        (P.neighborhoodInducedShading R.shading r).shadingMass := by
  have hsum :=
    refinement_shadingMass_mul_scale_le_inducedMass
      P R hindices r scale growth hgrowth
  unfold WithinFactor at hretained
  calc
    Y.shadingMass * scale ≤
        (loss • R.shading.shadingMass) * scale :=
      mul_le_mul' hretained le_rfl
    _ = (loss : ℝ≥0∞) *
        (R.shading.shadingMass * scale) := by
      simp only [nsmul_eq_mul]
      ac_rfl
    _ ≤ (loss : ℝ≥0∞) *
        (growth *
          (P.neighborhoodInducedShading R.shading r).shadingMass) :=
      mul_le_mul' le_rfl hsum
    _ = (loss : ℝ≥0∞) * growth *
        (P.neighborhoodInducedShading R.shading r).shadingMass := by
      ac_rfl

/-- The fully cross-multiplied GWZ-style conclusion.  The normalization says
that the covering-growth cost, after weighting by the source density and the
coarse family volume, is controlled at the covering scale by the fine family
volume. -/
theorem sourceMass_sq_mul_coarseVolume_le
    (P : ConvexFactorization F W) (Y : Shading F)
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (loss : ℕ) (r : ℝ) (scale growth normalization : ℝ≥0∞)
    (hscale_zero : scale ≠ 0) (hscale_top : scale ≠ ∞)
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass)
    (hgrowth : HasFiberCoveringGrowth P R.shading r scale growth)
    (hnormalize :
      growth * familyVolume W * Y.shadingDensity ≤
        normalization * scale * familyVolume F) :
    Y.shadingMass ^ 2 * familyVolume W ≤
      ((loss : ℝ≥0∞) * normalization) * familyVolume F ^ 2 *
        (P.neighborhoodInducedShading R.shading r).shadingMass := by
  have hmass :=
    source_shadingMass_mul_scale_le_inducedMass
      P Y R hindices loss r scale growth hretained hgrowth
  have hnormalizeMass :
      growth * Y.shadingMass * familyVolume W ≤
        normalization * scale * familyVolume F ^ 2 := by
    calc
      growth * Y.shadingMass * familyVolume W =
          (growth * familyVolume W * Y.shadingDensity) *
            familyVolume F := by
        rw [← shadingDensity_mul_familyVolume Y]
        ac_rfl
      _ ≤ (normalization * scale * familyVolume F) *
          familyVolume F :=
        mul_le_mul' hnormalize le_rfl
      _ = normalization * scale * familyVolume F ^ 2 := by
        rw [pow_two]
        ac_rfl
  apply (ENNReal.mul_le_mul_iff_left hscale_zero hscale_top).mp
  calc
    (Y.shadingMass ^ 2 * familyVolume W) * scale =
        (Y.shadingMass * scale) *
          (Y.shadingMass * familyVolume W) := by
      rw [pow_two]
      ac_rfl
    _ ≤ ((loss : ℝ≥0∞) * growth *
          (P.neighborhoodInducedShading R.shading r).shadingMass) *
        (Y.shadingMass * familyVolume W) :=
      mul_le_mul' hmass le_rfl
    _ = (loss : ℝ≥0∞) *
        (P.neighborhoodInducedShading R.shading r).shadingMass *
          (growth * Y.shadingMass * familyVolume W) := by
      ac_rfl
    _ ≤ (loss : ℝ≥0∞) *
        (P.neighborhoodInducedShading R.shading r).shadingMass *
          (normalization * scale * familyVolume F ^ 2) :=
      mul_le_mul' le_rfl hnormalizeMass
    _ = (((loss : ℝ≥0∞) * normalization) * familyVolume F ^ 2 *
        (P.neighborhoodInducedShading R.shading r).shadingMass) * scale := by
      ac_rfl

/-- A finite-denominator algebra lemma turning the cross-multiplied square
bound into a density inequality.  A zero fine-family volume is handled from
`mass ≤ familyVolume`; only the coarse denominator must explicitly be
nonzero. -/
theorem density_sq_le_factor_mul_of_cross
    {mass fineVolume inducedMass coarseVolume factor : ℝ≥0∞}
    (hmass : mass ≤ fineVolume)
    (hfine_top : fineVolume ≠ ∞)
    (hcoarse_zero : coarseVolume ≠ 0)
    (hcoarse_top : coarseVolume ≠ ∞)
    (hcross :
      mass ^ 2 * coarseVolume ≤
        factor * fineVolume ^ 2 * inducedMass) :
    (mass / fineVolume) ^ 2 ≤ factor * (inducedMass / coarseVolume) := by
  by_cases hfine_zero : fineVolume = 0
  · have hmass_zero : mass = 0 :=
      nonpos_iff_eq_zero.mp (hmass.trans_eq hfine_zero)
    simp [hmass_zero, hfine_zero]
  · have hdivpow :
        (mass / fineVolume) ^ 2 = mass ^ 2 / fineVolume ^ 2 := by
      simp only [div_eq_mul_inv, ENNReal.inv_pow]
      rw [pow_two, pow_two, pow_two]
      ac_rfl
    rw [hdivpow]
    apply (ENNReal.div_le_iff
      (ENNReal.pow_ne_zero hfine_zero 2)
      (ENNReal.pow_ne_top hfine_top)).2
    have hdiv :
        mass ^ 2 ≤
          (factor * fineVolume ^ 2 * inducedMass) / coarseVolume :=
      (ENNReal.le_div_iff_mul_le
        (Or.inl hcoarse_zero) (Or.inl hcoarse_top)).2 hcross
    calc
      mass ^ 2 ≤
          (factor * fineVolume ^ 2 * inducedMass) / coarseVolume := hdiv
      _ = factor * (inducedMass / coarseVolume) * fineVolume ^ 2 := by
        simp only [div_eq_mul_inv]
        ac_rfl

/-- The source density squared is bounded by the explicit normalization loss
times the actual neighborhood-induced density. -/
theorem sourceDensity_sq_le_mul_inducedDensity
    (P : ConvexFactorization F W) (Y : Shading F)
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (loss : ℕ) (r : ℝ) (scale growth normalization : ℝ≥0∞)
    (hscale_zero : scale ≠ 0) (hscale_top : scale ≠ ∞)
    (hcoarse_zero : familyVolume W ≠ 0)
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass)
    (hgrowth : HasFiberCoveringGrowth P R.shading r scale growth)
    (hnormalize :
      growth * familyVolume W * Y.shadingDensity ≤
        normalization * scale * familyVolume F) :
    Y.shadingDensity ^ 2 ≤
      ((loss : ℝ≥0∞) * normalization) *
        (P.neighborhoodInducedShading R.shading r).shadingDensity := by
  apply density_sq_le_factor_mul_of_cross
    Y.shadingMass_le_familyVolume
    (familyVolume_ne_top F)
    hcoarse_zero
    (familyVolume_ne_top W)
  exact sourceMass_sq_mul_coarseVolume_le
    P Y R hindices loss r scale growth normalization
    hscale_zero hscale_top hretained hgrowth hnormalize

/-- Safe quotient-form induced-density lower bound.  No nonzero or finite
assumption is needed on the explicit loss factor. -/
theorem sourceDensity_sq_div_loss_le_inducedDensity
    (P : ConvexFactorization F W) (Y : Shading F)
    (R : IndexedShadingRefinement Y)
    (hindices : R.indices ⊆ P.index.fine)
    (loss : ℕ) (r : ℝ) (scale growth normalization : ℝ≥0∞)
    (hscale_zero : scale ≠ 0) (hscale_top : scale ≠ ∞)
    (hcoarse_zero : familyVolume W ≠ 0)
    (hretained : WithinFactor loss Y.shadingMass R.shading.shadingMass)
    (hgrowth : HasFiberCoveringGrowth P R.shading r scale growth)
    (hnormalize :
      growth * familyVolume W * Y.shadingDensity ≤
        normalization * scale * familyVolume F) :
    Y.shadingDensity ^ 2 /
        ((loss : ℝ≥0∞) * normalization) ≤
      (P.neighborhoodInducedShading R.shading r).shadingDensity := by
  apply ENNReal.div_le_of_le_mul'
  exact sourceDensity_sq_le_mul_inducedDensity
    P Y R hindices loss r scale growth normalization
    hscale_zero hscale_top hcoarse_zero hretained hgrowth hnormalize

end InducedShadingDensityAlgebra

end

end Submission.Kakeya.ConvexFactoring
