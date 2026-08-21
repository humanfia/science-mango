import Submission.Kakeya.ConvexFactoring.CordobaAnalytic
import Submission.Kakeya.ConvexFactoring.NonConcentration

open scoped ENNReal NNReal
open MeasureTheory

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

/-!
# Pairwise overlap summation

This module isolates the finite summation step between geometric pairwise
overlap estimates and the analytic Córdoba inequality. The hypotheses keep
the geometric estimate visible: no bound on an individual overlap is inferred
from non-concentration alone.
-/

/-- Explicit majorants for every ordered pair of shaded pieces. -/
structure PairwiseOverlapBound {ι : Type*} {F : ConvexFamily ι}
    (Y : Shading F) where
  majorant : ι → ι → ℝ≥0∞
  pairwise_le : ∀ i j,
    volume (Y.carrier i ∩ Y.carrier j) ≤ majorant i j

namespace PairwiseOverlapBound

variable {ι : Type*} {F : ConvexFamily ι} {Y : Shading F}

/-- Summing the pointwise overlap estimates over all ordered pairs. -/
theorem overlapSum_le_majorantSum [Fintype ι]
    (B : PairwiseOverlapBound Y) :
    (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      ∑ i, ∑ j, B.majorant i j := by
  classical
  exact Finset.sum_le_sum fun i _ ↦
    Finset.sum_le_sum fun j _ ↦ B.pairwise_le i j

/-- A supplied total majorant immediately bounds the overlap sum. -/
theorem overlapSum_le_factor_mul_shadingMass_of_total_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q : ℝ≥0∞)
    (htotal : (∑ i, ∑ j, B.majorant i j) ≤ Q * Y.shadingMass) :
    (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      Q * Y.shadingMass :=
  B.overlapSum_le_majorantSum.trans htotal

/-- Row bounds sum to a total bound by `Q` times shaded mass. -/
theorem majorantSum_le_factor_mul_shadingMass_of_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q : ℝ≥0∞)
    (hrow : ∀ i, (∑ j, B.majorant i j) ≤ Q * volume (Y.carrier i)) :
    (∑ i, ∑ j, B.majorant i j) ≤ Q * Y.shadingMass := by
  classical
  calc
    (∑ i, ∑ j, B.majorant i j)
        ≤ ∑ i, Q * volume (Y.carrier i) :=
      Finset.sum_le_sum fun i _ ↦ hrow i
    _ = Q * Y.shadingMass := by
      simp [Shading.shadingMass, Finset.mul_sum]

/-- Pairwise estimates plus uniform row estimates bound the overlap sum. -/
theorem overlapSum_le_factor_mul_shadingMass_of_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q : ℝ≥0∞)
    (hrow : ∀ i, (∑ j, B.majorant i j) ≤ Q * volume (Y.carrier i)) :
    (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      Q * Y.shadingMass :=
  B.overlapSum_le_factor_mul_shadingMass_of_total_le Q
    (B.majorantSum_le_factor_mul_shadingMass_of_row_le Q hrow)

/-- The same row hypotheses control the second multiplicity moment. -/
theorem secondMoment_le_factor_mul_shadingMass_of_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q : ℝ≥0∞)
    (hrow : ∀ i, (∑ j, B.majorant i j) ≤ Q * volume (Y.carrier i)) :
    (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) ≤
      Q * Y.shadingMass := by
  rw [lintegral_pointMultiplicity_sq Y]
  exact B.overlapSum_le_factor_mul_shadingMass_of_row_le Q hrow

/-- The finite overlap summation layer followed by the Córdoba union bound. -/
theorem shadingMass_le_factor_mul_volume_shadedUnion_of_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q : ℝ≥0∞)
    (hrow : ∀ i, (∑ j, B.majorant i j) ≤ Q * volume (Y.carrier i)) :
    Y.shadingMass ≤ Q * volume Y.shadedUnion :=
  shadingMass_le_factor_mul_volume_shadedUnion_of_overlapSum_le Y Q
    (B.overlapSum_le_factor_mul_shadingMass_of_row_le Q hrow)

/-- Safe quotient-form union lower bound from the row estimates. -/
theorem shadingMass_div_factor_le_volume_shadedUnion_of_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q : ℝ≥0∞)
    (hrow : ∀ i, (∑ j, B.majorant i j) ≤ Q * volume (Y.carrier i)) :
    Y.shadingMass / Q ≤ volume Y.shadedUnion :=
  mass_div_factor_le_unionVolume_of_mass_le_factor_mul
    (B.shadingMass_le_factor_mul_volume_shadedUnion_of_row_le Q hrow)

/-- A cross-multiplied row estimate may be cancelled only when its common
factor is nonzero and finite. -/
theorem row_le_of_cross_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q D : ℝ≥0∞)
    (hD_zero : D ≠ 0) (hD_top : D ≠ ∞)
    (hcross : ∀ i,
      (∑ j, B.majorant i j) * D ≤
        (Q * volume (Y.carrier i)) * D) :
    ∀ i, (∑ j, B.majorant i j) ≤ Q * volume (Y.carrier i) := by
  intro i
  apply (ENNReal.mul_le_mul_iff_left hD_zero hD_top).mp
  simpa [mul_comm] using hcross i

/-- Cross-multiplied row estimates give the division-free overlap bound. -/
theorem overlapSum_le_factor_mul_shadingMass_of_cross_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q D : ℝ≥0∞)
    (hD_zero : D ≠ 0) (hD_top : D ≠ ∞)
    (hcross : ∀ i,
      (∑ j, B.majorant i j) * D ≤
        (Q * volume (Y.carrier i)) * D) :
    (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      Q * Y.shadingMass :=
  B.overlapSum_le_factor_mul_shadingMass_of_row_le Q
    (B.row_le_of_cross_row_le Q D hD_zero hD_top hcross)

/-- Cross-multiplied row estimates followed by the Córdoba union bound. -/
theorem shadingMass_le_factor_mul_volume_shadedUnion_of_cross_row_le [Fintype ι]
    (B : PairwiseOverlapBound Y) (Q D : ℝ≥0∞)
    (hD_zero : D ≠ 0) (hD_top : D ≠ ∞)
    (hcross : ∀ i,
      (∑ j, B.majorant i j) * D ≤
        (Q * volume (Y.carrier i)) * D) :
    Y.shadingMass ≤ Q * volume Y.shadedUnion :=
  shadingMass_le_factor_mul_volume_shadedUnion_of_overlapSum_le Y Q
    (B.overlapSum_le_factor_mul_shadingMass_of_cross_row_le
      Q D hD_zero hD_top hcross)

/-- The contribution of one active family member when it is contained in the
chosen row container. Packaging the conditional as a noncomputable function
keeps classical decidability out of downstream theorem signatures. -/
noncomputable def activeContainedVolume [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space)
    (j : ι) : ℝ≥0∞ := by
  classical
  exact if j ∈ active ∩ containedIndices F K
    then volume (F j : Set Space) else 0

/-- The sum of the supported contributions is exactly `containedMassOn`. -/
theorem sum_activeContainedVolume [Fintype ι]
    (F : ConvexFamily ι) (active : Finset ι) (K : ConvexBody Space) :
    (∑ j, activeContainedVolume F active K j) = containedMassOn F active K := by
  classical
  unfold activeContainedVolume containedMassOn
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro j hj
    rfl

/-- If a row majorant is supported on active bodies contained in `K`, it is
bounded by the active contained mass used by `IsKatzTaoOn`. -/
theorem rowMajorant_le_containedMassOn [Fintype ι]
    (B : PairwiseOverlapBound Y) (active : Finset ι)
    (K : ConvexBody Space) (i : ι)
    (hsupport : ∀ j,
      B.majorant i j ≤ activeContainedVolume F active K j) :
    (∑ j, B.majorant i j) ≤ containedMassOn F active K := by
  classical
  calc
    (∑ j, B.majorant i j) ≤
        ∑ j, activeContainedVolume F active K j :=
      Finset.sum_le_sum fun j _ ↦ hsupport j
    _ = containedMassOn F active K := sum_activeContainedVolume F active K

/-- Katz--Tao on each interaction row, plus a scale comparison between its
container and the shaded piece, supplies the uniform row estimate. -/
theorem row_le_of_isKatzTaoOn [Fintype ι]
    (B : PairwiseOverlapBound Y) (C A : ℝ≥0∞)
    (active : ι → Finset ι) (K : ι → ConvexBody Space)
    (hKT : ∀ i, IsKatzTaoOn C F (active i))
    (hsupport : ∀ i j,
      B.majorant i j ≤ activeContainedVolume F (active i) (K i) j)
    (hscale : ∀ i, volume (K i : Set Space) ≤ A * volume (Y.carrier i)) :
    ∀ i, (∑ j, B.majorant i j) ≤ (C * A) * volume (Y.carrier i) := by
  intro i
  calc
    (∑ j, B.majorant i j) ≤ containedMassOn F (active i) (K i) :=
      B.rowMajorant_le_containedMassOn (active i) (K i) i (hsupport i)
    _ ≤ C * volume (K i : Set Space) := hKT i (K i)
    _ ≤ C * (A * volume (Y.carrier i)) := by
      exact mul_le_mul' le_rfl (hscale i)
    _ = (C * A) * volume (Y.carrier i) := by
      ac_rfl

/-- The complete Katz--Tao-to-overlap finite summation step. -/
theorem overlapSum_le_katzTao_mul_scale_mul_shadingMass [Fintype ι]
    (B : PairwiseOverlapBound Y) (C A : ℝ≥0∞)
    (active : ι → Finset ι) (K : ι → ConvexBody Space)
    (hKT : ∀ i, IsKatzTaoOn C F (active i))
    (hsupport : ∀ i j,
      B.majorant i j ≤ activeContainedVolume F (active i) (K i) j)
    (hscale : ∀ i, volume (K i : Set Space) ≤ A * volume (Y.carrier i)) :
    (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      (C * A) * Y.shadingMass :=
  B.overlapSum_le_factor_mul_shadingMass_of_row_le (C * A)
    (B.row_le_of_isKatzTaoOn C A active K hKT hsupport hscale)

/-- The complete Katz--Tao row argument followed by the Córdoba union bound. -/
theorem shadingMass_le_katzTao_mul_scale_mul_volume_shadedUnion [Fintype ι]
    (B : PairwiseOverlapBound Y) (C A : ℝ≥0∞)
    (active : ι → Finset ι) (K : ι → ConvexBody Space)
    (hKT : ∀ i, IsKatzTaoOn C F (active i))
    (hsupport : ∀ i j,
      B.majorant i j ≤ activeContainedVolume F (active i) (K i) j)
    (hscale : ∀ i, volume (K i : Set Space) ≤ A * volume (Y.carrier i)) :
    Y.shadingMass ≤ (C * A) * volume Y.shadedUnion :=
  shadingMass_le_factor_mul_volume_shadedUnion_of_overlapSum_le Y (C * A)
    (B.overlapSum_le_katzTao_mul_scale_mul_shadingMass
      C A active K hKT hsupport hscale)

end PairwiseOverlapBound

end Submission.Kakeya.ConvexFactoring
