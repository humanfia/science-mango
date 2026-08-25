import FamilyStickyGrounding.FamilyStickyConvexClosedThickeningBoxGrowthV1

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyConvexCertifiedWidthGrowthV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyConvexClosedThickeningBoxGrowthV1

noncomputable section

/-!
# Closed-thickening growth from coordinate width factors

This layer turns a `HasBoxDimensions` inner/outer certificate and three
literal widened-side inequalities into a volume estimate.  Its assumptions
are coordinate geometry, not a renamed volume-ratio conclusion.
-/

/-- If widening the outer frame box by `r` multiplies coordinate `i` by at
most `factor i`, the certified inner box converts the product of those three
factors into a body-volume growth bound. -/
theorem HasBoxDimensions.volume_closedThickening_le_factorProduct
    {C : NNReal} {side factor : Fin 3 → NNReal}
    {K : ConvexBody Space} (h : HasBoxDimensions C side K)
    (r : NNReal)
    (hwiden : ∀ i, side i + 2 * r ≤ factor i * side i) :
    volume (Metric.cthickening (r : Real) (K : Set Space)) ≤
      (((C : ENNReal) ^ 3) * ∏ i, (factor i : ENNReal)) *
        volume (K : Set Space) := by
  rcases h with ⟨hC, B, hBside, hinner, houter⟩
  have hbox : HasBoxDimensions C side K :=
    ⟨hC, B, hBside, hinner, houter⟩
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hcancel :
      ((C : ENNReal) ^ 3) * (((C⁻¹ : NNReal) : ENNReal) ^ 3) = 1 := by
    rw [← mul_pow]
    norm_cast
    simp [hCpos.ne']
  calc
    volume (Metric.cthickening (r : Real) (K : Set Space)) ≤
        ∏ i, ((side i : ENNReal) + 2 * (r : ENNReal)) := by
      simpa [hBside] using
        FamilyStickyConvexClosedThickeningBoxGrowthV1.FrameBox.volume_cthickening_le_prod_side_add_two_mul
          B (K : Set Space) K.isCompact houter r
    _ ≤ ∏ i, ((factor i : ENNReal) * (side i : ENNReal)) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact bot_le
      · intro i hi
        exact_mod_cast hwiden i
    _ = (∏ i, (factor i : ENNReal)) * ∏ i, (side i : ENNReal) := by
      exact Finset.prod_mul_distrib
    _ = (((C : ENNReal) ^ 3) * ∏ i, (factor i : ENNReal)) *
        ((((C⁻¹ : NNReal) : ENNReal) ^ 3) *
          ∏ i, (side i : ENNReal)) := by
      symm
      rw [mul_mul_mul_comm, hcancel, one_mul]
    _ ≤ (((C : ENNReal) ^ 3) * ∏ i, (factor i : ENNReal)) *
        volume (K : Set Space) := by
      gcongr
      exact hbox.volume_lower_bound

#print axioms HasBoxDimensions.volume_closedThickening_le_factorProduct

end
end FamilyStickyConvexCertifiedWidthGrowthV1
