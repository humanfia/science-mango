import FamilyStickyGrounding.JohnActualDimThreeCertificate2
import FamilyStickyGrounding.JohnSideLowerCleanAdapterV1
import Mathlib.Analysis.Convex.Measure

open scoped NNReal
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# A captured-tube adapter for the dimension-three John certificate

This adapter avoids the finite-dyadic and greedy-occurrence branches.  A
positive-radius tube directly makes its containing convex body
full-dimensional, and the direct transverse side bound makes every side of
the resulting certificate positive.
-/

/-- A convex body containing a positive-radius tube is full-dimensional. -/
theorem finrank_direction_affineSpan_eq_three_of_tube_subset_clean
    {K : ConvexBody Space} {delta : NNReal} (T : Tube delta)
    (hdelta : 0 < delta) (hTK : T.carrier ⊆ (K : Set Space)) :
    Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3 := by
  have hball : Metric.ball T.axis.base (delta : ℝ) ⊆ (K : Set Space) := by
    intro x hx
    apply hTK
    exact Metric.closedBall_subset_cthickening
      T.axis.base_mem_carrier (delta : ℝ) (Metric.ball_subset_closedBall hx)
  have hbase : T.axis.base ∈ interior (K : Set Space) := by
    apply interior_mono hball
    rw [Metric.isOpen_ball.interior_eq]
    exact Metric.mem_ball_self (NNReal.coe_pos.2 hdelta)
  have hopenSpan : affineSpan ℝ (interior (K : Set Space)) = ⊤ :=
    isOpen_interior.affineSpan_eq_top ⟨T.axis.base, hbase⟩
  have hspan : affineSpan ℝ (K : Set Space) = ⊤ := by
    apply top_unique
    rw [← hopenSpan]
    exact affineSpan_mono ℝ interior_subset
  rw [hspan, AffineSubspace.direction_top, finrank_top]
  simp [Space]

/-- A positive-radius captured tube supplies an actual dimension-three John
certificate, while the direct side bound supplies positivity of all sides. -/
theorem exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean
    (K : ConvexBody Space) {delta : NNReal} (T : Tube delta)
    (hdelta : 0 < delta) (hTK : T.carrier ⊆ (K : Set Space)) :
    ∃ side : Fin 3 → NNReal,
      (∀ i, 0 < side i) ∧ Nonempty (BoxDimensionsCertificate 288 side K) := by
  obtain ⟨side, ⟨cert⟩⟩ :=
    exists_boxDimensionsCertificate_288_of_finrank_direction_affineSpan_eq_three2 K
      (finrank_direction_affineSpan_eq_three_of_tube_subset_clean T hdelta hTK)
  refine ⟨side, ?_, ⟨cert⟩⟩
  intro i
  have hside : 2 * delta ≤ side i :=
    JohnSideLowerFinal.boxCertificate_side_lower_of_tube_subset T hTK cert i
  exact (mul_pos (by norm_num) hdelta).trans_le hside

#print axioms finrank_direction_affineSpan_eq_three_of_tube_subset_clean
#print axioms exists_positive_boxDimensionsCertificate_288_of_tube_subset_clean

end
end Submission.Kakeya.ConvexGeometry
