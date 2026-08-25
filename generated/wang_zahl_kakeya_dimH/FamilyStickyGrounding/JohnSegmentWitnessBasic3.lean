import FamilyStickyGrounding.JohnDimOneSegment3

open scoped NNReal InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

def segmentUnitDirection (p q : Space) : Space :=
  (‖q - p‖ : ℝ)⁻¹ • (q - p)

def segmentAxisRadius (p q : Space) : ℝ≥0 :=
  ⟨‖q - p‖ / 2, div_nonneg (norm_nonneg _) (by norm_num)⟩

theorem norm_segmentUnitDirection {p q : Space} (hpq : p ≠ q) :
    ‖segmentUnitDirection p q‖ = 1 := by
  have hnorm : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpq.symm)
  simp [segmentUnitDirection, norm_smul, hnorm]

theorem segmentAxisRadius_smul_unitDirection {p q : Space} (hpq : p ≠ q) :
    (segmentAxisRadius p q : ℝ) • segmentUnitDirection p q =
      (2 : ℝ)⁻¹ • (q - p) := by
  have hnorm : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpq.symm)
  change (‖q - p‖ / 2 : ℝ) • ((‖q - p‖ : ℝ)⁻¹ • (q - p)) =
    (2 : ℝ)⁻¹ • (q - p)
  rw [smul_smul]
  congr 1
  field_simp [hnorm]

#print axioms norm_segmentUnitDirection
#print axioms segmentAxisRadius_smul_unitDirection

end
end Submission.Kakeya.ConvexGeometry
