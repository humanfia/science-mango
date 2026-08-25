import FamilyStickyGrounding.JohnMaxTriangleCompact3
import FamilyStickyGrounding.JohnDimTwoPositiveTriangle2

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- In affine dimension two, a maximal inscribed triangle can be selected
with strictly positive area. -/
theorem exists_nondegenerate_maximal_triangle
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space), ∃ r ∈ (K : Set Space),
      0 < triangleArea p q r ∧
      ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space), ∀ r' ∈ (K : Set Space),
        triangleArea p' q' r' ≤ triangleArea p q r := by
  obtain ⟨p, hp, q, hq, r, hr, hmax⟩ := exists_maximal_triangle K
  obtain ⟨p', hp', q', hq', r', hr', hpos'⟩ :=
    exists_positive_triangle_of_finrank_direction_affineSpan_eq_two K hdim
  have hpos : 0 < triangleArea p q r :=
    hpos'.trans_le (hmax p' hp' q' hq' r' hr')
  exact ⟨p, hp, q, hq, r, hr, hpos, hmax⟩

#print axioms exists_nondegenerate_maximal_triangle

end
end Submission.Kakeya.ConvexGeometry
