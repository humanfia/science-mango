import FamilyStickyGrounding.JohnTriangleReplacement1

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- Replacing the third vertex of a nondegenerate maximal triangle bounds
the corresponding affine edge coefficient by one in absolute value. -/
theorem abs_edgeCoeff_le_one_of_maximal_triangle
    (K : ConvexBody Space) {p q r x : Space} {a b : ℝ}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (_hr : r ∈ (K : Set Space)) (hx : x ∈ (K : Set Space))
    (hmax : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), triangleArea p' q' r' ≤ triangleArea p q r)
    (hpos : 0 < triangleArea p q r)
    (hxrep : x = p + a • (q - p) + b • (r - p)) :
    |b| ≤ 1 := by
  have hreplace := hmax p hp q hq x hx
  rw [hxrep, triangleArea_affine_edge_combination] at hreplace
  nlinarith [abs_nonneg b]

#print axioms abs_edgeCoeff_le_one_of_maximal_triangle

end
end Submission.Kakeya.ConvexGeometry
