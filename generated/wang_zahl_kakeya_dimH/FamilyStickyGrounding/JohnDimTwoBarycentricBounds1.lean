import FamilyStickyGrounding.JohnDimTwoEdgeCoordinates4
import FamilyStickyGrounding.JohnTriangleBarycentricBound2
import FamilyStickyGrounding.JohnTriangleSymmetry3

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- Every point of a body lies in the bounded barycentric-coordinate region
of a nondegenerate maximal inscribed triangle. -/
theorem exists_bounded_edge_coordinates_of_maximal_triangle
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2)
    {p q r x : Space}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (hr : r ∈ (K : Set Space)) (hx : x ∈ (K : Set Space))
    (hpos : 0 < triangleArea p q r)
    (hmax : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), triangleArea p' q' r' ≤ triangleArea p q r) :
    ∃ a b : ℝ,
      x = p + a • (q - p) + b • (r - p) ∧
      |a| ≤ 1 ∧ |b| ≤ 1 ∧ |1 - a - b| ≤ 1 := by
  obtain ⟨a, b, hxrep⟩ := exists_edge_coordinates K hdim hp hq hr hx hpos
  have hb : |b| ≤ 1 :=
    abs_edgeCoeff_le_one_of_maximal_triangle K hp hq hr hx hmax hpos hxrep
  have hmaxSwap : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), triangleArea p' q' r' ≤ triangleArea p r q := by
    intro p' hp' q' hq' r' hr'
    rw [triangleArea_swap_last p q r]
    exact hmax p' hp' q' hq' r' hr'
  have hposSwap : 0 < triangleArea p r q := by
    rw [triangleArea_swap_last]
    exact hpos
  have hxrepSwap : x = p + b • (r - p) + a • (q - p) := by
    rw [hxrep]
    abel
  have ha : |a| ≤ 1 :=
    abs_edgeCoeff_le_one_of_maximal_triangle K hp hr hq hx
      hmaxSwap hposSwap hxrepSwap
  have hmaxCycle : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), triangleArea p' q' r' ≤ triangleArea q r p := by
    intro p' hp' q' hq' r' hr'
    rw [triangleArea_cycle p q r]
    exact hmax p' hp' q' hq' r' hr'
  have hposCycle : 0 < triangleArea q r p := by
    rw [triangleArea_cycle]
    exact hpos
  have hxrepCycle : x = q + b • (r - q) + (1 - a - b) • (p - q) := by
    rw [hxrep]
    module
  have hzero : |1 - a - b| ≤ 1 :=
    abs_edgeCoeff_le_one_of_maximal_triangle K hq hr hp hx
      hmaxCycle hposCycle hxrepCycle
  exact ⟨a, b, hxrep, ha, hb, hzero⟩

#print axioms exists_bounded_edge_coordinates_of_maximal_triangle

end
end Submission.Kakeya.ConvexGeometry
