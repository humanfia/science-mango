import FamilyStickyGrounding.JohnDimThreeEdgeCoordinates1

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- Maximality bounds the coefficient of the fourth edge in any affine edge
representation. -/
theorem abs_fourthCoeff_le_one_of_maximal_tetrahedron
    (K : ConvexBody Space) {p q r s x : Space} {a b c : ℝ}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (hr : r ∈ (K : Set Space)) (_hs : s ∈ (K : Set Space))
    (hx : x ∈ (K : Set Space))
    (hmax : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
        tetraVolume p' q' r' s' ≤ tetraVolume p q r s)
    (hpos : 0 < tetraVolume p q r s)
    (hxrep : x =
      p + a • (q - p) + b • (r - p) + c • (s - p)) :
    |c| ≤ 1 := by
  have hineq := hmax p hp q hq r hr x hx
  rw [hxrep, tetraVolume_affine_edge_combination_fourth] at hineq
  nlinarith [abs_nonneg c]

/-- All four barycentric coefficients of a point of `K`, relative to a
positive-volume maximal inscribed tetrahedron, have absolute value at most
one. -/
theorem exists_bounded_tetra_edge_coordinates_of_maximal_tetrahedron
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3)
    {p q r s x : Space}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (hr : r ∈ (K : Set Space)) (hs : s ∈ (K : Set Space))
    (hx : x ∈ (K : Set Space))
    (hpos : 0 < tetraVolume p q r s)
    (hmax : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
        tetraVolume p' q' r' s' ≤ tetraVolume p q r s) :
    ∃ a b c : ℝ,
      x = p + a • (q - p) + b • (r - p) + c • (s - p) ∧
      |a| ≤ 1 ∧ |b| ≤ 1 ∧ |c| ≤ 1 ∧ |1 - a - b - c| ≤ 1 := by
  obtain ⟨a, b, c, hxrep⟩ :=
    exists_tetra_edge_coordinates K hdim hp hq hr hs hx hpos
  let d : ℝ := 1 - a - b - c
  have hc : |c| ≤ 1 :=
    abs_fourthCoeff_le_one_of_maximal_tetrahedron K hp hq hr hs hx
      hmax hpos hxrep
  have hmax₁ : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
        tetraVolume p' q' r' s' ≤ tetraVolume q r s p := by
    intro p' hp' q' hq' r' hr' s' hs'
    rw [tetraVolume_cycle_vertices p q r s]
    exact hmax p' hp' q' hq' r' hr' s' hs'
  have hpos₁ : 0 < tetraVolume q r s p := by
    rw [tetraVolume_cycle_vertices p q r s]
    exact hpos
  have hxrep₁ : x =
      q + b • (r - q) + c • (s - q) + d • (p - q) := by
    rw [hxrep]
    simp only [d]
    module
  have hd : |d| ≤ 1 :=
    abs_fourthCoeff_le_one_of_maximal_tetrahedron K hq hr hs hp hx
      hmax₁ hpos₁ hxrep₁
  have hmax₂ : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
        tetraVolume p' q' r' s' ≤ tetraVolume r s p q := by
    intro p' hp' q' hq' r' hr' s' hs'
    rw [tetraVolume_cycle_vertices q r s p,
      tetraVolume_cycle_vertices p q r s]
    exact hmax p' hp' q' hq' r' hr' s' hs'
  have hpos₂ : 0 < tetraVolume r s p q := by
    rw [tetraVolume_cycle_vertices q r s p,
      tetraVolume_cycle_vertices p q r s]
    exact hpos
  have hxrep₂ : x =
      r + c • (s - r) + d • (p - r) + a • (q - r) := by
    rw [hxrep]
    simp only [d]
    module
  have ha : |a| ≤ 1 :=
    abs_fourthCoeff_le_one_of_maximal_tetrahedron K hr hs hp hq hx
      hmax₂ hpos₂ hxrep₂
  have hmax₃ : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
        tetraVolume p' q' r' s' ≤ tetraVolume s p q r := by
    intro p' hp' q' hq' r' hr' s' hs'
    rw [tetraVolume_cycle_vertices r s p q,
      tetraVolume_cycle_vertices q r s p,
      tetraVolume_cycle_vertices p q r s]
    exact hmax p' hp' q' hq' r' hr' s' hs'
  have hpos₃ : 0 < tetraVolume s p q r := by
    rw [tetraVolume_cycle_vertices r s p q,
      tetraVolume_cycle_vertices q r s p,
      tetraVolume_cycle_vertices p q r s]
    exact hpos
  have hxrep₃ : x =
      s + d • (p - s) + a • (q - s) + b • (r - s) := by
    rw [hxrep]
    simp only [d]
    module
  have hb : |b| ≤ 1 :=
    abs_fourthCoeff_le_one_of_maximal_tetrahedron K hs hp hq hr hx
      hmax₃ hpos₃ hxrep₃
  exact ⟨a, b, c, hxrep, ha, hb, hc, by simpa [d] using hd⟩

#print axioms abs_fourthCoeff_le_one_of_maximal_tetrahedron
#print axioms exists_bounded_tetra_edge_coordinates_of_maximal_tetrahedron

end
end Submission.Kakeya.ConvexGeometry
