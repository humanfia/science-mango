import FamilyStickyGrounding.JohnConvexThree2
import FamilyStickyGrounding.JohnDimTwoNondegenerateMaxTriangle1

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

def triangleBarycenter (p q r : Space) : Space :=
  p + (1 / 3 : ℝ) • (q - p) + (1 / 3 : ℝ) • (r - p)

def triangleEdgeDisk (c e₀ e₁ : Space) (R : ℝ) : Set Space :=
  {x | ∃ u v : ℝ, u ^ 2 + v ^ 2 ≤ R ^ 2 ∧ x = c + u • e₀ + v • e₁}

/-- The small coordinate disk about the barycenter is in the triangle, hence
in every convex set containing its vertices. -/
theorem triangleEdgeDisk_inner
    {K : Set Space} (hK : Convex ℝ K)
    {p q r : Space} (hp : p ∈ K) (hq : q ∈ K) (hr : r ∈ K) :
    triangleEdgeDisk (triangleBarycenter p q r) (q - p) (r - p) (1 / 6) ⊆ K := by
  intro x hx
  obtain ⟨u, v, huv, rfl⟩ := hx
  have huSq : u ^ 2 ≤ (1 / 6 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg v]
  have hvSq : v ^ 2 ≤ (1 / 6 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg u]
  have huLower : -(1 / 6 : ℝ) ≤ u := by nlinarith
  have huUpper : u ≤ (1 / 6 : ℝ) := by nlinarith
  have hvLower : -(1 / 6 : ℝ) ≤ v := by nlinarith
  have hvUpper : v ≤ (1 / 6 : ℝ) := by nlinarith
  have hl₀ : 0 ≤ (1 / 3 : ℝ) - u - v := by linarith
  have hl₁ : 0 ≤ (1 / 3 : ℝ) + u := by linarith
  have hl₂ : 0 ≤ (1 / 3 : ℝ) + v := by linarith
  have hmem := convex_three_mem' hK hp hq hr hl₀ hl₁ hl₂ (by ring)
  convert hmem using 1 ; simp [triangleBarycenter] ; module

/-- Maximality bounds every point of the body by a fixed coordinate disk
about the barycenter. -/
theorem maximal_triangle_outer_edgeDisk
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2)
    {p q r : Space}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (hr : r ∈ (K : Set Space))
    (hpos : 0 < triangleArea p q r)
    (hmax : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), triangleArea p' q' r' ≤ triangleArea p q r) :
    (K : Set Space) ⊆
      triangleEdgeDisk (triangleBarycenter p q r) (q - p) (r - p) 2 := by
  intro x hx
  obtain ⟨a, b, hxrep, ha, hb, hzero⟩ :=
    exists_bounded_edge_coordinates_of_maximal_triangle
      K hdim hp hq hr hx hpos hmax
  have ha' := (abs_le.mp ha)
  have hb' := (abs_le.mp hb)
  let u : ℝ := a - 1 / 3
  let v : ℝ := b - 1 / 3
  have huLower : -(4 / 3 : ℝ) ≤ u := by dsimp [u]; linarith
  have huUpper : u ≤ (4 / 3 : ℝ) := by dsimp [u]; linarith
  have hvLower : -(4 / 3 : ℝ) ≤ v := by dsimp [v]; linarith
  have hvUpper : v ≤ (4 / 3 : ℝ) := by dsimp [v]; linarith
  have huProd : 0 ≤ (u + 4 / 3) * (4 / 3 - u) :=
    mul_nonneg (by linarith) (by linarith)
  have hvProd : 0 ≤ (v + 4 / 3) * (4 / 3 - v) :=
    mul_nonneg (by linarith) (by linarith)
  refine ⟨u, v, ?_, ?_⟩
  · nlinarith
  · rw [hxrep]
    simp [triangleBarycenter, u, v]
    module

/-- Actual affine-dimension-two linear-image disk sandwich, selected from a
maximal inscribed triangle. The ratio of the radii is twelve. -/
theorem exists_dimTwo_triangleEdgeDisk_sandwich
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space), ∃ r ∈ (K : Set Space),
      0 < triangleArea p q r ∧
      triangleEdgeDisk (triangleBarycenter p q r) (q - p) (r - p) (1 / 6) ⊆
        (K : Set Space) ∧
      (K : Set Space) ⊆
        triangleEdgeDisk (triangleBarycenter p q r) (q - p) (r - p) 2 := by
  obtain ⟨p, hp, q, hq, r, hr, hpos, hmax⟩ :=
    exists_nondegenerate_maximal_triangle K hdim
  exact ⟨p, hp, q, hq, r, hr, hpos,
    triangleEdgeDisk_inner K.convex hp hq hr,
    maximal_triangle_outer_edgeDisk K hdim hp hq hr hpos hmax⟩

#print axioms triangleEdgeDisk_inner
#print axioms maximal_triangle_outer_edgeDisk
#print axioms exists_dimTwo_triangleEdgeDisk_sandwich

end
end Submission.Kakeya.ConvexGeometry
