import FamilyStickyGrounding.JohnDimThreeBarycentricBounds1
import FamilyStickyGrounding.JohnMaxTetraCompact1
import Mathlib.Analysis.Convex.Combination

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- In affine dimension three, a maximal inscribed tetrahedron has positive
volume. -/
theorem exists_nondegenerate_maximal_tetrahedron
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space),
      ∃ r ∈ (K : Set Space), ∃ s ∈ (K : Set Space),
        0 < tetraVolume p q r s ∧
        ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
          ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
            tetraVolume p' q' r' s' ≤ tetraVolume p q r s := by
  obtain ⟨p, hp, q, hq, r, hr, s, hs, hmax⟩ :=
    exists_maximal_tetrahedron K
  obtain ⟨p', hp', q', hq', r', hr', s', hs', hpos'⟩ :=
    exists_positive_tetrahedron_of_finrank_direction_affineSpan_eq_three K hdim
  have hpos : 0 < tetraVolume p q r s :=
    hpos'.trans_le (hmax p' hp' q' hq' r' hr' s' hs')
  exact ⟨p, hp, q, hq, r, hr, s, hs, hpos, hmax⟩

/-- A four-point convex combination, specialized to the ambient space. -/
theorem convex_four_mem'
    {K : Set Space} (hK : Convex ℝ K)
    {p q r s : Space} (hp : p ∈ K) (hq : q ∈ K)
    (hr : r ∈ K) (hs : s ∈ K)
    {l₀ l₁ l₂ l₃ : ℝ}
    (hl₀ : 0 ≤ l₀) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hl₃ : 0 ≤ l₃)
    (hsum : l₀ + l₁ + l₂ + l₃ = 1) :
    l₀ • p + l₁ • q + l₂ • r + l₃ • s ∈ K := by
  let w : Fin 4 → ℝ := ![l₀, l₁, l₂, l₃]
  let z : Fin 4 → Space := ![p, q, r, s]
  have hw : ∑ i, w i = l₀ + l₁ + l₂ + l₃ := by
    rw [Fin.sum_univ_four]
    rfl
  have hwz : ∑ i, w i • z i =
      l₀ • p + l₁ • q + l₂ • r + l₃ • s := by
    rw [Fin.sum_univ_four]
    rfl
  have h := hK.sum_mem (t := Finset.univ) (w := w) (z := z) (by
    intro i hi
    fin_cases i <;> simp [w, hl₀, hl₁, hl₂, hl₃]) (by
    rw [hw]
    exact hsum) (by
    intro i hi
    fin_cases i <;> simp [z, hp, hq, hr, hs])
  rw [hwz] at h
  exact h

def tetraBarycenter (p q r s : Space) : Space :=
  p + (1 / 4 : ℝ) • (q - p) + (1 / 4 : ℝ) • (r - p) +
    (1 / 4 : ℝ) • (s - p)

/-- A Euclidean coordinate ball, mapped by the three tetrahedron edge
vectors and centered at `c`. -/
def tetraEdgeBall (c e₀ e₁ e₂ : Space) (R : ℝ) : Set Space :=
  {x | ∃ u v w : ℝ,
    u ^ 2 + v ^ 2 + w ^ 2 ≤ R ^ 2 ∧
    x = c + u • e₀ + v • e₁ + w • e₂}

/-- A radius-`1/12` coordinate ball about the tetrahedron barycenter lies in
the tetrahedron, hence in every convex set containing the four vertices. -/
theorem tetraEdgeBall_inner
    {K : Set Space} (hK : Convex ℝ K)
    {p q r s : Space} (hp : p ∈ K) (hq : q ∈ K)
    (hr : r ∈ K) (hs : s ∈ K) :
    tetraEdgeBall (tetraBarycenter p q r s)
      (q - p) (r - p) (s - p) (1 / 12) ⊆ K := by
  intro x hx
  obtain ⟨u, v, w, huv, rfl⟩ := hx
  have huSq : u ^ 2 ≤ (1 / 12 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg v, sq_nonneg w]
  have hvSq : v ^ 2 ≤ (1 / 12 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg u, sq_nonneg w]
  have hwSq : w ^ 2 ≤ (1 / 12 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg u, sq_nonneg v]
  have huLower : -(1 / 12 : ℝ) ≤ u := by nlinarith
  have huUpper : u ≤ (1 / 12 : ℝ) := by nlinarith
  have hvLower : -(1 / 12 : ℝ) ≤ v := by nlinarith
  have hvUpper : v ≤ (1 / 12 : ℝ) := by nlinarith
  have hwLower : -(1 / 12 : ℝ) ≤ w := by nlinarith
  have hwUpper : w ≤ (1 / 12 : ℝ) := by nlinarith
  have hl₀ : 0 ≤ (1 / 4 : ℝ) - u - v - w := by linarith
  have hl₁ : 0 ≤ (1 / 4 : ℝ) + u := by linarith
  have hl₂ : 0 ≤ (1 / 4 : ℝ) + v := by linarith
  have hl₃ : 0 ≤ (1 / 4 : ℝ) + w := by linarith
  have hmem := convex_four_mem' hK hp hq hr hs hl₀ hl₁ hl₂ hl₃ (by ring)
  convert hmem using 1 ; simp [tetraBarycenter] ; module

/-- Maximality puts every point of `K` in the radius-`9/4` edge-coordinate
ball about the tetrahedron barycenter. -/
theorem maximal_tetrahedron_outer_edgeBall
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3)
    {p q r s : Space}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (hr : r ∈ (K : Set Space)) (hs : s ∈ (K : Set Space))
    (hpos : 0 < tetraVolume p q r s)
    (hmax : ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
      ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
        tetraVolume p' q' r' s' ≤ tetraVolume p q r s) :
    (K : Set Space) ⊆
      tetraEdgeBall (tetraBarycenter p q r s)
        (q - p) (r - p) (s - p) (9 / 4) := by
  intro x hx
  obtain ⟨a, b, c, hxrep, ha, hb, hc, hd⟩ :=
    exists_bounded_tetra_edge_coordinates_of_maximal_tetrahedron
      K hdim hp hq hr hs hx hpos hmax
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  let u : ℝ := a - 1 / 4
  let v : ℝ := b - 1 / 4
  let w : ℝ := c - 1 / 4
  have huLower : -(5 / 4 : ℝ) ≤ u := by dsimp [u]; linarith
  have huUpper : u ≤ (5 / 4 : ℝ) := by dsimp [u]; linarith
  have hvLower : -(5 / 4 : ℝ) ≤ v := by dsimp [v]; linarith
  have hvUpper : v ≤ (5 / 4 : ℝ) := by dsimp [v]; linarith
  have hwLower : -(5 / 4 : ℝ) ≤ w := by dsimp [w]; linarith
  have hwUpper : w ≤ (5 / 4 : ℝ) := by dsimp [w]; linarith
  have huProd : 0 ≤ (u + 5 / 4) * (5 / 4 - u) :=
    mul_nonneg (by linarith) (by linarith)
  have hvProd : 0 ≤ (v + 5 / 4) * (5 / 4 - v) :=
    mul_nonneg (by linarith) (by linarith)
  have hwProd : 0 ≤ (w + 5 / 4) * (5 / 4 - w) :=
    mul_nonneg (by linarith) (by linarith)
  refine ⟨u, v, w, ?_, ?_⟩
  · nlinarith
  · rw [hxrep]
    simp [tetraBarycenter, u, v, w]
    module

/-- Actual affine-dimension-three linear-image ball sandwich selected from a
maximal inscribed tetrahedron.  The radius ratio is `27`. -/
theorem exists_dimThree_tetraEdgeBall_sandwich
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space),
      ∃ r ∈ (K : Set Space), ∃ s ∈ (K : Set Space),
        0 < tetraVolume p q r s ∧
        tetraEdgeBall (tetraBarycenter p q r s)
          (q - p) (r - p) (s - p) (1 / 12) ⊆ (K : Set Space) ∧
        (K : Set Space) ⊆
          tetraEdgeBall (tetraBarycenter p q r s)
            (q - p) (r - p) (s - p) (9 / 4) := by
  obtain ⟨p, hp, q, hq, r, hr, s, hs, hpos, hmax⟩ :=
    exists_nondegenerate_maximal_tetrahedron K hdim
  exact ⟨p, hp, q, hq, r, hr, s, hs, hpos,
    tetraEdgeBall_inner K.convex hp hq hr hs,
    maximal_tetrahedron_outer_edgeBall K hdim hp hq hr hs hpos hmax⟩

#print axioms exists_nondegenerate_maximal_tetrahedron
#print axioms convex_four_mem'
#print axioms tetraEdgeBall_inner
#print axioms maximal_tetrahedron_outer_edgeBall
#print axioms exists_dimThree_tetraEdgeBall_sandwich

end
end Submission.Kakeya.ConvexGeometry
