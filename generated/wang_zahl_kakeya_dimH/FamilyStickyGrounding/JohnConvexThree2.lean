import FamilyStickyGrounding.JohnDimTwoBarycentricBounds1
import Mathlib.Analysis.Convex.Combination

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- A three-point convex combination, in a form convenient for the triangle
argument below. -/
theorem convex_three_mem'
    {K : Set Space} (hK : Convex ℝ K)
    {p q r : Space} (hp : p ∈ K) (hq : q ∈ K) (hr : r ∈ K)
    {l₀ l₁ l₂ : ℝ}
    (hl₀ : 0 ≤ l₀) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (hsum : l₀ + l₁ + l₂ = 1) :
    l₀ • p + l₁ • q + l₂ • r ∈ K := by
  let w : Fin 3 → ℝ := ![l₀, l₁, l₂]
  let z : Fin 3 → Space := ![p, q, r]
  have hw : ∑ i, w i = l₀ + l₁ + l₂ := by
    rw [show (∑ i : Fin 3, w i) = w 0 + w 1 + w 2 by
      exact Fin.sum_univ_three w]
    rfl
  have hwz : ∑ i, w i • z i = l₀ • p + l₁ • q + l₂ • r := by
    rw [show (∑ i : Fin 3, w i • z i) = w 0 • z 0 + w 1 • z 1 + w 2 • z 2 by
      exact Fin.sum_univ_three (fun i ↦ w i • z i)]
    rfl
  have h := hK.sum_mem (t := Finset.univ) (w := w) (z := z) (by
    intro i hi
    fin_cases i <;> simp [w, hl₀, hl₁, hl₂]) (by
    rw [hw]
    exact hsum) (by
    intro i hi
    fin_cases i <;> simp [z, hp, hq, hr])
  rw [hwz] at h
  exact h

#print axioms convex_three_mem'

end
end Submission.Kakeya.ConvexGeometry
