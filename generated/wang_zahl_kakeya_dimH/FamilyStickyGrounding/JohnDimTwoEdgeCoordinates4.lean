import FamilyStickyGrounding.JohnDimTwoNondegenerateMaxTriangle1
import FamilyStickyGrounding.JohnTransverseIndependentIff1
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- A positive-area triangle in a two-dimensional affine span supplies edge
coordinates for every point of the body. -/
theorem exists_edge_coordinates
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2)
    {p q r x : Space}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (hr : r ∈ (K : Set Space)) (hx : x ∈ (K : Set Space))
    (hpos : 0 < triangleArea p q r) :
    ∃ a b : ℝ, x = p + a • (q - p) + b • (r - p) := by
  let A := affineSpan ℝ (K : Set Space)
  let edge : Fin 2 → A.direction := ![
    ⟨q - p, AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hq) (mem_affineSpan ℝ hp)⟩,
    ⟨r - p, AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hr) (mem_affineSpan ℝ hp)⟩]
  have hamb : LinearIndependent ℝ ![q - p, r - p] := by
    apply (transverseVector_ne_zero_iff_linearIndependent (q - p) (r - p)).mp
    rw [triangleArea_def] at hpos
    exact norm_pos_iff.mp hpos
  have hedge : LinearIndependent ℝ edge := by
    have h₀ : edge 0 ≠ 0 := by
      intro hzero
      have hv := congrArg Subtype.val hzero
      exact hamb.ne_zero 0 (by simpa [edge] using hv)
    have hambPair := (LinearIndependent.pair_iff' (hamb.ne_zero 0)).mp hamb
    change LinearIndependent ℝ ![edge 0, edge 1]
    rw [LinearIndependent.pair_iff' h₀]
    intro a ha
    apply hambPair a
    have hv := congrArg Subtype.val ha
    simpa [edge] using hv
  let ebasis : Module.Basis (Fin 2) ℝ A.direction :=
    basisOfLinearIndependentOfCardEqFinrank' edge hedge
      (by simpa [A] using hdim.symm)
  let vx : A.direction := ⟨x - p, AffineSubspace.vsub_mem_direction
    (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hp)⟩
  let a : ℝ := ebasis.repr vx 0
  let b : ℝ := ebasis.repr vx 1
  refine ⟨a, b, ?_⟩
  have hrepr := ebasis.sum_repr vx
  have hreprVal := congrArg Subtype.val hrepr
  rw [Fin.sum_univ_two] at hreprVal
  have hv : x - p = a • (q - p) + b • (r - p) := by
    simpa [a, b, ebasis, edge, vx] using hreprVal.symm
  calc
    x = p + (x - p) := by abel
    _ = p + (a • (q - p) + b • (r - p)) := by rw [hv]
    _ = p + a • (q - p) + b • (r - p) := by abel

#print axioms exists_edge_coordinates

end
end Submission.Kakeya.ConvexGeometry
