import FamilyStickyGrounding.JohnDimThreePositiveTetra1
import FamilyStickyGrounding.JohnTetraReplacement1
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- A positive-volume tetrahedron in a three-dimensional affine span gives
edge coordinates for every point of the body. -/
theorem exists_tetra_edge_coordinates
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3)
    {p q r s x : Space}
    (hp : p ∈ (K : Set Space)) (hq : q ∈ (K : Set Space))
    (hr : r ∈ (K : Set Space)) (hs : s ∈ (K : Set Space))
    (hx : x ∈ (K : Set Space))
    (hpos : 0 < tetraVolume p q r s) :
    ∃ a b c : ℝ,
      x = p + a • (q - p) + b • (r - p) + c • (s - p) := by
  let A := affineSpan ℝ (K : Set Space)
  let edge : Fin 3 → A.direction := ![
    ⟨q - p, AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hq) (mem_affineSpan ℝ hp)⟩,
    ⟨r - p, AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hr) (mem_affineSpan ℝ hp)⟩,
    ⟨s - p, AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hs) (mem_affineSpan ℝ hp)⟩]
  have hdet : LinearMap.det
      (innerCoordinateMap ![q - p, r - p, s - p]) ≠ 0 := by
    rw [← tetraSignedVolume_eq_det]
    rw [tetraVolume_def] at hpos
    exact abs_pos.mp hpos
  have hgram : (Matrix.gram ℝ ![q - p, r - p, s - p]).det ≠ 0 := by
    rw [← det_innerCoordinateMap_sq_eq_det_gram]
    exact pow_ne_zero 2 hdet
  have hamb : LinearIndependent ℝ ![q - p, r - p, s - p] :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mp hgram
  have hambVal : LinearIndependent ℝ (fun i ↦ (edge i : Space)) := by
    convert hamb using 1
    funext i
    fin_cases i <;> rfl
  have hedge : LinearIndependent ℝ edge := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hval := congrArg Subtype.val hg
    exact (Fintype.linearIndependent_iff.mp hambVal) g (by simpa using hval) i
  let ebasis : Module.Basis (Fin 3) ℝ A.direction :=
    basisOfLinearIndependentOfCardEqFinrank' edge hedge
      (by simpa [A] using hdim.symm)
  let vx : A.direction := ⟨x - p, AffineSubspace.vsub_mem_direction
    (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hp)⟩
  let a : ℝ := ebasis.repr vx 0
  let b : ℝ := ebasis.repr vx 1
  let c : ℝ := ebasis.repr vx 2
  refine ⟨a, b, c, ?_⟩
  have hrepr := ebasis.sum_repr vx
  have hreprVal := congrArg Subtype.val hrepr
  rw [Fin.sum_univ_three] at hreprVal
  have hv : x - p =
      a • (q - p) + b • (r - p) + c • (s - p) := by
    simpa [a, b, c, ebasis, edge, vx] using hreprVal.symm
  calc
    x = p + (x - p) := by abel
    _ = p + (a • (q - p) + b • (r - p) + c • (s - p)) := by rw [hv]
    _ = p + a • (q - p) + b • (r - p) + c • (s - p) := by abel

#print axioms exists_tetra_edge_coordinates

end
end Submission.Kakeya.ConvexGeometry
