import FamilyStickyGrounding.JohnTetraVolume1
import FamilyStickyGrounding.JohnTriangleReplacement1

open scoped InnerProductSpace Matrix
namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

theorem transverseVector_neg_swap (u v : Space) :
    transverseVector u v = -transverseVector v u := by
  have h := (neg_cross (WithLp.ofLp v) (WithLp.ofLp u)).symm
  change WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v) =
    WithLp.toLp 2 (-(WithLp.ofLp v ⨯₃ WithLp.ofLp u))
  exact congrArg (WithLp.toLp 2) h

theorem transverseVector_sub_right (u v w : Space) :
    transverseVector u (v - w) =
      transverseVector u v - transverseVector u w := by
  exact (transverseLinearMap u).map_sub v w

theorem transverseVector_sub_left (u v w : Space) :
    transverseVector (u - v) w =
      transverseVector u w - transverseVector v w := by
  rw [transverseVector_neg_swap (u - v) w,
    transverseVector_sub_right w u v,
    transverseVector_neg_swap u w, transverseVector_neg_swap v w]
  module

theorem inner_transverseVector_cycle (u v w : Space) :
    ⟪u, transverseVector v w⟫_ℝ =
      ⟪v, transverseVector w u⟫_ℝ := by
  simp only [transverseVector, EuclideanSpace.inner_eq_star_dotProduct]
  have hu : star (WithLp.ofLp u) = WithLp.ofLp u := by
    ext i
    simp
  have hv : star (WithLp.ofLp v) = WithLp.ofLp v := by
    ext i
    simp
  rw [hu, hv]
  calc
    (WithLp.ofLp v ⨯₃ WithLp.ofLp w) ⬝ᵥ WithLp.ofLp u =
        WithLp.ofLp u ⬝ᵥ (WithLp.ofLp v ⨯₃ WithLp.ofLp w) :=
      dotProduct_comm _ _
    _ = WithLp.ofLp v ⬝ᵥ (WithLp.ofLp w ⨯₃ WithLp.ofLp u) :=
      triple_product_permutation _ _ _
    _ = (WithLp.ofLp w ⨯₃ WithLp.ofLp u) ⬝ᵥ WithLp.ofLp v :=
      dotProduct_comm _ _

/-- Replacing the fourth vertex by affine edge coordinates scales oriented
tetrahedron volume by its third edge coefficient. -/
theorem tetraSignedVolume_affine_edge_combination_fourth
    (p q r s : Space) (a b c : ℝ) :
    tetraSignedVolume p q r
        (p + a • (q - p) + b • (r - p) + c • (s - p)) =
      c * tetraSignedVolume p q r s := by
  unfold tetraSignedVolume
  have hsub :
      p + a • (q - p) + b • (r - p) + c • (s - p) - p =
        a • (q - p) + b • (r - p) + c • (s - p) := by abel
  rw [hsub, transverseVector_add_right, transverseVector_add_right,
    transverseVector_smul_right, transverseVector_smul_right,
    transverseVector_smul_right, inner_add_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right]
  have hfirst :
      ⟪q - p, transverseVector (r - p) (q - p)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_transverseVector_right _ _
  have hsecond :
      ⟪q - p, transverseVector (r - p) (r - p)⟫_ℝ = 0 := by
    simp [transverseVector]
  rw [hfirst, hsecond]
  ring

theorem tetraVolume_affine_edge_combination_fourth
    (p q r s : Space) (a b c : ℝ) :
    tetraVolume p q r
        (p + a • (q - p) + b • (r - p) + c • (s - p)) =
      |c| * tetraVolume p q r s := by
  rw [tetraVolume_def, tetraVolume_def,
    tetraSignedVolume_affine_edge_combination_fourth, abs_mul]


/-- Moving the first tetrahedron vertex to the end reverses orientation. -/
theorem tetraSignedVolume_cycle_vertices (p q r s : Space) :
    tetraSignedVolume q r s p = -tetraSignedVolume p q r s := by
  unfold tetraSignedVolume
  have hrq : r - q = (r - p) - (q - p) := by abel
  have hsq : s - q = (s - p) - (q - p) := by abel
  have hpq : p - q = -(q - p) := by abel
  rw [hrq, hsq, hpq]
  have hneg :
      transverseVector ((s - p) - (q - p)) (-(q - p)) =
        -transverseVector ((s - p) - (q - p)) (q - p) :=
    (transverseLinearMap ((s - p) - (q - p))).map_neg (q - p)
  rw [hneg, transverseVector_sub_left]
  have hself : transverseVector (q - p) (q - p) = 0 := by
    simp [transverseVector]
  rw [hself, sub_zero, inner_neg_right, inner_sub_left]
  have horth :
      ⟪q - p, transverseVector (s - p) (q - p)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact inner_transverseVector_right _ _
  rw [horth, sub_zero, inner_transverseVector_cycle (q - p) (r - p) (s - p)]

theorem tetraVolume_cycle_vertices (p q r s : Space) :
    tetraVolume q r s p = tetraVolume p q r s := by
  rw [tetraVolume_def, tetraVolume_def, tetraSignedVolume_cycle_vertices,
    abs_neg]

#print axioms tetraSignedVolume_affine_edge_combination_fourth
#print axioms tetraVolume_affine_edge_combination_fourth
#print axioms tetraVolume_cycle_vertices

end
end Submission.Kakeya.ConvexGeometry
