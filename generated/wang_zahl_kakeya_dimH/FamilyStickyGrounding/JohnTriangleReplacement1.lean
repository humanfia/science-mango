import FamilyStickyGrounding.JohnTriangleContinuity2

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem transverseVector_add_right (u v w : Space) :
    transverseVector u (v + w) = transverseVector u v + transverseVector u w := by
  exact (transverseLinearMap u).map_add v w

theorem transverseVector_smul_right (a : ℝ) (u v : Space) :
    transverseVector u (a • v) = a • transverseVector u v := by
  exact (transverseLinearMap u).map_smul a v

theorem triangleArea_affine_edge_combination
    (p q r : Space) (a b : ℝ) :
    triangleArea p q (p + a • (q - p) + b • (r - p)) =
      |b| * triangleArea p q r := by
  rw [triangleArea_def, triangleArea_def]
  have hsub : p + a • (q - p) + b • (r - p) - p =
      a • (q - p) + b • (r - p) := by abel
  rw [hsub, transverseVector_add_right,
    transverseVector_smul_right, transverseVector_smul_right]
  have hself : transverseVector (q - p) (q - p) = 0 := by
    simp [transverseVector]
  rw [hself, smul_zero, zero_add, norm_smul, Real.norm_eq_abs]

#print axioms triangleArea_affine_edge_combination

end
end Submission.Kakeya.ConvexGeometry
