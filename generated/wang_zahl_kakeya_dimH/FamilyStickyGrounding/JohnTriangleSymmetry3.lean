import FamilyStickyGrounding.JohnTriangleReplacement1

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem transverseVector_anticomm (u v : Space) :
    transverseVector v u = -transverseVector u v := by
  apply (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective
  change crossProduct (WithLp.ofLp v) (WithLp.ofLp u) =
    -crossProduct (WithLp.ofLp u) (WithLp.ofLp v)
  exact (cross_anticomm _ _).symm

theorem transverseVector_sub_left (u v w : Space) :
    transverseVector (u - v) w = transverseVector u w - transverseVector v w := by
  have h := congrArg (fun f : Space →ₗ[ℝ] Space ↦ f w)
    (transverseLinearMap.map_sub u v)
  exact h

theorem transverseVector_neg_right (u v : Space) :
    transverseVector u (-v) = -transverseVector u v := by
  exact (transverseLinearMap u).map_neg v

theorem transverseVector_self (u : Space) : transverseVector u u = 0 := by
  simp [transverseVector]

theorem triangleArea_swap_last (p q r : Space) :
    triangleArea p r q = triangleArea p q r := by
  rw [triangleArea_def, triangleArea_def, transverseVector_anticomm, norm_neg]

theorem triangleArea_cycle (p q r : Space) :
    triangleArea q r p = triangleArea p q r := by
  rw [triangleArea_def, triangleArea_def]
  have h₁ : r - q = (r - p) - (q - p) := by abel
  have h₂ : p - q = -(q - p) := by abel
  rw [h₁, h₂, transverseVector_sub_left,
    transverseVector_neg_right, transverseVector_neg_right,
    transverseVector_self, neg_zero, sub_zero,
    transverseVector_anticomm, neg_neg]

#print axioms triangleArea_swap_last
#print axioms triangleArea_cycle

end
end Submission.Kakeya.ConvexGeometry
