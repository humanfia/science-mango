import FamilyStickyGrounding.JohnDimTwoFeasibleDisk6
import Submission.Kakeya.ConvexFactoring.TransverseUnit

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

def transverseLinearMap : Space →ₗ[ℝ] Space →ₗ[ℝ] Space := by
  apply LinearMap.mk₂ ℝ transverseVector
  · intro u v w
    ext i
    simp [transverseVector]
  · intro a u v
    ext i
    simp [transverseVector]
  · intro u v w
    ext i
    simp [transverseVector]
  · intro a u v
    ext i
    simp [transverseVector]

def transverseCLM : Space →L[ℝ] Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Space →ₗ[ℝ] Space) ≃ₗ[ℝ] (Space →L[ℝ] Space)).toLinearMap.comp
        transverseLinearMap)

@[simp] theorem transverseCLM_apply (u v : Space) :
    transverseCLM u v = transverseVector u v := rfl

/-- Triangle area is kept irreducible so compact-optimization statements do
not repeatedly unfold the transported cross-product implementation. -/
irreducible_def triangleArea (p q r : Space) : ℝ :=
  ‖transverseVector (q - p) (r - p)‖

theorem continuous_triangleArea :
    Continuous (fun x : Space × (Space × Space) ↦ triangleArea x.1 x.2.1 x.2.2) := by
  rw [show (fun x : Space × (Space × Space) ↦ triangleArea x.1 x.2.1 x.2.2) =
      (fun x ↦ ‖transverseVector (x.2.1 - x.1) (x.2.2 - x.1)‖) by
        funext x
        rw [triangleArea_def]]
  have hargs : Continuous (fun x : Space × (Space × Space) ↦
      (x.2.1 - x.1, x.2.2 - x.1)) := by fun_prop
  have hcross := transverseCLM.continuous₂.comp hargs
  have hnorm := hcross.norm
  convert hnorm using 1
  funext x
  rfl

#print axioms continuous_triangleArea

end
end Submission.Kakeya.ConvexGeometry
