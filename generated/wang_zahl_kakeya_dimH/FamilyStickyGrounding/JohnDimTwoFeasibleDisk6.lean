import FamilyStickyGrounding.JohnRelativeBall4
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

def affineDirectionBasisTwo (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2) :
    OrthonormalBasis (Fin 2) ℝ (affineSpan ℝ (K : Set Space)).direction :=
  (stdOrthonormalBasis ℝ (affineSpan ℝ (K : Set Space)).direction).reindex
    (finCongr hdim)

/-- Isometric coordinates on the two-dimensional direction of the affine span. -/
def affineDirectionEquivTwo (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] (affineSpan ℝ (K : Set Space)).direction :=
  (affineDirectionBasisTwo K hdim).repr.symm

/-- In affine dimension two there is an actual positive-radius Euclidean disk
inside `K`, expressed in isometric coordinates on its affine span. -/
theorem exists_dimTwo_feasible_disk (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2) :
    ∃ c : affineSpan ℝ (K : Set Space), ∃ r : ℝ, 0 < r ∧
      ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ ≤ r →
        ((affineDirectionEquivTwo K hdim u :
            (affineSpan ℝ (K : Set Space)).direction) : Space) + (c : Space) ∈ K := by
  obtain ⟨c, r, hr, hball⟩ := exists_relative_closedBall_subset K
  refine ⟨c, r, hr, ?_⟩
  intro u hu
  let v := affineDirectionEquivTwo K hdim u
  let y : affineSpan ℝ (K : Set Space) :=
    ⟨(v : Space) + (c : Space),
      AffineSubspace.vadd_mem_of_mem_direction v.property c.property⟩
  have hyball : y ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall]
    change dist ((v : Space) + (c : Space)) (c : Space) ≤ r
    rw [dist_eq_norm]
    simp only [add_sub_cancel_right]
    calc
      ‖(v : Space)‖ = ‖v‖ := rfl
      _ = ‖u‖ := (affineDirectionEquivTwo K hdim).norm_map u
      _ ≤ r := hu
  exact hball hyball

#print axioms exists_dimTwo_feasible_disk

end
end Submission.Kakeya.ConvexGeometry
