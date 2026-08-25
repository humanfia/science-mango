import FamilyStickyGrounding.JohnActualDimOne2
import Mathlib.Analysis.Convex.Intrinsic

open Set Filter

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- Every nonempty finite-dimensional convex set contains a positive-radius
closed ball relative to its affine span.  This supplies the nondegenerate
feasible point needed by a later maximum-area ellipsoid optimization. -/
theorem exists_relative_closedBall_subset (K : ConvexBody Space) :
    ∃ c : affineSpan ℝ (K : Set Space), ∃ r : ℝ, 0 < r ∧
      Metric.closedBall c r ⊆
        ((↑) ⁻¹' (K : Set Space) : Set (affineSpan ℝ (K : Set Space))) := by
  obtain ⟨x, hx⟩ := K.nonempty.intrinsicInterior K.convex
  rcases (mem_intrinsicInterior (𝕜 := ℝ)).mp hx with ⟨c, hcint, rfl⟩
  have hcnhds :
      ((↑) ⁻¹' (K : Set Space) : Set (affineSpan ℝ (K : Set Space))) ∈ nhds c :=
    mem_interior_iff_mem_nhds.mp hcint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hcnhds
  refine ⟨c, ε / 2, by positivity, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hball

#print axioms exists_relative_closedBall_subset

end
end Submission.Kakeya.ConvexGeometry
