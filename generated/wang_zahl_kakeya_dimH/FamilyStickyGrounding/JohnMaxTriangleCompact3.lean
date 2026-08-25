import FamilyStickyGrounding.JohnTriangleContinuity2

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- A compact convex body admits a triangle of maximal Euclidean area.
Convexity is not needed for this compactness layer. -/
theorem exists_maximal_triangle (K : ConvexBody Space) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space), ∃ r ∈ (K : Set Space),
      ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space), ∀ r' ∈ (K : Set Space),
        triangleArea p' q' r' ≤ triangleArea p q r := by
  let T : Set (Space × (Space × Space)) :=
    (K : Set Space) ×ˢ ((K : Set Space) ×ˢ (K : Set Space))
  have hTc : IsCompact T := K.isCompact.prod (K.isCompact.prod K.isCompact)
  have hTne : T.Nonempty := K.nonempty.prod (K.nonempty.prod K.nonempty)
  obtain ⟨x, hxT, hxmax⟩ := hTc.exists_isMaxOn hTne continuous_triangleArea.continuousOn
  refine ⟨x.1, hxT.1, x.2.1, hxT.2.1, x.2.2, hxT.2.2, ?_⟩
  intro p hp q hq r hr
  exact hxmax (show (p, (q, r)) ∈ T from ⟨hp, ⟨hq, hr⟩⟩)

#print axioms exists_maximal_triangle

end
end Submission.Kakeya.ConvexGeometry
