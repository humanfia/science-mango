import FamilyStickyGrounding.JohnTetraVolume1

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- A compact convex body admits a tetrahedron of maximal absolute oriented
volume.  Convexity is not needed for this compactness layer. -/
theorem exists_maximal_tetrahedron (K : ConvexBody Space) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space),
      ∃ r ∈ (K : Set Space), ∃ s ∈ (K : Set Space),
        ∀ p' ∈ (K : Set Space), ∀ q' ∈ (K : Set Space),
          ∀ r' ∈ (K : Set Space), ∀ s' ∈ (K : Set Space),
            tetraVolume p' q' r' s' ≤ tetraVolume p q r s := by
  let T : Set (Space × (Space × (Space × Space))) :=
    (K : Set Space) ×ˢ
      ((K : Set Space) ×ˢ ((K : Set Space) ×ˢ (K : Set Space)))
  have hTc : IsCompact T :=
    K.isCompact.prod (K.isCompact.prod (K.isCompact.prod K.isCompact))
  have hTne : T.Nonempty :=
    K.nonempty.prod (K.nonempty.prod (K.nonempty.prod K.nonempty))
  obtain ⟨x, hxT, hxmax⟩ :=
    hTc.exists_isMaxOn hTne continuous_tetraVolume.continuousOn
  refine ⟨x.1, hxT.1, x.2.1, hxT.2.1,
    x.2.2.1, hxT.2.2.1, x.2.2.2, hxT.2.2.2, ?_⟩
  intro p hp q hq r hr s hs
  exact hxmax (show (p, (q, (r, s))) ∈ T from ⟨hp, ⟨hq, ⟨hr, hs⟩⟩⟩)

#print axioms exists_maximal_tetrahedron

end
end Submission.Kakeya.ConvexGeometry
