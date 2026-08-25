import FamilyStickyGrounding.JohnSegmentWitness1

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- Actual John-axis witness existence in the affine-dimension-one branch. -/
theorem exists_johnAxisWitness_of_finrank_direction_affineSpan_eq_one
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1) :
    Nonempty (JohnAxisWitness K) := by
  obtain ⟨p, hpK, q, hqK, hK⟩ :=
    exists_eq_segment_of_finrank_direction_affineSpan_eq_one K hdim
  by_cases hpq : p = q
  · apply exists_johnAxisWitness_of_subsingleton K
    intro x hx y hy
    rw [hK, hpq, segment_same] at hx hy
    exact hx.trans hy.symm
  · exact exists_johnAxisWitness_of_eq_segment_of_ne K hpq hK

#print axioms exists_johnAxisWitness_of_finrank_direction_affineSpan_eq_one

end
end Submission.Kakeya.ConvexGeometry
