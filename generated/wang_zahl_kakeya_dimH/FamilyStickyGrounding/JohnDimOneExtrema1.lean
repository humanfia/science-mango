import FamilyStickyGrounding.JohnDimOneScalar2

open scoped InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem continuous_affineLineCoord (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1)
    (c : Space) : Continuous (affineLineCoord K hdim c) := by
  unfold affineLineCoord
  fun_prop

/-- The coordinate in the unique affine-span direction realizes both extrema on `K`. -/
theorem exists_affineLineCoord_extrema (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1)
    (c : Space) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space),
      IsMinOn (affineLineCoord K hdim c) K p ∧
      IsMaxOn (affineLineCoord K hdim c) K q := by
  obtain ⟨p, hpK, hp⟩ := K.isCompact.exists_isMinOn K.nonempty
    (continuous_affineLineCoord K hdim c).continuousOn
  obtain ⟨q, hqK, hq⟩ := K.isCompact.exists_isMaxOn K.nonempty
    (continuous_affineLineCoord K hdim c).continuousOn
  exact ⟨p, hpK, q, hqK, hp, hq⟩

#print axioms continuous_affineLineCoord
#print axioms exists_affineLineCoord_extrema

end
end Submission.Kakeya.ConvexGeometry
