import FamilyStickyGrounding.JohnAxisBridge5

open scoped NNReal InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- A concrete ambient orthonormal frame, used in the zero-dimensional case. -/
def standardFrame3 : OrthonormalBasis (Fin 3) ℝ Space :=
  (stdOrthonormalBasis ℝ Space).reindex (finCongr (by simp [Space]))

/-- Actual John witness existence for a convex body whose carrier is a
subsingleton.  All three semiaxes vanish. -/
theorem exists_johnAxisWitness_of_subsingleton (K : ConvexBody Space)
    (hsub : (K : Set Space).Subsingleton) :
    Nonempty (JohnAxisWitness K) := by
  obtain ⟨c, hc⟩ := K.nonempty
  let radius : Fin 3 → ℝ≥0 := fun _ ↦ 0
  refine ⟨{
    center := c
    frame := standardFrame3
    radius := radius
    inner := ?_
    outer := ?_ }⟩
  · intro x hx
    rcases hx with ⟨z, _hz, hxrep⟩
    have hxc : x = c := by simpa [radius] using hxrep
    exact hxc.symm ▸ hc
  · intro x hx
    have hxc : x = c := hsub hx hc
    subst x
    refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · norm_num
    · simp [radius]

/-- The affine-span dimension-zero branch of actual John witness existence. -/
theorem exists_johnAxisWitness_of_finrank_direction_affineSpan_eq_zero
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 0) :
    Nonempty (JohnAxisWitness K) := by
  apply exists_johnAxisWitness_of_subsingleton K
  intro x hx y hy
  have hxy : x - y ∈ (affineSpan ℝ (K : Set Space)).direction :=
    AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hy)
  have hbot : (affineSpan ℝ (K : Set Space)).direction = ⊥ :=
    Submodule.finrank_eq_zero.mp hdim
  rw [hbot] at hxy
  have hzero : x - y = 0 := by simpa using hxy
  exact sub_eq_zero.mp hzero

#print axioms exists_johnAxisWitness_of_subsingleton
#print axioms exists_johnAxisWitness_of_finrank_direction_affineSpan_eq_zero

end
end Submission.Kakeya.ConvexGeometry
