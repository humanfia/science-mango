import FamilyStickyGrounding.JohnActualDegenerate1

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- Extend a unit vector to a `Fin 3` ambient orthonormal frame, placing it in
the first coordinate. -/
theorem exists_frame_zero_eq {e : Space} (he : ‖e‖ = 1) :
    ∃ frame : OrthonormalBasis (Fin 3) ℝ Space, frame 0 = e := by
  let v : Fin 3 → Space := fun _ ↦ e
  let s : Set (Fin 3) := {0}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact he
  obtain ⟨frame, hframe⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (ι := Fin 3) (by simp [Space])
  refine ⟨frame, ?_⟩
  exact hframe 0 (by simp [s])

#print axioms exists_frame_zero_eq

end
end Submission.Kakeya.ConvexGeometry
