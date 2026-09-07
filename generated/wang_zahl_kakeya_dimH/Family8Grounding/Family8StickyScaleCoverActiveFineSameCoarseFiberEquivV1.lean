import Family8Grounding.Family8StickyScaleCoverActiveFineSameCoarseCoverV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineSameCoarseFiberEquivV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineSameCoarseCoverV1.StickyScaleCover

noncomputable section

/-!
# Fibre equivalence for the same-coarse active-fine reindexing

This file contains only the finite equivalence.  Geometry and normalized
Frostman consumers are deliberately deferred to successor modules.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Remove or insert the active-membership proof inside one fixed parent
fibre. -/
noncomputable def activeFineSameCoarseFiberEquiv
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    {j // j ∈ (activeFineSameCoarseCover S).fiber k} ≃
      {i // i ∈ S.fiber k} := by
  classical
  refine
    { toFun := fun j => ⟨j.1.1, ?_⟩
      invFun := fun i => ⟨⟨i.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hj := ((activeFineSameCoarseCover S).mem_fiber j.1 k).1 j.2
    apply (S.mem_fiber j.1.1 k).2
    exact ⟨j.1.2, hj.2⟩
  · exact ((S.mem_fiber i.1 k).1 i.2).1
  · apply ((activeFineSameCoarseCover S).mem_fiber
      ⟨i.1, ((S.mem_fiber i.1 k).1 i.2).1⟩ k).2
    exact ⟨Finset.mem_univ _, ((S.mem_fiber i.1 k).1 i.2).2⟩
  · intro j
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro i
    apply Subtype.ext
    rfl

#print axioms activeFineSameCoarseFiberEquiv

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineSameCoarseFiberEquivV1
