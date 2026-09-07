import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedParentTransportV2

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineRestrictedFiberEquivV4

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictedParentTransportV2.StickyScaleCover

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The fully restricted fibre is the original fibre at the corresponding
active parent, with only subtype proofs inserted. -/
noncomputable def activeFineRestrictedFiberEquiv
    (S : StickyScaleCover fine rho)
    (q : Fin (activeFineRestrictedScaleCover S).coarseCard) :
    {j // j ∈ (activeFineRestrictedScaleCover S).fiber q} ≃
      {i // i ∈ S.fiber (restrictedCoarseEquivActive S q).1} := by
  classical
  have hiff (j : {i // i ∈ S.activeFine}) :
      j ∈ (activeFineRestrictedScaleCover S).fiber q ↔
        j.1 ∈ S.fiber (restrictedCoarseEquivActive S q).1 := by
    rw [(activeFineRestrictedScaleCover S).mem_fiber, S.mem_fiber]
    constructor
    · intro hj
      refine ⟨j.2, ?_⟩
      have hp := congrArg (restrictedCoarseEquivActive S) hj.2
      rw [restrictedCoarseEquivActive_parent] at hp
      exact congrArg Subtype.val hp
    · intro hj
      refine ⟨Finset.mem_univ _, ?_⟩
      apply (restrictedCoarseEquivActive S).injective
      rw [restrictedCoarseEquivActive_parent]
      apply Subtype.ext
      exact hj.2
  exact
    (Equiv.subtypeEquivRight hiff).trans
      (Equiv.subtypeSubtypeEquivSubtype fun h =>
        ((S.mem_fiber _ (restrictedCoarseEquivActive S q).1).1 h).1)

#print axioms activeFineRestrictedFiberEquiv

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineRestrictedFiberEquivV4
