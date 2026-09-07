import Family8Grounding.Family8StickyScaleCoverActiveFineSameCoarseFiberEquivV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineSameCoarseFiberBodyV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineSameCoarseCoverV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseFiberEquivV1.StickyScaleCover

noncomputable section

/-! # Pointwise body identity for the active-fine reindexing -/

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The explicit fibre equivalence changes only subtype proofs, hence every
convex body is definitionally the same. -/
@[simp]
theorem activeFineSameCoarseFiberEquiv_body
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (j : {j // j ∈ (activeFineSameCoarseCover S).fiber k}) :
    (activeFineSameCoarseCover S).fiberFamily k j =
      S.fiberFamily k (activeFineSameCoarseFiberEquiv S k j) := by
  rfl

#print axioms activeFineSameCoarseFiberEquiv_body

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineSameCoarseFiberBodyV1
