import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedFiberEquivV4

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineRestrictedFiberBodyV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictedFiberEquivV4.StickyScaleCover

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The fibre equivalence changes only finite index proofs, so its tube body
is pointwise unchanged. -/
@[simp]
theorem activeFineRestrictedFiberEquiv_body
    (S : StickyScaleCover fine rho)
    (q : Fin (activeFineRestrictedScaleCover S).coarseCard)
    (j : {j // j ∈ (activeFineRestrictedScaleCover S).fiber q}) :
    (activeFineRestrictedScaleCover S).fiberFamily q j =
      S.fiberFamily (restrictedCoarseEquivActive S q).1
        (activeFineRestrictedFiberEquiv S q j) := by
  rfl

#print axioms activeFineRestrictedFiberEquiv_body

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineRestrictedFiberBodyV1
