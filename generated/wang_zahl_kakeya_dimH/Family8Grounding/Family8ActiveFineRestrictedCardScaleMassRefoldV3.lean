import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Mathlib.Tactic

/-!
# Active-fine restricted card-scale refold, V3

V1 and V2 are frozen simplification drafts.  This successor first folds the
restricted cover, so `Fintype.card_fin` sees its exact inferred instance,
and only then unfolds the coarse-card definition.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ActiveFineRestrictedCardScaleMassRefoldV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The card-scale mass of the original active coarse set is exactly the
base card-scale mass of its active-fine restricted reindexing. -/
theorem activeCoarseCardScaleMass_eq_restricted_coarse_card
    (S : StickyScaleCover fine rho) :
    (activeCoarseCardScaleMass S : ENNReal) =
      (Fintype.card
          (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
        (rho : ENNReal) ^ 2 := by
  let U := activeFineRestrictedScaleCover S
  change (activeCoarseCardScaleMass S : ENNReal) =
    (Fintype.card (Fin U.coarseCard) : ENNReal) * (rho : ENNReal) ^ 2
  rw [Fintype.card_fin]
  simp only [activeCoarseCardScaleMass, U, activeFineRestrictedScaleCover,
    ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_pow]

#print axioms activeCoarseCardScaleMass_eq_restricted_coarse_card

end
end Family8ActiveFineRestrictedCardScaleMassRefoldV3
