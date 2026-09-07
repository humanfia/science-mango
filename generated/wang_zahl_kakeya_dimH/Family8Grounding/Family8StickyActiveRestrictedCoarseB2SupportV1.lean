import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickyActiveCoarseB2SupportV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8StickyActiveRestrictedCoarseB2SupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveCoarseB2SupportV5

noncomputable section

/-!
# Automatic B2 support after active-index reindexing

The active-fine restricted Sticky cover reindexes the actual active parents
by `Fin activeCoarse.card`.  Its coarse tubes are definitionally the original
active parent tubes transported along `Finset.equivFin`.  Hence the sharp
radius-two support theorem survives this reindexing without any geometric
premise or callback.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Every coarse tube of the fully active reindexed cover has the automatic
radius-two support inherited from its actual original parent. -/
theorem activeFineRestrictedScaleCover_coarse_carrier_subset_closedBall_two
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : rho <= (1 / 16 : NNReal)) :
    forall q,
      ((activeFineRestrictedScaleCover S).coarse.tubes q).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro q
  let e : {k // k ∈ S.activeCoarse} ≃ Fin S.activeCoarse.card :=
    S.activeCoarse.equivFin
  have hsupport :=
    activeCoarseFamily_body_subset_closedBall_two
      D hD S hrho (e.symm q)
  change (S.coarse.tubes (e.symm q).1).carrier ⊆
    Metric.closedBall (0 : Space) 2
  simpa only [StickyScaleCover.activeCoarseFamily,
    UniformTubeFamily.bodyFamily_apply, Tube.coe_body] using hsupport

#print axioms
  activeFineRestrictedScaleCover_coarse_carrier_subset_closedBall_two

end
end Family8StickyActiveRestrictedCoarseB2SupportV1
