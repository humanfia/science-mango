import Family8Grounding.Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2
import Family8Grounding.Family8ConvexWolffReindexV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8DoubledParentConflictWeightedCWAInheritanceV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8ConvexWolffReindexV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}
  {S : StickyScaleCover fine rho}
variable {weight : Fin S.coarseCard → ENNReal} {B C : ENNReal}

/-- The rescaled selected fibre is the old rescaled fibre transported across
the exact fibre equivalence. -/
theorem rescaledFiberFamily_restrictToWeightedSelection_eq_reindex
    (R : UnitRescalingGeometry S)
    (W : DoubledParentConflictWeightedSelection S weight B)
    (q : {q // q ∈
      (weightedSelectedParentScaleCover W).activeCoarse}) :
    (Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover.UnitRescalingGeometry.restrictToWeightedSelection R W).rescaledFiberFamily q =
      reindexConvexFamily
        (weightedSelectedParentScaleCover_fiberEquiv W q.1)
        (R.rescaledFiberFamily
          ⟨(W.selected.equivFin.symm q.1).1,
            W.selected_subset (W.selected.equivFin.symm q.1).2⟩) := by
  funext i
  rfl

/-- Convex Wolff axioms on all old normalized fibres pass to the selected
cover with exactly the same constant. -/
theorem UnitRescalingGeometry.fibresSatisfyCWA_restrictToWeightedSelection
    (R : UnitRescalingGeometry S)
    (W : DoubledParentConflictWeightedSelection S weight B)
    (hCWA : R.FibresSatisfyCWA C) :
    (Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover.UnitRescalingGeometry.restrictToWeightedSelection R W).FibresSatisfyCWA C := by
  intro q
  let oldParent : {k // k ∈ S.activeCoarse} :=
    ⟨(W.selected.equivFin.symm q.1).1,
      W.selected_subset (W.selected.equivFin.symm q.1).2⟩
  have hsource := hCWA oldParent
  have hreindexed := satisfiesConvexWolffAxioms_reindex
    (weightedSelectedParentScaleCover_fiberEquiv W q.1) hsource
  rw [rescaledFiberFamily_restrictToWeightedSelection_eq_reindex]
  exact hreindexed

#print axioms rescaledFiberFamily_restrictToWeightedSelection_eq_reindex
#print axioms UnitRescalingGeometry.fibresSatisfyCWA_restrictToWeightedSelection

end ScaleCover
end
end Family8DoubledParentConflictWeightedCWAInheritanceV2
