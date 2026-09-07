import Family8Grounding.Family8DoubledParentConflictWeightedCWAInheritanceV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8DoubledParentConflictWeightedDef212EndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8DoubledParentConflictWeightedCWAInheritanceV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}
  {S : StickyScaleCover fine rho}
variable {weight : Fin S.coarseCard → ENNReal} {B C : ENNReal}

/-!
# One complete selected Definition 2.12 scale endpoint

The only new quantitative premise is the literal closed doubled-parent
conflict degree bound.  All other fields are inherited from the actual old
cover by restriction and exact finite reindexing.
-/

structure WeightedDef212ScaleEndpoint
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B C : ENNReal) where
  base : WeightedRestrictedCoverEndpoint S weight B C
  unitRescalingGeometry :
    UnitRescalingGeometry
      (weightedSelectedParentScaleCover base.selection)
  rescaled_fibres_cwa : unitRescalingGeometry.FibresSatisfyCWA C

/-- Build the complete selected-cover endpoint from one honest source
Definition 2.12 scale and the explicit `2A` conflict-degree budget. -/
theorem exists_weightedDef212ScaleEndpoint
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B C : ENNReal)
    (hneighbour : ClosedDoubledParentConflictDegreeBound S B)
    (huniform : IsCUniform S C)
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (R : UnitRescalingGeometry S)
    (hCWA : R.FibresSatisfyCWA C) :
    Nonempty (WeightedDef212ScaleEndpoint S weight B C) := by
  obtain ⟨E⟩ := exists_weightedRestrictedCoverEndpoint
    S weight B C hneighbour huniform hpaper
  let R' :=
    Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover.UnitRescalingGeometry.restrictToWeightedSelection
      R E.selection
  have hCWA' : R'.FibresSatisfyCWA C :=
    Family8DoubledParentConflictWeightedCWAInheritanceV2.ScaleCover.UnitRescalingGeometry.fibresSatisfyCWA_restrictToWeightedSelection
      R E.selection hCWA
  exact ⟨
    { base := E
      unitRescalingGeometry := R'
      rescaled_fibres_cwa := hCWA' }⟩

#print axioms exists_weightedDef212ScaleEndpoint

end ScaleCover
end
end Family8DoubledParentConflictWeightedDef212EndpointV1
