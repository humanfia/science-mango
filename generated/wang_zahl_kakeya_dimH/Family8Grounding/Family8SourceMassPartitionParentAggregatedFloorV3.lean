import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import FamilyStickyGrounding.FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SourceMassPartitionParentAggregatedFloorV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5

noncomputable section

/-!
# Actual source-mass partition and parent-aggregation floors

The source-mass coarse partition uses every index of the active-fine subtype.
Consequently its literal `sourceActiveFineShading` has exactly the original
active shading mass.  Separately, the standard fibre-cardinality inequality
can be cancelled whenever the chosen natural cap is positive.  These facts
turn a division-free source power budget into the exact `hsourceLower` datum
consumed by the frozen outer endpoint.  V1 and V2 were namespace/reducibility
drafts and are intentionally not imported.
-/

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The source shading named by the literal source-mass partition is the
actual active-fine shading, with no retention loss. -/
theorem sourceMassCoarseTubePartition_sourceActiveFineShading_mass_eq
    (S : StickyScaleCover fine rho) (hscale : delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0) :
    (sourceActiveFineShading
      (sourceMassCoarseTubePartition
        (activeFineRestrictedScaleCover S) hscale
        (activeFineRestrictedShading S Y)
        (activeFineRestrictedSourceMass_ne_zero S Y hsource)).asConvexFactorization
      (activeFineRestrictedShading S Y)).shadingMass =
        (activeFineShading S Y).shadingMass := by
  rw [sourceActiveFineShading_shadingMass]
  change
    (IndexedShadingRefinement.restrictTo
      (activeFineRestrictedShading S Y)
      (sourceMassCoarseTubePartition
        (activeFineRestrictedScaleCover S) hscale
        (activeFineRestrictedShading S Y)
        (activeFineRestrictedSourceMass_ne_zero S Y hsource)).fineIndices).shading.shadingMass =
      (activeFineShading S Y).shadingMass
  rw [sourceMassCoarseTubePartition_fineIndices,
    activeFineRestrictedScaleCover_activeFine,
    restrictTo_univ_shadingMass,
    activeFineRestrictedShading_shadingMass]

/-- A positive uniform fibre-card cap can be cancelled from the exact active
fine-to-parent mass comparison.  The input is division-free. -/
theorem sourceFloor_le_parentAggregatedShading_of_fiberCard
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (M : Nat) (hMpos : 0 < M)
    (hM : ∀ k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card ≤ M)
    {sourceFloor : ENNReal}
    (hscaled :
      (M : ENNReal) * sourceFloor ≤
        (activeFineShading S Y).shadingMass) :
    sourceFloor ≤ (parentAggregatedShading S Y).shadingMass := by
  have hupper : (activeFineShading S Y).shadingMass ≤
      (M : ENNReal) * (parentAggregatedShading S Y).shadingMass := by
    simpa only [nsmul_eq_mul] using
      activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
        S Y M hM
  have hM0 : (M : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hMpos
  have hMTop : (M : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hscaledRight : sourceFloor * (M : ENNReal) ≤
      (parentAggregatedShading S Y).shadingMass * (M : ENNReal) := by
    calc
      sourceFloor * (M : ENNReal) =
          (M : ENNReal) * sourceFloor := mul_comm _ _
      _ ≤ (activeFineShading S Y).shadingMass := hscaled
      _ ≤ (M : ENNReal) *
          (parentAggregatedShading S Y).shadingMass := hupper
      _ = (parentAggregatedShading S Y).shadingMass *
          (M : ENNReal) := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_left hM0 hMTop).mp hscaledRight

#print axioms
  sourceMassCoarseTubePartition_sourceActiveFineShading_mass_eq
#print axioms sourceFloor_le_parentAggregatedShading_of_fiberCard

end
end Family8SourceMassPartitionParentAggregatedFloorV3
