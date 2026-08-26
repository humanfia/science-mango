import FamilyStickyGrounding.FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainWZPackedSeedLocalCardBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedRestrictionParentPartitionCollisionBindingV1
open FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2
open FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2

noncomputable section

/-!
# WZ-packed local-card budget for the generated Family 7 seed

The actual level-zero parent partition and the WZ common-`100 T` packing
theorem bound the initial refined family by

`levelZeroParentCount * commonHundredNeighbourPackingConstant`.

This file feeds that genuine geometric cardinality estimate into the sole
local-card premise of the fully automatic fixed-`n` endpoint.  The bound
still contains the hierarchy's active parent count; it is not asserted to be
dimension-only.  Its hypotheses explicitly retain the hierarchy, random
geometry, joint random-motion certificate, WZ separation, and (for the final
producer) the adjacent-radius compatibility that creates canonical coverage.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {gapEpsilon : Real}

/-! ## The parent-count-times-WZ bound -/

/-- The honest fixed local-card parameter supplied by the level-zero parent
partition.  The WZ factor is dimension-only, while the parent count remains
actual hierarchy data. -/
def hierarchyWZPackedSeedCardBound
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) : Nat :=
  levelZeroParentCount H hdepth * commonHundredNeighbourPackingConstant

/-- A real parent-partition collision-cell capture and hierarchy-level WZ
separation bound the cardinality of the effective level-zero refined family. -/
theorem hierarchyWZPacked_refined_card_le
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {G : HierarchyRandomMotionGeometry H}
    {J : HierarchyJointRandomMotionCertificate H G}
    {hdepth : 0 < depth}
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H) :
    (H.effectiveFamily 0).refinement.refined.card <=
      hierarchyWZPackedSeedCardBound H hdepth := by
  change (H.family 0).refinement.refined.card <=
    levelZeroParentCount H hdepth * commonHundredNeighbourPackingConstant
  exact
    Z.initialRefined_card_le_parentCount_mul_commonHundredNeighbourPackingConstant W

/-! ## Capture-to-seed adapters -/

/-- The WZ-packed refined-card estimate supplies the generated seed budget
for an arbitrary coherent cover of the effective level-zero family. -/
theorem hierarchyWZPacked_fullyAutomaticFixedLocalCardSeedBudget
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
    {G : HierarchyRandomMotionGeometry H}
    {J : HierarchyJointRandomMotionCertificate H G}
    {hdepth : 0 < depth}
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (hierarchyWZPackedSeedCardBound H hdepth) eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget C
      (hierarchyWZPackedSeedCardBound H hdepth)
      eta N gap_pos delta_le := by
  exact fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le C
    (hierarchyWZPackedSeedCardBound H hdepth) eta N gap_pos delta_le
    (hierarchyWZPacked_refined_card_le H Z W)

/-- Identity-cover specialization of the WZ-packed generated-seed budget. -/
theorem hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {G : HierarchyRandomMotionGeometry H}
    {J : HierarchyJointRandomMotionCertificate H G}
    {hdepth : 0 < depth}
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (hierarchyWZPackedSeedCardBound H hdepth) eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover (H.effectiveFamily 0))
      (hierarchyWZPackedSeedCardBound H hdepth)
      eta N gap_pos delta_le := by
  exact hierarchyWZPacked_fullyAutomaticFixedLocalCardSeedBudget H
    (identityRadiusCoherentCover (H.effectiveFamily 0)) Z W eta N
    gap_pos delta_le

/-! ## Canonical coverage and radius-compatible producers -/

/-- Canonical parent-cell coverage is enough: its existing adapter constructs
the complete parent-partition capture before applying WZ packing. -/
theorem hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_canonicalCoverage
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {G : HierarchyRandomMotionGeometry H}
    {J : HierarchyJointRandomMotionCertificate H G}
    {hdepth : 0 < depth}
    (U : CanonicalLevelZeroParentCellCoverage
      (H := H) (G := G) (J := J) hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (hierarchyWZPackedSeedCardBound H hdepth) eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover (H.effectiveFamily 0))
      (hierarchyWZPackedSeedCardBound H hdepth)
      eta N gap_pos delta_le := by
  exact hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget H
    (parentPartitionCaptureOfCanonicalCoverage U) W eta N gap_pos delta_le

/-- The actual hierarchy radius compatibility produces canonical coverage;
the coverage produces the parent-partition capture; WZ separation then
supplies the generated identity seed's local-card budget. -/
theorem hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {G : HierarchyRandomMotionGeometry H}
    {J : HierarchyJointRandomMotionCertificate H G}
    {hdepth : 0 < depth}
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (hierarchyWZPackedSeedCardBound H hdepth) eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover (H.effectiveFamily 0))
      (hierarchyWZPackedSeedCardBound H hdepth)
      eta N gap_pos delta_le := by
  exact
    hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_canonicalCoverage
      H
      (canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
        (G := G) (J := J) H R)
      W eta N gap_pos delta_le

/-! ## Optional finite parent-code compression -/

/-- If the active level-zero parents embed into `Fin parentLoss`, the same
packing argument replaces the actual parent count by `parentLoss`. -/
theorem hierarchyWZPacked_refined_card_le_parentLoss
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {G : HierarchyRandomMotionGeometry H}
    {J : HierarchyJointRandomMotionCertificate H G}
    {hdepth : 0 < depth} {parentLoss : Nat}
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H) :
    (H.effectiveFamily 0).refinement.refined.card <=
      parentLoss * commonHundredNeighbourPackingConstant := by
  exact (hierarchyWZPacked_refined_card_le H Z W).trans
    (Nat.mul_le_mul_right commonHundredNeighbourPackingConstant
      (LevelZeroParentCode.parentCount_le P))

/-- Parent-code compression also directly supplies the generated identity
seed budget at `parentLoss * commonHundredNeighbourPackingConstant`. -/
theorem hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_parentCode
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    {G : HierarchyRandomMotionGeometry H}
    {J : HierarchyJointRandomMotionCertificate H G}
    {hdepth : 0 < depth} {parentLoss : Nat}
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        (parentLoss * commonHundredNeighbourPackingConstant)
        eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover (H.effectiveFamily 0))
      (parentLoss * commonHundredNeighbourPackingConstant)
      eta N gap_pos delta_le := by
  exact identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
    (H.effectiveFamily 0)
    (parentLoss * commonHundredNeighbourPackingConstant)
    eta N gap_pos delta_le
    (hierarchyWZPacked_refined_card_le_parentLoss H P Z W)

#print axioms hierarchyWZPacked_refined_card_le
#print axioms hierarchyWZPacked_fullyAutomaticFixedLocalCardSeedBudget
#print axioms hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget
#print axioms hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_canonicalCoverage
#print axioms hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_levelZeroRadiusCompatible
#print axioms hierarchyWZPacked_refined_card_le_parentLoss
#print axioms hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_parentCode

end
end FamilyStickyScaleChainWZPackedSeedLocalCardBudgetV2
