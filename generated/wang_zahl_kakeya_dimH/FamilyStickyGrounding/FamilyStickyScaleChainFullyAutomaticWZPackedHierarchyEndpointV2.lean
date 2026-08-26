import FamilyStickyGrounding.FamilyStickyScaleChainWZPackedSeedLocalCardBudgetV2
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticRefinedCardEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticWZPackedHierarchyEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2
open FamilyStickyScaleChainFullyAutomaticRefinedNonemptyBridgeV2
open FamilyStickyScaleChainFullyAutomaticRefinedCardEndpointV2
open FamilyStickyScaleChainWZPackedSeedLocalCardBudgetV2
open FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainSelectedRestrictionParentPartitionCollisionBindingV1
open FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1

noncomputable section

/-!
# Fully automatic hierarchy endpoint from real WZ parent packing

At positive hierarchy depth, the actual level-zero parent partition and the
WZ common-`100 T` packing theorem bound the refined source cardinality by

`levelZeroParentCount * commonHundredNeighbourPackingConstant`.

The corresponding fixed-local-card threshold is therefore a complete
Family 7 input once parent-cell capture is available.  Canonical coverage,
and in turn the genuine adjacent-radius compatibility, construct that
capture automatically.  The preferred final wrapper exposes only the real
hierarchy/random-motion/WZ/radius data and numerical assumptions; it does
not expose a seed-budget proposition.

The natural number used by this endpoint still contains the active
level-zero parent count.  It is not a dimension-only bound.  Also, only the
two-exponent branch benefits from the local WZ cardinality estimate: the
Sticky branch deliberately retains its existing ambient-index-cardinality
loss.
-/

universe u

variable {depth N : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {gapEpsilon targetExponent : Real} {eta : Nat -> Real}

/-! ## One WZ-packed threshold -/

/-- The fixed-local-card threshold at the honest parent-count-times-WZ
cardinality bound. -/
def fullyAutomaticWZPackedHierarchyDeltaThreshold
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) : NNReal :=
  fullyAutomaticFixedLocalCardDeltaThreshold
    (hierarchyWZPackedSeedCardBound H hdepth) eta N gapEpsilon

theorem fullyAutomaticWZPackedHierarchyDeltaThreshold_pos
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    0 < fullyAutomaticWZPackedHierarchyDeltaThreshold
      H hdepth eta N gapEpsilon := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_pos
    (hierarchyWZPackedSeedCardBound H hdepth) eta N gapEpsilon

theorem fullyAutomaticWZPackedHierarchyDeltaThreshold_le_one
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    fullyAutomaticWZPackedHierarchyDeltaThreshold
      H hdepth eta N gapEpsilon <= 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_le_one
    (hierarchyWZPackedSeedCardBound H hdepth) eta N gapEpsilon

theorem fullyAutomaticWZPackedHierarchyDeltaThreshold_lt_one
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) {N : Nat}
    (N_pos : 1 <= N) (gapEpsilon : Real) :
    fullyAutomaticWZPackedHierarchyDeltaThreshold
      H hdepth eta N gapEpsilon < 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_lt_one
    (hierarchyWZPackedSeedCardBound H hdepth) eta N_pos gapEpsilon

/-! ## Capture-level terminal stage and endpoints -/

/-- Readable terminal stage of the fixed-local-card recursion whose seed
budget comes from an actual parent-partition capture and WZ separation.
Initial-radius positivity is supplied by the random-motion geometry and
refined nonemptiness by positive hierarchy depth. -/
def fullyAutomaticWZPackedHierarchyTerminalStage
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) : Nat :=
  fullyAutomaticFixedLocalCardTerminalStage
    (identityRadiusCoherentCover (H.effectiveFamily 0))
    (hierarchyWZPackedSeedCardBound H hdepth)
    (randomMotionGeometry_levelZero_childRadius_pos
      (G := G) (hdepth := hdepth) H)
    gap_pos eta_monotone two_lt_eta_zero exponent_budget
    (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
    delta_le
    (hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget
      H Z W eta N gap_pos delta_le)

/-- Actual parent-partition capture plus WZ separation closes the automatic
identity-cover dichotomy without a public seed-budget hypothesis. -/
theorem identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticWZPackedHierarchyTerminalStage H G J hdepth Z W
            gap_pos eta_monotone two_lt_eta_zero exponent_budget delta_le)
          targetExponent)) := by
  simpa [fullyAutomaticWZPackedHierarchyTerminalStage] using
    (identityFullyAutomaticFixedLocalCard_sticky_or_recoveredWitness
      (H.effectiveFamily 0)
      (hierarchyWZPackedSeedCardBound H hdepth)
      (randomMotionGeometry_levelZero_childRadius_pos
        (G := G) (hdepth := hdepth) H)
      gap_pos eta_monotone two_lt_eta_zero exponent_budget room_at_bound
      (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
      delta_le
      (hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget
        H Z W eta N gap_pos delta_le))

/-- V1 literal-witness projection of the capture-level WZ-packed endpoint. -/
theorem identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredLiteralWitness
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticWZPackedHierarchyTerminalStage H G J hdepth Z W
            gap_pos eta_monotone two_lt_eta_zero exponent_budget delta_le)
          targetExponent)) := by
  rcases identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness
      H G J hdepth Z W gap_pos eta_monotone two_lt_eta_zero
      exponent_budget room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨witness⟩
    exact Or.inr ⟨witness.toV1⟩

/-! ## Canonical-coverage endpoint -/

/-- Terminal stage after canonical coverage has been converted to the real
parent-partition capture. -/
def fullyAutomaticWZPackedHierarchyTerminalStage_of_canonicalCoverage
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (U : CanonicalLevelZeroParentCellCoverage
      (H := H) (G := G) (J := J) hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) : Nat :=
  fullyAutomaticWZPackedHierarchyTerminalStage H G J hdepth
    (parentPartitionCaptureOfCanonicalCoverage U) W gap_pos
    eta_monotone two_lt_eta_zero exponent_budget delta_le

/-- Canonical parent-cell coverage closes the complete two-exponent
dichotomy through the existing capture adapter. -/
theorem identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness_of_canonicalCoverage
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (U : CanonicalLevelZeroParentCellCoverage
      (H := H) (G := G) (J := J) hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticWZPackedHierarchyTerminalStage_of_canonicalCoverage
            H G J hdepth U W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  simpa [fullyAutomaticWZPackedHierarchyTerminalStage_of_canonicalCoverage] using
    (identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness
      H G J hdepth (parentPartitionCaptureOfCanonicalCoverage U) W
      gap_pos eta_monotone two_lt_eta_zero exponent_budget
      room_at_bound delta_le)

/-! ## Preferred actual-radius endpoint -/

/-- Readable terminal stage after actual adjacent-radius compatibility has
generated canonical coverage and hence the WZ-packed seed budget. -/
def fullyAutomaticWZPackedHierarchyTerminalStage_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) : Nat :=
  fullyAutomaticWZPackedHierarchyTerminalStage_of_canonicalCoverage
    H G J hdepth
    (canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
      (G := G) (J := J) H R)
    W gap_pos eta_monotone two_lt_eta_zero exponent_budget delta_le

/-- Preferred real-data endpoint.  The hierarchy, random geometry, joint
certificate, positive depth, radius compatibility, and WZ separation
construct the seed budget internally.  Only numerical endpoint assumptions
remain besides those geometric inputs. -/
theorem identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticWZPackedHierarchyTerminalStage_of_levelZeroRadiusCompatible
            H G J hdepth R W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  simpa
      [fullyAutomaticWZPackedHierarchyTerminalStage_of_levelZeroRadiusCompatible]
    using
      (identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness_of_canonicalCoverage
        H G J hdepth
        (canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
          (G := G) (J := J) H R)
        W gap_pos eta_monotone two_lt_eta_zero exponent_budget
        room_at_bound delta_le)

/-- V1 literal-witness projection of the preferred actual-radius endpoint. -/
theorem identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredLiteralWitness_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H hdepth eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticWZPackedHierarchyTerminalStage_of_levelZeroRadiusCompatible
            H G J hdepth R W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  rcases
      identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
        H G J hdepth R W gap_pos eta_monotone two_lt_eta_zero
        exponent_budget room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨witness⟩
    exact Or.inr ⟨witness.toV1⟩

#print axioms fullyAutomaticWZPackedHierarchyDeltaThreshold_pos
#print axioms fullyAutomaticWZPackedHierarchyDeltaThreshold_le_one
#print axioms fullyAutomaticWZPackedHierarchyDeltaThreshold_lt_one
#print axioms fullyAutomaticWZPackedHierarchyTerminalStage
#print axioms identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness
#print axioms identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredLiteralWitness
#print axioms fullyAutomaticWZPackedHierarchyTerminalStage_of_canonicalCoverage
#print axioms identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness_of_canonicalCoverage
#print axioms fullyAutomaticWZPackedHierarchyTerminalStage_of_levelZeroRadiusCompatible
#print axioms identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
#print axioms identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredLiteralWitness_of_levelZeroRadiusCompatible

end
end FamilyStickyScaleChainFullyAutomaticWZPackedHierarchyEndpointV2
