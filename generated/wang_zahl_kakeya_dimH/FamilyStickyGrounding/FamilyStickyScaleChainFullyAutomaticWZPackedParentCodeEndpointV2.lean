import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticWZPackedHierarchyEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticWZPackedParentCodeEndpointV2

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
# Fully automatic WZ-packed endpoint with a finite parent code

A `LevelZeroParentCode` embeds the genuinely active level-zero parent
subtype into `Fin parentLoss`.  Combining that real code with the WZ
common-`100 T` packing theorem gives the local-card parameter

`parentLoss * commonHundredNeighbourPackingConstant`.

The capture, canonical-coverage, and actual-radius-compatible interfaces
below feed that parameter into the fully automatic fixed-local-card
recursion.  Positive initial radius comes from the random-motion geometry,
and refined nonemptiness comes from positive hierarchy depth.  Consequently
the public endpoints expose neither of those propositions and expose no
seed-budget proposition.

The WZ factor is dimension-only, but `parentLoss` is an explicit code size
for the hierarchy's active parent set.  No dimension-only cardinality or
delta threshold is claimed.
-/

universe u

variable {depth N parentLoss : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {gapEpsilon targetExponent : Real} {eta : Nat -> Real}

/-! ## Parent-code WZ threshold -/

/-- The automatic threshold with local-card parameter
`parentLoss * commonHundredNeighbourPackingConstant`. -/
def fullyAutomaticWZPackedParentCodeDeltaThreshold
    (parentLoss : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) : NNReal :=
  fullyAutomaticFixedLocalCardDeltaThreshold
    (parentLoss * commonHundredNeighbourPackingConstant)
    eta N gapEpsilon

theorem fullyAutomaticWZPackedParentCodeDeltaThreshold_pos
    (parentLoss : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    0 < fullyAutomaticWZPackedParentCodeDeltaThreshold
      parentLoss eta N gapEpsilon := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_pos
    (parentLoss * commonHundredNeighbourPackingConstant)
    eta N gapEpsilon

theorem fullyAutomaticWZPackedParentCodeDeltaThreshold_le_one
    (parentLoss : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    fullyAutomaticWZPackedParentCodeDeltaThreshold
      parentLoss eta N gapEpsilon <= 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_le_one
    (parentLoss * commonHundredNeighbourPackingConstant)
    eta N gapEpsilon

theorem fullyAutomaticWZPackedParentCodeDeltaThreshold_lt_one
    (parentLoss : Nat) (eta : Nat -> Real) {N : Nat}
    (N_pos : 1 <= N) (gapEpsilon : Real) :
    fullyAutomaticWZPackedParentCodeDeltaThreshold
      parentLoss eta N gapEpsilon < 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_lt_one
    (parentLoss * commonHundredNeighbourPackingConstant)
    eta N_pos gapEpsilon

/-! ## Capture-level terminal and endpoint -/

/-- Terminal stage whose seed budget is discharged by the genuine parent
code, parent-partition capture, and WZ separation data. -/
def fullyAutomaticWZPackedParentCodeTerminalStage
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) : Nat :=
  fullyAutomaticFixedLocalCardTerminalStage
    (identityRadiusCoherentCover (H.effectiveFamily 0))
    (parentLoss * commonHundredNeighbourPackingConstant)
    (randomMotionGeometry_levelZero_childRadius_pos
      (G := G) (hdepth := hdepth) H)
    gap_pos eta_monotone two_lt_eta_zero exponent_budget
    (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
    delta_le
    (hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_parentCode
      H P Z W eta N gap_pos delta_le)

/-- Capture-level parent-code endpoint.  Its local-card seed certificate,
initial-radius positivity, and refined nonemptiness are all internal. -/
theorem identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) :
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
          (fullyAutomaticWZPackedParentCodeTerminalStage
            H G J hdepth P Z W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  simpa [fullyAutomaticWZPackedParentCodeTerminalStage] using
    (identityFullyAutomaticFixedLocalCard_sticky_or_recoveredWitness
      (H.effectiveFamily 0)
      (parentLoss * commonHundredNeighbourPackingConstant)
      (randomMotionGeometry_levelZero_childRadius_pos
        (G := G) (hdepth := hdepth) H)
      gap_pos eta_monotone two_lt_eta_zero exponent_budget room_at_bound
      (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
      delta_le
      (hierarchyWZPackedIdentity_fullyAutomaticFixedLocalCardSeedBudget_of_parentCode
        H P Z W eta N gap_pos delta_le))

/-- V1 literal-witness projection of the capture-level parent-code
endpoint. -/
theorem identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredLiteralWitness
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (Z : LevelZeroParentPartitionCollisionCellCapture H G J hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) :
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
          (fullyAutomaticWZPackedParentCodeTerminalStage
            H G J hdepth P Z W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  rcases identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness
      H G J hdepth P Z W gap_pos eta_monotone two_lt_eta_zero
      exponent_budget room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨witness⟩
    exact Or.inr ⟨witness.toV1⟩

/-! ## Canonical-coverage endpoint -/

/-- Terminal stage after canonical coverage has generated the required
parent-partition capture. -/
def fullyAutomaticWZPackedParentCodeTerminalStage_of_canonicalCoverage
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (U : CanonicalLevelZeroParentCellCoverage
      (H := H) (G := G) (J := J) hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) : Nat :=
  fullyAutomaticWZPackedParentCodeTerminalStage H G J hdepth P
    (parentPartitionCaptureOfCanonicalCoverage U) W gap_pos
    eta_monotone two_lt_eta_zero exponent_budget delta_le

/-- Canonical coverage closes the complete parent-code WZ-packed
two-exponent dichotomy. -/
theorem identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_canonicalCoverage
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (U : CanonicalLevelZeroParentCellCoverage
      (H := H) (G := G) (J := J) hdepth)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) :
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
          (fullyAutomaticWZPackedParentCodeTerminalStage_of_canonicalCoverage
            H G J hdepth P U W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  simpa
      [fullyAutomaticWZPackedParentCodeTerminalStage_of_canonicalCoverage]
    using
      (identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness
        H G J hdepth P (parentPartitionCaptureOfCanonicalCoverage U) W
        gap_pos eta_monotone two_lt_eta_zero exponent_budget
        room_at_bound delta_le)

/-! ## Preferred actual-radius-compatible endpoint -/

/-- Terminal stage after actual hierarchy radius compatibility has produced
canonical coverage and hence the compressed WZ seed budget. -/
def fullyAutomaticWZPackedParentCodeTerminalStage_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) : Nat :=
  fullyAutomaticWZPackedParentCodeTerminalStage_of_canonicalCoverage
    H G J hdepth P
    (canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
      (G := G) (J := J) H R)
    W gap_pos eta_monotone two_lt_eta_zero exponent_budget delta_le

/-- Preferred parent-code endpoint.  The public geometric data construct
capture, seed budget, initial-radius positivity, and refined nonemptiness;
the caller supplies only the parent code, radius/WZ certificates, and the
remaining numerical assumptions. -/
theorem identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) :
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
          (fullyAutomaticWZPackedParentCodeTerminalStage_of_levelZeroRadiusCompatible
            H G J hdepth P R W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  simpa
      [fullyAutomaticWZPackedParentCodeTerminalStage_of_levelZeroRadiusCompatible]
    using
      (identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_canonicalCoverage
        H G J hdepth P
        (canonicalLevelZeroParentCellCoverage_of_levelZeroRadiusCompatible
          (G := G) (J := J) H R)
        W gap_pos eta_monotone two_lt_eta_zero exponent_budget
        room_at_bound delta_le)

/-- V1 literal-witness projection of the preferred radius-compatible
parent-code endpoint. -/
theorem identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredLiteralWitness_of_levelZeroRadiusCompatible
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (G : HierarchyRandomMotionGeometry H)
    (J : HierarchyJointRandomMotionCertificate H G)
    (hdepth : 0 < depth)
    (P : LevelZeroParentCode (H := H) hdepth parentLoss)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (W : HierarchyLevelWZSeparationData H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) :
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
          (fullyAutomaticWZPackedParentCodeTerminalStage_of_levelZeroRadiusCompatible
            H G J hdepth P R W gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  rcases
      identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
        H G J hdepth P R W gap_pos eta_monotone two_lt_eta_zero
        exponent_budget room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨witness⟩
    exact Or.inr ⟨witness.toV1⟩

#print axioms fullyAutomaticWZPackedParentCodeDeltaThreshold_pos
#print axioms fullyAutomaticWZPackedParentCodeDeltaThreshold_le_one
#print axioms fullyAutomaticWZPackedParentCodeDeltaThreshold_lt_one
#print axioms fullyAutomaticWZPackedParentCodeTerminalStage
#print axioms identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness
#print axioms identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredLiteralWitness
#print axioms fullyAutomaticWZPackedParentCodeTerminalStage_of_canonicalCoverage
#print axioms identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_canonicalCoverage
#print axioms fullyAutomaticWZPackedParentCodeTerminalStage_of_levelZeroRadiusCompatible
#print axioms identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
#print axioms identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredLiteralWitness_of_levelZeroRadiusCompatible

end
end FamilyStickyScaleChainFullyAutomaticWZPackedParentCodeEndpointV2
