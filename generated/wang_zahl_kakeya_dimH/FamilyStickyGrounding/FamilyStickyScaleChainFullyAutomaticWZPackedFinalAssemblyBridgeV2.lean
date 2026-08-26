import FamilyStickyGrounding.FamilyStickyFinalMultiscaleAssemblyCertificateV1
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticWZPackedHierarchyEndpointV2
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticWZPackedParentCodeEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticWZPackedFinalAssemblyBridgeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainParentPartitionCollisionCellSiblingRigidityProducerV1
open FamilyStickyScaleChainCanonicalParentCellCoverageProducerV1
open FamilyStickyScaleChainFullyAutomaticWZPackedHierarchyEndpointV2
open FamilyStickyScaleChainFullyAutomaticWZPackedParentCodeEndpointV2
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1

noncomputable section

/-!
# Final-assembly bridge for fully automatic WZ-packed stopping

A final multiscale assembly certificate already stores one joint
random-motion output, positive hierarchy depth, and hierarchy-level WZ
separation.  This module projects exactly those fields into the two
radius-compatible stopping endpoints:

* the active-parent-count WZ threshold; and
* the compressed `LevelZeroParentCode parentLoss` WZ threshold.

Actual level-zero radius compatibility remains an honest public geometric
premise.  The numerical stopping assumptions also remain explicit.  These
wrappers prove the scale-chain Sticky-or-recovered-witness dichotomy; they do
not claim the full analytic Sticky theorem or identify the dichotomy with the
final paper conclusion.
-/

universe u

variable {depth N parentLoss : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {gapEpsilon targetExponent : Real} {eta : Nat -> Real}
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {packingPlan : HierarchyPackingPlan.Plan H}
  {C : CoherentStickyMultiscaleCover (H.effectiveFamily 0)}
  {S : FiniteScaleSequence (H.effectiveRadius 0) depth}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}

/-! ## Parent-count-times-WZ final-assembly wrapper -/

/-- The readable terminal stage obtained by projecting the stored joint
output, positive depth, and WZ separation data from a final assembly
certificate. -/
def finalAssemblyFullyAutomaticWZPackedHierarchyTerminalStage
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G packingPlan C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H A.depth_pos eta N gapEpsilon) : Nat :=
  fullyAutomaticWZPackedHierarchyTerminalStage_of_levelZeroRadiusCompatible
    H G A.hierarchy.joint A.depth_pos R A.levelWZ gap_pos
    eta_monotone two_lt_eta_zero exponent_budget delta_le

/-- The stored joint output, positive depth, and WZ data close the
parent-count WZ endpoint.  Radius compatibility and the numerical stopping
conditions remain explicit. -/
theorem identityFinalAssemblyFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G packingPlan C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H A.depth_pos eta N gapEpsilon) :
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
          (finalAssemblyFullyAutomaticWZPackedHierarchyTerminalStage
            A R gap_pos eta_monotone two_lt_eta_zero exponent_budget
            delta_le)
          targetExponent)) := by
  simpa [finalAssemblyFullyAutomaticWZPackedHierarchyTerminalStage] using
    (identityFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
      H G A.hierarchy.joint A.depth_pos R A.levelWZ gap_pos
      eta_monotone two_lt_eta_zero exponent_budget room_at_bound delta_le)

/-- V1 literal-witness projection of the parent-count WZ final-assembly
endpoint. -/
theorem identityFinalAssemblyFullyAutomaticWZPackedHierarchy_sticky_or_recoveredLiteralWitness
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G packingPlan C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedHierarchyDeltaThreshold
        H A.depth_pos eta N gapEpsilon) :
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
          (finalAssemblyFullyAutomaticWZPackedHierarchyTerminalStage
            A R gap_pos eta_monotone two_lt_eta_zero exponent_budget
            delta_le)
          targetExponent)) := by
  rcases
      identityFinalAssemblyFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness
        A R gap_pos eta_monotone two_lt_eta_zero exponent_budget
        room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨witness⟩
    exact Or.inr ⟨witness.toV1⟩

/-! ## Parent-code-times-WZ final-assembly wrapper -/

/-- The compressed terminal stage using an actual finite code for the
active level-zero parent subtype. -/
def finalAssemblyFullyAutomaticWZPackedParentCodeTerminalStage
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G packingPlan C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (parentCode : LevelZeroParentCode
      (H := H) A.depth_pos parentLoss)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticWZPackedParentCodeDeltaThreshold
        parentLoss eta N gapEpsilon) : Nat :=
  fullyAutomaticWZPackedParentCodeTerminalStage_of_levelZeroRadiusCompatible
    H G A.hierarchy.joint A.depth_pos parentCode R A.levelWZ gap_pos
    eta_monotone two_lt_eta_zero exponent_budget delta_le

/-- Parent-code compression replaces the actual active-parent count by
`parentLoss`, while the assembly certificate still supplies the joint
output, positive depth, and WZ separation internally. -/
theorem identityFinalAssemblyFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G packingPlan C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (parentCode : LevelZeroParentCode
      (H := H) A.depth_pos parentLoss)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
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
          (finalAssemblyFullyAutomaticWZPackedParentCodeTerminalStage
            A parentCode R gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  simpa [finalAssemblyFullyAutomaticWZPackedParentCodeTerminalStage] using
    (identityFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness_of_levelZeroRadiusCompatible
      H G A.hierarchy.joint A.depth_pos parentCode R A.levelWZ gap_pos
      eta_monotone two_lt_eta_zero exponent_budget room_at_bound delta_le)

/-- V1 literal-witness projection of the parent-code WZ final-assembly
endpoint. -/
theorem identityFinalAssemblyFullyAutomaticWZPackedParentCode_sticky_or_recoveredLiteralWitness
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G packingPlan C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (parentCode : LevelZeroParentCode
      (H := H) A.depth_pos parentLoss)
    (R : LevelZeroCanonicalHundredRadiusCompatible H)
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
          (finalAssemblyFullyAutomaticWZPackedParentCodeTerminalStage
            A parentCode R gap_pos eta_monotone two_lt_eta_zero
            exponent_budget delta_le)
          targetExponent)) := by
  rcases
      identityFinalAssemblyFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness
        A parentCode R gap_pos eta_monotone two_lt_eta_zero exponent_budget
        room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨witness⟩
    exact Or.inr ⟨witness.toV1⟩

#print axioms finalAssemblyFullyAutomaticWZPackedHierarchyTerminalStage
#print axioms identityFinalAssemblyFullyAutomaticWZPackedHierarchy_sticky_or_recoveredWitness
#print axioms identityFinalAssemblyFullyAutomaticWZPackedHierarchy_sticky_or_recoveredLiteralWitness
#print axioms finalAssemblyFullyAutomaticWZPackedParentCodeTerminalStage
#print axioms identityFinalAssemblyFullyAutomaticWZPackedParentCode_sticky_or_recoveredWitness
#print axioms identityFinalAssemblyFullyAutomaticWZPackedParentCode_sticky_or_recoveredLiteralWitness

end
end FamilyStickyScaleChainFullyAutomaticWZPackedFinalAssemblyBridgeV2
