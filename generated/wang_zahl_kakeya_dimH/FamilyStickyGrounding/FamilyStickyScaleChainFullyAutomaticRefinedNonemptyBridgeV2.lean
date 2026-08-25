import FamilyStickyGrounding.FamilyStickyHierarchyEndpointNonemptyProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticRefinedNonemptyBridgeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainFullyAutomaticDeltaThresholdV2
open FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1

noncomputable section

/-!
# Refined-nonempty bridge for the fully automatic Family 7 endpoint

A general `UniformTubeFamily` may have an empty refined index set, so no
unconditional nonemptiness theorem is possible.  A positive-depth
`MultiscaleTubeHierarchy` is different: its certified level-zero step has an
occupied coarse set and a surjective parent map.  The existing hierarchy
nonemptiness theorem therefore supplies exactly the refined-nonempty premise
of the fully automatic endpoint.

The bridge below only specializes to the literal family
`H.effectiveFamily 0`.  It does not use the exact-hierarchy constructor from a
coherent cover, since that constructor already accepts refined nonemptiness
and would make the argument circular.
-/

universe u

variable {depth N : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {gapEpsilon targetExponent : Real} {eta : Nat -> Real}

/-! ## The non-circular hierarchy and certificate projections -/

/-- Positive hierarchy depth supplies the exact refined-nonempty premise
needed by the automatic seed construction at the effective level-zero
family. -/
theorem hierarchyEffectiveFamilyZero_refined_nonempty
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) :
    (H.effectiveFamily 0).refinement.refined.Nonempty :=
  FamilyStickyHierarchyEndpointNonemptyProducerV1.MultiscaleTubeHierarchy.effectiveFamily_zero_refined_nonempty
    H hdepth

variable
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  {C : CoherentStickyMultiscaleCover (H.effectiveFamily 0)}
  {S : FiniteScaleSequence (H.effectiveRadius 0) depth}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}

/-- A final multiscale assembly certificate carries positive depth, so its
literal hierarchy level-zero family is refined-nonempty with no additional
caller premise. -/
theorem finalAssemblyEffectiveFamilyZero_refined_nonempty
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError) :
    (H.effectiveFamily 0).refinement.refined.Nonempty :=
  hierarchyEffectiveFamilyZero_refined_nonempty H A.depth_pos

/-! ## Direct endpoint adapters -/

/-- Specialize the fully automatic two-exponent endpoint to the level-zero
effective family of any positive-depth hierarchy.  The only removed premise
is refined nonemptiness; all genuine numerical and positivity assumptions
remain explicit. -/
theorem identityFullyAutomaticRelevant_sticky_or_recoveredWitness_of_hierarchy
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticDeltaThreshold (Index 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover (H.effectiveFamily 0)).base.IsStickyAtEveryScale
        ((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1)
        (((Fintype.card (Index 0) : ENNReal) *
            capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
          (Fintype.card (Index 0) : ENNReal)) ∨
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticRelevantTerminalStage
            (identityRadiusCoherentCover (H.effectiveFamily 0))
            delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
            (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le)
          targetExponent)) :=
  identityFullyAutomaticRelevant_sticky_or_recoveredWitness
    (H.effectiveFamily 0) delta_pos gap_pos eta_monotone
      two_lt_eta_zero exponent_budget room_at_bound
      (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le

/-- V1 literal-witness compatibility form of the hierarchy specialization. -/
theorem identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness_of_hierarchy
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticDeltaThreshold (Index 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover (H.effectiveFamily 0)).base.IsStickyAtEveryScale
        ((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1)
        (((Fintype.card (Index 0) : ENNReal) *
            capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
          (Fintype.card (Index 0) : ENNReal)) ∨
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticRelevantTerminalStage
            (identityRadiusCoherentCover (H.effectiveFamily 0))
            delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
            (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le)
          targetExponent)) :=
  identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness
    (H.effectiveFamily 0) delta_pos gap_pos eta_monotone
      two_lt_eta_zero exponent_budget room_at_bound
      (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le

/-- A final assembly certificate supplies both positivity hypotheses that
come from the hierarchy (`depth > 0` and positive level-zero radius), hence
the fully automatic identity endpoint needs only its numerical assumptions. -/
theorem identityFullyAutomaticRelevant_sticky_or_recoveredWitness_of_finalAssembly
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticDeltaThreshold (Index 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover (H.effectiveFamily 0)).base.IsStickyAtEveryScale
        ((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1)
        (((Fintype.card (Index 0) : ENNReal) *
            capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
          (Fintype.card (Index 0) : ENNReal)) ∨
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticRelevantTerminalStage
            (identityRadiusCoherentCover (H.effectiveFamily 0))
            A.initialRadius_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
            (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le)
          targetExponent)) :=
  identityFullyAutomaticRelevant_sticky_or_recoveredWitness
    (H.effectiveFamily 0) A.initialRadius_pos gap_pos eta_monotone
      two_lt_eta_zero exponent_budget room_at_bound
      (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le

/-- V1 literal-witness compatibility form of the final-assembly adapter. -/
theorem identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness_of_finalAssembly
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticDeltaThreshold (Index 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover (H.effectiveFamily 0)).base.IsStickyAtEveryScale
        ((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1)
        (((Fintype.card (Index 0) : ENNReal) *
            capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
          (Fintype.card (Index 0) : ENNReal)) ∨
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticRelevantTerminalStage
            (identityRadiusCoherentCover (H.effectiveFamily 0))
            A.initialRadius_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
            (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le)
          targetExponent)) :=
  identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness
    (H.effectiveFamily 0) A.initialRadius_pos gap_pos eta_monotone
      two_lt_eta_zero exponent_budget room_at_bound
      (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le

#print axioms hierarchyEffectiveFamilyZero_refined_nonempty
#print axioms finalAssemblyEffectiveFamilyZero_refined_nonempty
#print axioms identityFullyAutomaticRelevant_sticky_or_recoveredWitness_of_hierarchy
#print axioms identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness_of_hierarchy
#print axioms identityFullyAutomaticRelevant_sticky_or_recoveredWitness_of_finalAssembly
#print axioms identityFullyAutomaticRelevant_sticky_or_recoveredLiteralWitness_of_finalAssembly

end
end FamilyStickyScaleChainFullyAutomaticRefinedNonemptyBridgeV2
