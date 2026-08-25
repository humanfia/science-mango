import FamilyStickyGrounding.FamilyStickyScaleChainConcreteAutomaticFinalOutcomeV2
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticRefinedNonemptyBridgeV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainConcreteAutomaticHierarchyEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainConcreteAutomaticNumericsV2
open FamilyStickyScaleChainConcreteAutomaticFinalOutcomeV2
open FamilyStickyScaleChainFullyAutomaticRefinedNonemptyBridgeV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1

noncomputable section

/-!
# Concrete automatic Family 7 endpoint for a hierarchy

Positive hierarchy depth supplies refined nonemptiness at the literal
effective level-zero family.  The concrete automatic endpoint can therefore
retain its terminal all-large certificate without asking callers for a
separate refined-nonempty premise.  A final multiscale assembly certificate
also supplies both positive depth and the positive initial radius.
-/

universe u

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-! ## Positive-depth hierarchy endpoint -/

/-- The concrete automatic terminal state attached to the effective
level-zero family of a positive-depth hierarchy. -/
def hierarchyConcreteAutomaticFinalTerminalState
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (delta_le : H.effectiveRadius 0 <=
      concreteAutomaticDeltaThreshold (Index 0)) :=
  concreteAutomaticFinalTerminalState (H.effectiveFamily 0) delta_pos
    (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le

/-- The fixed concrete run on `H.effectiveFamily 0` either retains the
literal all-large certificate of its automatic terminal scale chain together
with Sticky, or gives the recovered two-exponent witness. -/
theorem identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness_of_hierarchy
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (delta_le : H.effectiveRadius 0 <=
      concreteAutomaticDeltaThreshold (Index 0)) :
    ((hierarchyConcreteAutomaticFinalTerminalState H hdepth delta_pos
          delta_le).counted.data.scales.AllStepsLarge
        concreteAutomaticGap /\
      (identityRadiusCoherentCover
          (H.effectiveFamily 0)).base.IsStickyAtEveryScale
        ((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1)
        (((Fintype.card (Index 0) : ENNReal) *
            capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
          (Fintype.card (Index 0) : ENNReal))) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) concreteAutomaticStageBound
        concreteAutomaticGap concreteAutomaticTargetExponent
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage (H.effectiveFamily 0) delta_pos
            (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
            delta_le)
          concreteAutomaticTargetExponent)) := by
  simpa [hierarchyConcreteAutomaticFinalTerminalState] using
    (identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness
      (H.effectiveFamily 0) delta_pos
      (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le)

/-- V1 literal-witness projection of the concrete positive-depth hierarchy
endpoint. -/
theorem identityConcreteAutomaticFinal_sticky_or_recoveredLiteralWitness_of_hierarchy
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (delta_le : H.effectiveRadius 0 <=
      concreteAutomaticDeltaThreshold (Index 0)) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) concreteAutomaticStageBound
        concreteAutomaticGap
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage (H.effectiveFamily 0) delta_pos
            (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
            delta_le)
          concreteAutomaticTargetExponent)) := by
  rcases
      identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness_of_hierarchy
        H hdepth delta_pos delta_le with ⟨_hall, sticky⟩ | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

/-! ## Final multiscale assembly endpoint -/

variable
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  {C : CoherentStickyMultiscaleCover (H.effectiveFamily 0)}
  {S : FiniteScaleSequence (H.effectiveRadius 0) depth}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}

/-- The concrete terminal state generated from a final assembly certificate;
positive depth, positive initial radius, and refined nonemptiness are all
projected from `A`. -/
def finalAssemblyConcreteAutomaticFinalTerminalState
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (delta_le : H.effectiveRadius 0 <=
      concreteAutomaticDeltaThreshold (Index 0)) :=
  concreteAutomaticFinalTerminalState (H.effectiveFamily 0)
    A.initialRadius_pos
    (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le

/-- Certificate-preserving concrete outcome from a final multiscale assembly
certificate.  Besides `A`, the only public premise is the single concrete
delta-threshold comparison. -/
theorem identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness_of_finalAssembly
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (delta_le : H.effectiveRadius 0 <=
      concreteAutomaticDeltaThreshold (Index 0)) :
    ((finalAssemblyConcreteAutomaticFinalTerminalState A
          delta_le).counted.data.scales.AllStepsLarge
        concreteAutomaticGap /\
      (identityRadiusCoherentCover
          (H.effectiveFamily 0)).base.IsStickyAtEveryScale
        ((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1)
        (((Fintype.card (Index 0) : ENNReal) *
            capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
          (Fintype.card (Index 0) : ENNReal))) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) concreteAutomaticStageBound
        concreteAutomaticGap concreteAutomaticTargetExponent
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage (H.effectiveFamily 0)
            A.initialRadius_pos
            (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le)
          concreteAutomaticTargetExponent)) := by
  simpa [finalAssemblyConcreteAutomaticFinalTerminalState] using
    (identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness
      (H.effectiveFamily 0) A.initialRadius_pos
      (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le)

/-- V1 literal-witness projection of the final-assembly concrete endpoint. -/
theorem identityConcreteAutomaticFinal_sticky_or_recoveredLiteralWitness_of_finalAssembly
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (delta_le : H.effectiveRadius 0 <=
      concreteAutomaticDeltaThreshold (Index 0)) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) concreteAutomaticStageBound
        concreteAutomaticGap
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage (H.effectiveFamily 0)
            A.initialRadius_pos
            (finalAssemblyEffectiveFamilyZero_refined_nonempty A) delta_le)
          concreteAutomaticTargetExponent)) := by
  rcases
      identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness_of_finalAssembly
        A delta_le with ⟨_hall, sticky⟩ | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms hierarchyConcreteAutomaticFinalTerminalState
#print axioms identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness_of_hierarchy
#print axioms identityConcreteAutomaticFinal_sticky_or_recoveredLiteralWitness_of_hierarchy
#print axioms finalAssemblyConcreteAutomaticFinalTerminalState
#print axioms identityConcreteAutomaticFinal_allLargeAndSticky_or_recoveredWitness_of_finalAssembly
#print axioms identityConcreteAutomaticFinal_sticky_or_recoveredLiteralWitness_of_finalAssembly

end
end FamilyStickyScaleChainConcreteAutomaticHierarchyEndpointV2
