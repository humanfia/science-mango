import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainConcreteAutomaticNumericsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainFullyAutomaticDeltaThresholdV2
open FamilyStickyScaleChainFullyAutomaticRelevantEndpointV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# One concrete feasible automatic parameter choice

Take five counted stages, gap exponent one half, the constant profile three,
and target exponent four.  These values satisfy every numerical premise of
the fully automatic relevant endpoint.  The resulting wrapper exposes only
the fine family, positivity/nonemptiness geometry, and one comparison with a
fixed positive delta threshold.
-/

universe u

/-- Concrete counted-stage budget. -/
def concreteAutomaticStageBound : Nat := 5

/-- Concrete separating gap exponent. -/
def concreteAutomaticGap : Real := 1 / 2

/-- Concrete constant exponent profile. -/
def concreteAutomaticEta : Nat -> Real := fun _ => 3

/-- Concrete recovered target exponent. -/
def concreteAutomaticTargetExponent : Real := 4

@[simp] theorem concreteAutomaticEta_apply (n : Nat) :
    concreteAutomaticEta n = 3 :=
  rfl

theorem concreteAutomaticGap_pos : 0 < concreteAutomaticGap := by
  norm_num [concreteAutomaticGap]

theorem concreteAutomaticEta_monotone : Monotone concreteAutomaticEta := by
  intro a b _hab
  exact le_rfl

theorem concreteAutomaticEta_zero_gt_two :
    2 < concreteAutomaticEta 0 := by
  norm_num

theorem concreteAutomaticExponentBudget :
    1 < (concreteAutomaticGap * concreteAutomaticGap) *
      (concreteAutomaticStageBound : Real) := by
  norm_num [concreteAutomaticGap, concreteAutomaticStageBound]

theorem concreteAutomaticRoomAtBound :
    concreteAutomaticEta concreteAutomaticStageBound <
      concreteAutomaticTargetExponent := by
  norm_num [concreteAutomaticTargetExponent]

/-- The single concrete threshold consumed by both the capped seed and the
recovered adjacent-card endpoint. -/
def concreteAutomaticDeltaThreshold
    (iota : Type*) [Fintype iota] : NNReal :=
  fullyAutomaticDeltaThreshold iota concreteAutomaticEta
    concreteAutomaticStageBound concreteAutomaticGap

theorem concreteAutomaticDeltaThreshold_pos
    (iota : Type*) [Fintype iota] :
    0 < concreteAutomaticDeltaThreshold iota := by
  exact fullyAutomaticDeltaThreshold_pos iota concreteAutomaticEta
    concreteAutomaticStageBound concreteAutomaticGap

theorem concreteAutomaticDeltaThreshold_lt_one
    (iota : Type*) [Fintype iota] :
    concreteAutomaticDeltaThreshold iota < 1 := by
  exact fullyAutomaticDeltaThreshold_lt_one iota concreteAutomaticEta
    (by norm_num [concreteAutomaticStageBound]) concreteAutomaticGap

variable {delta : NNReal}
  {iota : Type u} [Fintype iota] [DecidableEq iota]

/-- The exact terminal stage of the concrete automatic identity-cover run. -/
def concreteAutomaticTerminalStage
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= concreteAutomaticDeltaThreshold iota) : Nat :=
  fullyAutomaticRelevantTerminalStage (identityRadiusCoherentCover fine)
    delta_pos concreteAutomaticGap_pos concreteAutomaticEta_monotone
    concreteAutomaticEta_zero_gt_two concreteAutomaticExponentBudget
    fine_refined_nonempty delta_le

/-- With the concrete feasible numerical choice, the identity-cover endpoint
requires no remaining abstract profile, stage-window, cap, successor, initial
state, or terminal-stage hypothesis. -/
theorem identityConcreteAutomatic_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= concreteAutomaticDeltaThreshold iota) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta
        concreteAutomaticStageBound concreteAutomaticGap
        concreteAutomaticTargetExponent
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage fine delta_pos
            fine_refined_nonempty delta_le)
          concreteAutomaticTargetExponent)) := by
  simpa [concreteAutomaticTerminalStage,
      concreteAutomaticDeltaThreshold] using
    (identityFullyAutomaticRelevant_sticky_or_recoveredWitness
      (N := concreteAutomaticStageBound) (eta := concreteAutomaticEta)
      (targetExponent := concreteAutomaticTargetExponent)
      fine delta_pos concreteAutomaticGap_pos concreteAutomaticEta_monotone
      concreteAutomaticEta_zero_gt_two concreteAutomaticExponentBudget
      concreteAutomaticRoomAtBound fine_refined_nonempty delta_le)

/-- Compatibility projection of the concrete endpoint to the V1 literal
witness API, with the same exact automatic terminal stage in its profile. -/
theorem identityConcreteAutomatic_sticky_or_recoveredLiteralWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <= concreteAutomaticDeltaThreshold iota) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta concreteAutomaticStageBound
        concreteAutomaticGap
        (recoveredProfileV2 concreteAutomaticEta
          (concreteAutomaticTerminalStage fine delta_pos
            fine_refined_nonempty delta_le)
          concreteAutomaticTargetExponent)) := by
  rcases identityConcreteAutomatic_sticky_or_recoveredWitness fine delta_pos
      fine_refined_nonempty delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms concreteAutomaticGap_pos
#print axioms concreteAutomaticEta_monotone
#print axioms concreteAutomaticEta_zero_gt_two
#print axioms concreteAutomaticExponentBudget
#print axioms concreteAutomaticRoomAtBound
#print axioms concreteAutomaticDeltaThreshold_pos
#print axioms concreteAutomaticDeltaThreshold_lt_one
#print axioms concreteAutomaticTerminalStage
#print axioms identityConcreteAutomatic_sticky_or_recoveredWitness
#print axioms identityConcreteAutomatic_sticky_or_recoveredLiteralWitness

end
end FamilyStickyScaleChainConcreteAutomaticNumericsV2
