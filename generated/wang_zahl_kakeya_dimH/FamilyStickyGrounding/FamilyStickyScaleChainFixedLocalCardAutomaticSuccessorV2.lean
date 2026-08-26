import FamilyStickyGrounding.FamilyStickyScaleChainLocalCardBudgetInvariantV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFixedLocalCardAutomaticSuccessorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainNormalizedTerminalObstructionV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleChainAutomaticRelevantSuccessorV2
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# Fixed-local-card automatic relevant successor

The analytic atom imported from `LocalCardBudgetInvariantV2` uses one fixed
natural number `n` both as an upper bound for the literal local cardinality
maximum and in the explicit small-theta threshold.  This file applies that
atom to the two children of the relevant canonical insertion.

Every fresh hypothesis is guarded by non-largeness of the same child.  In
particular, no normalized-terminal estimate is assumed at each reachable
split, and a large child has no local-card, profile-room, or small-theta
obligation.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

variable
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C (Q.toState C delta_pos))

/-! ## Fixed-card packages for the two inserted children -/

/-- Fixed-`n` normalized-terminal package for the inserted upper child.
The card premise is the literal canonical local maximum at that child. -/
def relevantUpperNormalizedTerminalBound_of_fixedLocalCardSmallTheta
    (n : Nat)
    (profile_gt_two : 2 < eta Q.stage)
    (local_card_le :
      canonicalOneStepLocalCardBound C
          (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <= n)
    (theta_le_threshold :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold n (eta Q.stage)) :
    OneStepNormalizedTerminalExponentBound C
      (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
      (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      eta (Q.stage + 1)
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) := by
  let automaticBound :=
    ofFiniteScaleSequence_automatic_oneStepExponentBound_of_fixedCardSmallTheta
      C (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      Q.fine_refined_nonempty delta_pos eta (Q.stage + 1)
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) n
      (by
        simpa only [relevantInsertedExactFamily] using local_card_le)
      (by simpa only [Nat.add_sub_cancel] using profile_gt_two)
      (by simpa only [Nat.add_sub_cancel] using theta_le_threshold)
  exact oneStepNormalizedTerminalExponentBound_of_eq_at C
    (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
    (fun k => canonicalTerminalUnitBody
      ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy k))
    (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
    (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
    (Q.stage + 1)
    (upperChildIndex (relevantSelectedStep C delta_pos Q bad))
    (relevantAutomaticInsertedBody_upperChild C gap_nonneg delta_pos Q bad).symm
    automaticBound

/-- Fixed-`n` normalized-terminal package for the inserted lower child.
The card premise is the literal canonical local maximum at that child. -/
def relevantLowerNormalizedTerminalBound_of_fixedLocalCardSmallTheta
    (n : Nat)
    (profile_gt_two : 2 < eta Q.stage)
    (local_card_le :
      canonicalOneStepLocalCardBound C
          (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <= n)
    (theta_le_threshold :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold n (eta Q.stage)) :
    OneStepNormalizedTerminalExponentBound C
      (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
      (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      eta (Q.stage + 1)
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) := by
  let automaticBound :=
    ofFiniteScaleSequence_automatic_oneStepExponentBound_of_fixedCardSmallTheta
      C (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      Q.fine_refined_nonempty delta_pos eta (Q.stage + 1)
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) n
      (by
        simpa only [relevantInsertedExactFamily] using local_card_le)
      (by simpa only [Nat.add_sub_cancel] using profile_gt_two)
      (by simpa only [Nat.add_sub_cancel] using theta_le_threshold)
  exact oneStepNormalizedTerminalExponentBound_of_eq_at C
    (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
    (fun k => canonicalTerminalUnitBody
      ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy k))
    (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
    (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
    (Q.stage + 1)
    (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))
    (relevantAutomaticInsertedBody_lowerChild C gap_nonneg delta_pos Q bad).symm
    automaticBound

/-! ## Honest conditional data and certificate adapter -/

/-- Exactly the fixed-`n` data queried for each non-large child.  The local
card premise is stated at the inserted child itself rather than as a global
cardinality bound on `iota`. -/
structure RelevantFixedLocalCardAutomaticChildConditions (n : Nat) : Prop where
  upper :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    2 < eta Q.stage /\
      canonicalOneStepLocalCardBound C
          (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <= n /\
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold n (eta Q.stage)
  lower :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    2 < eta Q.stage /\
      canonicalOneStepLocalCardBound C
          (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <= n /\
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold n (eta Q.stage)

/-- Turn the child-local fixed-card facts into exactly the conditional
normalized-terminal interface used by the relevant invariant. -/
def relevantConditionalNormalizedTerminalBounds_of_fixedLocalCardSmallTheta
    (n : Nat)
    (conditions : RelevantFixedLocalCardAutomaticChildConditions C gap_nonneg
      delta_pos Q bad n) :
    RelevantConditionalNormalizedTerminalBounds C gap_nonneg delta_pos Q bad
    where
  upper := fun child_not_large =>
    relevantUpperNormalizedTerminalBound_of_fixedLocalCardSmallTheta C
      gap_nonneg delta_pos Q bad n
      (conditions.upper child_not_large).1
      (conditions.upper child_not_large).2.1
      (conditions.upper child_not_large).2.2
  lower := fun child_not_large =>
    relevantLowerNormalizedTerminalBound_of_fixedLocalCardSmallTheta C
      gap_nonneg delta_pos Q bad n
      (conditions.lower child_not_large).1
      (conditions.lower child_not_large).2.1
      (conditions.lower child_not_large).2.2

/-- Produce the canonical two-child certificate from fixed-local-card and
small-theta data.  No normalized-terminal package remains an input. -/
def relevantCanonicalChildCertificate_of_fixedLocalCardSmallTheta
    (n : Nat)
    (conditions : RelevantFixedLocalCardAutomaticChildConditions C gap_nonneg
      delta_pos Q bad n) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad :=
  relevantCanonicalChildCertificate_of_conditionalNormalizedBounds C
    gap_nonneg delta_pos Q bad
    (relevantConditionalNormalizedTerminalBounds_of_fixedLocalCardSmallTheta
      C gap_nonneg delta_pos Q bad n conditions)

/-! ## Statewise successor adapter -/

/-- Statewise fixed-local-card hypotheses for the counted recursion.  The
same natural bound `n` is used at every state, while each child obligation
remains conditional on literal non-largeness. -/
def RelevantCanonicalFixedLocalCardAutomaticSuccessorConditions
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (n : Nat) : Prop :=
  forall (X : RelevantCanonicalCountedState C N gapEpsilon eta),
    forall _stage_lt : X.data.stage < N,
    forall bad : RelevantSelectedActualBadSplit C
      (X.toState C delta_pos),
      RelevantFixedLocalCardAutomaticChildConditions C gap_nonneg delta_pos
        X.data bad n

/-- Adapter to the successor type consumed by the relevant counted driver.
It performs no recursion and adds no per-split normalized-terminal premise. -/
def relevantCanonicalChildSuccessor_of_fixedLocalCardSmallTheta
    (n : Nat)
    (conditions :
      RelevantCanonicalFixedLocalCardAutomaticSuccessorConditions
        (N := N) (eta := eta) C gap_nonneg delta_pos n) :
    RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos :=
  fun X stage_lt bad =>
    relevantCanonicalChildCertificate_of_fixedLocalCardSmallTheta C
      gap_nonneg delta_pos X.data bad n (conditions X stage_lt bad)

#print axioms relevantUpperNormalizedTerminalBound_of_fixedLocalCardSmallTheta
#print axioms relevantLowerNormalizedTerminalBound_of_fixedLocalCardSmallTheta
#print axioms relevantConditionalNormalizedTerminalBounds_of_fixedLocalCardSmallTheta
#print axioms relevantCanonicalChildCertificate_of_fixedLocalCardSmallTheta
#print axioms relevantCanonicalChildSuccessor_of_fixedLocalCardSmallTheta

end
end FamilyStickyScaleChainFixedLocalCardAutomaticSuccessorV2
