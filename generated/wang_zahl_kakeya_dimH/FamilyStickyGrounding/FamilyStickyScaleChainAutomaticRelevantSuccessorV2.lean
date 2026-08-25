import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantCountedStoppingDriverV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainAutomaticRelevantSuccessorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# Automatic small-scale successor for the relevant Family 7 recursion

The explicit canonical normalized-terminal upper bound supplies a new child
whenever that child is non-large, its profile exponent has room strictly
beyond two, and its upper endpoint is below the displayed finite-cardinality
threshold.  A large child is never queried for any analytic bound.

The final adapter has exactly the `RelevantCanonicalChildSuccessor` type
consumed by the counted stopping driver.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Body-local transport of a normalized terminal package -/

/-- A normalized terminal package depends on the body family only at its
chosen interval.  This adapter makes that extensionality explicit. -/
def oneStepNormalizedTerminalExponentBound_of_eq_at
    {outerDepth : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (body₁ body₂ : Fin outerDepth -> ConvexBody Space)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (body_eq : body₁ m = body₂ m)
    (bound : OneStepNormalizedTerminalExponentBound C F body₁
      S profile stage m) :
    OneStepNormalizedTerminalExponentBound C F body₂
      S profile stage m where
  exponent := bound.exponent
  normalizedTerminal_upper := by
    simpa only [canonicalOneStepNormalizedTerminalAt, body_eq] using
      bound.normalizedTerminal_upper
  exponent_balance := bound.exponent_balance

variable
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C (Q.toState C delta_pos))

@[simp] theorem relevantAutomaticInsertedBody_upperChild :
    relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) =
      canonicalTerminalUnitBody
        ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) := by
  simp only [relevantAutomaticInsertedBody, relevantInsertedBody,
    relevantInsertedUpperBody, insertedInitialBody_upperChild]

@[simp] theorem relevantAutomaticInsertedBody_lowerChild :
    relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad
        (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) =
      canonicalTerminalUnitBody
        ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) := by
  simp only [relevantAutomaticInsertedBody, relevantInsertedBody,
    relevantInsertedLowerBody, insertedInitialBody_lowerChild]

/-! ## The two child-local automatic packages -/

/-- The upper child's normalized-terminal package follows from precisely a
profile gap beyond two and the explicit upper-child theta threshold. -/
def relevantUpperNormalizedTerminalBound_of_smallTheta
    (profile_gt_two : 2 < eta Q.stage)
    (theta_le_threshold :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold (Fintype.card iota)
          (eta Q.stage)) :
    OneStepNormalizedTerminalExponentBound C
      (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
      (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      eta (Q.stage + 1)
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) := by
  let automaticBound :=
    ofFiniteScaleSequence_automatic_oneStepExponentBound_of_smallTheta
      C (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      Q.fine_refined_nonempty delta_pos eta (Q.stage + 1)
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad))
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

/-- The lower child's normalized-terminal package follows from precisely a
profile gap beyond two and the explicit lower-child theta threshold. -/
def relevantLowerNormalizedTerminalBound_of_smallTheta
    (profile_gt_two : 2 < eta Q.stage)
    (theta_le_threshold :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold (Fintype.card iota)
          (eta Q.stage)) :
    OneStepNormalizedTerminalExponentBound C
      (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
      (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      eta (Q.stage + 1)
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) := by
  let automaticBound :=
    ofFiniteScaleSequence_automatic_oneStepExponentBound_of_smallTheta
      C (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      Q.fine_refined_nonempty delta_pos eta (Q.stage + 1)
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))
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

/-! ## Conditional certificate and counted-driver adapter -/

/-- Exactly the small-scale facts which may be queried by the relevant
successor.  Each field is behind that same child's non-largeness premise, so
an already-large child carries no profile or theta obligation. -/
structure RelevantAutomaticChildSmallThetaConditions : Prop where
  upper :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    2 < eta Q.stage /\
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold (Fintype.card iota)
          (eta Q.stage)
  lower :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    2 < eta Q.stage /\
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold (Fintype.card iota)
          (eta Q.stage)

/-- Turn the conditional small-scale facts into exactly the conditional
normalized-terminal interface of the relevant invariant. -/
def relevantConditionalNormalizedTerminalBounds_of_smallTheta
    (conditions : RelevantAutomaticChildSmallThetaConditions C gap_nonneg
      delta_pos Q bad) :
    RelevantConditionalNormalizedTerminalBounds C gap_nonneg delta_pos Q bad
    where
  upper := fun child_not_large =>
    relevantUpperNormalizedTerminalBound_of_smallTheta C gap_nonneg delta_pos
      Q bad (conditions.upper child_not_large).1
      (conditions.upper child_not_large).2
  lower := fun child_not_large =>
    relevantLowerNormalizedTerminalBound_of_smallTheta C gap_nonneg delta_pos
      Q bad (conditions.lower child_not_large).1
      (conditions.lower child_not_large).2

/-- Fully automatic relevant child certificate at the explicit small-theta
threshold.  No normalized-terminal bound remains as an input. -/
def relevantCanonicalChildCertificate_of_smallTheta
    (conditions : RelevantAutomaticChildSmallThetaConditions C gap_nonneg
      delta_pos Q bad) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad :=
  relevantCanonicalChildCertificate_of_conditionalNormalizedBounds C
    gap_nonneg delta_pos Q bad
    (relevantConditionalNormalizedTerminalBounds_of_smallTheta C gap_nonneg
      delta_pos Q bad conditions)

/-- If the upper child is large, only the lower child's two small-scale
facts are needed. -/
def relevantCanonicalChildCertificate_of_upperLarge
    (upper_large :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
        gapEpsilon
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)))
    (lower_profile_gt_two : 2 < eta Q.stage)
    (lower_theta_le_threshold :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold (Fintype.card iota)
          (eta Q.stage)) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad :=
  relevantCanonicalChildCertificate_of_smallTheta C gap_nonneg delta_pos Q bad
    { upper := fun upper_not_large => (upper_not_large upper_large).elim
      lower := fun _ =>
        ⟨lower_profile_gt_two, lower_theta_le_threshold⟩ }

/-- If the lower child is large, only the upper child's two small-scale
facts are needed. -/
def relevantCanonicalChildCertificate_of_lowerLarge
    (lower_large :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
        gapEpsilon
        (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)))
    (upper_profile_gt_two : 2 < eta Q.stage)
    (upper_theta_le_threshold :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
        automaticOneStepSmallThetaThreshold (Fintype.card iota)
          (eta Q.stage)) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad :=
  relevantCanonicalChildCertificate_of_smallTheta C gap_nonneg delta_pos Q bad
    { upper := fun _ =>
        ⟨upper_profile_gt_two, upper_theta_le_threshold⟩
      lower := fun lower_not_large => (lower_not_large lower_large).elim }

/-- If both children are large, the child certificate has no analytic or
small-scale premise at all. -/
def relevantCanonicalChildCertificate_of_bothLarge
    (upper_large :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
        gapEpsilon
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)))
    (lower_large :
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
        gapEpsilon
        (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad :=
  relevantCanonicalChildCertificate_of_smallTheta C gap_nonneg delta_pos Q bad
    { upper := fun upper_not_large => (upper_not_large upper_large).elim
      lower := fun lower_not_large => (lower_not_large lower_large).elim }

/-- Statewise conditional small-theta data for the full counted recursion. -/
def RelevantCanonicalAutomaticSmallThetaSuccessorConditions
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta) : Prop :=
  forall (X : RelevantCanonicalCountedState C N gapEpsilon eta),
    forall _stage_lt : X.data.stage < N,
    forall bad : RelevantSelectedActualBadSplit C
      (X.toState C delta_pos),
      RelevantAutomaticChildSmallThetaConditions C gap_nonneg delta_pos
        X.data bad

/-- Direct adapter to the successor type consumed by
`relevantCanonicalCountingNext` and the bounded counted driver. -/
def relevantCanonicalChildSuccessor_of_automaticSmallTheta
    (conditions :
      RelevantCanonicalAutomaticSmallThetaSuccessorConditions
        (N := N) (eta := eta) C gap_nonneg delta_pos) :
    RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos :=
  fun X stage_lt bad =>
    relevantCanonicalChildCertificate_of_smallTheta C gap_nonneg delta_pos
      X.data bad (conditions X stage_lt bad)

#print axioms oneStepNormalizedTerminalExponentBound_of_eq_at
#print axioms relevantUpperNormalizedTerminalBound_of_smallTheta
#print axioms relevantLowerNormalizedTerminalBound_of_smallTheta
#print axioms relevantConditionalNormalizedTerminalBounds_of_smallTheta
#print axioms relevantCanonicalChildCertificate_of_smallTheta
#print axioms relevantCanonicalChildCertificate_of_upperLarge
#print axioms relevantCanonicalChildCertificate_of_lowerLarge
#print axioms relevantCanonicalChildCertificate_of_bothLarge
#print axioms relevantCanonicalChildSuccessor_of_automaticSmallTheta

end
end FamilyStickyScaleChainAutomaticRelevantSuccessorV2
