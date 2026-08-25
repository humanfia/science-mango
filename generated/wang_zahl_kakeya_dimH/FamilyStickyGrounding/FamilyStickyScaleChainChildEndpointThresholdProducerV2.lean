import FamilyStickyGrounding.FamilyStickyScaleChainAutomaticRelevantSuccessorV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainChildEndpointThresholdProducerV2

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleSequenceRefinesAtV2
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence
open FamilyStickyScaleSequenceInsertionTransportV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2.RelevantSelectedActualBadSplit
open FamilyStickyScaleChainAutomaticRelevantSuccessorV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2

noncomputable section

/-!
# Child-endpoint thresholds for the relevant Family 7 split

For a bad split at the interval `tau -> theta`, canonical insertion has the
literal endpoints

* upper child: `rho -> theta`;
* lower child: `tau -> rho`.

Consequently the upper endpoint is not made smaller at all.  The lower
endpoint, however, is genuinely controlled by the small global scale.  From
parent non-largeness and bufferedness one obtains the strict estimate

`rho < delta ^ (gapEpsilon ^ 2)`.

This module turns that estimate into an explicit delta threshold for the
automatic normalized-terminal producer.  It also records the exact remaining
upper-child branch: that child must already be large, or the selected parent
endpoint itself must lie below the automatic threshold.  The strict analytic
bad-split field supplies no further endpoint shrinkage.
-/

/-! ## An explicit inverse-power delta threshold -/

/-- The exact global-scale threshold whose `gap^2` power is `target`. -/
def childEndpointDeltaThreshold (target : NNReal) (gap : Real) : NNReal :=
  target ^ (1 / gap ^ 2)

theorem childEndpointDeltaThreshold_pos
    {target : NNReal} (target_pos : 0 < target) (gap : Real) :
    0 < childEndpointDeltaThreshold target gap := by
  exact NNReal.rpow_pos target_pos

/-- For positive gap, raising the inverse-power threshold back to `gap^2`
recovers the target exactly. -/
theorem childEndpointDeltaThreshold_rpow_sq
    (target : NNReal) {gap : Real} (gap_pos : 0 < gap) :
    (childEndpointDeltaThreshold target gap) ^ (gap ^ 2) = target := by
  rw [childEndpointDeltaThreshold, <- NNReal.rpow_mul]
  have gap_sq_pos : 0 < gap ^ 2 := sq_pos_of_pos gap_pos
  have exponent_eq : (1 / gap ^ 2) * gap ^ 2 = (1 : Real) := by
    field_simp [ne_of_gt gap_sq_pos]
  rw [exponent_eq, NNReal.rpow_one]

/-- A delta below the explicit inverse-power threshold has the required
`gap^2` power bound. -/
theorem delta_rpow_sq_le_target_of_le_childEndpointDeltaThreshold
    {delta target : NNReal} {gap : Real} (gap_pos : 0 < gap)
    (delta_le : delta <= childEndpointDeltaThreshold target gap) :
    delta ^ (gap ^ 2) <= target := by
  calc
    delta ^ (gap ^ 2) <=
        (childEndpointDeltaThreshold target gap) ^ (gap ^ 2) :=
      NNReal.rpow_le_rpow delta_le (sq_nonneg gap)
    _ = target := childEndpointDeltaThreshold_rpow_sq target gap_pos

/-- Specialization to the finite-cardinality normalized-terminal threshold. -/
def automaticLowerChildDeltaThreshold
    (n : Nat) (exponent gap : Real) : NNReal :=
  childEndpointDeltaThreshold
    (automaticOneStepSmallThetaThreshold n exponent) gap

theorem automaticLowerChildDeltaThreshold_pos
    (n : Nat) (exponent gap : Real) :
    0 < automaticLowerChildDeltaThreshold n exponent gap := by
  exact childEndpointDeltaThreshold_pos
    (automaticOneStepSmallThetaThreshold_pos n exponent) gap

/-! ## The buffered lower child is automatically small -/

variable {delta : NNReal} {depth : Nat} {gapEpsilon : Real}

/-- Parent non-largeness and bufferedness force the inserted radius below
`delta^(gapEpsilon^2)`.  This is the genuine scale gain available from a bad
split. -/
theorem bufferedRadius_lt_delta_rpow_gap_sq
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (parent_not_large : Not (S.IsLarge gapEpsilon m))
    (rho_buffered : S.IsBuffered gapEpsilon m rho) :
    rho < delta ^ (gapEpsilon ^ 2) := by
  have tau_pos : 0 < S.tau m :=
    delta_pos.trans_le (S.delta_le_tau m)
  have theta_pos : 0 < S.theta m :=
    tau_pos.trans_le (S.tau_le_theta m)
  have ratio_pos : 0 < S.tau m / S.theta m :=
    div_pos tau_pos theta_pos
  have parent_strict_ennreal :
      (S.tau m : ENNReal) <
        (delta : ENNReal) ^ gapEpsilon * (S.theta m : ENNReal) :=
    lt_of_not_ge parent_not_large
  have parent_strict :
      S.tau m < delta ^ gapEpsilon * S.theta m := by
    rw [<- ENNReal.coe_rpow_of_ne_zero delta_pos.ne' gapEpsilon,
      <- ENNReal.coe_mul] at parent_strict_ennreal
    exact_mod_cast parent_strict_ennreal
  have ratio_lt_delta_power :
      S.tau m / S.theta m < delta ^ gapEpsilon := by
    exact (div_lt_iff₀ theta_pos).2 (by
      simpa only [mul_comm] using parent_strict)
  have buffered_upper :
      rho <= S.theta m * (S.tau m / S.theta m) ^ gapEpsilon := by
    have h := rho_buffered.2
    rw [<- ENNReal.coe_rpow_of_ne_zero ratio_pos.ne' gapEpsilon,
      <- ENNReal.coe_mul] at h
    exact_mod_cast h
  have ratio_power_strict :
      (S.tau m / S.theta m) ^ gapEpsilon <
        (delta ^ gapEpsilon) ^ gapEpsilon :=
    NNReal.rpow_lt_rpow ratio_lt_delta_power gap_pos
  have rho_lt_nested :
      rho < S.theta m * (delta ^ gapEpsilon) ^ gapEpsilon := by
    exact buffered_upper.trans_lt
      (mul_lt_mul_of_pos_left ratio_power_strict theta_pos)
  calc
    rho < S.theta m * (delta ^ gapEpsilon) ^ gapEpsilon := rho_lt_nested
    _ <= 1 * (delta ^ gapEpsilon) ^ gapEpsilon := by
      gcongr
      exact S.theta_le_one m
    _ = delta ^ (gapEpsilon ^ 2) := by
      rw [one_mul, <- NNReal.rpow_mul]
      congr 1
      ring

/-- The explicit delta threshold therefore places every such inserted lower
endpoint below an arbitrary positive target. -/
theorem bufferedRadius_le_target_of_delta_le_threshold
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho target : NNReal)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (parent_not_large : Not (S.IsLarge gapEpsilon m))
    (rho_buffered : S.IsBuffered gapEpsilon m rho)
    (delta_le : delta <= childEndpointDeltaThreshold target gapEpsilon) :
    rho <= target := by
  exact (bufferedRadius_lt_delta_rpow_gap_sq S m rho delta_pos gap_pos
    parent_not_large rho_buffered).le.trans
      (delta_rpow_sq_le_target_of_le_childEndpointDeltaThreshold
        gap_pos delta_le)

/-! ## Exact child endpoints: the upper child does not shrink -/

theorem upperChild_theta_le_iff_parent_theta_le
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho target : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (href : FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence.ScaleSequenceRefinesAt
      S m rho S') :
    S'.theta (upperChildIndex m) <= target <-> S.theta m <= target := by
  rw [theta_upperChild_eq href]

theorem lowerChild_theta_le_iff_rho_le
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho target : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1))
    (href : FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence.ScaleSequenceRefinesAt
      S m rho S') :
    S'.theta (lowerChildIndex m) <= target <-> rho <= target := by
  rw [theta_lowerChild_eq href]

/-! ## The weakest scale-sequence-wide upper-endpoint cutoff -/

/-- Every non-large interval already has a small upper endpoint.  Equivalently,
every interval whose upper endpoint exceeds `target` is large. -/
def NonLargeEndpointCutoff
    (S : FiniteScaleSequence delta depth) (gap : Real)
    (target : NNReal) : Prop :=
  forall m, Not (S.IsLarge gap m) -> S.theta m <= target

theorem nonLargeEndpointCutoff_iff_aboveCutoff_large
    (S : FiniteScaleSequence delta depth) (gap : Real)
    (target : NNReal) :
    NonLargeEndpointCutoff S gap target <->
      forall m, target < S.theta m -> S.IsLarge gap m := by
  constructor
  · intro cutoff m above
    by_contra not_large
    exact (not_le_of_gt above) (cutoff m not_large)
  · intro above m not_large
    exact le_of_not_gt fun target_lt => not_large (above m target_lt)

/-! ## Relevant-bad-split specialization and the minimal upper branch -/

universe u

variable {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
  (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
  (bad : RelevantSelectedActualBadSplit C (Q.toState C delta_pos))

theorem relevantUpperChild_theta_eq_parent :
    (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) =
      Q.scales.theta (relevantSelectedStep C delta_pos Q bad) := by
  exact theta_upperChild_eq
    (bad.refinedScales_refinesAt C (Q.toState C delta_pos)
      gap_nonneg delta_pos)

theorem relevantLowerChild_theta_eq_rho :
    (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
        (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) = bad.rho := by
  exact theta_lowerChild_eq
    (bad.refinedScales_refinesAt C (Q.toState C delta_pos)
      gap_nonneg delta_pos)

/-- The lower child is below the automatic threshold as soon as delta is
below the displayed inverse-power threshold. -/
theorem relevantLowerChild_theta_le_automaticThreshold
    (gap_pos : 0 < gapEpsilon) (exponent : Real)
    (delta_le : delta <= automaticLowerChildDeltaThreshold
      (Fintype.card iota) exponent gapEpsilon) :
    (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
        (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota) exponent := by
  rw [relevantLowerChild_theta_eq_rho C gap_nonneg delta_pos Q bad]
  exact bufferedRadius_le_target_of_delta_le_threshold Q.scales
    (relevantSelectedStep C delta_pos Q bad) bad.rho
    (automaticOneStepSmallThetaThreshold (Fintype.card iota) exponent)
    delta_pos gap_pos bad.selectedStep_not_large bad.rho_buffered delta_le

/-- Exact honest branch for the upper child: either it is already large, or
the unchanged parent endpoint is itself below the automatic threshold. -/
def RelevantUpperChildThresholdBranch (exponent : Real) : Prop :=
  (relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge gapEpsilon
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) \/
    Q.scales.theta (relevantSelectedStep C delta_pos Q bad) <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota) exponent

theorem relevantUpperChild_theta_le_automaticThreshold_of_branch
    (exponent : Real)
    (branch : RelevantUpperChildThresholdBranch C gap_nonneg delta_pos Q bad
      exponent)
    (upper_not_large :
      Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
        gapEpsilon
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)))) :
    (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota) exponent := by
  rcases branch with upper_large | parent_small
  · exact (upper_not_large upper_large).elim
  · rw [relevantUpperChild_theta_eq_parent C gap_nonneg delta_pos Q bad]
    exact parent_small

/-- The scale-sequence-wide cutoff is a sufficient global source for the
exact local upper-child branch. -/
theorem relevantUpperChildThresholdBranch_of_nonLargeEndpointCutoff
    (exponent : Real)
    (cutoff : NonLargeEndpointCutoff Q.scales gapEpsilon
      (automaticOneStepSmallThetaThreshold (Fintype.card iota) exponent)) :
    RelevantUpperChildThresholdBranch C gap_nonneg delta_pos Q bad
      exponent := by
  exact Or.inr (cutoff (relevantSelectedStep C delta_pos Q bad)
    bad.selectedStep_not_large)

/-- Equivalent formulation of the minimal upper branch.  Thus this module
does not hide any stronger scale hypothesis inside the producer. -/
theorem relevantUpperChildThresholdBranch_iff
    (exponent : Real) :
    RelevantUpperChildThresholdBranch C gap_nonneg delta_pos Q bad exponent <->
      (Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
          gapEpsilon
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
        (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
            (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
          automaticOneStepSmallThetaThreshold (Fintype.card iota)
            exponent) := by
  constructor
  · exact relevantUpperChild_theta_le_automaticThreshold_of_branch
      C gap_nonneg delta_pos Q bad exponent
  · intro conditional
    by_cases upper_large :
        (relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
          gapEpsilon
          (upperChildIndex (relevantSelectedStep C delta_pos Q bad))
    · exact Or.inl upper_large
    · right
      rw [<- relevantUpperChild_theta_eq_parent C gap_nonneg delta_pos Q bad]
      exact conditional upper_large

/-! ## Direct production of the automatic relevant successor input -/

/-- The lower scale follows from delta; the upper scale follows from exactly
the branch isolated above. -/
theorem relevantAutomaticChildSmallThetaConditions_of_geometry
    (gap_pos : 0 < gapEpsilon)
    (profile_gt_two : 2 < eta Q.stage)
    (delta_le : delta <= automaticLowerChildDeltaThreshold
      (Fintype.card iota) (eta Q.stage) gapEpsilon)
    (upper_branch : RelevantUpperChildThresholdBranch C gap_nonneg delta_pos
      Q bad (eta Q.stage)) :
    RelevantAutomaticChildSmallThetaConditions C gap_nonneg delta_pos Q bad
    where
  upper := fun upper_not_large =>
    ⟨profile_gt_two,
      relevantUpperChild_theta_le_automaticThreshold_of_branch C gap_nonneg
        delta_pos Q bad (eta Q.stage) upper_branch upper_not_large⟩
  lower := fun _lower_not_large =>
    ⟨profile_gt_two,
      relevantLowerChild_theta_le_automaticThreshold C gap_nonneg delta_pos
        Q bad gap_pos (eta Q.stage) delta_le⟩

/-- Fully analytic child certificate from the explicit geometric threshold
and the exact upper-child branch. -/
def relevantCanonicalChildCertificate_of_geometry
    (gap_pos : 0 < gapEpsilon)
    (profile_gt_two : 2 < eta Q.stage)
    (delta_le : delta <= automaticLowerChildDeltaThreshold
      (Fintype.card iota) (eta Q.stage) gapEpsilon)
    (upper_branch : RelevantUpperChildThresholdBranch C gap_nonneg delta_pos
      Q bad (eta Q.stage)) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad :=
  relevantCanonicalChildCertificate_of_smallTheta C gap_nonneg delta_pos Q bad
    (relevantAutomaticChildSmallThetaConditions_of_geometry C gap_nonneg
      delta_pos Q bad gap_pos profile_gt_two delta_le upper_branch)

/-! ## Sharp unchanged-endpoint obstruction -/

theorem automaticOneStepSmallThetaThreshold_lt_one
    (n : Nat) (exponent : Real) :
    automaticOneStepSmallThetaThreshold n exponent < 1 := by
  exact (min_le_left _ _).trans_lt (by norm_num)

/-- If the selected parent is the top interval, the upper child can never
satisfy the automatic small-theta condition.  This holds for every delta,
buffered radius, strict bad-split value, cardinality, and profile exponent. -/
theorem relevantUpperChild_not_smallTheta_of_parent_theta_eq_one
    (exponent : Real)
    (parent_theta_eq_one :
      Q.scales.theta (relevantSelectedStep C delta_pos Q bad) = 1) :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).theta
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota) exponent) := by
  rw [relevantUpperChild_theta_eq_parent C gap_nonneg delta_pos Q bad,
    parent_theta_eq_one]
  exact not_le_of_gt
    (automaticOneStepSmallThetaThreshold_lt_one (Fintype.card iota) exponent)

/-- At a top parent and with a non-large upper child, the minimal branch is
formally impossible.  This is the precise residual obstruction in the
relevant-envelope successor, rather than a missing consequence of strictness. -/
theorem not_relevantUpperChildThresholdBranch_of_parent_theta_eq_one
    (exponent : Real)
    (parent_theta_eq_one :
      Q.scales.theta (relevantSelectedStep C delta_pos Q bad) = 1)
    (upper_not_large :
      Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
        gapEpsilon
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)))) :
    Not (RelevantUpperChildThresholdBranch C gap_nonneg delta_pos Q bad
      exponent) := by
  intro branch
  exact relevantUpperChild_not_smallTheta_of_parent_theta_eq_one C gap_nonneg
    delta_pos Q bad exponent parent_theta_eq_one
    (relevantUpperChild_theta_le_automaticThreshold_of_branch C gap_nonneg
      delta_pos Q bad exponent branch upper_not_large)

#print axioms childEndpointDeltaThreshold_rpow_sq
#print axioms delta_rpow_sq_le_target_of_le_childEndpointDeltaThreshold
#print axioms bufferedRadius_lt_delta_rpow_gap_sq
#print axioms bufferedRadius_le_target_of_delta_le_threshold
#print axioms upperChild_theta_le_iff_parent_theta_le
#print axioms nonLargeEndpointCutoff_iff_aboveCutoff_large
#print axioms relevantLowerChild_theta_le_automaticThreshold
#print axioms relevantUpperChildThresholdBranch_of_nonLargeEndpointCutoff
#print axioms relevantUpperChildThresholdBranch_iff
#print axioms relevantAutomaticChildSmallThetaConditions_of_geometry
#print axioms relevantCanonicalChildCertificate_of_geometry
#print axioms relevantUpperChild_not_smallTheta_of_parent_theta_eq_one
#print axioms not_relevantUpperChildThresholdBranch_of_parent_theta_eq_one

end
end FamilyStickyScaleChainChildEndpointThresholdProducerV2
