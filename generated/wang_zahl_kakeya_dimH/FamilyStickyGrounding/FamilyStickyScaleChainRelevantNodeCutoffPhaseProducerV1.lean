import FamilyStickyGrounding.FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainRelevantNodeCutoffPhaseProducerV1

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1

noncomputable section

/-!
# Sharp cutoff phase for relevant rooted-tree nodes

The rooted tree starts exactly at `tau`.  This makes the exponent `1` the
sharp transition for the buffered cutoffs.

* If `1 < epsilon`, a relevant node can exist only on a degenerate interval
  `tau = theta`; consequently it is never below the lower cutoff and every
  relevant-node failure is an actual buffered bad scale.
* If `0 < epsilon <= 1` and `tau < theta`, the root itself is relevant and
  lies strictly below the lower cutoff.  Thus the generic below-cutoff branch
  cannot be removed without the large-exponent input.

These are scale facts only.  No concentration, hierarchy, or fabricated
geometric data enter either direction.
-/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {profile : Nat -> Real} {stage : Nat}
  {S : FiniteScaleSequence delta depth}
  {A : ActualIntervalCovers S}
  {R : IntervalRootedRefinementScaleTree S}
  {m : Fin depth}

/-! ## Above exponent one, the upper cutoff falls below the root -/

/-- On a strict interval, an exponent larger than one pushes the buffered
upper cutoff strictly below the rooted-tree floor `tau`. -/
theorem bufferedUpperCutoff_lt_tau_of_tau_lt_theta
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (tau_pos : 0 < S.tau m)
    (tau_lt_theta : S.tau m < S.theta m)
    (one_lt_epsilon : (1 : Real) < epsilon) :
    bufferedUpperCutoff S epsilon m < (S.tau m : ENNReal) := by
  let q : NNReal := S.tau m / S.theta m
  have theta_pos : 0 < S.theta m := tau_pos.trans tau_lt_theta
  have q_pos : 0 < q := div_pos tau_pos theta_pos
  have q_lt_one : q < 1 :=
    (div_lt_one theta_pos).2 tau_lt_theta
  have qpow_lt_q_nn : q ^ epsilon < q := by
    have h := NNReal.rpow_lt_rpow_of_exponent_gt
      q_pos q_lt_one one_lt_epsilon
    simpa only [NNReal.rpow_one] using h
  have qpow_lt_q : (q : ENNReal) ^ epsilon < (q : ENNReal) := by
    rw [<- ENNReal.coe_rpow_of_ne_zero q_pos.ne' epsilon]
    exact_mod_cast qpow_lt_q_nn
  unfold bufferedUpperCutoff
  change (S.theta m : ENNReal) * (q : ENNReal) ^ epsilon <
    (S.tau m : ENNReal)
  calc
    (S.theta m : ENNReal) * (q : ENNReal) ^ epsilon <
        (S.theta m : ENNReal) * (q : ENNReal) :=
      ENNReal.mul_lt_mul_right
        (ENNReal.coe_ne_zero.mpr theta_pos.ne') ENNReal.coe_ne_top
        qpow_lt_q
    _ = (S.tau m : ENNReal) := by
      rw [ENNReal.coe_div theta_pos.ne']
      exact ENNReal.mul_div_cancel
        (ENNReal.coe_ne_zero.mpr theta_pos.ne') ENNReal.coe_ne_top

/-- For exponent larger than one, every relevant node lies at or above the
lower cutoff.  In the strict interval case relevance would contradict the
root floor; in the equality case both cutoffs and every relevant node equal
the common endpoint. -/
theorem bufferedLowerCutoff_le_relevantNode_scale_of_one_lt_epsilon
    (R : IntervalRootedRefinementScaleTree S)
    (one_lt_epsilon : (1 : Real) < epsilon)
    (m : Fin depth) (i : Fin (R.tree.levelCount m))
    (relevant : IsRelevantTreeNode (epsilon := epsilon) R m i) :
    bufferedLowerCutoff S epsilon m <=
      (R.tree.scale m i : ENNReal) := by
  rcases eq_or_lt_of_le (S.tau_le_theta m) with equal | strict
  · have theta_pos : 0 < S.theta m := equal ▸ R.tau_pos m
    have floor := R.tau_le_scale m i
    simpa [bufferedLowerCutoff, equal, theta_pos.ne'] using
      (show (S.tau m : ENNReal) <=
          (R.tree.scale m i : ENNReal) by exact_mod_cast floor)
  · have upper_lt_tau :=
      bufferedUpperCutoff_lt_tau_of_tau_lt_theta S m
        (R.tau_pos m) strict one_lt_epsilon
    have scale_lt_tau :
        (R.tree.scale m i : ENNReal) < (S.tau m : ENNReal) :=
      relevant.trans_lt upper_lt_tau
    have tau_le_scale :
        (S.tau m : ENNReal) <= (R.tree.scale m i : ENNReal) := by
      exact_mod_cast R.tau_le_scale m i
    exact False.elim ((not_lt_of_ge tau_le_scale) scale_lt_tau)

/-- Hence the analytic failure alternative is necessarily the genuine bad
scale branch whenever the stopping exponent is larger than one. -/
theorem FirstRelevantNodeFailure.isBadScale_of_one_lt_epsilon
    (F : FirstRelevantNodeFailure
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m)
    (one_lt_epsilon : (1 : Real) < epsilon) :
    IsBadScale A epsilon profile stage m (R.tree.scale m F.node) := by
  rcases F.actualBadScale_or_belowLowerCutoff with bad | below
  · exact bad
  · exact False.elim ((not_lt_of_ge
      (bufferedLowerCutoff_le_relevantNode_scale_of_one_lt_epsilon
        R one_lt_epsilon m F.node F.relevant)) below.1)

/-- This is the form used by the recovered endpoint: its ordinary exponent
room hypotheses automatically put `epsilon` above the sharp transition. -/
theorem FirstRelevantNodeFailure.isBadScale_of_two_le_profile_strict_room
    (F : FirstRelevantNodeFailure
      (epsilon := epsilon) (profile := profile) (stage := stage) A R m)
    (two_le_profile : (2 : Real) <= profile stage)
    (strict_room : profile stage < epsilon) :
    IsBadScale A epsilon profile stage m (R.tree.scale m F.node) := by
  exact FamilyStickyScaleChainRelevantNodeCutoffPhaseProducerV1.FirstRelevantNodeFailure.isBadScale_of_one_lt_epsilon F (by linarith)

/-! ## At or below exponent one, the root gives the sharp obstruction -/

/-- On a strict interval and for a positive exponent at most one, the root
is still below the upper cutoff and hence is a relevant node. -/
theorem root_isRelevant_of_epsilon_le_one
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin depth)
    (epsilon_le_one : epsilon <= (1 : Real))
    (tau_lt_theta : S.tau m < S.theta m) :
    IsRelevantTreeNode (epsilon := epsilon) R m
      ⟨0, R.tree.levelCount_pos m⟩ := by
  let q : NNReal := S.tau m / S.theta m
  have tau_pos : 0 < S.tau m := R.tau_pos m
  have theta_pos : 0 < S.theta m := tau_pos.trans tau_lt_theta
  have q_pos : 0 < q := div_pos tau_pos theta_pos
  have q_le_one : q <= 1 :=
    (div_le_one theta_pos).2 (S.tau_le_theta m)
  have q_le_qpow_nn : q <= q ^ epsilon := by
    have h := NNReal.rpow_le_rpow_of_exponent_ge
      q_pos q_le_one epsilon_le_one
    simpa only [NNReal.rpow_one] using h
  have q_le_qpow : (q : ENNReal) <= (q : ENNReal) ^ epsilon := by
    rw [<- ENNReal.coe_rpow_of_ne_zero q_pos.ne' epsilon]
    exact_mod_cast q_le_qpow_nn
  change (R.tree.scale m ⟨0, R.tree.levelCount_pos m⟩ : ENNReal) <=
    bufferedUpperCutoff S epsilon m
  rw [R.root_eq_tau m]
  unfold bufferedUpperCutoff
  change (S.tau m : ENNReal) <=
    (S.theta m : ENNReal) * (q : ENNReal) ^ epsilon
  calc
    (S.tau m : ENNReal) =
        (S.theta m : ENNReal) * (q : ENNReal) := by
      rw [ENNReal.coe_div theta_pos.ne']
      symm
      exact ENNReal.mul_div_cancel
        (ENNReal.coe_ne_zero.mpr theta_pos.ne') ENNReal.coe_ne_top
    _ <= (S.theta m : ENNReal) * (q : ENNReal) ^ epsilon := by
      exact mul_le_mul' le_rfl q_le_qpow

/-- A positive exponent makes that same root strictly lower than the lower
cutoff on every strict interval. -/
theorem root_lt_bufferedLowerCutoff
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin depth)
    (epsilon_pos : 0 < epsilon)
    (tau_lt_theta : S.tau m < S.theta m) :
    (R.tree.scale m ⟨0, R.tree.levelCount_pos m⟩ : ENNReal) <
      bufferedLowerCutoff S epsilon m := by
  let r : NNReal := S.theta m / S.tau m
  have tau_pos : 0 < S.tau m := R.tau_pos m
  have one_lt_r_nn : 1 < r :=
    (one_lt_div tau_pos).2 tau_lt_theta
  have one_lt_r : (1 : ENNReal) < (r : ENNReal) := by
    exact_mod_cast one_lt_r_nn
  have one_lt_rpow : (1 : ENNReal) < (r : ENNReal) ^ epsilon := by
    have h := ENNReal.rpow_lt_rpow one_lt_r epsilon_pos
    simpa using h
  rw [R.root_eq_tau m]
  unfold bufferedLowerCutoff
  change (S.tau m : ENNReal) <
    (S.tau m : ENNReal) * (r : ENNReal) ^ epsilon
  calc
    (S.tau m : ENNReal) = (S.tau m : ENNReal) * 1 := by simp
    _ < (S.tau m : ENNReal) * (r : ENNReal) ^ epsilon :=
      ENNReal.mul_lt_mul_right
        (ENNReal.coe_ne_zero.mpr tau_pos.ne') ENNReal.coe_ne_top
        one_lt_rpow

/-- Sharp obstruction below the transition: the actual root is both relevant
and strictly below the lower cutoff. -/
theorem exists_relevantNode_belowLowerCutoff_of_epsilon_le_one
    (R : IntervalRootedRefinementScaleTree S)
    (m : Fin depth)
    (epsilon_pos : 0 < epsilon)
    (epsilon_le_one : epsilon <= (1 : Real))
    (tau_lt_theta : S.tau m < S.theta m) :
    exists i : Fin (R.tree.levelCount m),
      IsRelevantTreeNode (epsilon := epsilon) R m i ∧
        (R.tree.scale m i : ENNReal) <
          bufferedLowerCutoff S epsilon m := by
  exact ⟨⟨0, R.tree.levelCount_pos m⟩,
    root_isRelevant_of_epsilon_le_one R m epsilon_le_one tau_lt_theta,
    root_lt_bufferedLowerCutoff R m epsilon_pos tau_lt_theta⟩

#print axioms bufferedUpperCutoff_lt_tau_of_tau_lt_theta
#print axioms bufferedLowerCutoff_le_relevantNode_scale_of_one_lt_epsilon
#print axioms FirstRelevantNodeFailure.isBadScale_of_one_lt_epsilon
#print axioms FirstRelevantNodeFailure.isBadScale_of_two_le_profile_strict_room
#print axioms root_isRelevant_of_epsilon_le_one
#print axioms root_lt_bufferedLowerCutoff
#print axioms exists_relevantNode_belowLowerCutoff_of_epsilon_le_one

end
end FamilyStickyScaleChainRelevantNodeCutoffPhaseProducerV1
