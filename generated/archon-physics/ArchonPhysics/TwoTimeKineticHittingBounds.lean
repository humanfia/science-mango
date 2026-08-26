import ArchonPhysics.HittingTimeStability

/-!
# Two-time kinetic hitting bounds without monotonicity

The first release target only needs positive finite lower and upper constants
for the scaled hitting time.  It does not need a unique limiting crossing
time.  Accordingly, this module replaces strict monotonicity of the complete
late-window distance by the two facts actually used for such a window:

* the limiting kinetic distance stays uniformly above threshold on one
  initial positive interval;
* it is uniformly below threshold at one later time.

Continuity at time zero, initial separation, and convergence to zero produce
these two margins.  Thus strict antitonicity remains necessary only for the
enhanced single-constant limit, not for the two-sided release law.
-/

namespace ArchonPhysics.TwoTimeKineticHittingBounds

open ArchonPhysics Filter

noncomputable section

/-- Robust lower and upper kinetic times for a threshold hit.  No monotonicity
or uniqueness of a crossing is asserted. -/
structure RobustKineticHittingWindow
    (distance : Real -> Real) (delta lower upper : Real) : Prop where
  lower_pos : 0 < lower
  lower_le_upper : lower <= upper
  beforeMargin : exists margin : Real, 0 < margin /\
    forall t : Real, 0 < t -> t <= lower ->
      delta + margin <= distance t
  afterMargin : exists margin : Real, 0 < margin /\
    distance upper <= delta - margin

/-- A robust two-time window is stable under one uniform path error on the
finite interval ending at its upper time. -/
theorem RobustKineticHittingWindow.exists_uniform_error_radius
    {distance : Real -> Real} {delta lower upper : Real}
    (window : RobustKineticHittingWindow distance delta lower upper) :
    exists eta : Real, 0 < eta /\
      forall approximation : Real -> Real,
        UniformlyCloseOnNonnegativeWindow approximation distance upper eta ->
          (Real.toNNReal lower : ENNReal) <=
              distanceThresholdHittingTime approximation delta /\
            distanceThresholdHittingTime approximation delta <=
              (Real.toNNReal upper : ENNReal) := by
  obtain ⟨beforeMargin, hbeforeMargin, hbefore⟩ := window.beforeMargin
  obtain ⟨afterMargin, hafterMargin, hafter⟩ := window.afterMargin
  refine ⟨min beforeMargin afterMargin,
    lt_min hbeforeMargin hafterMargin, ?_⟩
  intro approximation hclose
  have hupper_pos : 0 < upper :=
    window.lower_pos.trans_le window.lower_le_upper
  have hnoHit : forall t : Real, 0 < t -> t <= lower ->
      delta < approximation t := by
    intro t ht htLower
    have htUpper : t <= upper := htLower.trans window.lower_le_upper
    have hcloseMin := hclose t ht.le htUpper
    have hcloseBefore :
        |approximation t - distance t| < beforeMargin :=
      hcloseMin.trans_le (min_le_left _ _)
    have hlower := neg_abs_le (approximation t - distance t)
    have hlimit := hbefore t ht htLower
    linarith
  have hcloseMin := hclose upper hupper_pos.le le_rfl
  have hcloseAfter :
      |approximation upper - distance upper| < afterMargin :=
    hcloseMin.trans_le (min_le_right _ _)
  have hupperError := le_abs_self (approximation upper - distance upper)
  have hhit : approximation upper <= delta := by
    linarith
  constructor
  · exact coe_toNNReal_le_distanceThresholdHittingTime_of_no_hit_before
      window.lower_pos.le hnoHit
  · exact distanceThresholdHittingTime_le_of_hit hupper_pos hhit

/-- Minimal analytic input for a two-sided kinetic hitting window.  This is
strictly weaker than requiring the late-window distance to be strictly
decreasing or to possess a unique threshold root. -/
structure RelaxationToTwoTimeWindow
    (distance : Real -> Real) (delta : Real) : Prop where
  threshold_pos : 0 < delta
  initial_above : delta < distance 0
  continuousAt_zero : ContinuousAt distance 0
  tendsto_zero : Tendsto distance atTop (nhds 0)

/-- Initial continuity and eventual relaxation produce positive finite
two-sided hitting constants with strict robustness margins. -/
theorem RelaxationToTwoTimeWindow.exists_robustKineticHittingWindow
    {distance : Real -> Real} {delta : Real}
    (relaxation : RelaxationToTwoTimeWindow distance delta) :
    exists lower upper : Real,
      RobustKineticHittingWindow distance delta lower upper := by
  let initialMargin : Real := (distance 0 - delta) / 2
  have hinitialMargin : 0 < initialMargin := by
    dsimp [initialMargin]
    linarith [relaxation.initial_above]
  have hzero : delta + initialMargin < distance 0 := by
    dsimp [initialMargin]
    linarith [relaxation.initial_above]
  have heventuallyNear : ∀ᶠ t in nhds (0 : Real),
      delta + initialMargin < distance t :=
    relaxation.continuousAt_zero
      (Ioi_mem_nhds hzero)
  obtain ⟨radius, hradius, hnear⟩ :=
    Metric.eventually_nhds_iff.mp heventuallyNear
  let lower : Real := radius / 2
  have hlower : 0 < lower := by
    dsimp [lower]
    positivity
  have hbefore : forall t : Real, 0 < t -> t <= lower ->
      delta + initialMargin <= distance t := by
    intro t ht htLower
    apply le_of_lt
    apply hnear
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [lower] at htLower
    linarith [hradius]
  have hrelax : ∀ᶠ t : Real in atTop,
      dist (distance t) 0 < delta / 2 :=
    (Metric.tendsto_nhds.mp relaxation.tendsto_zero)
      (delta / 2) (div_pos relaxation.threshold_pos (by norm_num))
  have hlater : ∀ᶠ t : Real in atTop,
      lower < t /\ dist (distance t) 0 < delta / 2 :=
    (eventually_gt_atTop lower).and hrelax
  obtain ⟨upper, hlowerUpper, hupperDistance⟩ := hlater.exists
  have hupperValue : distance upper <= delta - delta / 2 := by
    rw [Real.dist_eq, sub_zero] at hupperDistance
    have := le_abs_self (distance upper)
    linarith
  exact ⟨lower, upper, {
    lower_pos := hlower
    lower_le_upper := hlowerUpper.le
    beforeMargin := ⟨initialMargin, hinitialMargin, hbefore⟩
    afterMargin := ⟨delta / 2,
      div_pos relaxation.threshold_pos (by norm_num), hupperValue⟩ }⟩

end

end ArchonPhysics.TwoTimeKineticHittingBounds
