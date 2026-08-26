import ArchonPhysics.TwoTimeKineticHittingBounds

/-!
# Minimal construction of a two-time kinetic hitting window

For the two-sided release law, full convergence to equilibrium is stronger
than necessary.  Continuity at time zero, strict initial separation, and one
finite strict hit already supply both robust margins.
-/

namespace ArchonPhysics.MinimalTwoTimeKineticHittingWindow

open ArchonPhysics
open ArchonPhysics.TwoTimeKineticHittingBounds

noncomputable section

/-- The minimal deterministic data needed to obtain a robust lower/upper
threshold window. -/
structure InitialSeparationAndStrictHit
    (distance : Real -> Real) (delta : Real) where
  hitTime : Real
  hitTime_pos : 0 < hitTime
  threshold_below_initial : delta < distance 0
  continuousAt_zero : ContinuousAt distance 0
  strict_hit : distance hitTime < delta

/-- One strict hit plus continuity at zero produces a positive finite robust
hitting window. -/
theorem InitialSeparationAndStrictHit.exists_robustKineticHittingWindow
    {distance : Real -> Real} {delta : Real}
    (data : InitialSeparationAndStrictHit distance delta) :
    exists lower upper : Real,
      RobustKineticHittingWindow distance delta lower upper := by
  let initialMargin : Real := (distance 0 - delta) / 2
  have hinitialMargin : 0 < initialMargin := by
    dsimp [initialMargin]
    linarith [data.threshold_below_initial]
  have hzero : delta + initialMargin < distance 0 := by
    dsimp [initialMargin]
    linarith [data.threshold_below_initial]
  have heventuallyNear : ∀ᶠ t in nhds (0 : Real),
      delta + initialMargin < distance t :=
    data.continuousAt_zero (Ioi_mem_nhds hzero)
  obtain ⟨radius, hradius, hnear⟩ :=
    Metric.eventually_nhds_iff.mp heventuallyNear
  let lower : Real := min (radius / 2) (data.hitTime / 2)
  have hlower : 0 < lower := by
    dsimp [lower]
    exact lt_min (div_pos hradius (by norm_num))
      (div_pos data.hitTime_pos (by norm_num))
  have hlowerRadius : lower <= radius / 2 := by
    exact min_le_left _ _
  have hlowerHit : lower <= data.hitTime / 2 := by
    exact min_le_right _ _
  have hlowerUpper : lower <= data.hitTime := by
    linarith [hlowerHit, data.hitTime_pos]
  have hbefore : forall t : Real, 0 < t -> t <= lower ->
      delta + initialMargin <= distance t := by
    intro t ht htLower
    apply le_of_lt
    apply hnear
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    have htRadius : t <= radius / 2 :=
      htLower.trans hlowerRadius
    linarith [hradius]
  let hitMargin : Real := (delta - distance data.hitTime) / 2
  have hhitMargin : 0 < hitMargin := by
    dsimp [hitMargin]
    linarith [data.strict_hit]
  have hhit : distance data.hitTime <= delta - hitMargin := by
    dsimp [hitMargin]
    linarith [data.strict_hit]
  exact ⟨lower, data.hitTime, {
    lower_pos := hlower
    lower_le_upper := hlowerUpper
    beforeMargin := ⟨initialMargin, hinitialMargin, hbefore⟩
    afterMargin := ⟨hitMargin, hhitMargin, hhit⟩ }⟩

end

end ArchonPhysics.MinimalTwoTimeKineticHittingWindow
