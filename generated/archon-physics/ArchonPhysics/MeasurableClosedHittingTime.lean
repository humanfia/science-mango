import ArchonPhysics.MeasurableHittingTime

/-!
# Closed-threshold hitting times from strict outer approximations

For a continuous path that starts strictly outside the closed target
`(-∞, delta]`, its first positive closed-threshold hitting time is the
supremum of the measurable strict hitting times at thresholds
`delta + 1/(n+1)`.  This gives closed-threshold measurability without assuming
that a path immediately crosses strictly below `delta` after first contact.

The initial strict separation is essential for the repository's convention
that only strictly positive times are candidates: an isolated contact at time
zero would otherwise not be recovered by outer strict approximations.
-/

namespace ArchonPhysics.MeasurableClosedHittingTime

open Filter MeasureTheory Set Topology
open ArchonPhysics ArchonPhysics.MeasurableHittingTime

noncomputable section

/-- Outer strict-threshold approximation to a closed first-hitting time. -/
def outerStrictApproximationHittingTime
    (distance : Real -> Real) (delta : Real) : ENNReal :=
  ⨆ n : Nat,
    strictDistanceThresholdHittingTime distance
      (delta + (((n + 1 : Nat) : Real)⁻¹))

/-- Measurable positive-rational version of the same outer approximation. -/
def outerRationalStrictApproximationHittingTime
    (distance : Real -> Real) (delta : Real) : ENNReal :=
  ⨆ n : Nat,
    rationalStrictDistanceThresholdHittingTime distance
      (delta + (((n + 1 : Nat) : Real)⁻¹))

/-- A local continuity hypothesis at a positive strict hit is enough to find
a strictly earlier positive rational hit. -/
theorem exists_positive_rational_before_of_continuousAt_lt
    {distance : Real -> Real} {delta u : Real}
    (hcontinuous : ContinuousAt distance u) (hu_pos : 0 < u)
    (hu_hit : distance u < delta) :
    ∃ q : Rat, 0 < (q : Real) ∧ (q : Real) < u ∧
      distance (q : Real) < delta := by
  have hpreimage : distance ⁻¹' Iio delta ∈ 𝓝 u :=
    hcontinuous.preimage_mem_nhds (Iio_mem_nhds hu_hit)
  obtain ⟨left, right, hu_interval, hsubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hpreimage
  have hmax_lt : max 0 left < u := max_lt hu_pos hu_interval.1
  obtain ⟨q, hmax_q, hq_u⟩ := exists_rat_btwn hmax_lt
  have hq_pos : 0 < (q : Real) :=
    lt_of_le_of_lt (le_max_left 0 left) hmax_q
  have hleft_q : left < (q : Real) :=
    lt_of_le_of_lt (le_max_right 0 left) hmax_q
  have hq_hit : distance (q : Real) < delta :=
    hsubset ⟨hleft_q, hq_u.trans hu_interval.2⟩
  exact ⟨q, hq_pos, hq_u, hq_hit⟩

/-- Every outer strict approximation hits no later than the closed target. -/
theorem outerStrictApproximationHittingTime_le_closed
    (distance : Real -> Real) (delta : Real) :
    outerStrictApproximationHittingTime distance delta <=
      distanceThresholdHittingTime distance delta := by
  unfold outerStrictApproximationHittingTime
  apply iSup_le
  intro n
  unfold strictDistanceThresholdHittingTime distanceThresholdHittingTime
  apply HittingTime.firstHittingTime_mono
  intro time htime
  exact lt_add_of_le_of_pos htime (by positivity)

/--
Uniform strict separation on every compact time interval lying before the
closed first hit.  Continuity plus strict separation at time zero will imply
this property below.
-/
def StrictlySeparatedBeforeClosedHit
    (distance : Real -> Real) (delta : Real) : Prop :=
  ∀ b : ENNReal,
    b < distanceThresholdHittingTime distance delta ->
      ∃ epsilon : Real, 0 < epsilon ∧
        ∀ time : ENNReal, 0 < time -> time <= b ->
          delta + epsilon <= distance time.toReal

/-- Positive-time continuity makes every rational outer approximation no
later than the closed hit. -/
theorem outerRationalStrictApproximationHittingTime_le_closed
    (distance : Real -> Real) (delta : Real)
    (hcontinuous : ∀ t : Real, 0 < t -> ContinuousAt distance t) :
    outerRationalStrictApproximationHittingTime distance delta <=
      distanceThresholdHittingTime distance delta := by
  unfold outerRationalStrictApproximationHittingTime
  apply iSup_le
  intro n
  rw [distanceThresholdHittingTime, HittingTime.firstHittingTime]
  apply le_sInf
  intro time htime
  change 0 < time ∧ distance time.toReal <= delta at htime
  by_cases htime_top : time = ⊤
  · simp only [htime_top, le_top]
  · have htime_toReal_pos : 0 < time.toReal :=
      ENNReal.toReal_pos (ne_of_gt htime.1) htime_top
    have hstrict :
        distance time.toReal <
          delta + (((n + 1 : Nat) : Real)⁻¹) :=
      lt_add_of_le_of_pos htime.2 (by positivity)
    obtain ⟨q, hq_pos, hq_lt, hq_hit⟩ :=
      exists_positive_rational_before_of_continuousAt_lt
        (hcontinuous time.toReal htime_toReal_pos)
        htime_toReal_pos hstrict
    calc
      rationalStrictDistanceThresholdHittingTime distance
          (delta + (((n + 1 : Nat) : Real)⁻¹)) <=
          (if 0 < ENNReal.ofReal (q : Real) ∧
              distance (q : Real) <
                delta + (((n + 1 : Nat) : Real)⁻¹) then
            ENNReal.ofReal (q : Real)
          else ⊤) := iInf_le _ q
      _ = ENNReal.ofReal (q : Real) :=
        if_pos ⟨ENNReal.ofReal_pos.mpr hq_pos, hq_hit⟩
      _ <= time := ENNReal.ofReal_le_of_le_toReal (le_of_lt hq_lt)

/-- Positive-time continuity and compact pre-hit separation identify the
measurable rational outer approximation with the true closed hit. -/
theorem outerRationalStrictApproximationHittingTime_eq_closed_of_separated
    (distance : Real -> Real) (delta : Real)
    (hcontinuous : ∀ t : Real, 0 < t -> ContinuousAt distance t)
    (hseparated : StrictlySeparatedBeforeClosedHit distance delta) :
    outerRationalStrictApproximationHittingTime distance delta =
      distanceThresholdHittingTime distance delta := by
  apply le_antisymm
  · exact outerRationalStrictApproximationHittingTime_le_closed
      distance delta hcontinuous
  · by_contra hnot
    have hlt :
        outerRationalStrictApproximationHittingTime distance delta <
          distanceThresholdHittingTime distance delta :=
      lt_of_not_ge hnot
    obtain ⟨b, happ_b, hb_hit⟩ := exists_between hlt
    obtain ⟨epsilon, hepsilon_pos, hmargin⟩ := hseparated b hb_hit
    obtain ⟨m, hm_pos, hm_inv⟩ :=
      Real.exists_nat_pos_inv_lt hepsilon_pos
    let n : Nat := m - 1
    have hn_succ : n + 1 = m := by
      dsimp [n]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hm_pos))
    have hb_le_n :
        b <= rationalStrictDistanceThresholdHittingTime distance
          (delta + (((n + 1 : Nat) : Real)⁻¹)) := by
      unfold rationalStrictDistanceThresholdHittingTime
      apply le_iInf
      intro q
      by_cases hq : 0 < ENNReal.ofReal (q : Real) ∧
          distance (q : Real) <
            delta + (((n + 1 : Nat) : Real)⁻¹)
      · rw [if_pos hq]
        by_contra hnot_b_le
        have hq_lt_b : ENNReal.ofReal (q : Real) < b :=
          lt_of_not_ge hnot_b_le
        have hbefore := hmargin (ENNReal.ofReal (q : Real))
          hq.1 (le_of_lt hq_lt_b)
        have hq_real_pos : 0 < (q : Real) := ENNReal.ofReal_pos.mp hq.1
        rw [ENNReal.toReal_ofReal (le_of_lt hq_real_pos)] at hbefore
        rw [hn_succ] at hq
        linarith
      · rw [if_neg hq]
        exact le_top
    have hn_le :
        rationalStrictDistanceThresholdHittingTime distance
            (delta + (((n + 1 : Nat) : Real)⁻¹)) <=
          outerRationalStrictApproximationHittingTime distance delta := by
      exact le_iSup (fun k : Nat =>
        rationalStrictDistanceThresholdHittingTime distance
          (delta + (((k + 1 : Nat) : Real)⁻¹))) n
    exact (not_lt_of_ge (hb_le_n.trans hn_le)) happ_b

/-- Compact pre-hit separation identifies the closed hit with its outer strict approximations. -/
theorem outerStrictApproximationHittingTime_eq_closed_of_separated
    (distance : Real -> Real) (delta : Real)
    (hseparated : StrictlySeparatedBeforeClosedHit distance delta) :
    outerStrictApproximationHittingTime distance delta =
      distanceThresholdHittingTime distance delta := by
  apply le_antisymm
  · exact outerStrictApproximationHittingTime_le_closed distance delta
  · by_contra hnot
    have hlt :
        outerStrictApproximationHittingTime distance delta <
          distanceThresholdHittingTime distance delta :=
      lt_of_not_ge hnot
    obtain ⟨b, happ_b, hb_hit⟩ := exists_between hlt
    obtain ⟨epsilon, hepsilon_pos, hmargin⟩ := hseparated b hb_hit
    obtain ⟨m, hm_pos, hm_inv⟩ :=
      Real.exists_nat_pos_inv_lt hepsilon_pos
    let n : Nat := m - 1
    have hn_succ : n + 1 = m := by
      dsimp [n]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hm_pos))
    have hb_le_n :
        b <= strictDistanceThresholdHittingTime distance
          (delta + (((n + 1 : Nat) : Real)⁻¹)) := by
      unfold strictDistanceThresholdHittingTime HittingTime.firstHittingTime
      apply le_sInf
      intro time htime
      change 0 < time ∧
        distance time.toReal <
          delta + (((n + 1 : Nat) : Real)⁻¹) at htime
      by_contra hnot_b_le
      have htime_lt_b : time < b := lt_of_not_ge hnot_b_le
      have hbefore := hmargin time htime.1 (le_of_lt htime_lt_b)
      rw [hn_succ] at htime
      linarith
    have hn_le :
        strictDistanceThresholdHittingTime distance
            (delta + (((n + 1 : Nat) : Real)⁻¹)) <=
          outerStrictApproximationHittingTime distance delta := by
      exact le_iSup (fun k : Nat =>
        strictDistanceThresholdHittingTime distance
          (delta + (((k + 1 : Nat) : Real)⁻¹))) n
    exact (not_lt_of_ge (hb_le_n.trans hn_le)) happ_b

/--
For a continuous path starting strictly outside the target, compactness gives
a positive distance margin on every interval strictly before the closed hit.
-/
theorem strictlySeparatedBeforeClosedHit_of_continuous
    (distance : Real -> Real) (delta : Real)
    (hcontinuous : Continuous distance)
    (hinitial : delta < distance 0) :
    StrictlySeparatedBeforeClosedHit distance delta := by
  intro b hb_hit
  have hb_ne_top : b ≠ ⊤ := ne_top_of_lt hb_hit
  obtain ⟨x, hx, hxmin⟩ :=
    isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr ENNReal.toReal_nonneg)
      hcontinuous.continuousOn
  have hx_strict : delta < distance x := by
    by_cases hx_zero : x = 0
    · simpa only [hx_zero] using hinitial
    · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_zero)
      by_contra hnot_strict
      have hx_hit : distance x <= delta := le_of_not_gt hnot_strict
      have hclosed_le_x :
          distanceThresholdHittingTime distance delta <=
            (Real.toNNReal x : ENNReal) :=
        distanceThresholdHittingTime_le_of_hit hx_pos hx_hit
      have hx_le_b : (Real.toNNReal x : ENNReal) <= b := by
        apply (ENNReal.toReal_le_toReal (by simp) hb_ne_top).mp
        rw [ENNReal.coe_toReal, Real.coe_toNNReal _ hx.1]
        exact hx.2
      exact (not_lt_of_ge (hclosed_le_x.trans hx_le_b)) hb_hit
  refine ⟨(distance x - delta) / 2, by linarith, ?_⟩
  intro time htime_pos htime_b
  have htime_ne_top : time ≠ ⊤ := by
    exact ne_top_of_lt (htime_b.trans_lt hb_hit)
  have htime_mem : time.toReal ∈ Icc (0 : Real) b.toReal := by
    constructor
    · exact ENNReal.toReal_nonneg
    · exact (ENNReal.toReal_le_toReal htime_ne_top hb_ne_top).2 htime_b
  have hmin_le : distance x <= distance time.toReal :=
    hxmin htime_mem
  linarith

/-- A continuous initially separated path has the exact outer-approximation formula. -/
theorem outerStrictApproximationHittingTime_eq_closed
    (distance : Real -> Real) (delta : Real)
    (hcontinuous : Continuous distance)
    (hinitial : delta < distance 0) :
    outerStrictApproximationHittingTime distance delta =
      distanceThresholdHittingTime distance delta := by
  exact outerStrictApproximationHittingTime_eq_closed_of_separated
    distance delta
    (strictlySeparatedBeforeClosedHit_of_continuous
      distance delta hcontinuous hinitial)

/-- Rational outer approximations are measurable using only countably many evaluations. -/
theorem measurable_outerRationalStrictApproximationHittingTime
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega -> Real -> Real) (delta : Real)
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real))) :
    Measurable (fun omega =>
      outerRationalStrictApproximationHittingTime
        (distance omega) delta) := by
  unfold outerRationalStrictApproximationHittingTime
  apply Measurable.iSup
  intro n
  exact measurable_rationalStrictDistanceThresholdHittingTime
    distance (delta + (((n + 1 : Nat) : Real)⁻¹)) heval

/-- Positive-time continuity and compact pre-hit separation suffice for
measurability of the true closed hit; no continuity at the totalized value
T = 0 is required. -/
theorem measurable_closedDistanceThresholdHittingTime_of_positiveTime
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega -> Real -> Real) (delta : Real)
    (hcontinuous : ∀ omega t, 0 < t ->
      ContinuousAt (distance omega) t)
    (hseparated : ∀ omega,
      StrictlySeparatedBeforeClosedHit (distance omega) delta)
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real))) :
    Measurable (fun omega =>
      distanceThresholdHittingTime (distance omega) delta) := by
  have heq :
      (fun omega => distanceThresholdHittingTime (distance omega) delta) =
        (fun omega => outerRationalStrictApproximationHittingTime
          (distance omega) delta) := by
    funext omega
    exact (outerRationalStrictApproximationHittingTime_eq_closed_of_separated
      (distance omega) delta (hcontinuous omega) (hseparated omega)).symm
  rw [heq]
  exact measurable_outerRationalStrictApproximationHittingTime
    distance delta heval

/-- Outer strict approximations are measurable from rational-time evaluations. -/
theorem measurable_outerStrictApproximationHittingTime
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega -> Real -> Real) (delta : Real)
    (hcontinuous : ∀ omega, Continuous (distance omega))
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real))) :
    Measurable (fun omega =>
      outerStrictApproximationHittingTime (distance omega) delta) := by
  unfold outerStrictApproximationHittingTime
  apply Measurable.iSup
  intro n
  exact measurable_strictDistanceThresholdHittingTime
    distance (delta + (((n + 1 : Nat) : Real)⁻¹)) hcontinuous heval

/--
Closed-threshold first hitting is measurable for continuous random paths that
start strictly outside the target.
-/
theorem measurable_closedDistanceThresholdHittingTime
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega -> Real -> Real) (delta : Real)
    (hcontinuous : ∀ omega, Continuous (distance omega))
    (hinitial : ∀ omega, delta < distance omega 0)
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real))) :
    Measurable (fun omega =>
      distanceThresholdHittingTime (distance omega) delta) := by
  have heq :
      (fun omega => distanceThresholdHittingTime (distance omega) delta) =
        (fun omega =>
          outerStrictApproximationHittingTime (distance omega) delta) := by
    funext omega
    exact (outerStrictApproximationHittingTime_eq_closed
      (distance omega) delta (hcontinuous omega) (hinitial omega)).symm
  rw [heq]
  exact measurable_outerStrictApproximationHittingTime
    distance delta hcontinuous heval

end

end ArchonPhysics.MeasurableClosedHittingTime
