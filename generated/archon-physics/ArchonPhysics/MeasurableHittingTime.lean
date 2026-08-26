import ArchonPhysics.HittingTimeStability

/-!
# Measurability of countable and continuous-path hitting times

Countable hitting times are measurable infima of measurable two-valued
functions.  Continuous strict-threshold hitting times reduce to positive
rational times by density.  For the repository's closed threshold `≤ delta`,
the same reduction needs an explicit entry condition; continuity alone does
not imply that a path moves strictly inside the threshold after touching it.
-/

namespace ArchonPhysics.MeasurableHittingTime

open MeasureTheory Set
open ArchonPhysics

noncomputable section

/-- A candidate time, or `top` when its indexed event does not occur. -/
def countableHittingCandidate {I Omega : Type*}
    (time : I → ENNReal) (event : I → Omega → Prop)
    (omega : Omega) (i : I) : ENNReal := by
  classical
  exact if 0 < time i ∧ event i omega then time i else ⊤

/-- The first hit in a countable time family, with `top` for every failed candidate. -/
def countableFirstHittingTime {I Omega : Type*} [Countable I]
    (time : I → ENNReal) (event : I → Omega → Prop) (omega : Omega) : ENNReal := by
  exact ⨅ i, countableHittingCandidate time event omega i

/-- The countable infimum is literally the infimum of its candidate-time range. -/
theorem countableFirstHittingTime_eq_sInf_range
    {I Omega : Type*} [Countable I]
    (time : I → ENNReal) (event : I → Omega → Prop) (omega : Omega) :
    countableFirstHittingTime time event omega =
      sInf (range (countableHittingCandidate time event omega)) := by
  rw [countableFirstHittingTime, sInf_range]

/-- Countably many measurable time events give a measurable first hitting time. -/
theorem measurable_countableFirstHittingTime
    {I Omega : Type*} [Countable I] [MeasurableSpace Omega]
    (time : I → ENNReal) (event : I → Omega → Prop)
    (hevent : ∀ i, MeasurableSet {omega | event i omega}) :
    Measurable (countableFirstHittingTime time event) := by
  classical
  unfold countableFirstHittingTime countableHittingCandidate
  apply Measurable.iInf
  intro i
  by_cases htime : 0 < time i
  · have hite : Measurable (fun omega =>
        if event i omega then time i else ⊤) :=
      Measurable.ite (hevent i) measurable_const measurable_const
    simpa only [htime, true_and] using hite
  · simp only [htime, false_and, if_false]
    exact measurable_const

/-- First strictly positive real time at which the strict threshold is met. -/
def strictDistanceThresholdHittingTime
    (distance : Real → Real) (delta : Real) : ENNReal :=
  HittingTime.firstHittingTime
    (fun time => distance time.toReal < delta)

/-- First positive rational time at which the strict threshold is met. -/
def rationalStrictDistanceThresholdHittingTime
    (distance : Real → Real) (delta : Real) : ENNReal := by
  classical
  exact ⨅ q : Rat,
    if 0 < ENNReal.ofReal (q : Real) ∧ distance (q : Real) < delta then
      ENNReal.ofReal (q : Real)
    else ⊤

/-- Rational-time strict hitting is measurable from measurable rational evaluations. -/
theorem measurable_rationalStrictDistanceThresholdHittingTime
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega → Real → Real) (delta : Real)
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real))) :
    Measurable (fun omega =>
      rationalStrictDistanceThresholdHittingTime (distance omega) delta) := by
  classical
  unfold rationalStrictDistanceThresholdHittingTime
  apply Measurable.iInf
  intro q
  by_cases hq_pos : 0 < ENNReal.ofReal (q : Real)
  · have hite : Measurable (fun omega =>
        if distance omega (q : Real) < delta then
          ENNReal.ofReal (q : Real)
        else ⊤) :=
      Measurable.ite (measurableSet_Iio.preimage (heval q))
        measurable_const measurable_const
    simpa only [hq_pos, true_and] using hite
  · simp only [hq_pos, false_and, if_false]
    exact measurable_const

/--
A positive strict hit of a continuous real path has a positive rational strict
hit immediately before it.  This is the only density step used below.
-/
theorem exists_positive_rational_before_of_continuous_lt
    {distance : Real → Real} {delta u : Real}
    (hcontinuous : Continuous distance) (hu_pos : 0 < u)
    (hu_hit : distance u < delta) :
    ∃ q : Rat, 0 < (q : Real) ∧ (q : Real) < u ∧
      distance (q : Real) < delta := by
  have hopen : IsOpen (distance ⁻¹' Iio delta) :=
    isOpen_Iio.preimage hcontinuous
  obtain ⟨left, right, hu_interval, hsubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hu_hit)
  have hmax_lt : max 0 left < u := max_lt hu_pos hu_interval.1
  obtain ⟨q, hmax_q, hq_u⟩ := exists_rat_btwn hmax_lt
  have hq_pos : 0 < (q : Real) :=
    lt_of_le_of_lt (le_max_left 0 left) hmax_q
  have hleft_q : left < (q : Real) :=
    lt_of_le_of_lt (le_max_right 0 left) hmax_q
  have hq_hit : distance (q : Real) < delta :=
    hsubset ⟨hleft_q, hq_u.trans hu_interval.2⟩
  exact ⟨q, hq_pos, hq_u, hq_hit⟩

/-- A continuous strict-threshold hitting time equals its positive-rational version. -/
theorem rationalStrictDistanceThresholdHittingTime_eq_strict
    (distance : Real → Real) (delta : Real)
    (hcontinuous : Continuous distance) :
    rationalStrictDistanceThresholdHittingTime distance delta =
      strictDistanceThresholdHittingTime distance delta := by
  classical
  apply le_antisymm
  · rw [strictDistanceThresholdHittingTime,
      HittingTime.firstHittingTime, HittingTime.hittingTimes]
    apply le_sInf
    intro time htime
    by_cases htime_top : time = ⊤
    · simp only [htime_top, le_top]
    · have htime_toReal_pos : 0 < time.toReal :=
        ENNReal.toReal_pos (ne_of_gt htime.1) htime_top
      obtain ⟨q, hq_pos, hq_lt, hq_hit⟩ :=
        exists_positive_rational_before_of_continuous_lt
          hcontinuous htime_toReal_pos htime.2
      calc
        rationalStrictDistanceThresholdHittingTime distance delta ≤
            (if 0 < ENNReal.ofReal (q : Real) ∧
                distance (q : Real) < delta then
              ENNReal.ofReal (q : Real)
            else ⊤) := iInf_le _ q
        _ = ENNReal.ofReal (q : Real) :=
          if_pos ⟨ENNReal.ofReal_pos.mpr hq_pos, hq_hit⟩
        _ ≤ time := ENNReal.ofReal_le_of_le_toReal (le_of_lt hq_lt)
  · apply le_iInf
    intro q
    by_cases hq : 0 < ENNReal.ofReal (q : Real) ∧
        distance (q : Real) < delta
    · rw [if_pos hq, strictDistanceThresholdHittingTime]
      apply HittingTime.firstHittingTime_le_of_mem
      refine ⟨hq.1, ?_⟩
      have hq_real_pos : 0 < (q : Real) := ENNReal.ofReal_pos.mp hq.1
      change distance (ENNReal.ofReal (q : Real)).toReal < delta
      rw [ENNReal.toReal_ofReal (le_of_lt hq_real_pos)]
      exact hq.2
    · rw [if_neg hq]
      exact le_top

/-- Continuous random paths have measurable strict-threshold hitting times. -/
theorem measurable_strictDistanceThresholdHittingTime
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega → Real → Real) (delta : Real)
    (hcontinuous : ∀ omega, Continuous (distance omega))
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real))) :
    Measurable (fun omega =>
      strictDistanceThresholdHittingTime (distance omega) delta) := by
  have heq :
      (fun omega => strictDistanceThresholdHittingTime
        (distance omega) delta) =
      (fun omega => rationalStrictDistanceThresholdHittingTime
        (distance omega) delta) := by
    funext omega
    exact (rationalStrictDistanceThresholdHittingTime_eq_strict
      (distance omega) delta (hcontinuous omega)).symm
  rw [heq]
  exact measurable_rationalStrictDistanceThresholdHittingTime
    distance delta heval

/--
Dense-entry condition for the repository's closed threshold: every positive
closed hit and every strictly later extended time have a positive rational
strict hit before that later time.
-/
def RationalStrictEntryCondition
    (distance : Real → Real) (delta : Real) : Prop :=
  ∀ t b : ENNReal, 0 < t → distance t.toReal ≤ delta → t < b →
    ∃ q : Rat, 0 < (q : Real) ∧
      ENNReal.ofReal (q : Real) < b ∧ distance (q : Real) < delta

/--
An explicit real-time condition saying that after every positive closed hit,
the path enters the strict threshold before any later real time.
-/
def ImmediateStrictEntryAfterClosedHit
    (distance : Real → Real) (delta : Real) : Prop :=
  ∀ t b : Real, 0 < t → distance t ≤ delta → t < b →
    ∃ u : Real, t < u ∧ u < b ∧ distance u < delta

/-- Continuity and immediate strict entry imply the rational dense-entry condition. -/
theorem rationalStrictEntryCondition_of_continuous_of_immediateStrictEntry
    (distance : Real → Real) (delta : Real)
    (hcontinuous : Continuous distance)
    (hentry : ImmediateStrictEntryAfterClosedHit distance delta) :
    RationalStrictEntryCondition distance delta := by
  intro t b ht_pos ht_hit ht_b
  have ht_ne_top : t ≠ ⊤ := ne_top_of_lt ht_b
  have ht_toReal_pos : 0 < t.toReal :=
    ENNReal.toReal_pos (ne_of_gt ht_pos) ht_ne_top
  by_cases hb_top : b = ⊤
  · have hnext : t.toReal < t.toReal + 1 := by linarith
    obtain ⟨u, _ht_u, hu_next, hu_hit⟩ :=
      hentry t.toReal (t.toReal + 1) ht_toReal_pos ht_hit hnext
    obtain ⟨q, hq_pos, hq_u, hq_hit⟩ :=
      exists_positive_rational_before_of_continuous_lt
        hcontinuous (ht_toReal_pos.trans _ht_u) hu_hit
    refine ⟨q, hq_pos, ?_, hq_hit⟩
    simpa only [hb_top] using (ENNReal.ofReal_lt_top :
      ENNReal.ofReal (q : Real) < ⊤)
  · have ht_b_toReal : t.toReal < b.toReal :=
      (ENNReal.toReal_lt_toReal ht_ne_top hb_top).2 ht_b
    obtain ⟨u, _ht_u, hu_b, hu_hit⟩ :=
      hentry t.toReal b.toReal ht_toReal_pos ht_hit ht_b_toReal
    obtain ⟨q, hq_pos, hq_u, hq_hit⟩ :=
      exists_positive_rational_before_of_continuous_lt
        hcontinuous (ht_toReal_pos.trans _ht_u) hu_hit
    refine ⟨q, hq_pos, ?_, hq_hit⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hq_pos) hb_top).2
      (hq_u.trans hu_b)

/-- Under the dense-entry condition, the current closed hitting time is rationally encoded. -/
theorem distanceThresholdHittingTime_eq_rationalStrict
    (distance : Real → Real) (delta : Real)
    (hentry : RationalStrictEntryCondition distance delta) :
    distanceThresholdHittingTime distance delta =
      rationalStrictDistanceThresholdHittingTime distance delta := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro q
    by_cases hq : 0 < ENNReal.ofReal (q : Real) ∧
        distance (q : Real) < delta
    · rw [if_pos hq]
      exact distanceThresholdHittingTime_le_of_hit
        (ENNReal.ofReal_pos.mp hq.1) (le_of_lt hq.2)
    · rw [if_neg hq]
      exact le_top
  · rw [distanceThresholdHittingTime, HittingTime.firstHittingTime]
    apply le_sInf
    intro time htime
    change 0 < time ∧ distance time.toReal ≤ delta at htime
    by_contra hnot
    have htime_lt : time <
        rationalStrictDistanceThresholdHittingTime distance delta :=
      lt_of_not_ge hnot
    obtain ⟨q, hq_pos, hq_before, hq_hit⟩ :=
      hentry time
        (rationalStrictDistanceThresholdHittingTime distance delta)
        htime.1 htime.2 htime_lt
    have hinf_le :
        rationalStrictDistanceThresholdHittingTime distance delta ≤
          ENNReal.ofReal (q : Real) := by
      exact iInf_le_of_le q
        (le_of_eq (if_pos
          ⟨ENNReal.ofReal_pos.mpr hq_pos, hq_hit⟩))
    exact (not_lt_of_ge hinf_le) hq_before

/-- Closed-threshold hitting is measurable under rational evaluation and dense entry. -/
theorem measurable_distanceThresholdHittingTime_of_rationalStrictEntry
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega → Real → Real) (delta : Real)
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real)))
    (hentry : ∀ omega,
      RationalStrictEntryCondition (distance omega) delta) :
    Measurable (fun omega =>
      distanceThresholdHittingTime (distance omega) delta) := by
  have heq :
      (fun omega => distanceThresholdHittingTime
        (distance omega) delta) =
      (fun omega => rationalStrictDistanceThresholdHittingTime
        (distance omega) delta) := by
    funext omega
    exact distanceThresholdHittingTime_eq_rationalStrict
      (distance omega) delta (hentry omega)
  rw [heq]
  exact measurable_rationalStrictDistanceThresholdHittingTime
    distance delta heval

/-- A continuous-path adapter for the closed threshold with explicit entry behavior. -/
theorem measurable_distanceThresholdHittingTime_of_continuous_of_immediateStrictEntry
    {Omega : Type*} [MeasurableSpace Omega]
    (distance : Omega → Real → Real) (delta : Real)
    (hcontinuous : ∀ omega, Continuous (distance omega))
    (hentry : ∀ omega,
      ImmediateStrictEntryAfterClosedHit (distance omega) delta)
    (heval : ∀ q : Rat,
      Measurable (fun omega => distance omega (q : Real))) :
    Measurable (fun omega =>
      distanceThresholdHittingTime (distance omega) delta) := by
  apply measurable_distanceThresholdHittingTime_of_rationalStrictEntry
    distance delta heval
  intro omega
  exact rationalStrictEntryCondition_of_continuous_of_immediateStrictEntry
    (distance omega) delta (hcontinuous omega) (hentry omega)

end

end ArchonPhysics.MeasurableHittingTime
