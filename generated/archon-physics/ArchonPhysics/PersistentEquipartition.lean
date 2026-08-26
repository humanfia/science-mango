import Mathlib
import ArchonPhysics.HittingTime

/-!
# Persistent equipartition tails and settling times

A first threshold hit need not be permanent.  This module therefore separates
the first-hitting convention from a tail event which holds at every *finite*
future extended time.  Excluding `⊤` is essential for real-valued paths:
`ENNReal.toReal ⊤ = 0`, so evaluating an event at `⊤` would incorrectly inspect
the initial real time again.

The results are purely order-theoretic and asymptotic.  They do not assert that
a microscopic lattice trajectory converges to equipartition.
-/

namespace ArchonPhysics.PersistentEquipartition

open Filter Set Topology
open scoped ENNReal

noncomputable section

/-- An event holds at every finite extended time at or after `start`.

The condition `future < ⊤` deliberately prevents a real-time event composed
with `ENNReal.toReal` from being evaluated at `⊤`. -/
def TailPersistsFor (A : ENNReal → Prop) (start : ENNReal) : Prop :=
  ∀ future, start ≤ future → future < ⊤ → A future

/-- Strictly positive finite starts whose entire finite future satisfies the
event. -/
def settlingTimes (A : ENNReal → Prop) : Set ENNReal :=
  {start | 0 < start ∧ start < ⊤ ∧ TailPersistsFor A start}

/-- The first possible permanent-tail start, with `⊤` when there is no such
start.  As with any `sInf`, this definition alone does not assert attainment. -/
def settlingTime (A : ENNReal → Prop) : ENNReal :=
  sInf (settlingTimes A)

/-- A finite permanent-tail witness bounds the settling time from above. -/
theorem settlingTime_le_of_mem (A : ENNReal → Prop) {start : ENNReal}
    (hstart : start ∈ settlingTimes A) :
    settlingTime A ≤ start := by
  exact sInf_le hstart

/-- Every permanent-tail start is in particular an event time, so the first
hit is no later than the settling-time infimum.  No attainment of either
infimum is used. -/
theorem firstHittingTime_le_settlingTime (A : ENNReal → Prop) :
    HittingTime.firstHittingTime A ≤ settlingTime A := by
  unfold settlingTime
  apply le_sInf
  intro start hstart
  change 0 < start ∧ start < ⊤ ∧ TailPersistsFor A start at hstart
  exact HittingTime.firstHittingTime_le_of_mem A
    ⟨hstart.1, hstart.2.2 start le_rfl hstart.2.1⟩

/-- A strict real-valued distance threshold, explicitly disabled at `⊤`. -/
def strictFiniteDistanceEvent (distance : Real → Real) (delta : Real)
    (time : ENNReal) : Prop :=
  time < ⊤ ∧ distance time.toReal < delta

/-- The permanent settling time for the strict distance threshold. -/
def strictDistanceSettlingTime (distance : Real → Real)
    (delta : Real) : ENNReal :=
  settlingTime (strictFiniteDistanceEvent distance delta)

/-- Convergence of a real distance to zero produces a positive real time after
which the strict threshold holds forever. -/
theorem exists_real_tail_of_tendsto_zero
    (distance : Real → Real) (delta : Real)
    (hzero : Tendsto distance atTop (nhds 0)) (hdelta : 0 < delta) :
    ∃ start : Real, 0 < start ∧
      ∀ future : Real, start ≤ future → distance future < delta := by
  have heventually : ∀ᶠ future : Real in atTop, distance future < delta :=
    (tendsto_order.mp hzero).2 delta hdelta
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 heventually
  refine ⟨max 1 cutoff, lt_of_lt_of_le zero_lt_one (le_max_left 1 cutoff), ?_⟩
  intro future hfuture
  exact hcutoff future ((le_max_right 1 cutoff).trans hfuture)

/-- The same convergence gives a positive finite `ENNReal` tail witness. -/
theorem exists_ennreal_tail_of_tendsto_zero
    (distance : Real → Real) (delta : Real)
    (hzero : Tendsto distance atTop (nhds 0)) (hdelta : 0 < delta) :
    ∃ start : ENNReal, 0 < start ∧ start < ⊤ ∧
      TailPersistsFor (strictFiniteDistanceEvent distance delta) start := by
  obtain ⟨start, hstartPos, htail⟩ :=
    exists_real_tail_of_tendsto_zero distance delta hzero hdelta
  refine ⟨ENNReal.ofReal start, ENNReal.ofReal_pos.mpr hstartPos,
    ENNReal.ofReal_lt_top, ?_⟩
  intro future hstartFuture hfutureFinite
  refine ⟨hfutureFinite, htail future.toReal ?_⟩
  have htoReal : (ENNReal.ofReal start).toReal ≤ future.toReal :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (ne_top_of_lt hfutureFinite)).2 hstartFuture
  simpa [ENNReal.toReal_ofReal hstartPos.le] using htoReal

/-- Consequently the strict-threshold settling time is finite. -/
theorem strictDistanceSettlingTime_lt_top_of_tendsto_zero
    (distance : Real → Real) (delta : Real)
    (hzero : Tendsto distance atTop (nhds 0)) (hdelta : 0 < delta) :
    strictDistanceSettlingTime distance delta < ⊤ := by
  obtain ⟨start, hstartPos, hstartFinite, htail⟩ :=
    exists_ennreal_tail_of_tendsto_zero distance delta hzero hdelta
  exact (settlingTime_le_of_mem
    (strictFiniteDistanceEvent distance delta)
    ⟨hstartPos, hstartFinite, htail⟩).trans_lt hstartFinite

/-- On nonnegative real time, an antitone distance remains below a strict
threshold after any strict hit. -/
theorem strict_threshold_persists_on_real_tail_of_antitoneOn
    (distance : Real → Real) (delta start : Real)
    (hanti : AntitoneOn distance (Ici 0))
    (hstart : 0 ≤ start) (hhit : distance start < delta) :
    ∀ future : Real, start ≤ future → distance future < delta := by
  intro future hstartFuture
  have hfuture : 0 ≤ future := hstart.trans hstartFuture
  exact (hanti (mem_Ici.mpr hstart) (mem_Ici.mpr hfuture)
    hstartFuture).trans_lt hhit

/-- The finite-extended-time version of forward persistence under
antitonicity on nonnegative real time. -/
theorem tailPersistsFor_strictFiniteDistanceEvent_of_antitoneOn
    (distance : Real → Real) (delta : Real) {start : ENNReal}
    (hstartFinite : start < ⊤)
    (hanti : AntitoneOn distance (Ici 0))
    (hhit : distance start.toReal < delta) :
    TailPersistsFor (strictFiniteDistanceEvent distance delta) start := by
  intro future hstartFuture hfutureFinite
  refine ⟨hfutureFinite, ?_⟩
  have hrealOrder : start.toReal ≤ future.toReal :=
    (ENNReal.toReal_le_toReal (ne_top_of_lt hstartFinite)
      (ne_top_of_lt hfutureFinite)).2 hstartFuture
  exact strict_threshold_persists_on_real_tail_of_antitoneOn
    distance delta start.toReal hanti ENNReal.toReal_nonneg hhit
      future.toReal hrealOrder

/-- A positive finite hit of an antitone distance is a settling-time
candidate and therefore bounds the settling time. -/
theorem strictDistanceSettlingTime_le_of_antitoneOn_hit
    (distance : Real → Real) (delta : Real) {start : ENNReal}
    (hstartPos : 0 < start) (hstartFinite : start < ⊤)
    (hanti : AntitoneOn distance (Ici 0))
    (hhit : distance start.toReal < delta) :
    strictDistanceSettlingTime distance delta ≤ start := by
  exact settlingTime_le_of_mem
    (strictFiniteDistanceEvent distance delta)
    ⟨hstartPos, hstartFinite,
      tailPersistsFor_strictFiniteDistanceEvent_of_antitoneOn
        distance delta hstartFinite hanti hhit⟩

/-- A globally antitone distance is a convenient specialization of the
nonnegative-time result. -/
theorem strictDistanceSettlingTime_le_of_antitone_hit
    (distance : Real → Real) (delta : Real) {start : ENNReal}
    (hstartPos : 0 < start) (hstartFinite : start < ⊤)
    (hanti : Antitone distance)
    (hhit : distance start.toReal < delta) :
    strictDistanceSettlingTime distance delta ≤ start := by
  apply strictDistanceSettlingTime_le_of_antitoneOn_hit
    distance delta hstartPos hstartFinite
  · intro left _hleft right _hright hleftRight
    exact hanti hleftRight
  · exact hhit

/-! ## Transport and kinetic time rescaling -/

/-- Settling time is equivariant under an arbitrary order isomorphism of
extended nonnegative time.  The transported event is evaluated after the
isomorphism, while its settling time is transported back by the same map. -/
theorem settlingTime_transport (A : ENNReal → Prop)
    (e : ENNReal ≃o ENNReal) :
    e (settlingTime (fun time ↦ A (e time))) = settlingTime A := by
  have htimes :
      e '' settlingTimes (fun time ↦ A (e time)) = settlingTimes A := by
    ext start
    constructor
    · rintro ⟨preimage, hpreimage, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · calc
          0 = e 0 := e.map_bot.symm
          _ < e preimage := e.strictMono hpreimage.1
      · have hmapped := e.strictMono hpreimage.2.1
        simpa using hmapped
      · intro future hfuture hfutureFinite
        have hpreimageFuture : preimage ≤ e.symm future := by
          have hmapped := e.symm.monotone hfuture
          simpa using hmapped
        have hpreimageFutureFinite : e.symm future < ⊤ := by
          have hmapped := e.symm.strictMono hfutureFinite
          simpa using hmapped
        simpa using hpreimage.2.2 (e.symm future)
          hpreimageFuture hpreimageFutureFinite
    · intro hstart
      refine ⟨e.symm start, ?_, e.apply_symm_apply start⟩
      refine ⟨?_, ?_, ?_⟩
      · calc
          0 = e.symm 0 := e.symm.map_bot.symm
          _ < e.symm start := e.symm.strictMono hstart.1
      · have hmapped := e.symm.strictMono hstart.2.1
        simpa using hmapped
      · intro future hfuture hfutureFinite
        have himageFuture : start ≤ e future := by
          have hmapped := e.monotone hfuture
          simpa using hmapped
        have himageFutureFinite : e future < ⊤ := by
          have hmapped := e.strictMono hfutureFinite
          simpa using hmapped
        exact hstart.2.2 (e future) himageFuture himageFutureFinite
  unfold settlingTime
  calc
    e (sInf (settlingTimes (fun time ↦ A (e time)))) =
        sInf (e '' settlingTimes (fun time ↦ A (e time))) :=
      sInfHomClass.map_sInf e _
    _ = sInf (settlingTimes A) := congrArg sInf htimes

/-- Dividing the real argument of a distance by a positive constant multiplies
its strict-threshold settling time by that constant. -/
theorem strictDistanceSettlingTime_timeScale
    (distance : Real → Real) (delta c : Real) (hc : 0 < c) :
    ENNReal.ofReal c * strictDistanceSettlingTime distance delta =
      strictDistanceSettlingTime (fun time ↦ distance (time / c)) delta := by
  let scale : ENNReal ≃o ENNReal :=
    ENNReal.mulLeftOrderIso (ENNReal.ofReal c)
      (ENNReal.isUnit_iff.mpr
        ⟨ENNReal.ofReal_ne_zero_iff.mpr hc, ENNReal.ofReal_ne_top⟩)
  have hevent :
      (fun time ↦
        strictFiniteDistanceEvent (fun realTime ↦ distance (realTime / c))
          delta (scale time)) =
        strictFiniteDistanceEvent distance delta := by
    funext time
    apply propext
    have hfinite : scale time < ⊤ ↔ time < ⊤ := by
      constructor
      · intro htime
        have hmapped := scale.symm.strictMono htime
        simpa using hmapped
      · intro htime
        have hmapped := scale.strictMono htime
        simpa using hmapped
    have htime : (scale time).toReal / c = time.toReal := by
      simp [scale, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hc.le, hc.ne']
    change (scale time < ⊤ ∧ distance ((scale time).toReal / c) < delta) ↔
      (time < ⊤ ∧ distance time.toReal < delta)
    exact and_congr hfinite (by rw [htime])
  change
    scale (settlingTime (strictFiniteDistanceEvent distance delta)) =
      settlingTime
        (strictFiniteDistanceEvent (fun time ↦ distance (time / c)) delta)
  calc
    scale (settlingTime (strictFiniteDistanceEvent distance delta)) =
        scale (settlingTime (fun time ↦
          strictFiniteDistanceEvent (fun realTime ↦ distance (realTime / c))
            delta (scale time))) := by
      exact congrArg scale (congrArg settlingTime hevent.symm)
    _ = settlingTime
        (strictFiniteDistanceEvent (fun time ↦ distance (time / c)) delta) :=
      settlingTime_transport
        (strictFiniteDistanceEvent (fun time ↦ distance (time / c)) delta) scale

/-- The kinetic `g²` specialization of positive time rescaling. -/
theorem strictDistanceSettlingTime_g_sq_timeScale
    (distance : Real → Real) (delta g : Real) (hg : g ≠ 0) :
    ENNReal.ofReal (g ^ 2) * strictDistanceSettlingTime distance delta =
      strictDistanceSettlingTime (fun time ↦ distance (time / g ^ 2)) delta := by
  exact strictDistanceSettlingTime_timeScale distance delta (g ^ 2)
    (sq_pos_of_ne_zero hg)

/-! ## Recurrence obstruction -/

/-- If every positive finite start has a later finite failure, no such start
can support a permanent tail. -/
theorem not_tailPersistsFor_of_recurrent_failure
    (A : ENNReal → Prop)
    (hfailure : ∀ start : ENNReal, 0 < start → start < ⊤ →
      ∃ future : ENNReal,
        start ≤ future ∧ future < ⊤ ∧ ¬ A future) :
    ∀ start : ENNReal, 0 < start → start < ⊤ →
      ¬ TailPersistsFor A start := by
  intro start hstartPos hstartFinite htail
  obtain ⟨future, hstartFuture, hfutureFinite, hnot⟩ :=
    hfailure start hstartPos hstartFinite
  exact hnot (htail future hstartFuture hfutureFinite)

/-- Under recurrent finite failures, there are no settling-time candidates. -/
theorem settlingTimes_eq_empty_of_recurrent_failure
    (A : ENNReal → Prop)
    (hfailure : ∀ start : ENNReal, 0 < start → start < ⊤ →
      ∃ future : ENNReal,
        start ≤ future ∧ future < ⊤ ∧ ¬ A future) :
    settlingTimes A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro start hstart
  exact not_tailPersistsFor_of_recurrent_failure A hfailure start
    hstart.1 hstart.2.1 hstart.2.2

/-- Recurrent finite failures force the settling time to be `⊤`; this is the
strongest conclusion available from the non-attainment definition by `sInf`. -/
theorem settlingTime_eq_top_of_recurrent_failure
    (A : ENNReal → Prop)
    (hfailure : ∀ start : ENNReal, 0 < start → start < ⊤ →
      ∃ future : ENNReal,
        start ≤ future ∧ future < ⊤ ∧ ¬ A future) :
    settlingTime A = ⊤ := by
  rw [settlingTime,
    settlingTimes_eq_empty_of_recurrent_failure A hfailure, sInf_empty]

/-- A one-time event gives a concrete counterexample: it is hit at time one
but does not persist even until time two. -/
def isolatedHitEvent (time : ENNReal) : Prop :=
  time = 1

theorem firstHittingTime_isolatedHitEvent :
    HittingTime.firstHittingTime isolatedHitEvent = 1 := by
  rw [HittingTime.firstHittingTime, HittingTime.hittingTimes]
  have hset : {time : ENNReal | 0 < time ∧ isolatedHitEvent time} = {1} := by
    ext time
    change (0 < time ∧ time = 1) ↔ time = 1
    constructor
    · exact fun htime ↦ htime.2
    · intro htime
      subst time
      exact ⟨by norm_num, rfl⟩
  rw [hset]
  exact csInf_singleton 1

theorem isolatedHitEvent_holds_at_one : isolatedHitEvent 1 := by
  rfl

theorem not_tailPersistsFor_isolatedHitEvent :
    ¬ TailPersistsFor isolatedHitEvent 1 := by
  intro htail
  have htwo := htail 2 (by norm_num) (by norm_num)
  norm_num [isolatedHitEvent] at htwo

/-- First hitting alone is therefore insufficient for permanent
equipartition, even when the first hit is finite and attained. -/
theorem first_hitting_alone_does_not_imply_tail_persistence :
    HittingTime.firstHittingTime isolatedHitEvent = 1 ∧
      isolatedHitEvent 1 ∧ ¬ TailPersistsFor isolatedHitEvent 1 := by
  exact ⟨firstHittingTime_isolatedHitEvent,
    isolatedHitEvent_holds_at_one,
    not_tailPersistsFor_isolatedHitEvent⟩

end

end ArchonPhysics.PersistentEquipartition
