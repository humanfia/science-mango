import Mathlib
import ArchonPhysics.HittingTime
import ArchonPhysics.QuantitativeKineticRelaxation

/-!
# Deterministic stability of positive-time threshold hitting

This module transports a robust first crossing through locally uniform
deterministic approximations.  Hitting times use ENNReal and the strictly
positive-time convention from ArchonPhysics.HittingTime, so an empty event set
has hitting time top.

The main theorem gives an arbitrary-epsilon two-sided squeeze.  In particular,
its finite upper bound explicitly rules out top for every sufficiently large
approximation.  No exact collision kernel, convergence theorem, or crossing
witness is constructed here: both local uniform convergence and the robust
crossing contract are hypotheses.
-/

namespace ArchonPhysics

open Filter

noncomputable section

/-- The threshold event for a real-valued distance observed at extended time. -/
def distanceThresholdEvent (distance : Real → Real) (delta : Real)
    (time : ENNReal) : Prop :=
  distance time.toReal ≤ delta

/--
The first strictly positive threshold-hit time.  It is top when the event set
is empty, by the convention of HittingTime.firstHittingTime.
-/
def distanceThresholdHittingTime (distance : Real → Real)
    (delta : Real) : ENNReal :=
  HittingTime.firstHittingTime (distanceThresholdEvent distance delta)

/-- The threshold hitting time is the infimum of its positive event times. -/
theorem distanceThresholdHittingTime_eq_sInf
    (distance : Real → Real) (delta : Real) :
    distanceThresholdHittingTime distance delta =
      sInf {time : ENNReal |
        0 < time ∧ distance time.toReal ≤ delta} := by
  rfl

/-- If the extended-time threshold event is empty, its hitting time is top. -/
theorem distanceThresholdHittingTime_eq_top_of_no_event
    {distance : Real → Real} {delta : Real}
    (hnever : ∀ time : ENNReal,
      ¬ distanceThresholdEvent distance delta time) :
    distanceThresholdHittingTime distance delta = ⊤ := by
  have hevent :
      distanceThresholdEvent distance delta =
        fun _ : ENNReal => False := by
    funext time
    apply propext
    exact ⟨fun h => (hnever time h).elim, False.elim⟩
  rw [distanceThresholdHittingTime, hevent]
  exact HittingTime.firstHittingTime_empty

/-- Uniform closeness on the nonnegative compact time window from zero to T. -/
def UniformlyCloseOnNonnegativeWindow
    (approximation limit : Real → Real) (T error : Real) : Prop :=
  ∀ t, 0 ≤ t → t ≤ T →
    |approximation t - limit t| < error

/-- Locally uniform convergence on every positive compact time window. -/
def LocallyUniformConvergesOnNonnegativeTime
    (approximation : Nat → Real → Real) (limit : Real → Real) : Prop :=
  ∀ T, 0 < T → ∀ error, 0 < error →
    ∀ᶠ n in atTop,
      UniformlyCloseOnNonnegativeWindow (approximation n) limit T error

/-- A finite positive real hit gives a finite ENNReal upper bound. -/
theorem distanceThresholdHittingTime_le_of_hit
    {distance : Real → Real} {delta t : Real}
    (ht_pos : 0 < t) (ht_hit : distance t ≤ delta) :
    distanceThresholdHittingTime distance delta ≤
      (Real.toNNReal t : ENNReal) := by
  apply HittingTime.firstHittingTime_le_of_mem
  change
    0 < (Real.toNNReal t : ENNReal) ∧
      distance (Real.toNNReal t : ENNReal).toReal ≤ delta
  constructor
  · rw [ENNReal.coe_pos]
    exact Real.toNNReal_pos.mpr ht_pos
  · simpa only [ENNReal.coe_toReal,
      Real.coe_toNNReal _ (le_of_lt ht_pos)] using ht_hit

/--
If no positive real event occurs through L, then L is a lower bound for the
extended hitting time.  The top candidate in the defining set is handled
separately, rather than being treated as a finite real time.
-/
theorem coe_toNNReal_le_distanceThresholdHittingTime_of_no_hit_before
    {distance : Real → Real} {delta L : Real}
    (hL_nonneg : 0 ≤ L)
    (hno : ∀ t, 0 < t → t ≤ L → delta < distance t) :
    (Real.toNNReal L : ENNReal) ≤
      distanceThresholdHittingTime distance delta := by
  rw [distanceThresholdHittingTime, HittingTime.firstHittingTime]
  apply le_sInf
  intro time htime
  change
    0 < time ∧ distance time.toReal ≤ delta at htime
  rcases htime with ⟨htime_pos, htime_event⟩
  by_cases htime_top : time = ⊤
  · simp [htime_top]
  · have htime_ne_zero : time ≠ 0 := ne_of_gt htime_pos
    have htime_toReal_pos : 0 < time.toReal :=
      ENNReal.toReal_pos htime_ne_zero htime_top
    apply
      (ENNReal.toReal_le_toReal
        (by simp : (Real.toNNReal L : ENNReal) ≠ ⊤)
        htime_top).mp
    rw [ENNReal.coe_toReal, Real.coe_toNNReal _ hL_nonneg]
    by_contra hnot
    have htime_toReal_lt : time.toReal < L := lt_of_not_ge hnot
    exact (not_lt_of_ge htime_event)
      (hno time.toReal htime_toReal_pos (le_of_lt htime_toReal_lt))

/--
Arbitrary-epsilon deterministic hitting-time stability.

For every epsilon strictly between zero and tauStar, all sufficiently late
approximations have first positive threshold-hit time between
tauStar - epsilon and tauStar + epsilon.  The lower bound uses the compact
pre-crossing margin; the upper bound uses the corrected right-window witness
from RobustKineticFirstCrossing.  Thus post-crossing existence is present as an
explicit hypothesis, not hidden in the conclusion.
-/
theorem deterministic_hitting_stability
    {limit : Real → Real} {approximation : Nat → Real → Real}
    {delta tauStar ε : Real}
    (hcross : RobustKineticFirstCrossing limit delta tauStar)
    (hconverges :
      LocallyUniformConvergesOnNonnegativeTime approximation limit)
    (hε_pos : 0 < ε) (hε_lt : ε < tauStar) :
    ∀ᶠ n in atTop,
      (Real.toNNReal (tauStar - ε) : ENNReal) ≤
          distanceThresholdHittingTime (approximation n) delta ∧
        distanceThresholdHittingTime (approximation n) delta ≤
          (Real.toNNReal (tauStar + ε) : ENNReal) := by
  obtain ⟨beforeMargin, hbeforeMargin_pos, hbefore⟩ :=
    hcross.beforeMargin ε hε_pos hε_lt
  obtain
      ⟨hitTime, afterMargin, hhit_after, hhit_before,
        hafterMargin_pos, hlimit_hit⟩ :=
    hcross.afterMargin ε hε_pos
  have hleft_pos : 0 < tauStar - ε := sub_pos.mpr hε_lt
  have hright_pos : 0 < tauStar + ε := by
    linarith [hcross.tauStar_pos]
  have hclose_before_eventually :=
    hconverges (tauStar - ε) hleft_pos
      beforeMargin hbeforeMargin_pos
  have hclose_after_eventually :=
    hconverges (tauStar + ε) hright_pos
      afterMargin hafterMargin_pos
  filter_upwards
    [hclose_before_eventually, hclose_after_eventually]
      with n hclose_before hclose_after
  have hno_hit_before :
      ∀ t, 0 < t → t ≤ tauStar - ε →
        delta < approximation n t := by
    intro t ht_pos ht_le
    have hlimit_before :=
      hbefore t ht_pos ht_le
    have hclose :=
      hclose_before t (le_of_lt ht_pos) ht_le
    have hlower :=
      neg_abs_le (approximation n t - limit t)
    linarith
  have hhit_pos : 0 < hitTime :=
    lt_trans hcross.tauStar_pos hhit_after
  have hhit_le_right : hitTime ≤ tauStar + ε :=
    le_of_lt hhit_before
  have hclose_hit :=
    hclose_after hitTime (le_of_lt hhit_pos) hhit_le_right
  have hupper :=
    le_abs_self (approximation n hitTime - limit hitTime)
  have happrox_hit : approximation n hitTime ≤ delta := by
    linarith
  constructor
  · exact
      coe_toNNReal_le_distanceThresholdHittingTime_of_no_hit_before
        (le_of_lt hleft_pos) hno_hit_before
  · calc
      distanceThresholdHittingTime (approximation n) delta ≤
          (Real.toNNReal hitTime : ENNReal) :=
        distanceThresholdHittingTime_le_of_hit hhit_pos happrox_hit
      _ ≤ (Real.toNNReal (tauStar + ε) : ENNReal) :=
        ENNReal.coe_le_coe.mpr
          (Real.toNNReal_le_toNNReal hhit_le_right)

end

end ArchonPhysics
