import Mathlib.Analysis.Calculus.Deriv.MeanValue
import ArchonPhysics.MinimalTwoTimeKineticHittingWindow

/-!
# A strict kinetic hit from bounded entropy and threshold dissipation

For the two-sided release law, asymptotic relaxation is unnecessary.  If a
Lyapunov entropy is bounded above and its production has a positive lower
bound whenever the observable remains above the chosen threshold, the
observable must cross that threshold in finite positive time.  Otherwise the
entropy would grow linearly past its ceiling.
-/

namespace ArchonPhysics.BoundedEntropyDissipationStrictHit

open Set
open ArchonPhysics.MinimalTwoTimeKineticHittingWindow
open ArchonPhysics.TwoTimeKineticHittingBounds

noncomputable section

/-- A bounded entropy with threshold-level positive production forces one
finite strict hit.  No convergence or global coercivity inequality is used. -/
theorem exists_strict_hit
    (distance entropy production : Real -> Real)
    (delta kappa entropyCeiling : Real)
    (hkappa : 0 < kappa)
    (hinitial : delta <= distance 0)
    (hentropy_deriv : forall t, 0 <= t ->
      HasDerivAt entropy (production t) t)
    (hproduction : forall t, 0 <= t -> delta <= distance t ->
      kappa <= production t)
    (hentropy_upper : forall t, 0 <= t -> entropy t <= entropyCeiling) :
    exists t : Real, 0 < t /\ distance t < delta := by
  by_contra hno
  have hdistance : forall t : Real, 0 <= t -> delta <= distance t := by
    intro t ht
    rcases ht.eq_or_lt with hzero | hpositive
    · simpa [hzero] using hinitial
    · exact le_of_not_gt fun hlt => hno ⟨t, hpositive, hlt⟩
  let T : Real := max 1 ((entropyCeiling - entropy 0) / kappa + 1)
  have hT_pos : 0 < T :=
    zero_lt_one.trans_le (le_max_left 1
      ((entropyCeiling - entropy 0) / kappa + 1))
  have hcontinuous : ContinuousOn entropy (Icc 0 T) := by
    intro t ht
    exact (hentropy_deriv t ht.1).continuousAt.continuousWithinAt
  have hdifferentiable :
      DifferentiableOn Real entropy (interior (Icc 0 T)) := by
    intro t ht
    exact (hentropy_deriv t (interior_subset ht).1).differentiableAt
      |>.differentiableWithinAt
  have hderiv_lower : forall t, t ∈ interior (Icc 0 T) ->
      kappa <= deriv entropy t := by
    intro t ht
    have ht_nonnegative : 0 <= t := (interior_subset ht).1
    rw [(hentropy_deriv t ht_nonnegative).deriv]
    exact hproduction t ht_nonnegative (hdistance t ht_nonnegative)
  have hgrowth : kappa * T <= entropy T - entropy 0 := by
    simpa only [sub_zero] using
      Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 T)
        hcontinuous hdifferentiable hderiv_lower
        0 (left_mem_Icc.mpr hT_pos.le)
        T (right_mem_Icc.mpr hT_pos.le) hT_pos.le
  have hT_lower :
      (entropyCeiling - entropy 0) / kappa + 1 <= T :=
    le_max_right 1 ((entropyCeiling - entropy 0) / kappa + 1)
  have hscaled_lower :
      kappa * ((entropyCeiling - entropy 0) / kappa + 1) <=
        kappa * T :=
    mul_le_mul_of_nonneg_left hT_lower hkappa.le
  have hstrict_growth : entropyCeiling - entropy 0 < kappa * T := by
    calc
      entropyCeiling - entropy 0 <
          entropyCeiling - entropy 0 + kappa := by linarith
      _ = kappa * ((entropyCeiling - entropy 0) / kappa + 1) := by
        field_simp [ne_of_gt hkappa]
      _ <= kappa * T := hscaled_lower
  have hgap_upper :
      entropy T - entropy 0 <= entropyCeiling - entropy 0 :=
    sub_le_sub_right (hentropy_upper T hT_pos.le) (entropy 0)
  exact (not_lt_of_ge (hgrowth.trans hgap_upper)) hstrict_growth

/-- Adding strict initial separation and continuity at zero turns the entropy
hit into the robust lower/upper window used by the release theorem. -/
theorem exists_robustKineticHittingWindow
    (distance entropy production : Real -> Real)
    (delta kappa entropyCeiling : Real)
    (hkappa : 0 < kappa)
    (hinitial : delta < distance 0)
    (hcontinuous : ContinuousAt distance 0)
    (hentropy_deriv : forall t, 0 <= t ->
      HasDerivAt entropy (production t) t)
    (hproduction : forall t, 0 <= t -> delta <= distance t ->
      kappa <= production t)
    (hentropy_upper : forall t, 0 <= t -> entropy t <= entropyCeiling) :
    exists lower upper : Real,
      RobustKineticHittingWindow distance delta lower upper := by
  obtain ⟨hitTime, hitTime_pos, strict_hit⟩ :=
    exists_strict_hit distance entropy production delta kappa entropyCeiling
      hkappa hinitial.le hentropy_deriv hproduction hentropy_upper
  exact ({
    hitTime := hitTime
    hitTime_pos := hitTime_pos
    threshold_below_initial := hinitial
    continuousAt_zero := hcontinuous
    strict_hit := strict_hit } :
      InitialSeparationAndStrictHit distance delta)
    |>.exists_robustKineticHittingWindow

end

end ArchonPhysics.BoundedEntropyDissipationStrictHit
