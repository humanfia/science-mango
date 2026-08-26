import Mathlib

/-!
# Quantitative thermodynamic relaxation

This module isolates the transparent estimate used to pass from a kinetic
relaxation law to a thermodynamic error tolerance. It does not derive the
estimate from a microscopic lattice. The finite-size remainder, kinetic rate,
and exponential envelope remain explicit inputs.

For an error bounded by

`C * exp (-(kappa * g^2 * t)) + r`,

the settling time below `eta` is

`(kappa * g^2)⁻¹ * log (C / (eta - r))`.

The hypotheses `r < eta` and `eta - r <= C` make this time nonnegative, so
no truncation by `max 0` is needed. A vanishing-tolerance schedule is also
provided for thermodynamic sequences.
-/

namespace ArchonPhysics.QuantitativeThermodynamicRelaxation

open Filter Topology

noncomputable section

/-- Quantitative time needed for an exponential envelope with remainder `r`
to fall below the tolerance `eta`. -/
def exponentialSettlingBound
    (C kappa g r eta : Real) : Real :=
  (kappa * g ^ 2)⁻¹ * Real.log (C / (eta - r))

/-- Under the admissible parameter inequalities, the settling bound is a
nonnegative physical time. -/
theorem exponentialSettlingBound_nonnegative
    {C kappa g r eta : Real}
    (hkappa : 0 < kappa) (hg : g ≠ 0)
    (hremainder : r < eta) (htolerance : eta - r ≤ C) :
    0 ≤ exponentialSettlingBound C kappa g r eta := by
  have hgap : 0 < eta - r := sub_pos.mpr hremainder
  have hrate : 0 < kappa * g ^ 2 :=
    mul_pos hkappa (sq_pos_of_ne_zero hg)
  have hratio : 1 ≤ C / (eta - r) :=
    (le_div_iff₀ hgap).mpr (by simpa only [one_mul] using htolerance)
  exact mul_nonneg (inv_nonneg.mpr hrate.le) (Real.log_nonneg hratio)

/-- Every time after the explicit settling bound has error at most `eta`,
provided the stated exponential tail bound holds. -/
theorem error_le_of_exponential_tail_of_settlingBound_le
    (Delta : Real → Real)
    {C kappa g r eta t : Real}
    (hC : 0 < C) (hkappa : 0 < kappa) (hg : g ≠ 0)
    (hremainder : r < eta) (htolerance : eta - r ≤ C)
    (htail : ∀ s, 0 ≤ s →
      Delta s ≤ C * Real.exp (-(kappa * g ^ 2 * s)) + r)
    (ht : exponentialSettlingBound C kappa g r eta ≤ t) :
    Delta t ≤ eta := by
  let rate : Real := kappa * g ^ 2
  let gap : Real := eta - r
  have hgap : 0 < gap := by
    simpa only [gap] using sub_pos.mpr hremainder
  have hrate : 0 < rate := by
    simpa only [rate] using mul_pos hkappa (sq_pos_of_ne_zero hg)
  have hbound_nonneg :
      0 ≤ exponentialSettlingBound C kappa g r eta :=
    exponentialSettlingBound_nonnegative hkappa hg hremainder htolerance
  have ht_nonneg : 0 ≤ t := hbound_nonneg.trans ht
  have hlog_le : Real.log (C / gap) ≤ rate * t := by
    have hscaled := mul_le_mul_of_nonneg_left ht hrate.le
    rw [exponentialSettlingBound] at hscaled
    change rate * (rate⁻¹ * Real.log (C / gap)) ≤ rate * t at hscaled
    simpa [ne_of_gt hrate] using hscaled
  have hratio_pos : 0 < C / gap := div_pos hC hgap
  have hexp_le :
      Real.exp (-(rate * t)) ≤ gap / C := by
    calc
      Real.exp (-(rate * t)) ≤
          Real.exp (-Real.log (C / gap)) :=
        Real.exp_le_exp.mpr (neg_le_neg hlog_le)
      _ = (C / gap)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hratio_pos]
      _ = gap / C := by
        field_simp
  have hdecay_le : C * Real.exp (-(rate * t)) ≤ gap := by
    calc
      C * Real.exp (-(rate * t)) ≤ C * (gap / C) :=
        mul_le_mul_of_nonneg_left hexp_le hC.le
      _ = gap := by field_simp
  have htail_t := htail t ht_nonneg
  change Delta t ≤ C * Real.exp (-(rate * t)) + r at htail_t
  simp only [gap] at hdecay_le
  linarith

/-- Exact `g²` scaling of the settling bound at fixed envelope, rate
coefficient, remainder, and tolerance. -/
theorem g_sq_mul_exponentialSettlingBound
    {C kappa g r eta : Real}
    (hkappa : kappa ≠ 0) (hg : g ≠ 0) :
    g ^ 2 * exponentialSettlingBound C kappa g r eta =
      kappa⁻¹ * Real.log (C / (eta - r)) := by
  unfold exponentialSettlingBound
  field_simp

/-- A thermodynamic error schedule: the finite-size remainder and requested
tolerance both vanish, while the tolerance eventually strictly exceeds the
remainder. -/
def IsVanishingToleranceSchedule
    (remainder tolerance : Nat → Real) : Prop :=
  Tendsto remainder atTop (nhds 0) ∧
    Tendsto tolerance atTop (nhds 0) ∧
      ∀ᶠ N in atTop, remainder N < tolerance N

/-- Projection of remainder convergence from a vanishing schedule. -/
theorem IsVanishingToleranceSchedule.remainder_tendsto
    {remainder tolerance : Nat → Real}
    (h : IsVanishingToleranceSchedule remainder tolerance) :
    Tendsto remainder atTop (nhds 0) :=
  h.1

/-- Projection of tolerance convergence from a vanishing schedule. -/
theorem IsVanishingToleranceSchedule.tolerance_tendsto
    {remainder tolerance : Nat → Real}
    (h : IsVanishingToleranceSchedule remainder tolerance) :
    Tendsto tolerance atTop (nhds 0) :=
  h.2.1

/-- Projection of eventual strict separation from a vanishing schedule. -/
theorem IsVanishingToleranceSchedule.eventually_remainder_lt_tolerance
    {remainder tolerance : Nat → Real}
    (h : IsVanishingToleranceSchedule remainder tolerance) :
    ∀ᶠ N in atTop, remainder N < tolerance N :=
  h.2.2

/-- Independent squeeze bridge: a nonnegative error sampled along any
late-time thermodynamic path tends to zero when it is eventually bounded by a
vanishing tolerance. The schedule records separately that the finite-size
remainder also vanishes and eventually fits below that tolerance. -/
theorem tendsto_error_zero_of_vanishingToleranceSchedule
    {remainder tolerance error : Nat → Real}
    (hschedule : IsVanishingToleranceSchedule remainder tolerance)
    (herror_nonnegative : ∀ N, 0 ≤ error N)
    (herror_le : ∀ᶠ N in atTop, error N ≤ tolerance N) :
    Tendsto error atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hschedule.tolerance_tendsto
  · exact Filter.Eventually.of_forall herror_nonnegative
  · exact herror_le

/-- A direct thermodynamic-path endpoint. At every finite size the error has
the same exponential kinetic envelope with a size-dependent remainder. If the
observation time is eventually later than the corresponding settling bound,
then the sampled error tends to zero along any vanishing-tolerance schedule.
-/
theorem tendsto_error_zero_along_settlingPath
    (Delta : Nat → Real → Real)
    (remainder tolerance time : Nat → Real)
    {C kappa g : Real}
    (hC : 0 < C) (hkappa : 0 < kappa) (hg : g ≠ 0)
    (hschedule : IsVanishingToleranceSchedule remainder tolerance)
    (htolerance : ∀ᶠ N in atTop,
      tolerance N - remainder N ≤ C)
    (htail : ∀ N s, 0 ≤ s →
      Delta N s ≤
        C * Real.exp (-(kappa * g ^ 2 * s)) + remainder N)
    (htime : ∀ᶠ N in atTop,
      exponentialSettlingBound C kappa g
        (remainder N) (tolerance N) ≤ time N)
    (herror_nonnegative : ∀ N, 0 ≤ Delta N (time N)) :
    Tendsto (fun N ↦ Delta N (time N)) atTop (nhds 0) := by
  apply tendsto_error_zero_of_vanishingToleranceSchedule
      hschedule herror_nonnegative
  filter_upwards
      [hschedule.eventually_remainder_lt_tolerance, htolerance, htime]
      with N hremainder_N htolerance_N htime_N
  exact error_le_of_exponential_tail_of_settlingBound_le
    (Delta N) hC hkappa hg hremainder_N htolerance_N (htail N) htime_N

end

end ArchonPhysics.QuantitativeThermodynamicRelaxation
