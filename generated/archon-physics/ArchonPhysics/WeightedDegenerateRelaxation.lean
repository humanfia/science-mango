import Mathlib

/-!
# Weighted relaxation with an acoustically degenerate rate

A full-spectrum observable need not have a uniform spectral gap.  If its
modewise relaxation rate is strictly positive almost everywhere and the
initial error is integrable, dominated convergence still makes the weighted
integrated error tend to zero.  Consequently every positive fixed threshold
is crossed at a finite kinetic time.

This is a model-independent analytic lemma.  A concrete collision operator
must still prove that its nonlinear evolution is controlled by such a decay,
that the rate is positive almost everywhere, and that the microscopic
observable converges to it.
-/

namespace ArchonPhysics.WeightedDegenerateRelaxation

open Filter MeasureTheory Set Topology

noncomputable section

variable {Alpha : Type*} [MeasurableSpace Alpha]

/-- Weighted absolute error after `n` units of kinetic time. -/
def weightedDecayIntegrand (rate error : Alpha → Real) (n : Nat)
    (x : Alpha) : Real :=
  |error x| * Real.exp (-(rate x * (n : Real)))

/-- Integrated weighted error. -/
def weightedDecayIntegral (mu : Measure Alpha)
    (rate error : Alpha → Real) (n : Nat) : Real :=
  ∫ x, weightedDecayIntegrand rate error n x ∂mu

omit [MeasurableSpace Alpha] in
/-- A nonnegative rate keeps every decaying factor between zero and one. -/
theorem weightedDecayIntegrand_le_abs
    (rate error : Alpha → Real) (n : Nat) (x : Alpha)
    (hrate : 0 ≤ rate x) :
    ‖weightedDecayIntegrand rate error n x‖ ≤ |error x| := by
  have hexponent : -(rate x * (n : Real)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hrate (Nat.cast_nonneg n))
  have hexp_le : Real.exp (-(rate x * (n : Real))) ≤ 1 :=
    Real.exp_le_one_iff.mpr hexponent
  have hexp_pos : 0 < Real.exp (-(rate x * (n : Real))) := Real.exp_pos _
  rw [weightedDecayIntegrand, Real.norm_eq_abs, abs_mul,
    abs_abs, abs_of_pos hexp_pos]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hexp_le (abs_nonneg (error x))

omit [MeasurableSpace Alpha] in
/-- With a positive modewise rate, the weighted integrand tends pointwise to
zero even when the infimum of the rates is zero. -/
theorem tendsto_weightedDecayIntegrand
    (rate error : Alpha → Real) (x : Alpha) (hrate : 0 < rate x) :
    Tendsto (fun n ↦ weightedDecayIntegrand rate error n x)
      atTop (nhds 0) := by
  have hscale : Tendsto (fun n : Nat ↦ rate x * (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  have hexp : Tendsto
      (fun n : Nat ↦ Real.exp (-(rate x * (n : Real)))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  simpa [weightedDecayIntegrand] using
    (tendsto_const_nhds.mul hexp :
      Tendsto (fun n : Nat ↦ |error x| *
        Real.exp (-(rate x * (n : Real)))) atTop (nhds (|error x| * 0)))

/-- Dominated convergence for a rate which may approach zero but is positive
almost everywhere.  No uniform lower bound on `rate` is assumed. -/
theorem tendsto_weightedDecayIntegral
    (mu : Measure Alpha) (rate error : Alpha → Real)
    (hrate_measurable : Measurable rate)
    (herror_integrable : Integrable error mu)
    (hrate_nonneg : ∀ᵐ x ∂mu, 0 ≤ rate x)
    (hrate_pos : ∀ᵐ x ∂mu, 0 < rate x) :
    Tendsto (weightedDecayIntegral mu rate error) atTop (nhds 0) := by
  have hmeas : ∀ n,
      AEStronglyMeasurable (weightedDecayIntegrand rate error n) mu := by
    intro n
    have herror_abs : AEStronglyMeasurable (fun x ↦ |error x|) mu := by
      simpa only [Real.norm_eq_abs] using
        herror_integrable.aestronglyMeasurable.norm
    exact herror_abs.mul
      ((hrate_measurable.mul_const (n : Real)).neg.exp.aestronglyMeasurable)
  have hbound : ∀ n, ∀ᵐ x ∂mu,
      ‖weightedDecayIntegrand rate error n x‖ ≤ |error x| := by
    intro n
    filter_upwards [hrate_nonneg] with x hx
    exact weightedDecayIntegrand_le_abs rate error n x hx
  have hlimit : ∀ᵐ x ∂mu,
      Tendsto (fun n ↦ weightedDecayIntegrand rate error n x)
        atTop (nhds (0 : Real)) := by
    filter_upwards [hrate_pos] with x hx
    exact tendsto_weightedDecayIntegrand rate error x hx
  change Tendsto
    (fun n ↦ ∫ x, weightedDecayIntegrand rate error n x ∂mu)
    atTop (nhds 0)
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence
      (μ := mu) (F := fun n x ↦ weightedDecayIntegrand rate error n x)
      (f := fun _ ↦ (0 : Real)) (fun x ↦ |error x|)
      hmeas herror_integrable.abs hbound hlimit)

/-- Every positive fixed error threshold is crossed at a finite integer
kinetic time, without a uniform spectral gap. -/
theorem exists_weightedDecayIntegral_lt
    (mu : Measure Alpha) (rate error : Alpha → Real)
    (hrate_measurable : Measurable rate)
    (herror_integrable : Integrable error mu)
    (hrate_nonneg : ∀ᵐ x ∂mu, 0 ≤ rate x)
    (hrate_pos : ∀ᵐ x ∂mu, 0 < rate x)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ n : Nat, weightedDecayIntegral mu rate error n < delta := by
  have htendsto := tendsto_weightedDecayIntegral mu rate error
    hrate_measurable herror_integrable hrate_nonneg hrate_pos
  have heventually : ∀ᶠ n in atTop,
      weightedDecayIntegral mu rate error n ∈ Iio delta :=
    htendsto.eventually (Iio_mem_nhds hdelta)
  exact heventually.exists

end

end ArchonPhysics.WeightedDegenerateRelaxation
