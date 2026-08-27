import ArchonPhysics.ResonanceWeightSinc

/-!
# Uniform decay away from the resonance surface

The sinc-squared resonance profile converges uniformly to zero on every
closed set whose phase mismatch stays a fixed positive distance from zero.
This is the far-from-resonance half of an approximate-delta argument.

No assertion is made about the shrinking near-resonant region or total kernel
mass.
-/

namespace ArchonPhysics.UniformOffResonanceDecay

open ArchonPhysics.FiniteTimeResonanceWeight
open Filter

noncomputable section

/-- Uniform inverse-threshold bound with a non-strict gap hypothesis. -/
theorem finiteTimeResonanceWeight_le_inverseThreshold
    {Omega T delta : Real} (hT : 0 < T) (hdelta : 0 < delta)
    (hgap : delta ≤ |Omega|) :
    finiteTimeResonanceWeight Omega T ≤ (2 / delta) ^ 2 / T := by
  have hOmega : Omega ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hgap
    exact (not_lt_of_ge hgap) hdelta
  have hquotient : 2 / |Omega| ≤ 2 / delta :=
    div_le_div_of_nonneg_left (by norm_num) hdelta hgap
  have hsquare : (2 / |Omega|) ^ 2 ≤ (2 / delta) ^ 2 := by
    exact (sq_le_sq₀
      (div_nonneg (by norm_num) (abs_nonneg Omega))
      (div_nonneg (by norm_num) hdelta.le)).2 hquotient
  exact (finiteTimeResonanceWeight_le_inverse_gap hOmega hT).trans
    (div_le_div_of_nonneg_right hsquare hT.le)

/-- Along integer observation times, the resonance profile tends uniformly
to zero on `{Omega | delta ≤ |Omega|}` for every `delta > 0`. -/
theorem tendstoUniformlyOn_finiteTimeResonanceWeight_nat_off_gap
    {delta : Real} (hdelta : 0 < delta) :
    TendstoUniformlyOn
      (fun n : Nat ↦ fun Omega : Real ↦
        finiteTimeResonanceWeight Omega (n + 1))
      (fun _Omega : Real ↦ 0) atTop {Omega | delta ≤ |Omega|} := by
  have hconstant : Tendsto
      (fun _n : Nat ↦ ((2 / delta) ^ 2 : Real)) atTop
      (nhds ((2 / delta) ^ 2)) := tendsto_const_nhds
  have hinverse :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)
  have hbound : Tendsto
      (fun n : Nat ↦ (2 / delta) ^ 2 / ((n : Real) + 1))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
      hconstant.mul hinverse
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have heventually : ∀ᶠ n : Nat in atTop,
      (2 / delta) ^ 2 / ((n : Real) + 1) < epsilon := by
    filter_upwards [(Metric.tendsto_nhds.mp hbound) epsilon hepsilon] with n hn
    have hnonneg : 0 ≤ (2 / delta) ^ 2 / ((n : Real) + 1) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hn
    exact hn
  filter_upwards [heventually] with n hn
  intro Omega hOmega
  rw [Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg (finiteTimeResonanceWeight_nonneg Omega (n + 1))]
  exact (finiteTimeResonanceWeight_le_inverseThreshold
    (by positivity) hdelta hOmega).trans_lt hn

end

end ArchonPhysics.UniformOffResonanceDecay
