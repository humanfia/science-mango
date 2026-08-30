import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import ArchonPhysics.WeakCouplingLogarithmicKineticScale

/-!
# Qualitative Fourier decay on the weak-coupling kinetic window

The quantitative kinetic closure uses a `1 / |t|` Fourier bound.  At fixed
volume a weaker statement is enough: if a continuous signal tends to zero as
`t -> +infinity`, its continuous Cesaro average on `[0,T]` tends to zero.
With `T = g^-2`, this is exactly the weak-coupling accumulation.

Consequently an `L1` mismatch density already closes every fixed channel by
the Riemann--Lebesgue lemma.  No rate uniform in a growing volume follows.
-/

namespace ArchonPhysics.WeakCouplingQualitativeFourierKineticScale

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open Filter MeasureTheory
open scoped FourierTransform Real RealInnerProductSpace Topology

noncomputable section

/-- The kinetic time tends to infinity as the positive coupling tends to
zero. -/
theorem tendsto_weakCouplingKineticTime_nhdsGT_zero_atTop :
    Tendsto weakCouplingKineticTime (𝓝[>] (0 : Real)) atTop := by
  have hinv : Tendsto (fun g : Real => g⁻¹) (𝓝[>] (0 : Real)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hpow : Tendsto (fun x : Real => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  convert hpow.comp hinv using 1
  funext g
  simp [weakCouplingKineticTime, inv_pow]

/-- Continuous-time Cesaro closure in the variables used by the kinetic
window.  A qualitative pointwise limit at positive infinite time suffices. -/
theorem tendsto_weakCouplingKineticAccumulation_of_tendsto_zero_atTop
    (signal : Real -> Complex) (hcontinuous : Continuous signal)
    (hzero : Tendsto signal atTop (𝓝 0)) :
    Tendsto (weakCouplingKineticAccumulation signal)
      (𝓝[>] (0 : Real)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hnormZero : Tendsto (fun time => ‖signal time‖) atTop (𝓝 0) := by
    simpa using hzero.norm
  have htailEventually : ∀ᶠ time in atTop,
      ‖signal time‖ < epsilon / 2 :=
    hnormZero.eventually (Iio_mem_nhds (half_pos hepsilon))
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp htailEventually
  let cutoff : Real := max threshold 0
  have hcutoffNonneg : 0 <= cutoff := le_max_right _ _
  have htail : forall time, cutoff <= time ->
      ‖signal time‖ <= epsilon / 2 := by
    intro time htime
    exact (hthreshold time ((le_max_left _ _).trans htime)).le
  let nearCost : Real := ∫ time in 0..cutoff, ‖signal time‖
  have hnearCostNonneg : 0 <= nearCost := by
    exact intervalIntegral.integral_nonneg hcutoffNonneg
      (fun time _ => norm_nonneg (signal time))
  have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
  have hsquare : Tendsto (fun g : Real => g ^ 2 * nearCost)
      (𝓝[>] (0 : Real)) (𝓝 0) := by
    have hid : Tendsto (fun g : Real => g) (𝓝 0) (𝓝 0) := tendsto_id
    have hsquareZero : Tendsto (fun g : Real => g ^ 2)
        (𝓝[>] (0 : Real)) (𝓝 0) := by
      simpa using (hid.pow 2).mono_left hfilter
    simpa using hsquareZero.mul_const nearCost
  have hnearSmall : ∀ᶠ g in 𝓝[>] (0 : Real),
      g ^ 2 * nearCost < epsilon / 2 :=
    hsquare.eventually (Iio_mem_nhds (half_pos hepsilon))
  have htimeLarge : ∀ᶠ g in 𝓝[>] (0 : Real),
      cutoff <= weakCouplingKineticTime g :=
    tendsto_weakCouplingKineticTime_nhdsGT_zero_atTop.eventually
      (eventually_ge_atTop cutoff)
  filter_upwards [self_mem_nhdsWithin, hnearSmall, htimeLarge] with
      g hg hnearAt htimeAt
  have hgPos : 0 < g := hg
  have hgNe : g ≠ 0 := hgPos.ne'
  have hnormContinuous : Continuous (fun time => ‖signal time‖) :=
    hcontinuous.norm
  have hnearIntegrable : IntervalIntegrable (fun time => ‖signal time‖)
      volume 0 cutoff := hnormContinuous.intervalIntegrable 0 cutoff
  have hfarIntegrable : IntervalIntegrable (fun time => ‖signal time‖)
      volume cutoff (weakCouplingKineticTime g) :=
    hnormContinuous.intervalIntegrable cutoff (weakCouplingKineticTime g)
  have htailIntegral :
      (∫ time in cutoff..weakCouplingKineticTime g, ‖signal time‖) <=
        (epsilon / 2) * (weakCouplingKineticTime g - cutoff) := by
    calc
      (∫ time in cutoff..weakCouplingKineticTime g, ‖signal time‖) <=
          ∫ _time in cutoff..weakCouplingKineticTime g, epsilon / 2 := by
        exact intervalIntegral.integral_mono_on htimeAt hfarIntegrable
          intervalIntegrable_const (fun time htime => htail time htime.1)
      _ = (epsilon / 2) *
          (weakCouplingKineticTime g - cutoff) := by
        rw [intervalIntegral.integral_const]
        simp [smul_eq_mul, mul_comm]
  have htimeProduct : g ^ 2 * weakCouplingKineticTime g = 1 := by
    unfold weakCouplingKineticTime
    exact mul_inv_cancel₀ (pow_ne_zero 2 hgNe)
  have hscaledLength :
      g ^ 2 * (weakCouplingKineticTime g - cutoff) <= 1 := by
    calc
      g ^ 2 * (weakCouplingKineticTime g - cutoff) <=
          g ^ 2 * weakCouplingKineticTime g :=
        mul_le_mul_of_nonneg_left
          (sub_le_self _ hcutoffNonneg) (sq_nonneg g)
      _ = 1 := htimeProduct
  have hsplit :
      (∫ time in 0..weakCouplingKineticTime g, ‖signal time‖) =
        nearCost +
          ∫ time in cutoff..weakCouplingKineticTime g, ‖signal time‖ := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      hnearIntegrable hfarIntegrable).symm
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (weakCouplingKineticAccumulation_nonneg signal g)]
  unfold weakCouplingKineticAccumulation
  rw [hsplit]
  calc
    g ^ 2 *
        (nearCost +
          ∫ time in cutoff..weakCouplingKineticTime g, ‖signal time‖) <=
      g ^ 2 * (nearCost +
        (epsilon / 2) * (weakCouplingKineticTime g - cutoff)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right htailIntegral nearCost)
        (sq_nonneg g)
    _ = g ^ 2 * nearCost +
        (epsilon / 2) *
          (g ^ 2 * (weakCouplingKineticTime g - cutoff)) := by ring
    _ <= g ^ 2 * nearCost + epsilon / 2 := by
      exact add_le_add_right
        (mul_le_of_le_one_right (half_pos hepsilon).le hscaledLength) _
    _ < epsilon := by linarith

/-! ## L1 Fourier-density certificate -/

/-- A qualitative density certificate: unlike the quantitative certificate,
it assumes no derivative of the mismatch density. -/
structure WeightedMismatchL1FourierCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) where
  density : Real -> Complex
  density_integrable : Integrable density
  expectation_eq : forall time,
    weightedMismatchExpectation measure mismatch weight time =
      weightedMismatchOscillatoryIntegral density time

/-- The physical-convention Fourier oscillation of any `L1` density tends to
zero at positive infinite time. -/
theorem tendsto_weightedMismatchOscillatoryIntegral_atTop_zero
    (density : Real -> Complex) :
    Tendsto (weightedMismatchOscillatoryIntegral density) atTop (𝓝 0) := by
  have hfrequency : Tendsto
      (fun time : Real => -time / (2 * Real.pi)) atTop atBot :=
    tendsto_neg_atTop_atBot.atBot_div_const (by positivity)
  have hfrequencyCocompact : Tendsto
      (fun time : Real => -time / (2 * Real.pi)) atTop (cocompact Real) :=
    hfrequency.mono_right atBot_le_cocompact
  rw [show weightedMismatchOscillatoryIntegral density =
      fun time => 𝓕 density (-time / (2 * Real.pi)) by
    funext time
    exact weightedMismatchOscillatoryIntegral_eq_fourier density time]
  exact (Real.zero_at_infty_fourier density).comp hfrequencyCocompact

theorem WeightedMismatchL1FourierCertificate.continuous_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchL1FourierCertificate
      measure mismatch weight) :
    Continuous (weightedMismatchExpectation measure mismatch weight) := by
  rw [show weightedMismatchExpectation measure mismatch weight =
      weightedMismatchOscillatoryIntegral certificate.density by
    funext time
    exact certificate.expectation_eq time]
  exact continuous_weightedMismatchOscillatoryIntegral certificate.density
    certificate.density_integrable

theorem WeightedMismatchL1FourierCertificate.tendsto_expectation_atTop_zero
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchL1FourierCertificate
      measure mismatch weight) :
    Tendsto (weightedMismatchExpectation measure mismatch weight)
      atTop (𝓝 0) := by
  rw [show weightedMismatchExpectation measure mismatch weight =
      weightedMismatchOscillatoryIntegral certificate.density by
    funext time
    exact certificate.expectation_eq time]
  exact tendsto_weightedMismatchOscillatoryIntegral_atTop_zero
    certificate.density

/-- Every fixed `L1` mismatch-density channel is negligible on the kinetic
window.  This conclusion is qualitative and carries no volume-uniform rate. -/
theorem WeightedMismatchL1FourierCertificate.tendsto_kineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchL1FourierCertificate
      measure mismatch weight) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] (0 : Real)) (𝓝 0) :=
  tendsto_weakCouplingKineticAccumulation_of_tendsto_zero_atTop
    (weightedMismatchExpectation measure mismatch weight)
    certificate.continuous_expectation
    certificate.tendsto_expectation_atTop_zero

end


end ArchonPhysics.WeakCouplingQualitativeFourierKineticScale
