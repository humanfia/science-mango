import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite-time logarithmic accumulation of expectation-level A2 decay

The preceding expectation-level Fourier bridge supplies two pointwise bounds
for a regular weighted mismatch density `rho`:

`‖F(t)‖ <= ‖rho‖_1` and `‖F(t)‖ <= ‖rho'‖_1 / |t|` for `t != 0`.

Splitting a positive time window at `0 < tau <= T` therefore gives the
explicit reusable estimate

`integral_0^T ‖F(t)‖ dt <= ‖rho‖_1 * tau + ‖rho'‖_1 * log (T / tau)`.

This module proves the underlying abstract interval-integral theorem, its
symmetric-window counterpart, and adapters for the actual iterated-A2
weighted mismatch channels and physical static coefficient.  The
`C^1 cap W^{1,1}` fibre-density certificate remains an explicit parameter.
No such certificate is derived here from the iid mass law, and the bounds do
not by themselves close the full nested `A2/A2` remainder.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory Set
open scoped FourierTransform Real RealInnerProductSpace

noncomputable section

/-! ## Abstract split-envelope integration -/

/-- Integrating a uniform bound up to `tau` and a `D / |t|` bound from
`tau` to `T` produces the exact logarithmic envelope. -/
theorem intervalIntegral_norm_le_split_log
    (signal : Real -> Complex) (L D tau T : Real)
    (hcontinuous : Continuous signal)
    (hL : forall time, ‖signal time‖ <= L)
    (hD : forall time, time ≠ 0 -> ‖signal time‖ <= D / |time|)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T, ‖signal time‖) <=
      L * tau + D * Real.log (T / tau) := by
  have hzeroTau : (0 : Real) <= tau := htau.le
  have hT : 0 < T := htau.trans_le htauT
  have hnormContinuous : Continuous (fun time => ‖signal time‖) :=
    hcontinuous.norm
  have hnormZeroTau : IntervalIntegrable
      (fun time => ‖signal time‖) volume 0 tau :=
    hnormContinuous.intervalIntegrable 0 tau
  have hnormTauT : IntervalIntegrable
      (fun time => ‖signal time‖) volume tau T :=
    hnormContinuous.intervalIntegrable tau T
  have hnear :
      (∫ time : Real in 0..tau, ‖signal time‖) <=
        ∫ _time : Real in 0..tau, L := by
    exact intervalIntegral.integral_mono_on hzeroTau hnormZeroTau
      intervalIntegrable_const (fun time _ => hL time)
  have hfarContinuous : ContinuousOn (fun time : Real => D / time)
      (Icc tau T) := by
    intro time htime
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (htau.trans_le htime.1)) |>.continuousWithinAt
  have hfarIntegrable : IntervalIntegrable (fun time : Real => D / time)
      volume tau T :=
    hfarContinuous.intervalIntegrable_of_Icc htauT
  have hfar :
      (∫ time : Real in tau..T, ‖signal time‖) <=
        ∫ time : Real in tau..T, D / time := by
    apply intervalIntegral.integral_mono_on htauT hnormTauT hfarIntegrable
    intro time htime
    have htimePos : 0 < time := htau.trans_le htime.1
    simpa only [abs_of_pos htimePos] using hD time htimePos.ne'
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hnormZeroTau hnormTauT]
  calc
    (∫ time : Real in 0..tau, ‖signal time‖) +
        ∫ time : Real in tau..T, ‖signal time‖ <=
      (∫ _time : Real in 0..tau, L) +
        ∫ time : Real in tau..T, D / time :=
      add_le_add hnear hfar
    _ = L * tau + D * Real.log (T / tau) := by
      rw [intervalIntegral.integral_const, sub_zero]
      simp only [smul_eq_mul, div_eq_mul_inv,
        intervalIntegral.integral_const_mul,
        integral_inv_of_pos htau hT]
      ring

/-- Applying the same split separately to positive and negative times gives
the corresponding symmetric-window estimate. -/
theorem intervalIntegral_norm_symmetric_le_two_mul_split_log
    (signal : Real -> Complex) (L D tau T : Real)
    (hcontinuous : Continuous signal)
    (hL : forall time, ‖signal time‖ <= L)
    (hD : forall time, time ≠ 0 -> ‖signal time‖ <= D / |time|)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T, ‖signal time‖) <=
      2 * (L * tau + D * Real.log (T / tau)) := by
  let reflected : Real -> Complex := fun time => signal (-time)
  have hreflectedContinuous : Continuous reflected :=
    hcontinuous.comp continuous_neg
  have hreflectedL : forall time, ‖reflected time‖ <= L :=
    fun time => hL (-time)
  have hreflectedD : forall time, time ≠ 0 ->
      ‖reflected time‖ <= D / |time| := by
    intro time htime
    simpa only [reflected, abs_neg] using hD (-time) (neg_ne_zero.mpr htime)
  have hpositive := intervalIntegral_norm_le_split_log
    signal L D tau T hcontinuous hL hD htau htauT
  have hnegative := intervalIntegral_norm_le_split_log
    reflected L D tau T hreflectedContinuous hreflectedL hreflectedD
      htau htauT
  have hnormContinuous : Continuous (fun time => ‖signal time‖) :=
    hcontinuous.norm
  have hnormNegative : IntervalIntegrable
      (fun time => ‖signal time‖) volume (-T) 0 :=
    hnormContinuous.intervalIntegrable (-T) 0
  have hnormPositive : IntervalIntegrable
      (fun time => ‖signal time‖) volume 0 T :=
    hnormContinuous.intervalIntegrable 0 T
  have hreflection :
      (∫ time : Real in 0..T, ‖reflected time‖) =
        ∫ time : Real in (-T)..0, ‖signal time‖ := by
    simpa only [reflected, neg_zero] using
      (intervalIntegral.integral_comp_neg
        (fun time : Real => ‖signal time‖) (a := 0) (b := T))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    hnormNegative hnormPositive, ← hreflection]
  linarith

/-! ## Density-certificate costs and pointwise minimum -/

/-- The nonoscillatory `L1` cost of the represented fibre density. -/
def WeightedMismatchC1L1FourierCertificate.densityL1Cost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) : Real :=
  ∫ value : Real, ‖certificate.density value‖

theorem WeightedMismatchC1L1FourierCertificate.densityL1Cost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) :
    0 <= WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate := by
  exact integral_nonneg fun _ => norm_nonneg _

/-- Every represented expectation has the uniform density-`L1` ceiling. -/
theorem WeightedMismatchC1L1FourierCertificate.norm_expectation_le_densityL1
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) (time : Real) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate := by
  rw [certificate.expectation_eq]
  exact norm_weightedMismatchOscillatoryIntegral_le_densityL1
    certificate.density time

/-- Away from zero the two estimates combine into their pointwise minimum. -/
theorem WeightedMismatchC1L1FourierCertificate.norm_expectation_le_min
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      min (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate)
        (certificate.derivativeL1Cost / |time|) := by
  exact le_min
    (WeightedMismatchC1L1FourierCertificate.norm_expectation_le_densityL1
      certificate time)
    (certificate.norm_expectation_le_div_abs_time htime)

/-! ## Continuity and finite-window certificate adapters -/

/-- An integrable density has a continuous physical-convention Fourier
oscillation. -/
theorem continuous_weightedMismatchOscillatoryIntegral
    (density : Real -> Complex) (hdensity : Integrable density) :
    Continuous (weightedMismatchOscillatoryIntegral density) := by
  have hfourier : Continuous (𝓕 density) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL Real).continuous₂ hdensity
  have heq : weightedMismatchOscillatoryIntegral density =
      fun time => 𝓕 density (-time / (2 * Real.pi)) := by
    funext time
    exact weightedMismatchOscillatoryIntegral_eq_fourier density time
  rw [heq]
  exact hfourier.comp (by fun_prop)

/-- The expectation signal represented by the certificate is continuous. -/
theorem WeightedMismatchC1L1FourierCertificate.continuous_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) :
    Continuous
      (weightedMismatchExpectation measure mismatch weight) := by
  have heq : weightedMismatchExpectation measure mismatch weight =
      weightedMismatchOscillatoryIntegral certificate.density := by
    funext time
    exact certificate.expectation_eq time
  rw [heq]
  exact continuous_weightedMismatchOscillatoryIntegral
    certificate.density certificate.density_integrable

/-- Direct finite-positive-window consequence of one regular density
certificate. -/
theorem WeightedMismatchC1L1FourierCertificate.intervalIntegral_norm_expectation_le_split_log
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate * tau +
        certificate.derivativeL1Cost * Real.log (T / tau) := by
  exact intervalIntegral_norm_le_split_log
    (weightedMismatchExpectation measure mismatch weight)
    (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate)
      certificate.derivativeL1Cost tau T
    (WeightedMismatchC1L1FourierCertificate.continuous_expectation certificate)
    (WeightedMismatchC1L1FourierCertificate.norm_expectation_le_densityL1 certificate)
    (fun time htime => certificate.norm_expectation_le_div_abs_time htime)
    htau htauT

/-- Symmetric-window consequence of the same certificate. -/
theorem WeightedMismatchC1L1FourierCertificate.intervalIntegral_norm_expectation_symmetric_le
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      2 * (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate * tau +
        certificate.derivativeL1Cost * Real.log (T / tau)) := by
  exact intervalIntegral_norm_symmetric_le_two_mul_split_log
    (weightedMismatchExpectation measure mismatch weight)
    (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate)
      certificate.derivativeL1Cost tau T
    (WeightedMismatchC1L1FourierCertificate.continuous_expectation certificate)
    (WeightedMismatchC1L1FourierCertificate.norm_expectation_le_densityL1 certificate)
    (fun time htime => certificate.norm_expectation_le_div_abs_time htime)
    htau htauT

/-! ## Actual iterated-A2 adapters -/

/-- The actual weighted A2 channel inherits the logarithmic finite-window
bound once its explicit fibre-density certificate is supplied. -/
theorem intervalIntegral_norm_actualIteratedA2WeightedChannelExpectation_le_split_log
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelC1L1Certificate
      ensemble channel weight observed term)
    (tau T : Real) (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T,
        ‖actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term time‖) <=
      WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate * tau +
        certificate.derivativeL1Cost * Real.log (T / tau) := by
  exact
    WeightedMismatchC1L1FourierCertificate.intervalIntegral_norm_expectation_le_split_log
      certificate tau T htau htauT

/-- Symmetric-window actual weighted-channel adapter. -/
theorem intervalIntegral_norm_actualIteratedA2WeightedChannelExpectation_symmetric_le
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelC1L1Certificate
      ensemble channel weight observed term)
    (tau T : Real) (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T,
        ‖actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term time‖) <=
      2 * (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate * tau +
        certificate.derivativeL1Cost * Real.log (T / tau)) := by
  exact
    WeightedMismatchC1L1FourierCertificate.intervalIntegral_norm_expectation_symmetric_le
      certificate tau T htau htauT

/-- Physical static-coefficient specialization of the positive-window
logarithmic bound. -/
theorem intervalIntegral_norm_actualIteratedA2StaticWeightedChannelExpectation_le_split_log
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2StaticWeightedChannelC1L1Certificate
      ensemble channel kappa radius observed term)
    (tau T : Real) (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T,
        ‖actualIteratedA2StaticWeightedChannelExpectation ensemble channel
          kappa radius observed term time‖) <=
      WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate * tau +
        certificate.derivativeL1Cost * Real.log (T / tau) := by
  exact
    WeightedMismatchC1L1FourierCertificate.intervalIntegral_norm_expectation_le_split_log
      certificate tau T htau htauT

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
