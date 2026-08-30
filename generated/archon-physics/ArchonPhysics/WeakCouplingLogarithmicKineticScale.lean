import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
import ArchonPhysics.WeightedMismatchCompactIntervalFiniteTimeLogBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic Fourier accumulation on the kinetic time scale

A pointwise mismatch expectation bounded near zero and by `D / |time|`
away from zero accumulates only logarithmically.  This module verifies that
the logarithm is harmless after multiplication by the kinetic prefactor:

`g^2 * integral_[0,g^-2] ‖F(t)‖ -> 0` as `g -> 0+`.

The result closes the scalar asymptotic step for every expectation-level A2
channel equipped with the explicit Fourier-density certificate.  It does not
construct that certificate for the nonlinear random-mass mismatch, sum a
growing family of channels, or control recollisions in a full nested history.
-/

namespace ArchonPhysics.WeakCouplingLogarithmicKineticScale

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The elementary logarithmic correction vanishes after kinetic scaling. -/
theorem tendsto_square_mul_log_inv_square_nhdsGT_zero :
    Tendsto (fun coupling : Real =>
      coupling ^ 2 * Real.log ((coupling ^ 2)⁻¹))
      (𝓝[>] 0) (𝓝 0) := by
  have hbase : Tendsto
      (fun coupling : Real => Real.log coupling * coupling ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (tendsto_log_mul_rpow_nhdsGT_zero
        (by norm_num : (0 : Real) < 2))
  have hconstant : Tendsto (fun _coupling : Real => (-2 : Real))
      (𝓝[>] 0) (𝓝 (-2)) := tendsto_const_nhds
  have hscaled : Tendsto
      (fun coupling : Real =>
        (-2 : Real) * (Real.log coupling * coupling ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hconstant.mul hbase
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with coupling hcoupling
  have hcouplingPos : 0 < coupling := hcoupling
  rw [Real.log_inv, Real.log_pow]
  norm_num
  ring

/-- A fixed near-time cost plus a fixed logarithmic cost is negligible after
multiplication by the kinetic prefactor `g^2`. -/
theorem tendsto_square_mul_splitLog_nhdsGT_zero (nearCost farCost : Real) :
    Tendsto
      (fun coupling : Real =>
        coupling ^ 2 *
          (nearCost + farCost * Real.log ((coupling ^ 2)⁻¹)))
      (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun coupling : Real => coupling)
      (𝓝 0) (𝓝 0) := tendsto_id
  have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
  have hsquare : Tendsto (fun coupling : Real => coupling ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hid.pow 2).mono_left hfilter
  have hnearConstant : Tendsto (fun _coupling : Real => nearCost)
      (𝓝[>] 0) (𝓝 nearCost) := tendsto_const_nhds
  have hnear : Tendsto (fun coupling : Real => coupling ^ 2 * nearCost)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hsquare.mul hnearConstant
  have hfarConstant : Tendsto (fun _coupling : Real => farCost)
      (𝓝[>] 0) (𝓝 farCost) := tendsto_const_nhds
  have hfar : Tendsto
      (fun coupling : Real =>
        farCost *
          (coupling ^ 2 * Real.log ((coupling ^ 2)⁻¹)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hfarConstant.mul
      tendsto_square_mul_log_inv_square_nhdsGT_zero
  have hsum : Tendsto
      (fun coupling : Real =>
        coupling ^ 2 * nearCost +
          farCost *
            (coupling ^ 2 * Real.log ((coupling ^ 2)⁻¹)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hnear.add hfar
  apply hsum.congr'
  filter_upwards with coupling
  ring

/-- Standard weak-coupling kinetic time `g^-2`, totalized at `g = 0`. -/
def weakCouplingKineticTime (coupling : Real) : Real :=
  (coupling ^ 2)⁻¹

/-- Kinetically weighted positive-time accumulation of a scalar channel. -/
def weakCouplingKineticAccumulation
    (signal : Real -> Complex) (coupling : Real) : Real :=
  coupling ^ 2 *
    ∫ time in 0..weakCouplingKineticTime coupling, ‖signal time‖

/-- The kinetically weighted accumulation is nonnegative for every coupling. -/
theorem weakCouplingKineticAccumulation_nonneg
    (signal : Real -> Complex) (coupling : Real) :
    0 <= weakCouplingKineticAccumulation signal coupling := by
  unfold weakCouplingKineticAccumulation weakCouplingKineticTime
  have htime : 0 <= (coupling ^ 2)⁻¹ :=
    inv_nonneg.mpr (sq_nonneg coupling)
  exact mul_nonneg (sq_nonneg coupling)
    (intervalIntegral.integral_nonneg htime
      (fun time _htime => norm_nonneg (signal time)))

/-- Abstract kinetic-scale closure for one channel with a uniform ceiling
and `1 / |time|` decay. -/
theorem tendsto_weakCouplingKineticAccumulation_nhdsGT_zero
    (signal : Real -> Complex) (nearCost farCost : Real)
    (hcontinuous : Continuous signal)
    (hnear : forall time, ‖signal time‖ <= nearCost)
    (hfar : forall time, time ≠ 0 ->
      ‖signal time‖ <= farCost / |time|) :
    Tendsto (weakCouplingKineticAccumulation signal)
      (𝓝[>] 0) (𝓝 0) := by
  have hnonneg : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      0 <= weakCouplingKineticAccumulation signal coupling := by
    exact Eventually.of_forall
      (weakCouplingKineticAccumulation_nonneg signal)
  have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
  have hcouplingLtOne : ∀ᶠ coupling in 𝓝[>] (0 : Real), coupling < 1 :=
    hfilter (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
  have hupper : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      weakCouplingKineticAccumulation signal coupling <=
        coupling ^ 2 *
          (nearCost + farCost * Real.log ((coupling ^ 2)⁻¹)) := by
    filter_upwards [self_mem_nhdsWithin, hcouplingLtOne] with
        coupling hcoupling hcouplingOne
    have hcouplingPos : 0 < coupling := hcoupling
    have hsquarePos : 0 < coupling ^ 2 := sq_pos_of_pos hcouplingPos
    have hsquareLeOne : coupling ^ 2 <= 1 := by
      have hproduct : 0 <= coupling * (1 - coupling) :=
        mul_nonneg hcouplingPos.le
          (sub_nonneg.mpr hcouplingOne.le)
      nlinarith
    have htime : 1 <= weakCouplingKineticTime coupling := by
      unfold weakCouplingKineticTime
      exact (one_le_inv_iff₀).2 ⟨hsquarePos, hsquareLeOne⟩
    have hlogBound := intervalIntegral_norm_le_split_log
      signal nearCost farCost 1 (weakCouplingKineticTime coupling)
      hcontinuous hnear hfar one_pos htime
    have hscaled := mul_le_mul_of_nonneg_left hlogBound
      (sq_nonneg coupling)
    simpa [weakCouplingKineticAccumulation, weakCouplingKineticTime] using
      hscaled
  exact squeeze_zero' hnonneg hupper
    (tendsto_square_mul_splitLog_nhdsGT_zero nearCost farCost)

/-! ## Fourier-certificate and actual-A2 adapters -/

/-- Every fixed `C^1 cap W^{1,1}` mismatch certificate makes its individual
expectation channel negligible after kinetic weighting. -/
theorem WeightedMismatchC1L1FourierCertificate.tendsto_kineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_weakCouplingKineticAccumulation_nhdsGT_zero
    (weightedMismatchExpectation measure mismatch weight)
    (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate)
    certificate.derivativeL1Cost
    (WeightedMismatchC1L1FourierCertificate.continuous_expectation certificate)
    (fun time =>
      WeightedMismatchC1L1FourierCertificate.norm_expectation_le_densityL1
        certificate time)
    (fun time htime => certificate.norm_expectation_le_div_abs_time htime)

/-- Actual iterated-A2 specialization.  The conclusion concerns one selected
weighted mismatch channel and retains the explicit density certificate. -/
theorem tendsto_actualIteratedA2WeightedChannel_kineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelC1L1Certificate
      ensemble channel weight observed term) :
    Tendsto
      (weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term))
      (𝓝[>] 0) (𝓝 0) :=
  WeightedMismatchC1L1FourierCertificate.tendsto_kineticAccumulation
    certificate

/-- Endpoint-aware compact-interval certificates give the same kinetic-scale
negligibility without requiring a globally smooth zero extension. -/
theorem
    WeightedMismatchCompactIntervalFourierCertificate.tendsto_kineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_weakCouplingKineticAccumulation_nhdsGT_zero
    (weightedMismatchExpectation measure mismatch weight)
    certificate.densityL1Cost certificate.variationCost
    certificate.continuous_expectation
    certificate.norm_expectation_le_densityL1
    (fun time htime => certificate.norm_expectation_le_div_abs_time htime)

/-- Actual iterated-A2 endpoint-aware specialization.  Its compact mismatch
chart remains an explicit model-specific certificate. -/
theorem tendsto_actualIteratedA2WeightedChannel_compact_kineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel weight observed term) :
    Tendsto
      (weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term))
      (𝓝[>] 0) (𝓝 0) :=
  WeightedMismatchCompactIntervalFourierCertificate.tendsto_kineticAccumulation
    certificate

end

end ArchonPhysics.WeakCouplingLogarithmicKineticScale
