import ArchonPhysics.WeakCouplingLogarithmicKineticScale
import ArchonPhysics.WeightedMismatchFiniteChartKineticClosure

/-!
# External weak-coupling scaling of an actual iterated-A2 channel

In the standard alpha--beta FPUT normalization, `kappa` and `beta` are fixed
coefficients while the perturbative parameter is an external `g`.  The exact
second-Picard extraction supplies `g^2 A2(kappa, beta)`.  Accordingly, this
module holds `kappa` and the initial radius fixed and inserts the external
`g^2` before integrating up to the kinetic time `g^-2`.

This is distinct from varying `kappa` itself.  It closes the scalar
weak-coupling normalization for one iterated-quadratic A2 channel, conditional
on an explicit Fourier-density certificate.  It does not estimate the exact
post-second-Picard remainder.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open ArchonPhysics.WeightedMismatchFiniteChartKineticClosure
open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Time accumulation of the externally scaled physical A2 channel.  The
base alpha coefficient `kappa` is fixed; `g` is the weak-coupling variable. -/
def actualIteratedA2StaticExternalWeakCouplingAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (g : Real) : Real :=
  ∫ time in 0..weakCouplingKineticTime g,
    ‖(((g ^ 2 : Real) : Complex) *
      actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time)‖

/-- Exact identification with the abstract kinetic accumulation.  This is
the correct external-`g` normalization of the extracted `g^2 A2` term. -/
theorem actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (g : Real) :
    actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term g =
      weakCouplingKineticAccumulation
        (actualIteratedA2StaticWeightedChannelExpectation ensemble channel
          kappa radius observed term) g := by
  unfold actualIteratedA2StaticExternalWeakCouplingAccumulation
    weakCouplingKineticAccumulation
  rw [show (fun time =>
      ‖(((g ^ 2 : Real) : Complex) *
        actualIteratedA2StaticWeightedChannelExpectation ensemble channel
          kappa radius observed term time)‖) =
      (fun time => g ^ 2 *
        ‖actualIteratedA2StaticWeightedChannelExpectation ensemble channel
          kappa radius observed term time‖) by
    funext time
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg g)]]
  rw [intervalIntegral.integral_const_mul]

/-- A global smooth density certificate at fixed `kappa` makes the externally
scaled physical A2 accumulation negligible on the `g^-2` window. -/
theorem tendsto_actualIteratedA2StaticExternalWeakCouplingAccumulation_c1
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2StaticWeightedChannelC1L1Certificate
      ensemble channel kappa radius observed term) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term) (𝓝[>] 0) (𝓝 0) := by
  rw [funext fun g =>
    actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble channel kappa radius observed term g]
  exact tendsto_actualIteratedA2WeightedChannel_kineticAccumulation
    ensemble channel
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
      observed term certificate

/-- The endpoint-aware compact certificate gives the same external-`g`
kinetic-window limit. -/
theorem tendsto_actualIteratedA2StaticExternalWeakCouplingAccumulation_compact
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term) (𝓝[>] 0) (𝓝 0) := by
  rw [funext fun g =>
    actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble channel kappa radius observed term g]
  exact tendsto_actualIteratedA2WeightedChannel_compact_kineticAccumulation
    ensemble channel
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
      observed term certificate

/-- A fixed finite monotone atlas gives the same external-`g` conclusion. -/
theorem
    tendsto_actualIteratedA2StaticExternalWeakCouplingAccumulation_finiteChart
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (certificate : ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term ChartIndex) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term) (𝓝[>] 0) (𝓝 0) := by
  rw [funext fun g =>
    actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble channel kappa radius observed term g]
  exact tendsto_actualIteratedA2WeightedChannel_finiteChart_kineticAccumulation
    ensemble channel
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
      observed term ChartIndex certificate

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
