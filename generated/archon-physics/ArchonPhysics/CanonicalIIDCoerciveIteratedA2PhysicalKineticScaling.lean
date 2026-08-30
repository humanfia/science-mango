import ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling
import ArchonPhysics.WeakCouplingLogarithmicKineticScale
import ArchonPhysics.WeightedMismatchFiniteChartKineticClosure

/-!
# Effective quadratic-coupling scaling of an actual iterated-A2 channel

The actual quadratic second-Picard coefficient already contains two powers
of the effective quadratic coupling.  Consequently its unweighted time accumulation on
the kinetic window `0 <= t <= g^-2` is exactly the abstract kinetically
weighted accumulation of the unit-coupling channel.

This distinction prevents inserting a second, spurious `g^2` prefactor.  The
limit below is conditional only on an explicit Fourier-density certificate
for the unit-coupling static weight; the coupling square itself is derived
directly from the Hamiltonian coefficients.

Here the variable sent to zero is `kappa` itself, equivalently the effective
quadratic coupling in the pure iterated-quadratic sector.  In the standard
alpha--beta convention, `kappa` is fixed and an external perturbative `g`
supplies the factor `g^2`; that distinct normalization is implemented in
`CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling`.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalKineticScaling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open ArchonPhysics.WeightedMismatchFiniteChartKineticClosure
open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The physical time accumulation has no additional external prefactor:
the two powers of `coupling` are already present in the A2 coefficient. -/
def actualIteratedA2StaticPhysicalKineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (coupling : Real) : Real :=
  ∫ time in 0..weakCouplingKineticTime coupling,
    ‖actualIteratedA2StaticWeightedChannelExpectation ensemble channel
      coupling radius observed term time‖

/-- Exact identification of the physical A2 accumulation with the abstract
kinetic accumulation of its unit-coupling expectation. -/
theorem actualIteratedA2StaticPhysicalKineticAccumulation_eq_unit
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (coupling : Real) :
    actualIteratedA2StaticPhysicalKineticAccumulation ensemble channel radius
        observed term coupling =
      weakCouplingKineticAccumulation
        (actualIteratedA2StaticWeightedChannelExpectation ensemble channel 1
          radius observed term) coupling := by
  unfold actualIteratedA2StaticPhysicalKineticAccumulation
    weakCouplingKineticAccumulation
  rw [show (fun time =>
      ‖actualIteratedA2StaticWeightedChannelExpectation ensemble channel
        coupling radius observed term time‖) =
      (fun time => coupling ^ 2 *
        ‖actualIteratedA2StaticWeightedChannelExpectation ensemble channel 1
          radius observed term time‖) by
    funext time
    rw [
      actualIteratedA2StaticWeightedChannelExpectation_eq_coupling_sq_mul_unit,
      norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]]
  rw [intervalIntegral.integral_const_mul]

/-- A global `C^1 cap W^{1,1}` unit-coupling density certificate makes the
physical A2 kinetic-window accumulation vanish as the coupling tends to zero. -/
theorem tendsto_actualIteratedA2StaticPhysicalKineticAccumulation_c1
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2StaticWeightedChannelC1L1Certificate
      ensemble channel 1 radius observed term) :
    Tendsto
      (actualIteratedA2StaticPhysicalKineticAccumulation ensemble channel
        radius observed term) (𝓝[>] 0) (𝓝 0) := by
  rw [funext fun coupling =>
    actualIteratedA2StaticPhysicalKineticAccumulation_eq_unit
      ensemble channel radius observed term coupling]
  exact tendsto_actualIteratedA2WeightedChannel_kineticAccumulation
    ensemble channel
      (actualIteratedA2StaticWeightSample ensemble 1 radius observed term)
      observed term certificate

/-- The endpoint-aware compact-interval certificate gives the same physical
kinetic-window limit. -/
theorem tendsto_actualIteratedA2StaticPhysicalKineticAccumulation_compact
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble 1 radius observed term)
        observed term) :
    Tendsto
      (actualIteratedA2StaticPhysicalKineticAccumulation ensemble channel
        radius observed term) (𝓝[>] 0) (𝓝 0) := by
  rw [funext fun coupling =>
    actualIteratedA2StaticPhysicalKineticAccumulation_eq_unit
      ensemble channel radius observed term coupling]
  exact tendsto_actualIteratedA2WeightedChannel_compact_kineticAccumulation
    ensemble channel
      (actualIteratedA2StaticWeightSample ensemble 1 radius observed term)
      observed term certificate

/-- A fixed finite monotone atlas for the unit-coupling mismatch law also
closes the physical A2 kinetic-window limit. -/
theorem tendsto_actualIteratedA2StaticPhysicalKineticAccumulation_finiteChart
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (certificate : ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble 1 radius observed term)
        observed term ChartIndex) :
    Tendsto
      (actualIteratedA2StaticPhysicalKineticAccumulation ensemble channel
        radius observed term) (𝓝[>] 0) (𝓝 0) := by
  rw [funext fun coupling =>
    actualIteratedA2StaticPhysicalKineticAccumulation_eq_unit
      ensemble channel radius observed term coupling]
  exact tendsto_actualIteratedA2WeightedChannel_finiteChart_kineticAccumulation
    ensemble channel
      (actualIteratedA2StaticWeightSample ensemble 1 radius observed term)
      observed term ChartIndex certificate

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalKineticScaling
