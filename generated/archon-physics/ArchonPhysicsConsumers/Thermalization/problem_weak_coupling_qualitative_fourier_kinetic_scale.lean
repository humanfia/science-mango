import ArchonPhysics.WeakCouplingQualitativeFourierKineticScale

/-! Consumer for fixed-channel qualitative Fourier kinetic scaling. -/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeakCouplingQualitativeFourierKineticScale
open Filter MeasureTheory
open scoped Topology

example (signal : Real -> Complex) (hcontinuous : Continuous signal)
    (hzero : Tendsto signal atTop (𝓝 0)) :
    Tendsto (weakCouplingKineticAccumulation signal)
      (𝓝[>] (0 : Real)) (𝓝 0) :=
  tendsto_weakCouplingKineticAccumulation_of_tendsto_zero_atTop
    signal hcontinuous hzero

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchL1FourierCertificate
      measure mismatch weight) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] (0 : Real)) (𝓝 0) :=
  certificate.tendsto_kineticAccumulation

#print axioms tendsto_weakCouplingKineticTime_nhdsGT_zero_atTop
#print axioms
  tendsto_weakCouplingKineticAccumulation_of_tendsto_zero_atTop
#print axioms tendsto_weightedMismatchOscillatoryIntegral_atTop_zero
#print axioms WeightedMismatchL1FourierCertificate.tendsto_kineticAccumulation

end ArchonPhysicsConsumers.Thermalization
