import ArchonPhysics.WeakCouplingLogarithmicKineticScale

/-!
Consumer and axiom audit for logarithmic mismatch accumulation on the
weak-coupling kinetic time scale.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory
open scoped Topology

noncomputable section

example : Tendsto (fun coupling : Real =>
      coupling ^ 2 * Real.log ((coupling ^ 2)⁻¹))
    (𝓝[>] 0) (𝓝 0) :=
  tendsto_square_mul_log_inv_square_nhdsGT_zero

example (signal : Real -> Complex) (nearCost farCost : Real)
    (hcontinuous : Continuous signal)
    (hnear : forall time, ‖signal time‖ <= nearCost)
    (hfar : forall time, time ≠ 0 ->
      ‖signal time‖ <= farCost / |time|) :
    Tendsto (weakCouplingKineticAccumulation signal)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_weakCouplingKineticAccumulation_nhdsGT_zero
    signal nearCost farCost hcontinuous hnear hfar

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] 0) (𝓝 0) :=
  WeightedMismatchC1L1FourierCertificate.tendsto_kineticAccumulation
    certificate

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] 0) (𝓝 0) :=
  WeightedMismatchCompactIntervalFourierCertificate.tendsto_kineticAccumulation
    certificate

end


#print axioms tendsto_square_mul_log_inv_square_nhdsGT_zero
#print axioms tendsto_square_mul_splitLog_nhdsGT_zero
#print axioms tendsto_weakCouplingKineticAccumulation_nhdsGT_zero
#print axioms WeightedMismatchC1L1FourierCertificate.tendsto_kineticAccumulation
#print axioms tendsto_actualIteratedA2WeightedChannel_kineticAccumulation
#print axioms
  WeightedMismatchCompactIntervalFourierCertificate.tendsto_kineticAccumulation
#print axioms
  tendsto_actualIteratedA2WeightedChannel_compact_kineticAccumulation

end ArchonPhysicsConsumers.Thermalization
