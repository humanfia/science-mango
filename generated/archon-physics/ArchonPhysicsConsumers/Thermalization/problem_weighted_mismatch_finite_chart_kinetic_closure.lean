import ArchonPhysics.WeightedMismatchFiniteChartKineticClosure

/-!
Consumer and axiom audit for fixed finite compact-chart atlas decay and
kinetic-scale closure.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchFiniteChartKineticClosure
open Filter MeasureTheory
open scoped Topology

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) (time : Real) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.densityL1Cost :=
  certificate.norm_expectation_le_densityL1 time

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.variationCost / |time| :=
  certificate.norm_expectation_le_variation_div_abs_time htime

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] 0) (𝓝 0) :=
  certificate.tendsto_kineticAccumulation

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (certificate : ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel weight observed term ChartIndex) :
    Tendsto
      (weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_actualIteratedA2WeightedChannel_finiteChart_kineticAccumulation
    ensemble channel weight observed term ChartIndex certificate

end

#print axioms CompactMismatchFourierChart.norm_oscillation_le_densityL1Cost
#print axioms
  CompactMismatchFourierChart.norm_oscillation_le_variation_div_abs_time
#print axioms
  WeightedMismatchFiniteChartFourierCertificate.norm_expectation_le_densityL1
#print axioms
  WeightedMismatchFiniteChartFourierCertificate.norm_expectation_le_variation_div_abs_time
#print axioms
  WeightedMismatchFiniteChartFourierCertificate.tendsto_kineticAccumulation
#print axioms
  tendsto_actualIteratedA2WeightedChannel_finiteChart_kineticAccumulation

end ArchonPhysicsConsumers.Thermalization
