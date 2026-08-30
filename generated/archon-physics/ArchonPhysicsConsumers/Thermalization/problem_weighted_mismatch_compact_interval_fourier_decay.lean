import ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay

/-!
Consumer and axiom audit for endpoint-aware compact-interval mismatch
Fourier decay and its actual iterated-A2 adapter.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open MeasureTheory Set

noncomputable section

example (density densityDeriv : Real -> Complex)
    {lower upper time : Real} (hlowerUpper : lower <= upper)
    (htime : time ≠ 0)
    (hdensity : ∀ value ∈ Set.uIcc lower upper,
      HasDerivAt density (densityDeriv value) value)
    (hderiv : IntervalIntegrable densityDeriv volume lower upper) :
    ‖weightedMismatchIntervalOscillatoryIntegral
        density lower upper time‖ <=
      intervalFourierVariationCost density densityDeriv lower upper /
        |time| :=
  norm_weightedMismatchIntervalOscillatoryIntegral_le_variation_div_abs_time
    density densityDeriv hlowerUpper htime hdensity hderiv

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.variationCost / |time| :=
  certificate.norm_expectation_le_div_abs_time htime

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel weight observed term)
    {time : Real} (htime : time ≠ 0) :
    ‖actualIteratedA2WeightedChannelExpectation ensemble channel weight
        observed term time‖ <=
      certificate.variationCost / |time| :=
  norm_actualIteratedA2WeightedChannelExpectation_le_compactVariation_div_abs_time
    ensemble channel weight observed term certificate htime

end

#print axioms weightedMismatchIntervalOscillatoryIntegral_eq_boundary_sub_deriv
#print axioms norm_weightedMismatchIntervalOscillatoryIntegral_le_variation_div_abs_time
#print axioms WeightedMismatchCompactIntervalFourierCertificate.norm_expectation_le_div_abs_time
#print axioms norm_actualIteratedA2WeightedChannelExpectation_le_compactVariation_div_abs_time

end ArchonPhysicsConsumers.Thermalization
