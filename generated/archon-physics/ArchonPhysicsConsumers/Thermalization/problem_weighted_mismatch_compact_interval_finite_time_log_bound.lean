import ArchonPhysics.WeightedMismatchCompactIntervalFiniteTimeLogBound

/-!
Consumer for endpoint-aware compact-interval Fourier ceilings and finite-time
logarithmic accumulation bounds.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open MeasureTheory

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      min certificate.densityL1Cost
        (certificate.variationCost / |time|) :=
  certificate.norm_expectation_le_min htime

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      certificate.densityL1Cost * tau +
        certificate.variationCost * Real.log (T / tau) :=
  certificate.intervalIntegral_norm_expectation_le_split_log
    tau T htau htauT

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      2 * (certificate.densityL1Cost * tau +
        certificate.variationCost * Real.log (T / tau)) :=
  certificate.intervalIntegral_norm_expectation_symmetric_le
    tau T htau htauT

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
      min certificate.densityL1Cost
        (certificate.variationCost / |time|) :=
  norm_actualIteratedA2WeightedChannelExpectation_le_compact_min
    ensemble channel weight observed term certificate htime

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel weight observed term)
    (tau T : Real) (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T,
        ‖actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term time‖) <=
      certificate.densityL1Cost * tau +
        certificate.variationCost * Real.log (T / tau) :=
  intervalIntegral_norm_actualIteratedA2WeightedChannelExpectation_le_compact_split_log
    ensemble channel weight observed term certificate tau T htau htauT

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel weight observed term)
    (tau T : Real) (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T,
        ‖actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term time‖) <=
      2 * (certificate.densityL1Cost * tau +
        certificate.variationCost * Real.log (T / tau)) :=
  intervalIntegral_norm_actualIteratedA2WeightedChannelExpectation_symmetric_le_compact_split_log
    ensemble channel weight observed term certificate tau T htau htauT

end

end ArchonPhysicsConsumers.Thermalization
