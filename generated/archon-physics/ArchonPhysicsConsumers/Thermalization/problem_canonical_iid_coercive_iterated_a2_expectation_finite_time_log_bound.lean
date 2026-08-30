import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound

/-!
Consumer for the finite-time logarithmic accumulation of expectation-level
iterated-A2 Fourier decay.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory

noncomputable section

example (signal : Real -> Complex) (L D tau T : Real)
    (hcontinuous : Continuous signal)
    (hL : forall time, ‖signal time‖ <= L)
    (hD : forall time, time ≠ 0 -> ‖signal time‖ <= D / |time|)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T, ‖signal time‖) <=
      L * tau + D * Real.log (T / tau) :=
  intervalIntegral_norm_le_split_log signal L D tau T
    hcontinuous hL hD htau htauT

example (signal : Real -> Complex) (L D tau T : Real)
    (hcontinuous : Continuous signal)
    (hL : forall time, ‖signal time‖ <= L)
    (hD : forall time, time ≠ 0 -> ‖signal time‖ <= D / |time|)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T, ‖signal time‖) <=
      2 * (L * tau + D * Real.log (T / tau)) :=
  intervalIntegral_norm_symmetric_le_two_mul_split_log signal L D tau T
    hcontinuous hL hD htau htauT

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      min
        (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate)
        (certificate.derivativeL1Cost / |time|) :=
  WeightedMismatchC1L1FourierCertificate.norm_expectation_le_min
    certificate htime

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate * tau +
        certificate.derivativeL1Cost * Real.log (T / tau) :=
  WeightedMismatchC1L1FourierCertificate.intervalIntegral_norm_expectation_le_split_log
    certificate tau T htau htauT

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      2 *
        (WeightedMismatchC1L1FourierCertificate.densityL1Cost certificate *
          tau + certificate.derivativeL1Cost * Real.log (T / tau)) :=
  WeightedMismatchC1L1FourierCertificate.intervalIntegral_norm_expectation_symmetric_le
    certificate tau T htau htauT

example {Omega : Type*} [MeasurableSpace Omega]
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
        certificate.derivativeL1Cost * Real.log (T / tau) :=
  intervalIntegral_norm_actualIteratedA2WeightedChannelExpectation_le_split_log
    ensemble channel weight observed term certificate tau T htau htauT

example {Omega : Type*} [MeasurableSpace Omega]
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
        certificate.derivativeL1Cost * Real.log (T / tau) :=
  intervalIntegral_norm_actualIteratedA2StaticWeightedChannelExpectation_le_split_log
    ensemble channel kappa radius observed term certificate tau T htau htauT

end

end ArchonPhysicsConsumers.Thermalization
