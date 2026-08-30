import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay

/-!
Consumer for the expectation-level iterated-A2 Fourier-decay adapter.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory
open scoped FourierTransform

noncomputable section

example (density : Real -> Complex) (time : Real) :
    weightedMismatchOscillatoryIntegral density time =
      𝓕 density (-time / (2 * Real.pi)) :=
  weightedMismatchOscillatoryIntegral_eq_fourier density time

example (density : Real -> Complex) (time : Real)
    (hdensity : Integrable density)
    (hdifferentiable : Differentiable Real density)
    (hderiv : Integrable (deriv density)) :
    |time| * ‖weightedMismatchOscillatoryIntegral density time‖ <=
      ∫ mismatch : Real, ‖deriv density mismatch‖ :=
  abs_time_mul_norm_weightedMismatchOscillatoryIntegral_le
    density time hdensity hdifferentiable hderiv

example (density : Real -> Complex) (time : Real)
    (hdensity : Integrable density)
    (hdifferentiable : Differentiable Real density)
    (hderiv : Integrable (deriv density)) (htime : time ≠ 0) :
    ‖weightedMismatchOscillatoryIntegral density time‖ <=
      (∫ mismatch : Real, ‖deriv density mismatch‖) / |time| :=
  norm_weightedMismatchOscillatoryIntegral_le_derivL1_div_abs_time
    density time hdensity hdifferentiable hderiv htime

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) (time : Real) :
    |time| * ‖weightedMismatchExpectation
        measure mismatch weight time‖ <=
      certificate.derivativeL1Cost :=
  certificate.abs_time_mul_norm_expectation_le time

example {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.derivativeL1Cost / |time| :=
  certificate.norm_expectation_le_div_abs_time htime

example {N : Nat} [NeZero N]
    (mass : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedA2MismatchChannel.total.value mass observed term =
      IteratedA2MismatchChannel.outerTwist.value mass observed term +
        IteratedA2MismatchChannel.innerTwist.value mass observed term :=
  IteratedA2MismatchChannel.total_value_eq_twisted_total
    mass observed term

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelC1L1Certificate
      ensemble channel weight observed term)
    {time : Real} (htime : time ≠ 0) :
    ‖actualIteratedA2WeightedChannelExpectation ensemble channel weight
        observed term time‖ <=
      certificate.derivativeL1Cost / |time| :=
  norm_actualIteratedA2WeightedChannelExpectation_le_div_abs_time
    ensemble channel weight observed term certificate htime

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2StaticWeightedChannelC1L1Certificate
      ensemble channel kappa radius observed term)
    {time : Real} (htime : time ≠ 0) :
    ‖actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time‖ <=
      certificate.derivativeL1Cost / |time| :=
  norm_actualIteratedA2StaticWeightedChannelExpectation_le_div_abs_time
    ensemble channel kappa radius observed term certificate htime

end

end ArchonPhysicsConsumers.Thermalization
