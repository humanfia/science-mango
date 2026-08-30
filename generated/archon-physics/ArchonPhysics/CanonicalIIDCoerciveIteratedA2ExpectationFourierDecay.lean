import ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge
import ArchonPhysics.RandomEnsemble
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Expectation-level Fourier decay for actual iterated-A2 mismatch channels

The natural pointwise partners of an actual iterated/iterated `A2` history do
not provide the desired cancellation.  This module records a logically
independent replacement: cancellation after averaging over a mismatch law.

For a complex conditional fibre density `rho`, Mathlib's Fourier
integration-by-parts theorem gives the quantitative estimate

`|t| * ‖integral exp(i t delta) rho(delta) d delta‖ <= integral ‖rho'(delta)‖ d delta`.

The regularity certificate used here is deliberately classical and stronger
than an abstract Sobolev representative: `rho` is integrable, differentiable
everywhere, and its classical derivative is integrable.  This is a concrete
`C^1 cap W^{1,1}` endpoint which can be replaced later by a weaker BV or weak
derivative interface without changing the model-facing adapter.

The final definitions instantiate the observable side for every outer,
inner, total, and twisted local mismatch of an actual iterated quadratic
second-Picard history.  Crucially, the certificate identifying its weighted
expectation with a regular density is an explicit theorem parameter.  No
such density certificate is proved here for the iid random-mass model, and
no decay of the full nested `A2/A2` remainder or kinetic closure is claimed.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory
open scoped FourierTransform Real RealInnerProductSpace

noncomputable section

/-! ## A normalized oscillatory integral and its Fourier realization -/

/-- Fourier oscillation with the physical convention `exp(i t delta)`.
Mathlib's real Fourier transform uses `exp(-2 pi i delta xi)`, so the
corresponding Fourier frequency is `xi = -t / (2 pi)`. -/
def weightedMismatchOscillatoryIntegral
    (density : Real -> Complex) (time : Real) : Complex :=
  ∫ mismatch : Real,
    Complex.exp (Complex.I * ((time * mismatch : Real) : Complex)) *
      density mismatch

/-- Exact normalization bridge to Mathlib's real Fourier transform. -/
theorem weightedMismatchOscillatoryIntegral_eq_fourier
    (density : Real -> Complex) (time : Real) :
    weightedMismatchOscillatoryIntegral density time =
      𝓕 density (-time / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold weightedMismatchOscillatoryIntegral
  apply integral_congr_ae
  filter_upwards with mismatch
  simp only [smul_eq_mul]
  have hphase :
      -2 * Real.pi * mismatch * (-time / (2 * Real.pi)) =
        time * mismatch := by
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  congr 2
  push_cast
  ring

/-- Quantitative Fourier integration by parts.  This is the useful
division-free form, valid also at `time = 0`. -/
theorem abs_time_mul_norm_weightedMismatchOscillatoryIntegral_le
    (density : Real -> Complex) (time : Real)
    (hdensity : Integrable density)
    (hdifferentiable : Differentiable Real density)
    (hderiv : Integrable (deriv density)) :
    |time| * ‖weightedMismatchOscillatoryIntegral density time‖ <=
      ∫ mismatch : Real, ‖deriv density mismatch‖ := by
  rw [weightedMismatchOscillatoryIntegral_eq_fourier]
  let frequency : Real := -time / (2 * Real.pi)
  have hfourier := congrFun
    (Real.fourier_deriv hdensity hdifferentiable hderiv) frequency
  have hcoefficient :
      ‖((2 * Real.pi * Complex.I * frequency : Complex))‖ = |time| := by
    dsimp [frequency]
    rw [norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Real.norm_eq_abs, mul_one]
    rw [abs_div, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    field_simp [Real.pi_ne_zero]
  have hnorm :
      ‖𝓕 (deriv density) frequency‖ =
        |time| * ‖𝓕 density frequency‖ := by
    rw [hfourier, norm_smul, hcoefficient]
  rw [← hnorm]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ Real) (deriv density) frequency

/-- The standard explicit `1 / |time|` form away from time zero. -/
theorem norm_weightedMismatchOscillatoryIntegral_le_derivL1_div_abs_time
    (density : Real -> Complex) (time : Real)
    (hdensity : Integrable density)
    (hdifferentiable : Differentiable Real density)
    (hderiv : Integrable (deriv density)) (htime : time ≠ 0) :
    ‖weightedMismatchOscillatoryIntegral density time‖ <=
      (∫ mismatch : Real, ‖deriv density mismatch‖) / |time| := by
  apply (le_div_iff₀ (abs_pos.mpr htime)).2
  simpa only [mul_comm] using
    abs_time_mul_norm_weightedMismatchOscillatoryIntegral_le
      density time hdensity hdifferentiable hderiv

/-- The nonoscillatory `L1` ceiling, useful near `time = 0`. -/
theorem norm_weightedMismatchOscillatoryIntegral_le_densityL1
    (density : Real -> Complex) (time : Real) :
    ‖weightedMismatchOscillatoryIntegral density time‖ <=
      ∫ mismatch : Real, ‖density mismatch‖ := by
  rw [weightedMismatchOscillatoryIntegral_eq_fourier]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ Real) density
      (-time / (2 * Real.pi))

/-! ## Abstract weighted expectation and its explicit regularity certificate -/

/-- A complex-weighted mismatch expectation.  The weight may include a
static interaction coefficient, a cutoff, or a conditional fibre weight. -/
def weightedMismatchExpectation
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) (time : Real) : Complex :=
  ∫ sample : Omega,
    Complex.exp
        (Complex.I * ((time * mismatch sample : Real) : Complex)) *
      weight sample ∂measure

/-- Explicit certificate that a weighted mismatch expectation is represented
by a classical `C^1 cap W^{1,1}` fibre density.  Producing this certificate
for an actual random-mass history is the model-specific analytic task left
open by this module. -/
structure WeightedMismatchC1L1FourierCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) where
  density : Real -> Complex
  expectation_eq : forall time,
    weightedMismatchExpectation measure mismatch weight time =
      weightedMismatchOscillatoryIntegral density time
  density_integrable : Integrable density
  density_differentiable : Differentiable Real density
  density_deriv_integrable : Integrable (deriv density)

/-- The explicit `L1` size of the density derivative. -/
def WeightedMismatchC1L1FourierCertificate.derivativeL1Cost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) : Real :=
  ∫ value : Real, ‖deriv certificate.density value‖

/-- The derivative cost is nonnegative. -/
theorem WeightedMismatchC1L1FourierCertificate.derivativeL1Cost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) :
    0 <= certificate.derivativeL1Cost := by
  exact integral_nonneg fun _ => norm_nonneg _

/-- Certificate-level division-free expectation decay. -/
theorem WeightedMismatchC1L1FourierCertificate.abs_time_mul_norm_expectation_le
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) (time : Real) :
    |time| * ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.derivativeL1Cost := by
  rw [certificate.expectation_eq]
  exact abs_time_mul_norm_weightedMismatchOscillatoryIntegral_le
    certificate.density time certificate.density_integrable
      certificate.density_differentiable certificate.density_deriv_integrable

/-- Certificate-level `1 / |time|` expectation decay. -/
theorem WeightedMismatchC1L1FourierCertificate.norm_expectation_le_div_abs_time
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchC1L1FourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.derivativeL1Cost / |time| := by
  rw [certificate.expectation_eq]
  exact norm_weightedMismatchOscillatoryIntegral_le_derivL1_div_abs_time
    certificate.density time certificate.density_integrable
      certificate.density_differentiable certificate.density_deriv_integrable
      htime

/-! ## Actual iterated-A2 channel adapter -/

/-- Local scalar mismatch channels occurring in one physical iterated-A2
twist orbit.  The common total mismatch is included because it is the phase
which occurs after the two ordered interactions. -/
inductive IteratedA2MismatchChannel where
  | outer
  | inner
  | total
  | outerTwist
  | innerTwist
  deriving DecidableEq

/-- Deterministic mismatch selected by an iterated-A2 channel. -/
def IteratedA2MismatchChannel.value
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (mass : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  match channel with
  | .outer => iteratedQuadraticOuterMismatch mass observed term
  | .inner => iteratedQuadraticInnerMismatch mass term
  | .total =>
      iteratedQuadraticOuterMismatch mass observed term +
        iteratedQuadraticInnerMismatch mass term
  | .outerTwist => iteratedQuadraticOuterMismatch mass observed
      (flipIteratedQuadraticInnerBranch term)
  | .innerTwist => iteratedQuadraticInnerMismatch mass
      (flipIteratedQuadraticInnerBranch term)

/-- The actual common total may equivalently be computed on the twisted
history. -/
theorem IteratedA2MismatchChannel.total_value_eq_twisted_total
    {N : Nat} [NeZero N] (mass : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedA2MismatchChannel.total.value mass observed term =
      IteratedA2MismatchChannel.outerTwist.value mass observed term +
        IteratedA2MismatchChannel.innerTwist.value mass observed term := by
  exact physicalIteratedA2_totalMismatch_flip_eq mass observed term

/-- One selected actual mismatch as a random variable under an iid positive
mass ensemble. -/
def actualIteratedA2MismatchSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) : Real :=
  channel.value (ensemble.restrictPositiveMass (N := N) sample)
    observed term

/-- Actual interaction coefficient before inserting an oscillatory channel.
The radius profile is allowed to depend on the initial sample. -/
def actualIteratedA2StaticWeightSample
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) : Complex :=
  iteratedQuadraticSecondPicardStaticCoefficient
    (ensemble.restrictPositiveMass (N := N) sample) kappa
      (radius sample) observed term

/-- Actual A2 expectation of one selected mismatch phase with an arbitrary
complex history weight.  This is the instantaneous Fourier building block;
it is not by itself the full nested A2 coefficient. -/
def actualIteratedA2WeightedChannelExpectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (time : Real) : Complex :=
  weightedMismatchExpectation ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term)
    weight time

/-- The exact density-regularity premise needed to apply Fourier decay to
one actual A2 weighted channel. -/
abbrev ActualIteratedA2WeightedChannelC1L1Certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :=
  WeightedMismatchC1L1FourierCertificate ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term) weight

/-- Quantitative actual-channel adapter.  The conclusion is unconditional
once the displayed density certificate is supplied, but this theorem does
not construct that certificate from the microscopic iid model. -/
theorem norm_actualIteratedA2WeightedChannelExpectation_le_div_abs_time
    {Omega : Type*} [MeasurableSpace Omega]
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
  certificate.norm_expectation_le_div_abs_time htime

/-- Static-coefficient specialization of the actual weighted expectation. -/
def actualIteratedA2StaticWeightedChannelExpectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (time : Real) : Complex :=
  actualIteratedA2WeightedChannelExpectation ensemble channel
    (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
    observed term time

/-- Explicit regularity premise for the physical static-coefficient
specialization. -/
abbrev ActualIteratedA2StaticWeightedChannelC1L1Certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :=
  ActualIteratedA2WeightedChannelC1L1Certificate ensemble channel
    (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
    observed term

/-- The physical static-weight channel inherits the same `1 / |time|`
bound under its explicit fibre-density certificate. -/
theorem norm_actualIteratedA2StaticWeightedChannelExpectation_le_div_abs_time
    {Omega : Type*} [MeasurableSpace Omega]
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
  norm_actualIteratedA2WeightedChannelExpectation_le_div_abs_time
    ensemble channel
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
      observed term certificate htime

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
