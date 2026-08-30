import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Compact-interval Fourier decay for weighted mismatch laws

The canonical iid mass law is uniform on a compact interval.  Consequently,
even a smooth change of one mass coordinate naturally produces a density
with endpoint jumps after extension by zero to the whole real line.  A global
`C^1` density certificate is therefore unnecessarily strong.

This module gives the matching endpoint-aware replacement.  A density which
is differentiable on one compact interval has `1 / |time|` Fourier decay,
with a cost consisting of its two endpoint values and the interval integral
of its derivative.  The final certificate and actual-A2 adapter expose the
remaining model-specific input without pretending that the nonlinear
eigenfrequency mismatch already satisfies it.
-/

namespace ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory Set

noncomputable section

/-- Oscillatory integral of a density confined to one oriented interval. -/
def weightedMismatchIntervalOscillatoryIntegral
    (density : Real -> Complex) (lower upper time : Real) : Complex :=
  ∫ mismatch in lower..upper,
    Complex.exp
        (Complex.I * ((time * mismatch : Real) : Complex)) *
      density mismatch

/-- A convenient antiderivative of a nonzero complex phase. -/
theorem hasDerivAt_expPhase_div
    {time : Real} (htime : time ≠ 0) (mismatch : Real) :
    HasDerivAt
      (fun value : Real =>
        Complex.exp ((Complex.I * (time : Complex)) * value) /
          (Complex.I * (time : Complex)))
      (Complex.exp ((Complex.I * (time : Complex)) * mismatch)) mismatch := by
  let coefficient : Complex := Complex.I * (time : Complex)
  have hcoefficient : coefficient ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr htime)
  have hlinear : HasDerivAt
      (fun value : Real => coefficient * value) coefficient mismatch := by
    simpa only [mul_one] using!
      (((hasDerivAt_id (mismatch : Complex)).const_mul coefficient).comp_ofReal)
  simpa [coefficient, Function.comp_def, hcoefficient] using
    ((Complex.hasDerivAt_exp _).comp mismatch hlinear).div_const coefficient

/-- Exact integration-by-parts identity, including the two endpoint terms
which are absent from a global `C^1 cap W^{1,1}` certificate. -/
theorem weightedMismatchIntervalOscillatoryIntegral_eq_boundary_sub_deriv
    (density densityDeriv : Real -> Complex)
    {lower upper time : Real} (htime : time ≠ 0)
    (hdensity : ∀ value ∈ Set.uIcc lower upper,
      HasDerivAt density (densityDeriv value) value)
    (hderiv : IntervalIntegrable densityDeriv volume lower upper) :
    weightedMismatchIntervalOscillatoryIntegral density lower upper time =
      density upper *
          (Complex.exp ((Complex.I * (time : Complex)) * upper) /
            (Complex.I * (time : Complex))) -
        density lower *
          (Complex.exp ((Complex.I * (time : Complex)) * lower) /
            (Complex.I * (time : Complex))) -
        ∫ value in lower..upper,
          densityDeriv value *
            (Complex.exp ((Complex.I * (time : Complex)) * value) /
              (Complex.I * (time : Complex))) := by
  have hphase : ∀ value ∈ Set.uIcc lower upper,
      HasDerivAt
        (fun argument : Real =>
          Complex.exp ((Complex.I * (time : Complex)) * argument) /
            (Complex.I * (time : Complex)))
        (Complex.exp ((Complex.I * (time : Complex)) * value)) value :=
    fun value _ => hasDerivAt_expPhase_div htime value
  have hphaseIntegrable : IntervalIntegrable
      (fun value : Real =>
        Complex.exp ((Complex.I * (time : Complex)) * value))
      volume lower upper := by
    exact Continuous.intervalIntegrable (μ := volume)
      (by fun_prop : Continuous
        (fun value : Real =>
          Complex.exp ((Complex.I * (time : Complex)) * value))) lower upper
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hdensity hphase hderiv hphaseIntegrable
  rw [show weightedMismatchIntervalOscillatoryIntegral density lower upper time =
      ∫ value in lower..upper,
        density value *
          Complex.exp ((Complex.I * (time : Complex)) * value) by
    unfold weightedMismatchIntervalOscillatoryIntegral
    apply intervalIntegral.integral_congr
    intro value _hvalue
    change Complex.exp
        (Complex.I * ((time * value : Real) : Complex)) * density value =
      density value *
        Complex.exp ((Complex.I * (time : Complex)) * (value : Complex))
    rw [mul_comm]
    have hcast : ((time * value : Real) : Complex) =
        (time : Complex) * (value : Complex) := by norm_cast
    rw [hcast]
    ring]
  exact hparts

/-- Endpoint-aware variation cost for one compact mismatch chart. -/
def intervalFourierVariationCost
    (density densityDeriv : Real -> Complex) (lower upper : Real) : Real :=
  ‖density lower‖ + ‖density upper‖ +
    ∫ value in lower..upper, ‖densityDeriv value‖

/-- The variation cost is nonnegative on a positively oriented interval. -/
theorem intervalFourierVariationCost_nonneg
    (density densityDeriv : Real -> Complex) {lower upper : Real}
    (hlowerUpper : lower <= upper) :
    0 <= intervalFourierVariationCost density densityDeriv lower upper := by
  unfold intervalFourierVariationCost
  have hintegral : 0 <= ∫ value in lower..upper, ‖densityDeriv value‖ :=
    intervalIntegral.integral_nonneg_of_forall hlowerUpper
      (fun value => norm_nonneg (densityDeriv value))
  exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hintegral

/-- Compact-interval `1 / |time|` Fourier decay.  The endpoint terms make
this applicable to densities created from compactly supported mass laws. -/
theorem norm_weightedMismatchIntervalOscillatoryIntegral_le_variation_div_abs_time
    (density densityDeriv : Real -> Complex)
    {lower upper time : Real} (hlowerUpper : lower <= upper)
    (htime : time ≠ 0)
    (hdensity : ∀ value ∈ Set.uIcc lower upper,
      HasDerivAt density (densityDeriv value) value)
    (hderiv : IntervalIntegrable densityDeriv volume lower upper) :
    ‖weightedMismatchIntervalOscillatoryIntegral density lower upper time‖ <=
      intervalFourierVariationCost density densityDeriv lower upper /
        |time| := by
  rw [weightedMismatchIntervalOscillatoryIntegral_eq_boundary_sub_deriv
    density densityDeriv htime hdensity hderiv]
  have hdenominatorNorm : ‖Complex.I * (time : Complex)‖ = |time| := by
    rw [norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul]
  have hphaseNorm : ∀ value : Real,
      ‖Complex.exp
        ((Complex.I * (time : Complex)) * (value : Complex))‖ = 1 := by
    intro value
    have hcast : (time : Complex) * (value : Complex) =
        ((time * value : Real) : Complex) := by norm_cast
    rw [show (Complex.I * (time : Complex)) * (value : Complex) =
        Complex.I * ((time * value : Real) : Complex) by
      rw [mul_assoc, hcast]]
    exact Complex.norm_exp_I_mul_ofReal (time * value)
  have hboundaryUpper :
      ‖density upper *
          (Complex.exp ((Complex.I * (time : Complex)) * upper) /
            (Complex.I * (time : Complex)))‖ =
        ‖density upper‖ / |time| := by
    rw [norm_mul, norm_div, hphaseNorm, hdenominatorNorm]
    ring
  have hboundaryLower :
      ‖density lower *
          (Complex.exp ((Complex.I * (time : Complex)) * lower) /
            (Complex.I * (time : Complex)))‖ =
        ‖density lower‖ / |time| := by
    rw [norm_mul, norm_div, hphaseNorm, hdenominatorNorm]
    ring
  have hintegral :
      ‖∫ value in lower..upper,
          densityDeriv value *
            (Complex.exp ((Complex.I * (time : Complex)) * value) /
              (Complex.I * (time : Complex)))‖ <=
        (∫ value in lower..upper, ‖densityDeriv value‖) / |time| := by
    calc
      _ <= ∫ value in lower..upper,
          ‖densityDeriv value *
            (Complex.exp ((Complex.I * (time : Complex)) * value) /
              (Complex.I * (time : Complex)))‖ :=
        intervalIntegral.norm_integral_le_integral_norm hlowerUpper
      _ = ∫ value in lower..upper, ‖densityDeriv value‖ / |time| := by
        apply intervalIntegral.integral_congr
        intro value _hvalue
        change ‖densityDeriv value *
            (Complex.exp ((Complex.I * (time : Complex)) * value) /
              (Complex.I * (time : Complex)))‖ =
          ‖densityDeriv value‖ / |time|
        rw [norm_mul, norm_div, hphaseNorm, hdenominatorNorm]
        ring
      _ = (∫ value in lower..upper, ‖densityDeriv value‖) / |time| := by
        rw [intervalIntegral.integral_div]
  calc
    _ <=
        ‖density upper *
          (Complex.exp ((Complex.I * (time : Complex)) * upper) /
            (Complex.I * (time : Complex)))‖ +
        ‖density lower *
          (Complex.exp ((Complex.I * (time : Complex)) * lower) /
            (Complex.I * (time : Complex)))‖ +
        ‖∫ value in lower..upper,
          densityDeriv value *
            (Complex.exp ((Complex.I * (time : Complex)) * value) /
              (Complex.I * (time : Complex)))‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ <= ‖density upper‖ / |time| + ‖density lower‖ / |time| +
        (∫ value in lower..upper, ‖densityDeriv value‖) / |time| := by
      rw [hboundaryUpper, hboundaryLower]
      gcongr
    _ = intervalFourierVariationCost density densityDeriv lower upper /
        |time| := by
      unfold intervalFourierVariationCost
      ring

/-! ## Compact-interval expectation certificate -/

/-- An endpoint-aware density certificate for a complex-weighted mismatch
expectation.  Constructing this record amounts to choosing one regular chart,
including all conditional weights in `density`, and proving the displayed
change-of-variables identity. -/
structure WeightedMismatchCompactIntervalFourierCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) where
  lower : Real
  upper : Real
  lower_le_upper : lower <= upper
  density : Real -> Complex
  densityDeriv : Real -> Complex
  expectation_eq : forall time,
    weightedMismatchExpectation measure mismatch weight time =
      weightedMismatchIntervalOscillatoryIntegral density lower upper time
  density_hasDeriv : ∀ value ∈ Set.uIcc lower upper,
    HasDerivAt density (densityDeriv value) value
  densityDeriv_intervalIntegrable :
    IntervalIntegrable densityDeriv volume lower upper

/-- Endpoint-aware variation cost stored by a compact-interval certificate. -/
def WeightedMismatchCompactIntervalFourierCertificate.variationCost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) : Real :=
  intervalFourierVariationCost certificate.density certificate.densityDeriv
    certificate.lower certificate.upper

/-- The certificate cost is nonnegative. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.variationCost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    0 <= certificate.variationCost := by
  exact intervalFourierVariationCost_nonneg
    certificate.density certificate.densityDeriv certificate.lower_le_upper

/-- Certificate-level `1 / |time|` expectation decay with endpoint cost. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.norm_expectation_le_div_abs_time
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.variationCost / |time| := by
  rw [certificate.expectation_eq]
  exact
    norm_weightedMismatchIntervalOscillatoryIntegral_le_variation_div_abs_time
      certificate.density certificate.densityDeriv
      certificate.lower_le_upper htime certificate.density_hasDeriv
      certificate.densityDeriv_intervalIntegrable

/-! ## Actual iterated-A2 adapter -/

/-- Compact-interval alternative to the global `C^1 cap W^{1,1}` actual-A2
certificate.  It permits the endpoint jumps naturally produced by the
canonical compact uniform mass law. -/
abbrev ActualIteratedA2WeightedChannelCompactIntervalCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :=
  WeightedMismatchCompactIntervalFourierCertificate ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term) weight

/-- Actual-channel decay under the endpoint-aware compact-interval density
certificate.  This theorem does not construct the chart for the nonlinear
eigenfrequency mismatch and is not a full nested-A2 closure. -/
theorem norm_actualIteratedA2WeightedChannelExpectation_le_compactVariation_div_abs_time
    {Omega : Type*} [MeasurableSpace Omega]
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
  certificate.norm_expectation_le_div_abs_time htime

end

end ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
