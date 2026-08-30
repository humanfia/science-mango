import ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite-time logarithmic bounds for compact-interval mismatch charts

An endpoint-aware compact mismatch chart supplies a uniform interval-`L1`
ceiling and `variationCost / |time|` decay.  Combining those two estimates
with the abstract split-envelope theorem gives explicit logarithmic bounds on
positive and symmetric finite time windows.

The chart certificate remains an input.  In particular, this module does not
construct a nonlinear mass-to-mismatch chart for the actual iid model and does
not close the full nested iterated-`A2` remainder.
-/

namespace ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory Set
open scoped Interval

noncomputable section

/-! ## Compact density ceiling -/

/-- The interval-`L1` cost of the density represented by a compact chart. -/
def WeightedMismatchCompactIntervalFourierCertificate.densityL1Cost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) : Real :=
  ∫ value in certificate.lower..certificate.upper,
    ‖certificate.density value‖

/-- Differentiability on the certified interval supplies continuity there. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.density_continuousOn
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    ContinuousOn certificate.density
      (uIcc certificate.lower certificate.upper) := by
  intro value hvalue
  exact (certificate.density_hasDeriv value hvalue).continuousAt.continuousWithinAt

/-- The compact density and its norm are interval-integrable. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.density_intervalIntegrable
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    IntervalIntegrable certificate.density volume
      certificate.lower certificate.upper :=
  certificate.density_continuousOn.intervalIntegrable

theorem WeightedMismatchCompactIntervalFourierCertificate.norm_density_intervalIntegrable
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    IntervalIntegrable (fun value => ‖certificate.density value‖) volume
      certificate.lower certificate.upper :=
  certificate.density_intervalIntegrable.norm

/-- The compact density ceiling is nonnegative. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.densityL1Cost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    0 <= certificate.densityL1Cost := by
  exact intervalIntegral.integral_nonneg_of_forall certificate.lower_le_upper
    (fun value => norm_nonneg (certificate.density value))

/-- The compact interval representation has its natural uniform `L1`
ceiling at every time. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.norm_expectation_le_densityL1
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) (time : Real) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.densityL1Cost := by
  rw [certificate.expectation_eq]
  unfold weightedMismatchIntervalOscillatoryIntegral
  calc
    _ <= ∫ value in certificate.lower..certificate.upper,
        ‖Complex.exp
            (Complex.I * ((time * value : Real) : Complex)) *
          certificate.density value‖ :=
      intervalIntegral.norm_integral_le_integral_norm
        certificate.lower_le_upper
    _ = certificate.densityL1Cost := by
      apply intervalIntegral.integral_congr
      intro value _hvalue
      change
        ‖Complex.exp
            (Complex.I * ((time * value : Real) : Complex)) *
          certificate.density value‖ = ‖certificate.density value‖
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

/-- Away from zero, the uniform and endpoint-variation bounds combine into
their pointwise minimum. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.norm_expectation_le_min
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      min certificate.densityL1Cost
        (certificate.variationCost / |time|) := by
  exact le_min (certificate.norm_expectation_le_densityL1 time)
    (certificate.norm_expectation_le_div_abs_time htime)

/-! ## Continuity of the compact Fourier signal -/

/-- A density continuous on its compact integration interval produces a
continuous oscillatory signal in the time parameter. -/
theorem continuous_weightedMismatchIntervalOscillatoryIntegral
    (density : Real -> Complex) {lower upper : Real}
    (hdensity : ContinuousOn density (uIcc lower upper)) :
    Continuous
      (weightedMismatchIntervalOscillatoryIntegral density lower upper) := by
  unfold weightedMismatchIntervalOscillatoryIntegral
  apply intervalIntegral.continuous_of_dominated_interval
      (bound := fun value => ‖density value‖)
  · intro time
    have hphase : Continuous (fun value : Real =>
        Complex.exp
          (Complex.I * ((time * value : Real) : Complex))) := by
      fun_prop
    exact
      (hphase.continuousOn.mul
        (hdensity.mono uIoc_subset_uIcc)).aestronglyMeasurable
          measurableSet_uIoc
  · intro time
    filter_upwards with value
    intro _hvalue
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  · exact hdensity.intervalIntegrable.norm
  · filter_upwards with value
    intro _hvalue
    fun_prop

/-- The expectation represented by a compact certificate is continuous. -/
theorem WeightedMismatchCompactIntervalFourierCertificate.continuous_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    Continuous (weightedMismatchExpectation measure mismatch weight) := by
  have heq : weightedMismatchExpectation measure mismatch weight =
      weightedMismatchIntervalOscillatoryIntegral certificate.density
        certificate.lower certificate.upper := by
    funext time
    exact certificate.expectation_eq time
  rw [heq]
  exact continuous_weightedMismatchIntervalOscillatoryIntegral
    certificate.density certificate.density_continuousOn

/-! ## Finite-window logarithmic accumulation -/

/-- Positive-window logarithmic accumulation for one compact certificate. -/
theorem
    WeightedMismatchCompactIntervalFourierCertificate.intervalIntegral_norm_expectation_le_split_log
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in 0..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      certificate.densityL1Cost * tau +
        certificate.variationCost * Real.log (T / tau) := by
  exact intervalIntegral_norm_le_split_log
    (weightedMismatchExpectation measure mismatch weight)
    certificate.densityL1Cost certificate.variationCost tau T
    certificate.continuous_expectation
    certificate.norm_expectation_le_densityL1
    (fun time htime => certificate.norm_expectation_le_div_abs_time htime)
    htau htauT

/-- Symmetric-window logarithmic accumulation for the same compact
certificate. -/
theorem
    WeightedMismatchCompactIntervalFourierCertificate.intervalIntegral_norm_expectation_symmetric_le
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) (tau T : Real)
    (htau : 0 < tau) (htauT : tau <= T) :
    (∫ time : Real in (-T)..T,
        ‖weightedMismatchExpectation measure mismatch weight time‖) <=
      2 * (certificate.densityL1Cost * tau +
        certificate.variationCost * Real.log (T / tau)) := by
  exact intervalIntegral_norm_symmetric_le_two_mul_split_log
    (weightedMismatchExpectation measure mismatch weight)
    certificate.densityL1Cost certificate.variationCost tau T
    certificate.continuous_expectation
    certificate.norm_expectation_le_densityL1
    (fun time htime => certificate.norm_expectation_le_div_abs_time htime)
    htau htauT

/-! ## Actual iterated-A2 adapters -/

/-- Pointwise compact-envelope adapter for an actual weighted A2 channel. -/
theorem norm_actualIteratedA2WeightedChannelExpectation_le_compact_min
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
      min certificate.densityL1Cost
        (certificate.variationCost / |time|) :=
  certificate.norm_expectation_le_min htime

/-- Positive finite-window compact-chart adapter for an actual weighted A2
channel. -/
theorem intervalIntegral_norm_actualIteratedA2WeightedChannelExpectation_le_compact_split_log
    {Omega : Type*} [MeasurableSpace Omega]
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
  certificate.intervalIntegral_norm_expectation_le_split_log
    tau T htau htauT

/-- Symmetric finite-window compact-chart adapter for an actual weighted A2
channel. -/
theorem
    intervalIntegral_norm_actualIteratedA2WeightedChannelExpectation_symmetric_le_compact_split_log
    {Omega : Type*} [MeasurableSpace Omega]
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
  certificate.intervalIntegral_norm_expectation_symmetric_le
    tau T htau htauT

end

end ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
