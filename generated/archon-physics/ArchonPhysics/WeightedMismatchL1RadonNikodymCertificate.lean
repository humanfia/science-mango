import ArchonPhysics.WeakCouplingQualitativeFourierKineticScale
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Radon--Nikodym construction of qualitative weighted Fourier certificates

At fixed volume, it is enough that the unweighted mismatch law is absolutely
continuous with respect to Lebesgue measure.  Multiplication by an integrable
complex weight preserves absolute continuity on the source, and measurable
pushforward preserves it on mismatch space.  Splitting the real and imaginary
parts of the weight into positive and negative parts then gives four finite
positive pushforwards.  Their Radon--Nikodym derivatives assemble into a
canonical complex `L1` density.

This module performs that construction and supplies the exact Fourier
representation required by `WeightedMismatchL1FourierCertificate`.  It gives
no quantitative decay rate and no estimate uniform in a growing volume.
-/

namespace ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.WeakCouplingQualitativeFourierKineticScale
open MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section

/-- Positive pushforward obtained from the positive part of a real source
weight. -/
def positiveRealWeightedMismatchPushforward
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Real) : Measure Real :=
  Measure.map mismatch
    (measure.withDensity (fun sample => ENNReal.ofReal (weight sample)))

/-- The signed real RN density obtained by subtracting the RN densities of
the positive and negative parts of a real source weight. -/
def realWeightedMismatchRNDensity
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Real) : Real -> Real :=
  fun value =>
    ((positiveRealWeightedMismatchPushforward measure mismatch weight).rnDeriv
          volume value).toReal -
      ((positiveRealWeightedMismatchPushforward measure mismatch
          (fun sample => -weight sample)).rnDeriv volume value).toReal

/-- Complex RN mismatch density, assembled from the signed RN densities of
the real and imaginary parts of the source weight. -/
def weightedMismatchRNDensity
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) : Real -> Complex :=
  fun value =>
    (realWeightedMismatchRNDensity measure mismatch
        (fun sample => (weight sample).re) value : Complex) +
      (realWeightedMismatchRNDensity measure mismatch
        (fun sample => (weight sample).im) value : Complex) * Complex.I

/-- Positive and negative parts reconstruct a real number. -/
private theorem toReal_ofReal_sub_toReal_ofReal_neg (value : Real) :
    (ENNReal.ofReal value).toReal -
        (ENNReal.ofReal (-value)).toReal = value := by
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total 0 value with hvalue | hvalue
  · simp [max_eq_left hvalue, max_eq_right (neg_nonpos.mpr hvalue)]
  · have hneg : 0 <= -value := neg_nonneg.mpr hvalue
    simp [max_eq_right hvalue, max_eq_left hneg]

/-- An integrable real source weight produces an integrable signed RN density
as soon as its two positive pushforwards are used.  Absolute continuity is not
needed for this integrability statement: finite positive measures always have
integrable RN derivatives. -/
theorem integrable_realWeightedMismatchRNDensity
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Real) (hweight : Integrable weight measure) :
    Integrable (realWeightedMismatchRNDensity measure mismatch weight) := by
  letI : IsFiniteMeasure
      (measure.withDensity (fun sample => ENNReal.ofReal (weight sample))) :=
    isFiniteMeasure_withDensity_ofReal hweight.2
  letI : IsFiniteMeasure
      (positiveRealWeightedMismatchPushforward measure mismatch weight) :=
    (measure.withDensity
      (fun sample => ENNReal.ofReal (weight sample))).isFiniteMeasure_map mismatch
  letI : IsFiniteMeasure
      (measure.withDensity (fun sample => ENNReal.ofReal (-weight sample))) :=
    isFiniteMeasure_withDensity_ofReal hweight.neg.2
  letI : IsFiniteMeasure
      (positiveRealWeightedMismatchPushforward measure mismatch
        (fun sample => -weight sample)) :=
    (measure.withDensity
      (fun sample => ENNReal.ofReal (-weight sample))).isFiniteMeasure_map mismatch
  exact (Measure.integrable_toReal_rnDeriv
    (μ := positiveRealWeightedMismatchPushforward measure mismatch weight)
    (ν := volume)).sub
      (Measure.integrable_toReal_rnDeriv
        (μ := positiveRealWeightedMismatchPushforward measure mismatch
          (fun sample => -weight sample)) (ν := volume))

/-- The canonical complex RN density is `L1` whenever the source weight is
Bochner integrable. -/
theorem integrable_weightedMismatchRNDensity
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) (hweight : Integrable weight measure) :
    Integrable (weightedMismatchRNDensity measure mismatch weight) := by
  have hre : Integrable
      (realWeightedMismatchRNDensity measure mismatch
        (fun sample => (weight sample).re)) :=
    integrable_realWeightedMismatchRNDensity measure mismatch _ hweight.re
  have him : Integrable
      (realWeightedMismatchRNDensity measure mismatch
        (fun sample => (weight sample).im)) :=
    integrable_realWeightedMismatchRNDensity measure mismatch _ hweight.im
  exact hre.ofReal.add (him.ofReal.mul_const Complex.I)

/-- A bounded measurable test pairs with the signed RN density exactly as it
pairs with the original real-weighted source law.  This is the core
pushforward/Radon--Nikodym identity. -/
theorem integral_test_mul_real_eq_integral_realWeightedMismatchRNDensity
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Real) (test : Real -> Complex)
    (hmismatch : Measurable mismatch) (hweightMeasurable : Measurable weight)
    (hweight : Integrable weight measure) (htest : Measurable test)
    (htestNorm : forall value, ‖test value‖ <= 1)
    (hpositive :
      positiveRealWeightedMismatchPushforward measure mismatch weight ≪ volume)
    (hnegative :
      positiveRealWeightedMismatchPushforward measure mismatch
        (fun sample => -weight sample) ≪ volume) :
    (∫ sample, test (mismatch sample) * (weight sample : Complex) ∂measure) =
      ∫ value, test value *
        (realWeightedMismatchRNDensity measure mismatch weight value : Complex) := by
  let positiveSource : Measure Omega :=
    measure.withDensity (fun sample => ENNReal.ofReal (weight sample))
  let negativeSource : Measure Omega :=
    measure.withDensity (fun sample => ENNReal.ofReal (-weight sample))
  let positivePushforward : Measure Real :=
    positiveRealWeightedMismatchPushforward measure mismatch weight
  let negativePushforward : Measure Real :=
    positiveRealWeightedMismatchPushforward measure mismatch
      (fun sample => -weight sample)
  letI : IsFiniteMeasure positiveSource :=
    isFiniteMeasure_withDensity_ofReal hweight.2
  letI : IsFiniteMeasure negativeSource :=
    isFiniteMeasure_withDensity_ofReal hweight.neg.2
  letI : IsFiniteMeasure positivePushforward :=
    positiveSource.isFiniteMeasure_map mismatch
  letI : IsFiniteMeasure negativePushforward :=
    negativeSource.isFiniteMeasure_map mismatch
  have htestComp : Measurable (fun sample => test (mismatch sample)) :=
    htest.comp hmismatch
  have htestPositiveSource :
      Integrable (fun sample => test (mismatch sample)) positiveSource := by
    apply Integrable.of_bound htestComp.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun sample => htestNorm (mismatch sample))
  have htestNegativeSource :
      Integrable (fun sample => test (mismatch sample)) negativeSource := by
    apply Integrable.of_bound htestComp.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun sample => htestNorm (mismatch sample))
  have hpositiveWeighted : Integrable
      (fun sample =>
        (ENNReal.ofReal (weight sample)).toReal • test (mismatch sample)) measure :=
    (integrable_withDensity_iff_integrable_smul'
      hweightMeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => by simp))).mp htestPositiveSource
  have hnegativeWeighted : Integrable
      (fun sample =>
        (ENNReal.ofReal (-weight sample)).toReal • test (mismatch sample)) measure :=
    (integrable_withDensity_iff_integrable_smul'
      hweightMeasurable.neg.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => by simp))).mp htestNegativeSource
  have hpositiveRepresentation :
      (∫ value, test value *
          ((positivePushforward.rnDeriv volume value).toReal : Complex)) =
        ∫ sample,
          (ENNReal.ofReal (weight sample)).toReal •
            test (mismatch sample) ∂measure := by
    calc
      (∫ value, test value *
          ((positivePushforward.rnDeriv volume value).toReal : Complex)) =
          ∫ value, (positivePushforward.rnDeriv volume value).toReal •
            test value := by
        apply integral_congr_ae
        filter_upwards with value
        simp [mul_comm]
      _ = ∫ value, test value ∂positivePushforward := by
        exact integral_rnDeriv_smul hpositive
      _ = ∫ sample, test (mismatch sample) ∂positiveSource := by
        exact integral_map hmismatch.aemeasurable htest.aestronglyMeasurable
      _ = ∫ sample,
          (ENNReal.ofReal (weight sample)).toReal •
            test (mismatch sample) ∂measure := by
        exact integral_withDensity_eq_integral_toReal_smul
          hweightMeasurable.ennreal_ofReal
          (Filter.Eventually.of_forall (fun _ => by simp)) _
  have hnegativeRepresentation :
      (∫ value, test value *
          ((negativePushforward.rnDeriv volume value).toReal : Complex)) =
        ∫ sample,
          (ENNReal.ofReal (-weight sample)).toReal •
            test (mismatch sample) ∂measure := by
    calc
      (∫ value, test value *
          ((negativePushforward.rnDeriv volume value).toReal : Complex)) =
          ∫ value, (negativePushforward.rnDeriv volume value).toReal •
            test value := by
        apply integral_congr_ae
        filter_upwards with value
        simp [mul_comm]
      _ = ∫ value, test value ∂negativePushforward := by
        exact integral_rnDeriv_smul hnegative
      _ = ∫ sample, test (mismatch sample) ∂negativeSource := by
        exact integral_map hmismatch.aemeasurable htest.aestronglyMeasurable
      _ = ∫ sample,
          (ENNReal.ofReal (-weight sample)).toReal •
            test (mismatch sample) ∂measure := by
        exact integral_withDensity_eq_integral_toReal_smul
          hweightMeasurable.neg.ennreal_ofReal
          (Filter.Eventually.of_forall (fun _ => by simp)) _
  rw [show (∫ sample,
      test (mismatch sample) * (weight sample : Complex) ∂measure) =
        (∫ sample,
          (ENNReal.ofReal (weight sample)).toReal • test (mismatch sample) ∂measure) -
        (∫ sample,
          (ENNReal.ofReal (-weight sample)).toReal • test (mismatch sample) ∂measure) by
    rw [← integral_sub hpositiveWeighted hnegativeWeighted]
    apply integral_congr_ae
    filter_upwards with sample
    rw [← sub_smul, toReal_ofReal_sub_toReal_ofReal_neg]
    simp [mul_comm]]
  rw [← hpositiveRepresentation, ← hnegativeRepresentation]
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with value
    simp only [realWeightedMismatchRNDensity, positivePushforward,
      negativePushforward]
    push_cast
    ring
  · exact Measure.integrable_toReal_rnDeriv.ofReal.bdd_mul
      htest.aestronglyMeasurable
      (Filter.Eventually.of_forall htestNorm)
  · exact Measure.integrable_toReal_rnDeriv.ofReal.bdd_mul
      htest.aestronglyMeasurable
      (Filter.Eventually.of_forall htestNorm)

/-- Absolute continuity of the unweighted mismatch law implies absolute
continuity of every positive weighted component used by the RN construction. -/
theorem positiveRealWeightedMismatchPushforward_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Real) (hmismatch : Measurable mismatch)
    (hunweighted : Measure.map mismatch measure ≪ volume) :
    positiveRealWeightedMismatchPushforward measure mismatch weight ≪ volume := by
  exact ((withDensity_absolutelyContinuous measure
    (fun sample => ENNReal.ofReal (weight sample))).map hmismatch).trans hunweighted

/-- Main fixed-volume bridge.  It requires exactly a measurable mismatch, a
measurable integrable complex weight, and absolute continuity of the
*unweighted* mismatch pushforward.  The resulting density is the canonical
four-positive-part RN density above. -/
def weightedMismatchL1FourierCertificate_of_map_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) (hmismatch : Measurable mismatch)
    (hweightMeasurable : Measurable weight) (hweight : Integrable weight measure)
    (hunweighted : Measure.map mismatch measure ≪ volume) :
    WeightedMismatchL1FourierCertificate measure mismatch weight where
  density := weightedMismatchRNDensity measure mismatch weight
  density_integrable :=
    integrable_weightedMismatchRNDensity measure mismatch weight hweight
  expectation_eq := by
    intro time
    let test : Real -> Complex := fun value =>
      Complex.exp (Complex.I * ((time * value : Real) : Complex))
    have htest : Measurable test := by
      fun_prop
    have htestNorm : forall value, ‖test value‖ <= 1 := by
      intro value
      rw [Complex.norm_exp]
      simp
    have hrePositive :
        positiveRealWeightedMismatchPushforward measure mismatch
          (fun sample => (weight sample).re) ≪ volume :=
      positiveRealWeightedMismatchPushforward_absolutelyContinuous
        measure mismatch _ hmismatch hunweighted
    have hreNegative :
        positiveRealWeightedMismatchPushforward measure mismatch
          (fun sample => -(weight sample).re) ≪ volume :=
      positiveRealWeightedMismatchPushforward_absolutelyContinuous
        measure mismatch _ hmismatch hunweighted
    have himPositive :
        positiveRealWeightedMismatchPushforward measure mismatch
          (fun sample => (weight sample).im) ≪ volume :=
      positiveRealWeightedMismatchPushforward_absolutelyContinuous
        measure mismatch _ hmismatch hunweighted
    have himNegative :
        positiveRealWeightedMismatchPushforward measure mismatch
          (fun sample => -(weight sample).im) ≪ volume :=
      positiveRealWeightedMismatchPushforward_absolutelyContinuous
        measure mismatch _ hmismatch hunweighted
    have hre := integral_test_mul_real_eq_integral_realWeightedMismatchRNDensity
      measure mismatch (fun sample => (weight sample).re) test hmismatch
      hweightMeasurable.re hweight.re htest htestNorm hrePositive hreNegative
    have him := integral_test_mul_real_eq_integral_realWeightedMismatchRNDensity
      measure mismatch (fun sample => (weight sample).im) test hmismatch
      hweightMeasurable.im hweight.im htest htestNorm himPositive himNegative
    unfold weightedMismatchExpectation weightedMismatchOscillatoryIntegral
    change (∫ sample, test (mismatch sample) * weight sample ∂measure) =
      ∫ value, test value * weightedMismatchRNDensity measure mismatch weight value
    have hreIntegrable : Integrable
        (fun sample => test (mismatch sample) * ((weight sample).re : Complex))
        measure := by
      apply hweight.re.ofReal.bdd_mul
      · exact (htest.comp hmismatch).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun sample => htestNorm _)
    have himIntegrable : Integrable
        (fun sample => test (mismatch sample) * ((weight sample).im : Complex))
        measure := by
      apply hweight.im.ofReal.bdd_mul
      · exact (htest.comp hmismatch).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun sample => htestNorm _)
    have hreDensityIntegrable : Integrable
        (fun value => test value *
          (realWeightedMismatchRNDensity measure mismatch
            (fun sample => (weight sample).re) value : Complex)) := by
      apply (integrable_realWeightedMismatchRNDensity measure mismatch _
        hweight.re).ofReal.bdd_mul
      · exact htest.aestronglyMeasurable
      · exact Filter.Eventually.of_forall htestNorm
    have himDensityIntegrable : Integrable
        (fun value => test value *
          (realWeightedMismatchRNDensity measure mismatch
            (fun sample => (weight sample).im) value : Complex)) := by
      apply (integrable_realWeightedMismatchRNDensity measure mismatch _
        hweight.im).ofReal.bdd_mul
      · exact htest.aestronglyMeasurable
      · exact Filter.Eventually.of_forall htestNorm
    calc
      (∫ sample, test (mismatch sample) * weight sample ∂measure) =
          (∫ sample, test (mismatch sample) * ((weight sample).re : Complex) ∂measure) +
          (∫ sample, test (mismatch sample) * ((weight sample).im : Complex) ∂measure) *
            Complex.I := by
        rw [← integral_mul_const, ← integral_add hreIntegrable
          (himIntegrable.mul_const Complex.I)]
        apply integral_congr_ae
        filter_upwards with sample
        calc
          test (mismatch sample) * weight sample =
              test (mismatch sample) *
                (((weight sample).re : Complex) +
                  ((weight sample).im : Complex) * Complex.I) :=
            congrArg (fun value : Complex => test (mismatch sample) * value)
              (Complex.re_add_im (weight sample)).symm
          _ = _ := by ring
      _ = (∫ value, test value *
          (realWeightedMismatchRNDensity measure mismatch
            (fun sample => (weight sample).re) value : Complex)) +
          (∫ value, test value *
          (realWeightedMismatchRNDensity measure mismatch
            (fun sample => (weight sample).im) value : Complex)) * Complex.I := by
        rw [hre, him]
      _ = ∫ value, test value *
          weightedMismatchRNDensity measure mismatch weight value := by
        rw [← integral_mul_const, ← integral_add hreDensityIntegrable
          (himDensityIntegrable.mul_const Complex.I)]
        apply integral_congr_ae
        filter_upwards with value
        simp only [weightedMismatchRNDensity]
        ring

/-- A domination estimate by a scalar multiple of Lebesgue measure is a
direct quantitative-looking input for the same qualitative certificate.  No
bound on the resulting `L1` norm is claimed here. -/
def weightedMismatchL1FourierCertificate_of_map_le_smul_volume
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) (hmismatch : Measurable mismatch)
    (hweightMeasurable : Measurable weight) (hweight : Integrable weight measure)
    (constant : ENNReal)
    (hunweighted : Measure.map mismatch measure <=
      constant • (volume : Measure Real)) :
    WeightedMismatchL1FourierCertificate measure mismatch weight := by
  apply weightedMismatchL1FourierCertificate_of_map_absolutelyContinuous
    measure mismatch weight hmismatch hweightMeasurable hweight
  exact hunweighted.absolutelyContinuous.trans Measure.smul_absolutelyContinuous

end

end ArchonPhysics.WeightedMismatchL1RadonNikodymCertificate
