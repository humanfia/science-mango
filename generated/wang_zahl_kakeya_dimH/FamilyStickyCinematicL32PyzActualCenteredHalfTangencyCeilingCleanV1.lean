import FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
import FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32PyzActualCenteredHalfTangencyCeilingCleanV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

/-!
# Automatic centered-half tangency ceiling

Every member of the post-norm localized family lies in the literal
coefficient ball of radius `3 * globalScale` about the same centre.  The
triangle inequality therefore gives coefficient distance at most
`6 * globalScale` for every pair.  On the normalized outer interval, the
attained centered-half tangency is at most six times coefficient distance,
which produces the paper-compatible ceiling `36 * globalScale`.
-/

theorem actualProjectedCenteredHalfTangencyDistance_le_thirtySix_mul_globalScale
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient active : Finset iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hfDeriv : ∀ z, HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, HasDerivAt f1 (f2 z) z)
    (hparameter : ∀ z, z ∈ Icc outerA outerB → |z| ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    (globalScale : Real) (globalCenter : Tube radius)
    (T U : Tube radius)
    (hT : T ∈ finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter active)
    (hU : U ∈ finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter active) :
    actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
        hOuter hfDeriv hf1Deriv active T U ≤ 36 * globalScale := by
  have hTdata := hT
  simp only [finiteIncidenceNormLocalizedFamilyValue,
    finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
    Finset.mem_filter] at hTdata
  have hUdata := hU
  simp only [finiteIncidenceNormLocalizedFamilyValue,
    finiteGlobalNormLocalizedFamily, finiteFamilyMetricBall,
    Finset.mem_filter] at hUdata
  have hTcoefficient : tubePairCoefficientDistance T globalCenter ≤
      3 * globalScale := by
    change projectedTubePairCoefficientDistance T globalCenter ≤
      3 * globalScale
    exact hTdata.2
  have hUcoefficient : tubePairCoefficientDistance U globalCenter ≤
      3 * globalScale := by
    change projectedTubePairCoefficientDistance U globalCenter ≤
      3 * globalScale
    exact hUdata.2
  have hcoefficient : tubePairCoefficientDistance T U ≤ 6 * globalScale :=
    tubePairCoefficientDistance_le_six_mul_of_common_center T U globalCenter
      hTcoefficient hUcoefficient
  have htangency :=
    tubePairAttainedTangencyDistance_le_six_coefficientDistance T U
      f f1 f2
      (centeredFractionLeft outerA outerB (1 / 2 : Real))
      (centeredFractionRight outerA outerB (1 / 2 : Real))
      (centered_half_and_quarter_endpoints_ordered hOuter).1
      (fun z _hz => hfDeriv z) (fun z _hz => hf1Deriv z)
      (fun z hz => hparameter z (half_subset_whole hOuter hz))
      (fun z hz => hfun z (half_subset_whole hOuter hz))
      (fun z hz => hfun1 z (half_subset_whole hOuter hz))
  change tubePairAttainedTangencyDistance T U f f1 f2
      (centeredFractionLeft outerA outerB (1 / 2 : Real))
      (centeredFractionRight outerA outerB (1 / 2 : Real))
      (centered_half_and_quarter_endpoints_ordered hOuter).1
      (fun z _hz => hfDeriv z) (fun z _hz => hf1Deriv z) ≤
        36 * globalScale
  calc
    _ ≤ 6 * tubePairCoefficientDistance T U := htangency
    _ ≤ 6 * (6 * globalScale) :=
      mul_le_mul_of_nonneg_left hcoefficient (by norm_num)
    _ = 36 * globalScale := by ring

/-- Direct `hfull` producer for tangency critical-score retention, with no
free tangency-ceiling parameter. -/
theorem actualProjectedCenteredHalfLocalizedFamily_full_tangencyCeiling
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient active : Finset iota)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hfDeriv : ∀ z, HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, HasDerivAt f1 (f2 z) z)
    (hparameter : ∀ z, z ∈ Icc outerA outerB → |z| ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    (globalScale : Real) (globalCenter testCenter : Tube radius)
    (htestCenter : testCenter ∈ finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter active) :
    ∀ T, T ∈ finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter active →
      actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
        hOuter hfDeriv hf1Deriv active T testCenter ≤ 36 * globalScale := by
  intro T hT
  exact
    actualProjectedCenteredHalfTangencyDistance_le_thirtySix_mul_globalScale
      fine ambient active f f1 f2 outerA outerB hOuter hfDeriv hf1Deriv
      hparameter hfun hfun1 globalScale globalCenter T testCenter hT
      htestCenter

end
end FamilyStickyCinematicL32PyzActualCenteredHalfTangencyCeilingCleanV1
