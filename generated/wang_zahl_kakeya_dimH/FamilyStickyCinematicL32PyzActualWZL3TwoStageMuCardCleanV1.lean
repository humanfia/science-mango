import FamilyStickyCinematicL32PyzActualTwoStageMuCardV1
import FamilyStickyCinematicL32WZL3FixedVerticalChartAdapterV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzActualWZL3TwoStageMuCardCleanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57IndexedCoefficientDedupV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32WZL3FixedVerticalChartAdapterV1
open FamilyStickyCinematicL32PyzActualTwoStageMuCardV1

noncomputable section

/-!
# Actual two-stage card transport from an original `L_3` source

This is the faithful source-level wrapper around the already closed
two-stage card chain.  The later PYZ stage no longer receives a free chart
hypothesis: it only receives the ordinary statement that its ambient indices
came from the original finite `L_3` source.
-/

theorem active_twoStage_weighted_card_le_degreeLower_of_WZL3Source
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (hambient : physical.ambient ⊆ S.source)
    (hunit : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (f f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (hparameter : ∀ z, z ∈ Icc outerA outerB → |z| ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    (globalScale : Real) (globalCenter : Tube radius)
    (normExponent tangencyExponent tangencyThreshold : Real)
    (label : Int) (q : Real × Real) (multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hpair : Set.Pairwise (physical.activeAtPoint q : Set iota) fun i j =>
      EssentiallyDistinct (S.family.tubes i) (S.family.tubes j))
    (hactiveCap : ∀ center,
      center ∈ actualProjectedCriticalFamily S.family
        (physical.activeAtPoint q) →
      (activeNearCoefficientIndices S.family (physical.activeAtPoint q) center
        (radius : Real)).card ≤ multiplicity)
    (hfamily : (actualProjectedAmbientCriticalFamily S.family physical.ambient
      (physical.activeAtPoint q)).Nonempty)
    (hnormBallSubset :
      finiteNormCriticalBall
        (actualProjectedAmbientCriticalFamily S.family physical.ambient
          (physical.activeAtPoint q))
        projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
        hfamily ⊆
      finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily S.family physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q))
    (htangencyScaleUpper :
      actualProjectedCenteredHalfLocalizedTangencyScale S.family physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent q ≤ tangencyThreshold)
    (hq : q ∈ projectedPositiveMultiplicityDyadicCell
      (actualProjectedCenteredHalfTangencyY1 base hbase S.family physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold) label)
    (hY1active :
      ((actualProjectedCenteredHalfTangencyY1 base hbase S.family physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold).activeAtPoint
          q).Nonempty) :
    let active := physical.activeAtPoint q
    let sourceFamily := actualProjectedAmbientCriticalFamily S.family
      physical.ambient active
    let localized := finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily S.family physical.ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter active
    let hlocalized : localized.Nonempty :=
      (finiteNormCriticalBall_nonempty sourceFamily
        projectedTubePairCoefficientDistance hfamily
        (fun T _hT => by
          rw [projectedTubePairCoefficientDistance_self]
          exact_mod_cast hradius.le)
        hradiusSixteen).mono hnormBallSubset
    let normScale := finiteCriticalMaximizerScale sourceFamily
      projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
      hfamily
    let tangencyScale := finiteCriticalMaximizerScale localized
      (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
        hOuter hf hf1 active)
      (radius : Real) (36 * globalScale) tangencyExponent hlocalized
    (active.card : Real) * (16 : Real) ^ (-normExponent) *
        (36 * globalScale) ^ (-tangencyExponent) ≤
      (multiplicity : Real) *
        ((2 * pyzE2DegreeLower label : Nat) : Real) *
        normScale ^ (-normExponent) * tangencyScale ^ (-tangencyExponent) := by
  exact active_twoStage_weighted_card_le_degreeLower base hbase S.family
    physical S.source
    (ambient_subset_fixedVerticalChartIndices S physical.ambient hambient)
    hunit f f1 f2 outerA outerB hOuter hf hf1 hparameter hfun hfun1
    globalScale globalCenter normExponent tangencyExponent tangencyThreshold
    label q multiplicity hradius hradiusSixteen hradiusTangency hnormExponent
    htangencyExponent hpair hactiveCap hfamily hnormBallSubset
    htangencyScaleUpper hq hY1active

end
end FamilyStickyCinematicL32PyzActualWZL3TwoStageMuCardCleanV1
