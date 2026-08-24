import FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
import FamilyStickyCinematicL32PyzActualCenteredHalfAutomaticTangencyRetentionV1
import FamilyStickyCinematicL32PyzActualCenteredHalfRetainedDegreeLowerV1
import FamilyStickyCinematicL32PyzTwoStageWeightedCardChainCleanV1
import FamilyStickyCinematicL32Lemma57IndexedCoefficientDedupV1

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32PyzActualTwoStageMuCardV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Lemma57IndexedCoefficientDedupV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfRetainedTubeFamilyV1
open FamilyStickyCinematicL32PyzFixedVerticalChartSelectionCleanV1
open FamilyStickyCinematicL32PyzActualCenteredHalfAutomaticTangencyRetentionV1
open FamilyStickyCinematicL32PyzActualCenteredHalfRetainedDegreeLowerV1
open FamilyStickyCinematicL32PyzTwoStageWeightedCardChainCleanV1

noncomputable section

/-!
# Actual two-stage denominator-free μ-card transport

At one selected point this theorem composes the literal coefficient
deduplication, automatic fixed-chart norm retention with ceiling 16, the
existing norm-cover localization, automatic centered-half tangency retention
with ceiling 36t, and the E2 dyadic degree window.  The conclusion keeps every
scale weight explicit and introduces no division.
-/

theorem active_twoStage_weighted_card_le_degreeLower
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (chartSource : Finset iota)
    (hchart : physical.ambient ⊆
      fixedVerticalChartIndices fine chartSource)
    (hunit : ∀ i, i ∈ physical.ambient →
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
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
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (hactiveCap : ∀ center,
      center ∈ actualProjectedCriticalFamily fine
        (physical.activeAtPoint q) →
      (activeNearCoefficientIndices fine (physical.activeAtPoint q) center
        (radius : Real)).card ≤ multiplicity)
    (hfamily : (actualProjectedAmbientCriticalFamily fine physical.ambient
      (physical.activeAtPoint q)).Nonempty)
    (hnormBallSubset :
      finiteNormCriticalBall
        (actualProjectedAmbientCriticalFamily fine physical.ambient
          (physical.activeAtPoint q))
        projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
        hfamily ⊆
      finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily fine physical.ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter
        (physical.activeAtPoint q))
    (htangencyScaleUpper :
      actualProjectedCenteredHalfLocalizedTangencyScale fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent q ≤ tangencyThreshold)
    (hq : q ∈ projectedPositiveMultiplicityDyadicCell
      (actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold) label)
    (hY1active :
      ((actualProjectedCenteredHalfTangencyY1 base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold).activeAtPoint
          q).Nonempty) :
    let active := physical.activeAtPoint q
    let sourceFamily := actualProjectedAmbientCriticalFamily fine
      physical.ambient active
    let localized := finiteIncidenceNormLocalizedFamilyValue
      (actualProjectedAmbientCriticalFamily fine physical.ambient)
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
  dsimp only
  let active := physical.activeAtPoint q
  let sourceFamily := actualProjectedAmbientCriticalFamily fine
    physical.ambient active
  let normBall := finiteNormCriticalBall sourceFamily
    projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
    hfamily
  let localized := finiteIncidenceNormLocalizedFamilyValue
    (actualProjectedAmbientCriticalFamily fine physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter active
  have hnormBallNonempty : normBall.Nonempty := by
    exact finiteNormCriticalBall_nonempty sourceFamily
      projectedTubePairCoefficientDistance hfamily
      (fun T _hT => by
        rw [projectedTubePairCoefficientDistance_self]
        exact_mod_cast hradius.le)
      hradiusSixteen
  have hlocalized : localized.Nonempty := by
    apply hnormBallNonempty.mono
    simpa only [normBall, localized, sourceFamily, active] using
      hnormBallSubset
  let retained := actualProjectedCenteredHalfRetainedTubeFamily fine physical
    f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
    (36 * globalScale) tangencyExponent tangencyThreshold q
  let normScale := finiteCriticalMaximizerScale sourceFamily
    projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
    hfamily
  let tangencyScale := finiteCriticalMaximizerScale localized
    (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
      hOuter hf hf1 active)
    (radius : Real) (36 * globalScale) tangencyExponent hlocalized
  have hdedupNat : active.card ≤ multiplicity * sourceFamily.card := by
    dsimp only [active, sourceFamily]
    rw [actualProjectedAmbientCriticalFamily_eq_activeAtPoint fine physical q]
    exact active_card_le_multiplicity_mul_selectedTubes_card fine
      (physical.activeAtPoint q) hradius hpair multiplicity hactiveCap
  have hdedupReal : (active.card : Real) ≤
      (multiplicity : Real) * (sourceFamily.card : Real) := by
    exact_mod_cast hdedupNat
  have hnorm : (sourceFamily.card : Real) *
        (16 : Real) ^ (-normExponent) ≤
      (normBall.card : Real) * normScale ^ (-normExponent) := by
    simpa only [sourceFamily, active, normBall, normScale] using
      (ambientCriticalFamily_weighted_card_retention_of_fixedVerticalChart
        fine chartSource physical.ambient (physical.activeAtPoint q) hchart
        hfamily hunit hradius hradiusSixteen normExponent hnormExponent
        hfamily.choose hfamily.choose_spec)
  have hlocalizedCard : (normBall.card : Real) ≤
      (localized.card : Real) := by
    exact_mod_cast Finset.card_le_card
      (by simpa only [normBall, localized, sourceFamily, active] using
        hnormBallSubset)
  have htangency : (localized.card : Real) *
        (36 * globalScale) ^ (-tangencyExponent) ≤
      (retained.card : Real) * tangencyScale ^ (-tangencyExponent) := by
    simpa only [localized, retained, tangencyScale, active] using
      (centeredHalfLocalized_weighted_card_le_retained_thirtySix fine
        physical f f1 f2 outerA outerB hOuter hf hf1 hparameter hfun hfun1
        globalScale globalCenter tangencyExponent tangencyThreshold q
        hlocalized hradius hradiusTangency htangencyExponent
        htangencyScaleUpper)
  have hretainedNat : retained.card ≤ 2 * pyzE2DegreeLower label := by
    simpa only [retained] using
      (retained_card_le_two_mul_degreeLower base hbase fine physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold label q
        hlocalized hq hY1active)
  have hretainedReal : (retained.card : Real) ≤
      ((2 * pyzE2DegreeLower label : Nat) : Real) := by
    exact_mod_cast hretainedNat
  have hradiusNonneg : (0 : Real) ≤ (radius : Real) := by
    exact_mod_cast hradius.le
  have hnormScaleNonneg : 0 ≤ normScale := by
    exact hradiusNonneg.trans
      (finiteCriticalMaximizerScale_bounds sourceFamily
        projectedTubePairCoefficientDistance hfamily hradiusSixteen).1
  have htangencyScaleNonneg : 0 ≤ tangencyScale := by
    exact hradiusNonneg.trans
      (finiteCriticalMaximizerScale_bounds localized
        (actualProjectedCenteredHalfTangencyDistance f f1 f2 outerA outerB
          hOuter hf hf1 active) hlocalized hradiusTangency).1
  have hceilingNonneg : 0 ≤ 36 * globalScale :=
    hradiusNonneg.trans hradiusTangency
  have hchain := twoStage_weighted_card_chain
    (show 0 ≤ (multiplicity : Real) by positivity)
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg hnormScaleNonneg _)
    (Real.rpow_nonneg hceilingNonneg _)
    hdedupReal hnorm hlocalizedCard htangency
  calc
    (active.card : Real) * (16 : Real) ^ (-normExponent) *
        (36 * globalScale) ^ (-tangencyExponent) ≤
      (multiplicity : Real) * (retained.card : Real) *
        normScale ^ (-normExponent) * tangencyScale ^ (-tangencyExponent) :=
      hchain
    _ ≤ (multiplicity : Real) *
        ((2 * pyzE2DegreeLower label : Nat) : Real) *
        normScale ^ (-normExponent) * tangencyScale ^ (-tangencyExponent) := by
      gcongr

end
end FamilyStickyCinematicL32PyzActualTwoStageMuCardV1
