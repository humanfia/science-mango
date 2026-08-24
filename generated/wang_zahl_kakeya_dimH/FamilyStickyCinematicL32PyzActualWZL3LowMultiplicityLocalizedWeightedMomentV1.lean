import FamilyStickyCinematicL32PyzActualWZL3TwoStageMuCardCleanV1
import FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedMomentRunV1
import FamilyStickyCinematicL32PyzTwoStageMomentConnectorV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualWZL3LowMultiplicityLocalizedWeightedMomentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedMomentRunV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzActualWZL3TwoStageMuCardCleanV1
open FamilyStickyCinematicL32PyzTwoStageMomentConnectorV1

noncomputable section

/-!
# Faithful actual low-multiplicity weighted moment in the fixed WZ chart

At one literal point of the actual centered-half E2 cell, this theorem uses
the same norm and tangency critical scales in the two-stage cardinality
transport and in the E2 three-halves moment.  The fixed chart comes only from
the original WZ L3 source certificate; no projected-stage chart or comparison
ceiling is an input.  All remaining scale and logarithmic factors are kept
visible for the later numerical absorption corresponding to PYZ (5.24).
-/

theorem actual_WZL3_lowMultiplicity_localized_weighted_active_rpow_mul_E2Volume_le
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    {E : Set (Real × Real)} {alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound (radius : Real) alpha C))
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (hunit : ∀ i, i ∈ ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (hbaseSubset : base ⊆ E)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (hparameter : ∀ z, z ∈ Icc outerA outerB → |z| ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    (globalScale : Real) (globalCenter : Tube radius)
    (normExponent tangencyExponent tangencyThreshold : Real)
    (label : Int) (logCount : Nat) (q : Real × Real)
    (multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hpair : let physical :=
        (FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1.actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      Set.Pairwise (physical.activeAtPoint q : Set iota) fun i j =>
        EssentiallyDistinct (S.family.tubes i) (S.family.tubes j))
    (hactiveCap : let physical :=
        (FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1.actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      (∀ center, center ∈ actualProjectedCriticalFamily S.family
          (physical.activeAtPoint q) →
        (activeNearCoefficientIndices S.family (physical.activeAtPoint q)
          center (radius : Real)).card ≤ multiplicity))
    (hfamily : let physical :=
        (FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1.actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      (actualProjectedAmbientCriticalFamily S.family physical.ambient
        (physical.activeAtPoint q)).Nonempty)
    (hnormBallSubset : let physical :=
        (FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1.actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      let family := (actualProjectedAmbientCriticalFamily S.family
        physical.ambient (physical.activeAtPoint q))
      finiteNormCriticalBall family projectedTubePairCoefficientDistance
          (radius : Real) 16 normExponent hfamily ⊆
        finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily S.family physical.ambient)
          projectedTubePairCoefficientDistance globalScale globalCenter
          (physical.activeAtPoint q))
    (htangencyScaleUpper : let physical :=
        (FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1.actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      actualProjectedCenteredHalfLocalizedTangencyScale S.family physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent q ≤ tangencyThreshold)
    (hactive : let Z := (FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1
        S.family ambient physicalBase hphysicalBase base hbase f hfContinuous
        f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold)
      (∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
        (Z.activeAtPoint x).Nonempty))
    (hq : let Z := (FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1
        S.family ambient physicalBase hphysicalBase base hbase f hfContinuous
        f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold)
      q ∈ projectedPositiveMultiplicityDyadicCell Z label)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    let physical := (FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1.actualProjectedNormFirstSixteenthPhysicalShading S.family
      ambient physicalBase hphysicalBase f hfContinuous outerA outerB)
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
    let Z := (FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1 S.family ambient
      physicalBase hphysicalBase base hbase f hfContinuous f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter (36 * globalScale)
      tangencyExponent tangencyThreshold)
    (ENNReal.ofReal ((active.card : Real) *
        (16 : Real) ^ (-normExponent) *
        (36 * globalScale) ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
        volume (projectedPositiveMultiplicityDyadicCell Z label) ≤
      (ENNReal.ofReal ((multiplicity : Real) * 2 *
        normScale ^ (-normExponent) *
        tangencyScale ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
      (((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
        (((actualProjectedNormThreeBallIndices S.family ambient globalScale
            globalCenter).card : ENNReal) *
          pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C outerA
            outerB)) := by
  dsimp only at hpair hactiveCap hfamily hnormBallSubset
  dsimp only at htangencyScaleUpper hactive hq ⊢
  let physical := FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1.actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
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
  let Z := FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1 S.family ambient
    physicalBase hphysicalBase base hbase f hfContinuous f1 f2 outerA outerB
    hOuter hf hf1 globalScale globalCenter (36 * globalScale)
    tangencyExponent tangencyThreshold
  have hphysicalAmbient : physical.ambient = ambient := rfl
  have hambient' : physical.ambient ⊆ S.source := by
    simpa only [hphysicalAmbient] using hambient
  have hunit' : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
    simpa only [hphysicalAmbient] using hunit
  have hcard : (active.card : Real) * (16 : Real) ^ (-normExponent) *
        (36 * globalScale) ^ (-tangencyExponent) ≤
      (multiplicity : Real) *
        ((2 * pyzE2DegreeLower label : Nat) : Real) *
        normScale ^ (-normExponent) * tangencyScale ^ (-tangencyExponent) := by
    simpa only [physical, active, sourceFamily, localized, hlocalized,
      normScale, tangencyScale] using
      (active_twoStage_weighted_card_le_degreeLower_of_WZL3Source S
        base hbase physical hambient' hunit' f f1 f2 outerA outerB hOuter hf
        hf1 hparameter hfun hfun1 globalScale globalCenter normExponent
        tangencyExponent tangencyThreshold label q multiplicity hradius
        hradiusSixteen hradiusTangency hnormExponent htangencyExponent hpair
        hactiveCap hfamily hnormBallSubset htangencyScaleUpper hq
        (hactive q hq))
  have hmoment : (pyzE2DegreeLower label : ENNReal) ^ (3 / 2 : Real) *
        volume (projectedPositiveMultiplicityDyadicCell Z label) ≤
      ((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
        (((actualProjectedNormThreeBallIndices S.family ambient globalScale
            globalCenter).card : ENNReal) *
          pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C outerA
            outerB) := by
    simpa only [Z] using
      (actual_centeredHalf_lowMultiplicity_localized_degreeLower_rpow_mul_E2Volume_le
        Q S.family ambient physicalBase hphysicalBase base hbase hbaseSubset f
        hfContinuous f1 f2 outerA outerB hOuter hf hf1 globalScale
        globalCenter (36 * globalScale) tangencyExponent tangencyThreshold
        label logCount hactive hlow)
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
  exact twoStage_card_to_threeHalf_moment
    (Real.rpow_nonneg hnormScaleNonneg _)
    (Real.rpow_nonneg htangencyScaleNonneg _) hcard hmoment

end
end FamilyStickyCinematicL32PyzActualWZL3LowMultiplicityLocalizedWeightedMomentV1
