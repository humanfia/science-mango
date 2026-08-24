import FamilyStickyCinematicL32PyzActualWZL3LowMultiplicityLocalizedScaleEndpointV1
import FamilyStickyCinematicL32PyzMultiplicityBandWeightedMomentV1
import FamilyStickyCinematicL32PyzActualMultiplicityBandPointTransportExactV1
import FamilyStickyCinematicL32PyzActualLocalScaleUniformityV1
import FamilyStickyCinematicL32ActualProjectedCriticalScaleValueBridgesV1

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualPositiveCenterLowMomentUniformV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfTangencyStageV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
open FamilyStickyCinematicL32PyzActualWZL3LowMultiplicityLocalizedScaleEndpointV1
open FamilyStickyCinematicL32PyzMultiplicityBandWeightedMomentV1
open FamilyStickyCinematicL32PyzActualMultiplicityBandPointTransportExactV1
open FamilyStickyCinematicL32PyzActualLocalScaleUniformityV1
open FamilyStickyCinematicL32ActualProjectedCriticalScaleValueBridgesV1

noncomputable section

/-!
# Centre-uniform low moment with a local three-ball cardinality

Starting from the localized WZL3 endpoint preserves the exact local
three-ball index count.  Physical-band membership replaces the selected
active cardinality by the band's lower endpoint.  The two half-bin lower
bounds then remove both centre-dependent critical scales.
-/

theorem actual_WZL3_lowMultiplicity_localized_bandLower_physicalRadius_endpoint
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
    (halpha : 0 ≤ alpha) (halphaOne : alpha ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    (globalScale : Real) (globalCenter : Tube radius)
    (normExponent tangencyExponent tangencyThreshold : Real)
    (label : Int) (logCount : Nat) (q : Real × Real)
    (lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hbaseBand : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      base ⊆ physical.multiplicityBand lower upper)
    (hpair : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      Set.Pairwise (physical.activeAtPoint q : Set iota) fun i j ↦
        EssentiallyDistinct (S.family.tubes i) (S.family.tubes j))
    (hactiveCap : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      ∀ center, center ∈ actualProjectedCriticalFamily S.family
          (physical.activeAtPoint q) →
        (activeNearCoefficientIndices S.family (physical.activeAtPoint q)
          center (radius : Real)).card ≤ multiplicity)
    (hfamily : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      (actualProjectedAmbientCriticalFamily S.family physical.ambient
        (physical.activeAtPoint q)).Nonempty)
    (hnormBallSubset : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
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
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      actualProjectedCenteredHalfLocalizedTangencyScale S.family physical
        f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent q ≤ tangencyThreshold)
    (hactive : let Z :=
        (FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1
          S.family ambient physicalBase hphysicalBase base hbase f hfContinuous
          f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
          (36 * globalScale) tangencyExponent tangencyThreshold)
      ∀ x, x ∈ projectedPositiveMultiplicityDyadicCell Z label →
        (Z.activeAtPoint x).Nonempty)
    (hq : let Z :=
        (FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1
          S.family ambient physicalBase hphysicalBase base hbase f hfContinuous
          f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
          (36 * globalScale) tangencyExponent tangencyThreshold)
      q ∈ projectedPositiveMultiplicityDyadicCell Z label)
    (hnormScaleLower : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      (radius : Real) / 2 <
        actualProjectedAmbientNormScale S.family physical 16 normExponent q)
    (htangencyScaleLower : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      (radius : Real) / 2 <
        actualProjectedCenteredHalfLocalizedTangencyScale S.family physical
          f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
          (36 * globalScale) tangencyExponent q)
    (hlow : pyzE2DegreeLower label < 24 * logCount) :
    let Z :=
      (FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1
        S.family ambient physicalBase hphysicalBase base hbase f hfContinuous
        f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent tangencyThreshold)
    (ENNReal.ofReal ((lower : Real) *
        (16 : Real) ^ (-normExponent) *
        (36 * globalScale) ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
        volume (projectedPositiveMultiplicityDyadicCell Z label) ≤
      (ENNReal.ofReal ((multiplicity : Real) * 2 *
        (2 ^ normExponent * 2 ^ tangencyExponent) *
        (radius : Real) ^ (-normExponent) *
        (radius : Real) ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
      (((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
        (((actualProjectedNormThreeBallIndices S.family ambient globalScale
            globalCenter).card : ENNReal) *
          ((C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha *
            (ENNReal.ofReal (radius : Real)) ^ (2 - alpha)))) := by
  have hmain :=
    actual_WZL3_lowMultiplicity_localized_weighted_active_scale_endpoint
      Q S ambient hambient hunit physicalBase hphysicalBase base hbase
      hbaseSubset f hfContinuous f1 f2 outerA outerB hOuter hf hf1
      hparameter halpha halphaOne hfun hfun1 globalScale globalCenter
      normExponent tangencyExponent tangencyThreshold label logCount q
      multiplicity hradius hradiusSixteen hradiusTangency hnormExponent
      htangencyExponent hpair hactiveCap hfamily hnormBallSubset
      htangencyScaleUpper hactive hq hlow
  have hqBand :=
    q_mem_actualPhysical_multiplicityBand_of_centeredHalfCell
      S.family ambient physicalBase hphysicalBase base hbase f hfContinuous
      f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent tangencyThreshold label q hbaseBand hq
  let physical := actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  let active := physical.activeAtPoint q
  let sourceFamily := actualProjectedAmbientCriticalFamily S.family
    physical.ambient active
  let localized := finiteIncidenceNormLocalizedFamilyValue
    (actualProjectedAmbientCriticalFamily S.family physical.ambient)
    projectedTubePairCoefficientDistance globalScale globalCenter active
  have hlocalized : localized.Nonempty := by
    have hballNonempty := finiteNormCriticalBall_nonempty (exponent := normExponent) sourceFamily
      projectedTubePairCoefficientDistance hfamily
      (fun T _hT ↦ by
        rw [projectedTubePairCoefficientDistance_self]
        exact_mod_cast hradius.le)
      hradiusSixteen
    exact hballNonempty.mono hnormBallSubset
  have hnormEq := actualProjectedAmbientNormScale_eq_finiteMaximizer
    S.family physical 16 normExponent q hfamily
  have htangencyEq :=
    actualProjectedCenteredHalfLocalizedTangencyScale_eq_finiteMaximizer
      S.family physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
      globalCenter (36 * globalScale) tangencyExponent q hlocalized
  dsimp only at hmain hqBand hnormScaleLower htangencyScaleLower ⊢
  have hglobalTangencyCeiling : 0 ≤ 36 * globalScale := by
    have hradiusNonneg : (0 : Real) ≤ (radius : Real) := by positivity
    exact hradiusNonneg.trans hradiusTangency
  have hband := multiplicityBand_lower_weighted_rpow_mul_le physical hqBand
    (Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 16) _)
    (Real.rpow_nonneg hglobalTangencyCeiling _) hmain
  rw [hnormEq] at hnormScaleLower
  rw [htangencyEq] at htangencyScaleLower
  exact moment_le_physical_radius_of_local_scales multiplicity
    (by exact_mod_cast hradius) hnormExponent htangencyExponent
    hnormScaleLower htangencyScaleLower hband

#print axioms
  actual_WZL3_lowMultiplicity_localized_bandLower_physicalRadius_endpoint

end

end FamilyStickyCinematicL32PyzActualPositiveCenterLowMomentUniformV5
