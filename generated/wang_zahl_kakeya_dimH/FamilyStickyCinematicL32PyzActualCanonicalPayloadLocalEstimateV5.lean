import FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
import FamilyStickyCinematicL32PyzActualPositiveCenterLowMomentUniformV5

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
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
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualPositiveCenterLowMomentUniformV5

noncomputable section

def actualCanonicalPayloadGlobalWeight (lower : Nat)
    (globalScale normExponent tangencyExponent : Real) : ENNReal :=
  (ENNReal.ofReal ((lower : Real) *
    (16 : Real) ^ (-normExponent) *
    (36 * globalScale) ^ (-tangencyExponent))) ^ (3 / 2 : Real)

def actualCanonicalPayloadUniformMomentCost (radius : NNReal)
    (multiplicity logCount : Nat) (normExponent tangencyExponent alpha : Real)
    (C : ENNReal) : ENNReal :=
  (ENNReal.ofReal ((multiplicity : Real) * 2 *
    (2 ^ normExponent * 2 ^ tangencyExponent) *
    (radius : Real) ^ (-normExponent) *
    (radius : Real) ^ (-tangencyExponent))) ^ (3 / 2 : Real) *
  (((48 * logCount : Nat) : ENNReal) ^ (1 / 2 : Real) *
    ((C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha *
      (ENNReal.ofReal (radius : Real)) ^ (2 - alpha)))

def actualCanonicalPayloadCommonCost (radius : NNReal)
    (globalScale : Real) (ambientCard multiplicity logCount : Nat)
    (normExponent tangencyExponent alpha : Real) (C : ENNReal) : ENNReal :=
  actualAllCenterPostNormBinLoss radius globalScale ambientCard *
    actualCanonicalPayloadUniformMomentCost radius multiplicity logCount
      normExponent tangencyExponent alpha C

/-! A canonical two-stage payload supplies the retained positive cell, its
tangency-bin bounds, and its active-set witness.  Applying the centre-uniform
low moment to that literal cell and then composing the retained measure gives
the exact local three-ball estimate. -/
theorem actualCanonicalPayload_localEstimate
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
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hbaseBand : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      base ⊆ physical.multiplicityBand lower upper)
    (payload : ActualPositiveCenterCanonicalPayload volume base hbase S.family
      (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB)
      f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
      tangencyExponent)
    (hpair : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      Set.Pairwise (physical.activeAtPoint payload.q : Set iota)
        (fun i j ↦ EssentiallyDistinct (S.family.tubes i) (S.family.tubes j)))
    (hactiveCap : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      ∀ center, center ∈ actualProjectedCriticalFamily S.family
          (physical.activeAtPoint payload.q) →
        (activeNearCoefficientIndices S.family
          (physical.activeAtPoint payload.q) center
          (radius : Real)).card ≤ multiplicity)
    (hfamily : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      (actualProjectedAmbientCriticalFamily S.family physical.ambient
        (physical.activeAtPoint payload.q)).Nonempty)
    (hnormBallSubset : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      let family := actualProjectedAmbientCriticalFamily S.family
        physical.ambient (physical.activeAtPoint payload.q)
      finiteNormCriticalBall family projectedTubePairCoefficientDistance
          (radius : Real) 16 normExponent hfamily ⊆
        finiteIncidenceNormLocalizedFamilyValue
          (actualProjectedAmbientCriticalFamily S.family physical.ambient)
          projectedTubePairCoefficientDistance globalScale globalCenter
          (physical.activeAtPoint payload.q))
    (hnormScaleLower : let physical :=
        (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
          physicalBase hphysicalBase f hfContinuous outerA outerB)
      (radius : Real) / 2 <
        actualProjectedAmbientNormScale S.family physical 16 normExponent
          payload.q)
    (hlow : pyzE2DegreeLower payload.finalLabel < 24 * logCount) :
    actualCanonicalPayloadGlobalWeight lower globalScale normExponent
        tangencyExponent * volume base ≤
      actualCanonicalPayloadCommonCost radius globalScale ambient.card
          multiplicity logCount normExponent tangencyExponent alpha C *
        ((actualProjectedNormThreeBallIndices S.family ambient globalScale
          globalCenter).card : ENNReal) := by
  let physical := actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  let E_t := positiveCenterTangencyCell base S.family physical f f1 f2
    outerA outerB hOuter hf hf1 globalScale globalCenter tangencyExponent
    payload.tangencyLabel
  have hEtMeasurable : MeasurableSet E_t := by
    exact measurableSet_continuumCriticalSingleDyadicCell hbase
      (measurable_actualProjectedCenteredHalfLocalizedTangencyScale S.family
        physical f f1 f2 outerA outerB hOuter hf hf1 globalScale globalCenter
        (36 * globalScale) tangencyExponent) payload.tangencyLabel
  rcases payload.certificate with ⟨_hfinalLabel, hq, hbaseMeasure,
    _hEtPos, hEtSubset, htangencyBin, _hE2Pos, _hE2Measurable,
    hE2Subset, hactive⟩
  have hqEt : payload.q ∈ E_t := by
    exact hE2Subset hq
  have htangencyUpper := (htangencyBin payload.q hqEt).2
  have hlabelLower := (Finset.mem_Icc.mp payload.tangencyLabel_mem).1
  have hphysicalToLabel : (radius : Real) ≤
      dyadicCeilUpper payload.tangencyLabel := by
    have hphysicalToBucket :=
      (dyadicCeilUpper_half_lt_and_le (by exact_mod_cast hradius)).2
    have hbucketMono :
        dyadicCeilUpper (dyadicCeilBucket (radius : Real)) ≤
          dyadicCeilUpper payload.tangencyLabel := by
      unfold dyadicCeilUpper
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by exact_mod_cast hlabelLower)
    exact hphysicalToBucket.trans hbucketMono
  have htangencyLower : (radius : Real) / 2 <
      positiveCenterTangencyScale S.family physical f f1 f2 outerA outerB
        hOuter hf hf1 globalScale globalCenter tangencyExponent payload.q := by
    have hbinLower := (htangencyBin payload.q hqEt).1
    linarith
  have hmoment :=
    actual_WZL3_lowMultiplicity_localized_bandLower_physicalRadius_endpoint
      Q S ambient hambient hunit physicalBase hphysicalBase E_t hEtMeasurable
      (hEtSubset.trans hbaseSubset) f hfContinuous f1 f2 outerA outerB hOuter
      hf hf1 hparameter halpha halphaOne hfun hfun1 globalScale globalCenter
      normExponent tangencyExponent (dyadicCeilUpper payload.tangencyLabel)
      payload.finalLabel logCount payload.q lower upper multiplicity hradius
      hradiusSixteen hradiusTangency hnormExponent htangencyExponent
      (hEtSubset.trans hbaseBand) hpair hactiveCap hfamily hnormBallSubset
      htangencyUpper hactive hq hnormScaleLower htangencyLower hlow
  have hmomentAligned := hmoment
  simp only [
    FamilyStickyCinematicL32PyzActualCenteredHalfY1CarrierStripCleanV1.actualProjectedNormFirstSixteenthCenteredHalfY1,
    E_t, physical] at hmomentAligned
  change actualCanonicalPayloadGlobalWeight lower globalScale normExponent
      tangencyExponent * volume base ≤ _
  calc
    actualCanonicalPayloadGlobalWeight lower globalScale normExponent
        tangencyExponent * volume base ≤
      actualCanonicalPayloadGlobalWeight lower globalScale normExponent
          tangencyExponent *
        (actualAllCenterPostNormBinLoss radius globalScale ambient.card *
          volume (positiveCenterE2 base hbase S.family physical f f1 f2
            outerA outerB hOuter hf hf1 globalScale globalCenter
            tangencyExponent payload.tangencyLabel payload.finalLabel)) :=
      mul_le_mul_right hbaseMeasure _
    _ = actualAllCenterPostNormBinLoss radius globalScale ambient.card *
        (actualCanonicalPayloadGlobalWeight lower globalScale normExponent
          tangencyExponent *
          volume (positiveCenterE2 base hbase S.family physical f f1 f2
            outerA outerB hOuter hf hf1 globalScale globalCenter
            tangencyExponent payload.tangencyLabel payload.finalLabel)) := by
      ac_rfl
    _ ≤ actualAllCenterPostNormBinLoss radius globalScale ambient.card *
        (actualCanonicalPayloadUniformMomentCost radius multiplicity logCount
          normExponent tangencyExponent alpha C *
          ((actualProjectedNormThreeBallIndices S.family ambient globalScale
            globalCenter).card : ENNReal)) := by
      apply mul_le_mul_right
      calc
        actualCanonicalPayloadGlobalWeight lower globalScale normExponent
            tangencyExponent *
            volume (positiveCenterE2 base hbase S.family physical f f1 f2
              outerA outerB hOuter hf hf1 globalScale globalCenter
              tangencyExponent payload.tangencyLabel payload.finalLabel) ≤
            _ := hmomentAligned
        _ = actualCanonicalPayloadUniformMomentCost radius multiplicity
              logCount normExponent tangencyExponent alpha C *
            ((actualProjectedNormThreeBallIndices S.family ambient
              globalScale globalCenter).card : ENNReal) := by
          unfold actualCanonicalPayloadUniformMomentCost
          ac_rfl
    _ = actualCanonicalPayloadCommonCost radius globalScale ambient.card
          multiplicity logCount normExponent tangencyExponent alpha C *
        ((actualProjectedNormThreeBallIndices S.family ambient globalScale
          globalCenter).card : ENNReal) := by
      unfold actualCanonicalPayloadCommonCost
      ac_rfl

#print axioms actualCanonicalPayload_localEstimate

end

end FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
