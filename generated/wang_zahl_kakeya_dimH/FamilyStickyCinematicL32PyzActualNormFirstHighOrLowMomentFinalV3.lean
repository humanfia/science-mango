import FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
import FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
import FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
import FamilyStickyCinematicL32PyzActualWeightedPositiveCenterOverlapV1
import FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstHighOrLowMomentFinalV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1
open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32PyzActualCanonicalPayloadLocalEstimateV5
open FamilyStickyCinematicL32PyzActualWeightedPositiveCenterOverlapV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
open FamilyStickyCinematicL32ActualProjectedContinuumCriticalCellBoundsV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Public actual high/low endpoint at the selected norm scale

All cover cells are retained.  In the low branch the selected rich payload
in each positive cell is fed to the local three-ball estimate, and indexed
bounded overlap removes the number of cover centres.  The high branch keeps
an actual payload and its positive measurable source cell.
-/

theorem exists_actualNormFirst_highPayload_or_lowMoment
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {E : Set (Real × Real)} {alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound (radius : Real) alpha C))
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (hunit : ∀ i, i ∈ ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
    (hparameter : ∀ z, z ∈ Icc outerA outerB → |z| ≤ 1)
    (halpha : 0 ≤ alpha) (halphaOne : alpha ≤ 1)
    (hfun : ∀ z, z ∈ Icc outerA outerB → |f z| ≤ 2)
    (hfun1 : ∀ z, z ∈ Icc outerA outerB → |f1 z| ≤ 2)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ ambient →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    (normExponent tangencyExponent : Real)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) ≤ 16)
    (hnormExponent : 0 ≤ normExponent)
    (htangencyExponent : 0 ≤ tangencyExponent)
    (hsourcePos : 0 < volume
      ((actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand lower upper))
    (hbandSubsetE :
      (actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand lower upper ⊆ E)
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity ≤ lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss ≤
      multiplicity) :
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      S.family ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    ∃ normLabel ∈ Finset.Icc (dyadicCeilBucket (radius : Real))
        (dyadicCeilBucket 16),
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      let globalScale := dyadicCeilUpper normLabel
      volume (physical.multiplicityBand lower upper) /
          (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
            ENNReal) ≤ volume E_norm ∧
      0 < volume E_norm ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < globalScale ∧ (radius : Real) ≤ globalScale ∧ globalScale ≤ 32 ∧
      ((∃ globalCenter : Tube radius, ∃ base : Set (Real × Real),
          ∃ hbase : MeasurableSet base,
          0 < volume base ∧ base ⊆ E_norm ∧
          ∃ payload : ActualPositiveCenterCanonicalPayload volume base hbase
              S.family physical f f1 f2 outerA outerB hOuter hf hf1
              globalScale globalCenter tangencyExponent,
            24 * logCount ≤ pyzE2DegreeLower payload.finalLabel) ∨
        actualCanonicalPayloadGlobalWeight lower globalScale normExponent
            tangencyExponent * volume E_norm ≤
          actualCanonicalPayloadCommonCost radius globalScale ambient.card
              multiplicity logCount normExponent tangencyExponent alpha C *
            ((19 ^ 3 * ambient.card : Nat) : ENNReal)) := by
  dsimp only
  let physical := actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  have hphysicalAmbient : physical.ambient = ambient := rfl
  obtain ⟨hambientPairwise, hbandPairwise, hactiveCap⟩ :=
    actualNormFirst_public_inputs_of_extremal_bucket (lower := lower)
      (upper := upper) S ambient hambient
      physicalBase hphysicalBase f hfContinuous outerA outerB G bucket hbucket
      hloss
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, _hnormNonempty,
      hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
      hnormBin, fallback, hcellData, hpartition, _hlabelRange,
      hdichotomy⟩ :=
    exists_actualNormFirst_allCenterPayload_high_or_all_low S ambient hambient
      physicalBase hphysicalBase f hfContinuous f1 f2 outerA outerB hOuter hf
      hf1 G bucket hbucket normExponent tangencyExponent logCount lower upper
      multiplicity hradius hradiusSixteen hsourcePos hmultiplicity hlower hloss
  let normScale := actualProjectedAmbientNormScale S.family physical 16
    normExponent
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) normScale normLabel
  let globalScale := dyadicCeilUpper normLabel
  let centers := finiteMetricCoverCenters
    (activeTubeImage S.family physical.ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
  let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
    (fun i x ↦ x ∈ physical.carrier i)
    (activeTubeImage S.family physical.ambient) fallback
    (actualProjectedAmbientCriticalFamily S.family physical.ambient)
    projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
    globalScale (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
  let cell := fun center ↦ measurableLabelCell E_norm label center
  have hglobalScaleUpper : globalScale ≤ 32 := by
    have hbounds := dyadicCeilUpper_bounds_of_mem_Icc
      (by exact_mod_cast hradius) hradiusSixteen hnormLabel
    norm_num at hbounds ⊢
    exact hbounds.2
  have hradiusTangency : (radius : Real) ≤ 36 * globalScale := by
    have hscale36 : globalScale ≤ 36 * globalScale := by nlinarith
    exact hradiusGlobalScale.trans hscale36
  refine ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormMeasurable,
    hnormSubset, hglobalScale, hradiusGlobalScale, hglobalScaleUpper, ?_⟩
  rcases hdichotomy with hhigh | hlow
  · rcases hhigh with ⟨center, hcenter, hcellPos, payload, hdegree⟩
    exact Or.inl ⟨center, cell center, (hcellData center hcenter).1,
      hcellPos, (hcellData center hcenter).2.1, payload, hdegree⟩
  · apply Or.inr
    have hpositiveCell : ∀ center, center ∈ centers →
        0 < volume (cell center) →
        actualCanonicalPayloadGlobalWeight lower globalScale normExponent
              tangencyExponent * volume (cell center) ≤
          actualCanonicalPayloadCommonCost radius globalScale ambient.card
              multiplicity logCount normExponent tangencyExponent alpha C *
            ((actualProjectedNormThreeBallIndices S.family physical.ambient globalScale
              center).card : ENNReal) := by
      intro center hcenter hcellPos
      obtain ⟨payload, hpayloadLow⟩ := hlow center hcenter hcellPos
      rcases payload.certificate with ⟨_hfinalLabel, hq, _hbaseMeasure,
        _hEtPos, hEtSubset, _htangencyBin, _hE2Pos, _hE2Measurable,
        hE2Subset, _hactive⟩
      have hqCell : payload.q ∈ cell center := hEtSubset (hE2Subset hq)
      have hqNorm : payload.q ∈ E_norm :=
        (hcellData center hcenter).2.1 hqCell
      have hqBand : payload.q ∈ physical.multiplicityBand lower upper :=
        hnormSubset hqNorm
      obtain ⟨hfamily, hnormBallSubset, _hlocalCard⟩ :=
        (hcellData center hcenter).2.2 payload.q hqCell
      have hnormScaleLower : (radius : Real) / 2 <
          actualProjectedAmbientNormScale S.family physical 16 normExponent
            payload.q := by
        have hbinLower := (hnormBin payload.q hqNorm).1
        linarith
      have hlocal := actualCanonicalPayload_localEstimate Q S ambient hambient
        hunit physicalBase hphysicalBase (cell center)
        (hcellData center hcenter).1
        ((hcellData center hcenter).2.1.trans
          (hnormSubset.trans hbandSubsetE))
        f hfContinuous f1 f2 outerA outerB hOuter hf hf1 hparameter halpha
        halphaOne hfun hfun1 globalScale center normExponent tangencyExponent
        logCount lower upper multiplicity hradius hradiusSixteen
        hradiusTangency hnormExponent htangencyExponent
        ((hcellData center hcenter).2.1.trans hnormSubset) payload
        (hbandPairwise payload.q hqBand) (hactiveCap payload.q hqBand)
        hfamily hnormBallSubset hnormScaleLower hpayloadLow
      simpa only [physical, normScale, E_norm, globalScale, centers, label,
        cell, hphysicalAmbient] using hlocal
    have haggregate := actual_weighted_positiveCenter_overlap volume E_norm
      S.family physical.ambient hradius
      (by simpa only [hphysicalAmbient] using hambientPairwise)
      hglobalScale cell
      (actualCanonicalPayloadGlobalWeight lower globalScale normExponent
        tangencyExponent)
      (actualCanonicalPayloadCommonCost radius globalScale ambient.card
        multiplicity logCount normExponent tangencyExponent alpha C)
      (by simpa only [physical, normScale, E_norm, globalScale, centers,
        label, cell] using hpartition)
      (by
        intro center hcenter hpositive
        exact hpositiveCell center (by simpa only [centers] using hcenter)
          hpositive)
    simpa only [physical, normScale, E_norm, globalScale, centers, label,
      cell, hphysicalAmbient] using haggregate

#print axioms exists_actualNormFirst_highPayload_or_lowMoment

end

end FamilyStickyCinematicL32PyzActualNormFirstHighOrLowMomentFinalV3
