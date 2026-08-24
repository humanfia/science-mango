import FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
import FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
import FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteIncidenceNormGlobalCoverCellV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
open FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual norm-first all-centre rich-payload dichotomy

The primitive extremal data produce all distinctness and coefficient-cap
facts.  The norm selector then retains the exact measurable partition, and
the two later dyadic selections are performed only in its positive cells.
The result is either an actual high-degree selected payload or a low-degree
payload in every positive cell.
-/

theorem exists_actualNormFirst_allCenterPayload_high_or_all_low
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real → Real) (hfContinuous : Continuous f)
    (f1 f2 : Real → Real) (outerA outerB : Real)
    (hOuter : outerA ≤ outerB)
    (hf : ∀ z, HasDerivAt f (f1 z) z)
    (hf1 : ∀ z, HasDerivAt f1 (f2 z) z)
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
    (hsourcePos : 0 < volume
      ((actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand lower upper))
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
      0 < volume E_norm ∧ E_norm.Nonempty ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < globalScale ∧ (radius : Real) ≤ globalScale ∧
      (∀ x ∈ E_norm,
        globalScale / 2 < normScale x ∧ normScale x ≤ globalScale) ∧
      ∃ fallback : FiniteMetricMember
          (activeTubeImage S.family physical.ambient),
        let centers := finiteMetricCoverCenters
          (activeTubeImage S.family physical.ambient)
          projectedTubePairCoefficientDistance globalScale
          (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
        let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
          (fun i x ↦ x ∈ physical.carrier i)
          (activeTubeImage S.family physical.ambient) fallback
          (actualProjectedAmbientCriticalFamily S.family physical.ambient)
          projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
          globalScale
          (fun T U ↦ projectedTubePairCoefficientDistance_comm T U)
        let cell := fun center ↦ measurableLabelCell E_norm label center
        ∃ hcellData : ∀ center, center ∈ centers →
          MeasurableSet (cell center) ∧ cell center ⊆ E_norm ∧
          ∀ x, x ∈ cell center →
            let active := physical.activeAtPoint x
            let localFamily := actualProjectedAmbientCriticalFamily S.family
              physical.ambient active
            ∃ hlocalFamily : localFamily.Nonempty,
              let localBall := finiteNormCriticalBall localFamily
                projectedTubePairCoefficientDistance (radius : Real) 16
                normExponent hlocalFamily
              let localized := finiteIncidenceNormLocalizedFamilyValue
                (actualProjectedAmbientCriticalFamily S.family
                  physical.ambient)
                projectedTubePairCoefficientDistance globalScale center active
              localBall ⊆ localized ∧ localBall.card ≤ localized.card,
          volume E_norm = ∑ center ∈ centers, volume (cell center) ∧
          (∀ x ∈ E_norm, label x ∈ centers) ∧
          let hcellMeasurable := fun center hcenter ↦
            (hcellData center hcenter).1
          ((∃ center, ∃ hcenter : center ∈ centers,
              0 < volume (cell center) ∧
              ∃ payload : ActualPositiveCenterCanonicalPayload volume
                  (cell center) (hcellMeasurable center hcenter) S.family
                  physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
                  center tangencyExponent,
                24 * logCount ≤ pyzE2DegreeLower payload.finalLabel) ∨
            (∀ center, ∀ hcenter : center ∈ centers,
              0 < volume (cell center) →
              ∃ payload : ActualPositiveCenterCanonicalPayload volume
                  (cell center) (hcellMeasurable center hcenter) S.family
                  physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
                  center tangencyExponent,
                pyzE2DegreeLower payload.finalLabel < 24 * logCount)) := by
  dsimp only
  let physical := actualProjectedNormFirstSixteenthPhysicalShading S.family
    ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  obtain ⟨hambientPairwise, hbandPairwise, hactiveCap⟩ :=
    actualNormFirst_public_inputs_of_extremal_bucket S ambient hambient
      physicalBase hphysicalBase f hfContinuous outerA outerB G bucket hbucket
      hloss
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormNonempty,
      hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
      hnormBin, fallback, hpartition, hlabelRange, hcellData⟩ :=
    exists_actualProjectedNormFirst_allCenterCells volume S.family physical
      16 normExponent hradius hradiusSixteen hsourcePos hmultiplicity hlower
      hbandPairwise hactiveCap
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
  have hcellMeasurable : ∀ center, center ∈ centers →
      MeasurableSet (cell center) := fun center hcenter ↦
    (hcellData center hcenter).1
  have hradiusTangency : (radius : Real) ≤ 36 * globalScale := by
    have hscale36 : globalScale ≤ 36 * globalScale := by nlinarith
    exact hradiusGlobalScale.trans hscale36
  have hlocalized : ∀ center, center ∈ centers → ∀ x, x ∈ cell center →
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily S.family physical.ambient)
        projectedTubePairCoefficientDistance globalScale center
        (physical.activeAtPoint x)).Nonempty := by
    intro center hcenter x hx
    obtain ⟨hlocalFamily, hballSubset, _hcard⟩ :=
      (hcellData center hcenter).2.2 x hx
    have hballNonempty := finiteNormCriticalBall_nonempty
      (exponent := normExponent) (actualProjectedAmbientCriticalFamily S.family physical.ambient
        (physical.activeAtPoint x))
      projectedTubePairCoefficientDistance hlocalFamily
      (fun T _hT ↦ by
        rw [projectedTubePairCoefficientDistance_self]
        exact_mod_cast hradius.le)
      hradiusSixteen
    exact hballNonempty.mono hballSubset
  have hdichotomy := actualAllCenter_canonicalPayload_high_or_all_low
    volume S.family physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
    centers cell tangencyExponent logCount hradius hradiusTangency
    hcellMeasurable hlocalized
  refine ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormNonempty,
    hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
    hnormBin, fallback, hcellData, ?_, ?_, ?_⟩
  · simpa only [physical, normScale, E_norm, globalScale, centers, label,
      cell] using hpartition
  · simpa only [physical, normScale, E_norm, globalScale, centers, label,
      cell] using hlabelRange
  · simpa only [physical, normScale, E_norm, globalScale, centers, label,
      cell, hcellMeasurable] using hdichotomy

#print axioms exists_actualNormFirst_allCenterPayload_high_or_all_low

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
