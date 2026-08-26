import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
import FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32Prop41CanonicalMaximizerHighPayloadAdapterV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32ContinuumFiniteMeasurableBucketV1
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
open FamilyStickyCinematicL32ActualProjectedNormSingleDyadicSourceV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalPublicInputsV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32ActualProjectedNormFirstAllCenterCellsFinalV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Retaining canonical norm non-concentration in the actual high branch

The preceding all-centre producer already exports, for every point of every
norm-cover cell, the actual local norm family together with its critical ball.
This adapter evaluates that data at the selected payload point and retains the
canonical maximizer beside the high payload.  The only new scalar input is the
paper condition that the norm exponent is nonnegative.

No property of a later coarse family, and no width or breadth conclusion, is
asserted here.
-/

/-- The actual norm-first high/low dichotomy with the canonical norm
non-concentration data retained in its high branch. -/
theorem exists_actualNormFirst_allCenterPayloadWithNonconcentration_high_or_all_low
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (ambient : Finset iota) (hambient : ambient ⊆ S.source)
    (physicalBase : Set (Real × Real))
    (hphysicalBase : MeasurableSet physicalBase)
    (f : Real -> Real) (hfContinuous : Continuous f)
    (f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    {Y : Shading S.family.bodyFamily}
    {parallelLoss : Nat} {extremalEpsilon extremalSigma : Real}
    (G : EpsilonExtremalTubeFamily S.family Y ambient parallelLoss
      extremalEpsilon extremalSigma)
    (bucket : Int)
    (hbucket : forall i, i ∈ ambient ->
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    (normExponent tangencyExponent : Real)
    (hnormExponent : 0 <= normExponent)
    (logCount lower upper multiplicity : Nat)
    (hradius : 0 < radius)
    (hradiusSixteen : (radius : Real) <= 16)
    (hsourcePos : 0 < volume
      ((actualProjectedNormFirstSixteenthPhysicalShading S.family ambient
        physicalBase hphysicalBase f hfContinuous outerA outerB).multiplicityBand
          lower upper))
    (hmultiplicity : 0 < multiplicity)
    (hlower : 3 * multiplicity <= lower)
    (hloss : actualHalfScaleCoefficientCoverLoss * parallelLoss <=
      multiplicity) :
    let physical := actualProjectedNormFirstSixteenthPhysicalShading
      S.family ambient physicalBase hphysicalBase f hfContinuous outerA outerB
    let normScale := actualProjectedAmbientNormScale S.family physical 16
      normExponent
    exists normLabel, normLabel ∈
        Finset.Icc (dyadicCeilBucket (radius : Real))
          (dyadicCeilBucket 16) ∧
      let E_norm := continuumCriticalSingleDyadicCell
        (physical.multiplicityBand lower upper) normScale normLabel
      let globalScale := dyadicCeilUpper normLabel
      volume (physical.multiplicityBand lower upper) /
          (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 :
            ENNReal) <= volume E_norm ∧
      0 < volume E_norm ∧ E_norm.Nonempty ∧ MeasurableSet E_norm ∧
      E_norm ⊆ physical.multiplicityBand lower upper ∧
      0 < globalScale ∧ (radius : Real) <= globalScale ∧
      (forall x, x ∈ E_norm ->
        globalScale / 2 < normScale x ∧ normScale x <= globalScale) ∧
      exists fallback : FiniteMetricMember
          (activeTubeImage S.family physical.ambient),
        let centers := finiteMetricCoverCenters
          (activeTubeImage S.family physical.ambient)
          projectedTubePairCoefficientDistance globalScale
          (fun T U => projectedTubePairCoefficientDistance_comm T U)
        let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
          (fun i x => x ∈ physical.carrier i)
          (activeTubeImage S.family physical.ambient) fallback
          (actualProjectedAmbientCriticalFamily S.family physical.ambient)
          projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
          globalScale
          (fun T U => projectedTubePairCoefficientDistance_comm T U)
        let cell := fun center => measurableLabelCell E_norm label center
        exists hcellData : forall center, center ∈ centers ->
          MeasurableSet (cell center) ∧ cell center ⊆ E_norm ∧
          forall x, x ∈ cell center ->
            let active := physical.activeAtPoint x
            let localFamily := actualProjectedAmbientCriticalFamily S.family
              physical.ambient active
            exists hlocalFamily : localFamily.Nonempty,
              let localBall := finiteNormCriticalBall localFamily
                projectedTubePairCoefficientDistance (radius : Real) 16
                normExponent hlocalFamily
              let localized := finiteIncidenceNormLocalizedFamilyValue
                (actualProjectedAmbientCriticalFamily S.family
                  physical.ambient)
                projectedTubePairCoefficientDistance globalScale center active
              localBall ⊆ localized ∧ localBall.card <= localized.card,
          volume E_norm = ∑ center ∈ centers, volume (cell center) ∧
          (forall x, x ∈ E_norm -> label x ∈ centers) ∧
          let hcellMeasurable := fun center hcenter =>
            (hcellData center hcenter).1
          ((exists center, exists hcenter : center ∈ centers,
              0 < volume (cell center) ∧
              Nonempty
                (ActualHighPayloadWithNormNonconcentration volume
                  (cell center) (hcellMeasurable center hcenter) S.family
                  physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
                  center tangencyExponent normExponent logCount)) ∨
            (forall center, forall hcenter : center ∈ centers,
              0 < volume (cell center) ->
              exists payload : ActualPositiveCenterCanonicalPayload volume
                  (cell center) (hcellMeasurable center hcenter) S.family
                  physical f f1 f2 outerA outerB hOuter hf hf1 globalScale
                  center tangencyExponent,
                pyzE2DegreeLower payload.finalLabel < 24 * logCount)) := by
  dsimp only
  let physical := actualProjectedNormFirstSixteenthPhysicalShading
    S.family ambient physicalBase hphysicalBase f hfContinuous outerA outerB
  let normScale := actualProjectedAmbientNormScale S.family physical 16
    normExponent
  obtain ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormNonempty,
      hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
      hnormBin, fallback, hcellData, hpartition, hlabelRange, hdichotomy⟩ :=
    exists_actualNormFirst_allCenterPayload_high_or_all_low
      S ambient hambient physicalBase hphysicalBase f hfContinuous f1 f2
      outerA outerB hOuter hf hf1 G bucket hbucket normExponent
      tangencyExponent logCount lower upper multiplicity hradius
      hradiusSixteen hsourcePos hmultiplicity hlower hloss
  let E_norm := continuumCriticalSingleDyadicCell
    (physical.multiplicityBand lower upper) normScale normLabel
  let globalScale := dyadicCeilUpper normLabel
  let centers := finiteMetricCoverCenters
    (activeTubeImage S.family physical.ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun T U => projectedTubePairCoefficientDistance_comm T U)
  let label := finiteIncidenceNormGlobalCoverLabel physical.ambient
    (fun i x => x ∈ physical.carrier i)
    (activeTubeImage S.family physical.ambient) fallback
    (actualProjectedAmbientCriticalFamily S.family physical.ambient)
    projectedTubePairCoefficientDistance (radius : Real) 16 normExponent
    globalScale (fun T U => projectedTubePairCoefficientDistance_comm T U)
  let cell := fun center => measurableLabelCell E_norm label center
  let hcellMeasurable := fun center hcenter =>
    (hcellData center hcenter).1
  refine ⟨normLabel, hnormLabel, hnormMeasure, hnormPos, hnormNonempty,
    hnormMeasurable, hnormSubset, hglobalScale, hradiusGlobalScale,
    hnormBin, fallback, hcellData, hpartition, hlabelRange, ?_⟩
  rcases hdichotomy with hhigh | hlow
  · left
    obtain ⟨center, hcenter, hcellPos, payload, hdegree⟩ := hhigh
    refine ⟨center, hcenter, hcellPos, ?_⟩
    let retained := ActualHighPayloadWithNormNonconcentration.ofPayload
      payload hdegree hradius hradiusSixteen hnormExponent ?_
    · exact ⟨retained⟩
    · intro x hx
      obtain ⟨hlocalFamily, _hsubset, _hcard⟩ :=
        (hcellData center hcenter).2.2 x hx
      exact hlocalFamily
  · right
    exact hlow

#print axioms
  exists_actualNormFirst_allCenterPayloadWithNonconcentration_high_or_all_low

end

end FamilyStickyCinematicL32Prop41CanonicalMaximizerHighPayloadAdapterV1
