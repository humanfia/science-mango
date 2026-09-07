import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeArbitraryPairE2FirstHitOwnerFubiniV3
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval

namespace FamilyStickyCinematicL32PyzActualNormFirstHighOwnerFubiniV5

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedNormLocalizedPointSourceV1
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32ActualProjectedShadingCriticalFamilyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitraryPairE2FirstHitOwnerFubiniV3
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairE2FirstHitOwnerCapProducerV2
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# The actual owner-Fubini sum at one native high centre

The native high data already contains every scalar and curve hypothesis used
to build the spatial paper-fine datum.  We reconstruct that datum, apply the
arbitrary-pair owner theorem to every separated centre pair, and retain the
resulting sum before any pair-cardinality envelope.

The endpoint is still not a cross-pair packing theorem.  Its last finite sum
is exactly the remaining owner-sharing quantity.
-/

/-- At one actual high centre, the pre-max first-hit pair mass and hence the
high-base degree-gap term are bounded by a sum of realized per-pair owner
envelopes. -/
theorem exists_nativeHighCenter_actualOwnerEnvelopeSum
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    let H := D.chosenHighPayloadAt c
    let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
    let N := positiveCenterHighPayloadGlobalNormData H
    let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
      D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
        D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
          (36 * D.globalScale) D.tangencyExponent
    exists ownerEnvelopeAt : iota × iota -> ENNReal,
      nativeHighPreMaxFirstHitCenterPairMass D G c <=
        ∑ pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N (G.ballRadius c))
          (fun _ _ => True), ownerEnvelopeAt pair ∧
      (forall pair, pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N (G.ballRadius c))
          (fun _ _ => True) ->
        actualGPrimeWeightedCommonFineCenterMass N R (fun _ _ => True)
            (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
            pair.1 pair.2 <= ownerEnvelopeAt pair) ∧
      (forall pair, pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N (G.ballRadius c))
          (fun _ _ => True) ->
        (actualGPrimeCommonFineCenterLabels
          N R (fun _ _ => True) pair.1 pair.2).Nonempty ->
        exists r, r ∈ actualGPrimeCommonFineCenterLabels
            N R (fun _ _ => True) pair.1 pair.2 ∧
          exists O : ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
            D.S.family N R (fun _ _ => True) pair (G.ballRadius c)
              (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
              D.f D.outerA D.outerB globalDelta D.globalScale,
            ownerEnvelopeAt pair =
              actualGPrimeArbitraryPairOwnerEnvelope D.S.family N R
                H.payload.finalLabel (fun _ _ => True) pair.1 pair.2
                  (G.ballRadius c) O.omega D.f D.outerA D.outerB globalDelta
                    D.globalScale O.package) ∧
      (forall pair, pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N (G.ballRadius c))
          (fun _ _ => True) ->
        ¬(actualGPrimeCommonFineCenterLabels
          N R (fun _ _ => True) pair.1 pair.2).Nonempty ->
        ownerEnvelopeAt pair = 0) ∧
      volume (D.highBase c) * nativeHighConcreteDegreeGap D G c <=
        actualAllCenterPostNormBinLoss radius D.globalScale
            D.physical.ambient.card *
          ∑ pair ∈ richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N (G.ballRadius c))
            (fun _ _ => True), ownerEnvelopeAt pair := by
  dsimp only
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let source := actualCenteredHalfPaperFineE2 E_t hEt D.S.family D.physical
    H.payload.finalLabel D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf
      D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
        D.tangencyExponent globalDelta
  let Y1 := actualCenteredHalfPaperFineY1 E_t hEt D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 (36 * D.globalScale) D.tangencyExponent globalDelta
  let patternAt := D.physical.activeAtPoint
  let fineLabels : Finset
      (ActualCenteredHalfPaperFineE2SpatialLabel E_t hEt D.S.family
        D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2 D.outerA
          D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
            (36 * D.globalScale) D.tangencyExponent globalDelta) :=
    Finset.univ
  let pointAt := spatialActivePatternRepresentative D.physical.ambient
    patternAt source (G.mesh c)
  let tubeAt := actualCenteredHalfPaperFineTubeAt D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 (36 * D.globalScale) D.tangencyExponent
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta D.globalScale
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, _hEtSubset, _hbin, _hE2Pos,
      _hE2Measurable, _hE2Subset, hactivePayload⟩ := H.payload.certificate
  have hactive : forall q, q ∈ source -> (Y1.activeAtPoint q).Nonempty := by
    intro q hqSource
    have hqPositive : q ∈ positiveCenterE2 (D.highBase c)
        (D.highBase_measurable c) D.S.family D.physical D.f D.f1 D.f2
          D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
            D.tangencyExponent H.payload.tangencyLabel
              H.payload.finalLabel := by
      simpa only [source, Y1, actualCenteredHalfPaperFineE2,
        actualCenteredHalfPaperFineY1, positiveCenterE2, positiveCenterY1,
        positiveCenterTangencyCell, E_t, hEt, globalDelta] using hqSource
    obtain ⟨i, hi⟩ := hactivePayload q hqPositive
    refine ⟨i, ?_⟩
    simpa only [Y1, actualCenteredHalfPaperFineY1, positiveCenterY1,
      positiveCenterTangencyCell, E_t, hEt, globalDelta] using hi
  have hambientCBucket : forall i, i ∈ D.ambient ->
      forall j, j ∈ D.ambient ->
        |tubeGraphC (D.S.family.tubes i) -
          tubeGraphC (D.S.family.tubes j)| <= (radius : Real) / 2 := by
    intro i hi j hj
    exact abs_projectedTubeGraphC_sub_le_of_bucket_eq
      (div_pos (by exact_mod_cast D.hradius) (by norm_num))
      ((G.hbucket i hi).trans (G.hbucket j hj).symm)
  have hlocalized : forall q, q ∈ source ->
      (finiteIncidenceNormLocalizedFamilyValue
        (actualProjectedAmbientCriticalFamily D.S.family D.physical.ambient)
        projectedTubePairCoefficientDistance D.globalScale c.1.1
        (D.physical.activeAtPoint q)).Nonempty := by
    intro q hqSource
    apply positiveCenterPayload_E2_localizedFamily_nonempty H.payload q
    simpa only [source, actualCenteredHalfPaperFineE2,
      actualCenteredHalfPaperFineY1, positiveCenterE2, positiveCenterY1,
      positiveCenterTangencyCell, E_t, hEt, globalDelta] using hqSource
  have hglobalCenter : c.1.1 ∈ finiteMetricCoverCenters
      (activeTubeImage D.S.family D.ambient)
      projectedTubePairCoefficientDistance D.globalScale
      (fun T U => projectedTubePairCoefficientDistance_comm T U) :=
    (Finset.mem_filter.mp c.1.2).1
  have pointSourceRaw :=
    actualCenteredHalfPointRectangleSource_of_outerSixteenthPhysical
      D.S.family D.ambient D.physicalBase D.hphysicalBase D.f
        D.hfContinuous D.outerA D.outerB D.f1 D.f2 D.hOuter D.hf D.hf1
          D.globalScale D.hglobalScale c.1.1 hglobalCenter
            (36 * D.globalScale) D.tangencyExponent source hlocalized
              hambientCBucket
  have pointSource : ActualCenteredHalfPointRectangleSource source c.1.1
      tubeAt D.f D.outerA D.outerB D.globalScale := by
    simpa only [NativeBranchCore.physical, nativePhysical, tubeAt,
      actualProjectedNormFirstSixteenthPhysicalShading,
      actualProjectedNormFirstOuterSixteenthPhysicalShading,
      actualCenteredHalfPaperFineTubeAt] using pointSourceRaw
  have hdeltaThreshold : (radius : Real) <= globalDelta := by
    simpa only [globalDelta] using
      positiveCenterHighPayload_radius_le_tangencyUpper H
  have factsRaw := actualCenteredHalfY1ActiveGeometryFacts E_t hEt
    D.S.family D.ambient D.physicalBase D.hphysicalBase D.f D.f1 D.f2
      D.hfContinuous D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 (36 * D.globalScale) D.tangencyExponent globalDelta source
          hambientCBucket hdeltaThreshold
  have facts : ActualCenteredHalfY1ActiveGeometryFacts D.S.family D.physical
      source Y1.activeAtPoint tubeAt D.f D.f1 D.f2 D.outerA D.outerB
        D.hOuter D.hf D.hf1 D.globalScale globalDelta := by
    simpa only [NativeBranchCore.physical, nativePhysical, Y1, tubeAt,
      actualProjectedNormFirstSixteenthPhysicalShading,
      actualProjectedNormFirstOuterSixteenthPhysicalShading,
      actualCenteredHalfPaperFineY1,
      actualCenteredHalfPaperFineTubeAt] using factsRaw
  have hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ source := by
    intro r _hr
    exact (spatialActivePatternRepresentative_spec D.physical.ambient
      patternAt source (G.mesh c) r).1
  have hDpaper : R = y1FineCoarseRectangleData D.S.family Y1 fineLabels
      pointAt tubeAt D.f D.f1 D.f2 D.hf D.hf1 (radius : Real) fineT
        globalDelta D.globalScale := by rfl
  have hDfine : R.fine = D.S.family := by rfl
  have hNfamily : N.family =
      actualGlobalNormIndexFamily D.S.family D.physical D.globalScale c.1.1 :=
    rfl
  have hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (R.fine.tubes i) (R.fine.tubes j) := by
    intro i j
    rfl
  have hsymm : forall x y, N.distance x y = N.distance y x := by
    intro x y
    rw [hdistance x y, hdistance y x]
    exact projectedTubePairCoefficientDistance_comm _ _
  have htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y := by
    intro x center y
    rw [hdistance x y, hdistance x center, hdistance center y]
    exact projectedTubePairCoefficientDistance_triangle _ _ _
  obtain ⟨ownerEnvelopeAt, howner, hrealized, hzero, htotal⟩ :=
    exists_actualGPrimeCenterPairOwnerEnvelopeSum
      D.S.family D.physical source Y1 fineLabels pointAt c.1.1 tubeAt
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          globalDelta facts pointSource hpointE (G.sharp c) G.hparameter
            G.hft G.hf1Lower G.hf1Upper G.hf2 G.hf2Continuous N R hDpaper
              H.payload.finalLabel (fun _ _ => True) (G.ballRadius c) hsymm
                htriangle (G.hballRadiusLower c) (G.hballRadiusUpper c)
                  hdistance (G.hsmall c) (G.hcount c) hDfine hNfamily
  have hpre : nativeHighPreMaxFirstHitCenterPairMass D G c <=
      ∑ pair ∈ richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N (G.ballRadius c))
        (fun _ _ => True), ownerEnvelopeAt pair := by
    simpa only [nativeHighPreMaxFirstHitCenterPairMass, H, E_t, hEt,
      globalDelta, N, R] using htotal
  refine ⟨ownerEnvelopeAt, hpre, howner, hrealized, hzero, ?_⟩
  calc
    volume (D.highBase c) * nativeHighConcreteDegreeGap D G c <=
        actualAllCenterPostNormBinLoss radius D.globalScale
            D.physical.ambient.card *
          nativeHighPreMaxFirstHitCenterPairMass D G c :=
      highBase_mul_degreeGap_le_binLoss_mul_preMaxFirstHitCenterPairMass
        D G c h
    _ <= actualAllCenterPostNormBinLoss radius D.globalScale
            D.physical.ambient.card *
          ∑ pair ∈ richSeparatedCenterPairs N.family
            (canonicalTenRadiusSeparated N (G.ballRadius c))
            (fun _ _ => True), ownerEnvelopeAt pair :=
      mul_le_mul' le_rfl hpre

#print axioms exists_nativeHighCenter_actualOwnerEnvelopeSum

end

end FamilyStickyCinematicL32PyzActualNormFirstHighOwnerFubiniV5
