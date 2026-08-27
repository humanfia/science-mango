import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedWideSourceFirstHitOwnerCapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FirstHitOwnerCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedWideSourceFirstHitOwnerCapV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

noncomputable section

universe u v w

/-!
# E2 specialization of the weighted wide-source owner cap

The source is the literal positive-multiplicity dyadic cell.  Consequently
the weight in this theorem is definitionally the same weight produced by the
weighted E2-to-G-prime sampling connector.
-/

theorem actualGPrimeThreeShiftCGridWeightedE2_clusterWeightAt_le_wideSourceArea
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    {code : Type w} [Fintype code] [DecidableEq code]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (fineT coarseDelta coarseT : Real)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real) fineT coarseDelta coarseT)
    (e2Label : Int)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep left right ballRadius omega
        (actualGPrimeE2FirstHitLabelWeight D e2Label)
        f outerA outerB globalDelta tGlobal)
    (hOuter : outerA <= outerB)
    (rawAt : code -> Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega))
    (hrawSubset : forall k, rawAt k ⊆ P.selected)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    (referenceScale comparisonLambda curvatureRatio centerGap
      externalRatio : Real)
    (codeBound : ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData
      rawAt
      (actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D keep left right
        ballRadius omega globalDelta tGlobal)
      (Icc outerA outerB) localCenterAt globalCenter
      (actualY1PaperFineCNormalizedChoiceLocalDelta
        (radius : Real) globalDelta tGlobal (4 * ballRadius))
      (4 * ballRadius) referenceScale comparisonLambda curvatureRatio
        centerGap externalRatio codeBound)
    (k : code)
    (pivot : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    finiteOccupiedCodeLocalCompactClusterWeightAt
        rawAt
        (actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D keep left
          right ballRadius omega globalDelta tGlobal)
        (Icc outerA outerB) localCenterAt globalCenter codeBound
        (fun _ a => actualGPrimeE2FirstHitLabelWeight D e2Label
          (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a))
        G k pivot <=
      ENNReal.ofReal
          (2 * ((radius : Real) + 6 * (4 * ballRadius))) *
        ENNReal.ofReal
          (Real.sqrt
              (pyzLemma312PackingLambda 100 *
                actualY1PaperFineCNormalizedChoiceLocalDelta
                  (radius : Real) globalDelta tGlobal (4 * ballRadius) /
                    (4 * ballRadius)) +
            Real.sqrt ((radius : Real) / fineT)) := by
  let source :=
    projectedPositiveMultiplicityDyadicCell D.shading e2Label
  have hsource : MeasurableSet source := by
    exact measurableSet_projectedPositiveMultiplicityDyadicCell
      D.shading e2Label
  have hweight : actualGPrimeWideSourceFirstHitLabelWeight D source =
      actualGPrimeE2FirstHitLabelWeight D e2Label := by
    rfl
  cases hweight
  have hcap :=
    actualGPrimeThreeShiftCGridWeighted_clusterWeightAt_le_wideSourceArea
      fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1 fineT coarseDelta
        coarseT N D hD keep left right ballRadius omega source hsource outerA
          outerB globalDelta tGlobal P hOuter rawAt
            (by
              intro k' i hi
              exact hrawSubset k' hi)
            localCenterAt globalCenter referenceScale comparisonLambda
              curvatureRatio centerGap externalRatio codeBound G k pivot
  exact hcap

#print axioms actualGPrimeThreeShiftCGridWeightedE2_clusterWeightAt_le_wideSourceArea

end

end FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedE2FirstHitOwnerCapV1
