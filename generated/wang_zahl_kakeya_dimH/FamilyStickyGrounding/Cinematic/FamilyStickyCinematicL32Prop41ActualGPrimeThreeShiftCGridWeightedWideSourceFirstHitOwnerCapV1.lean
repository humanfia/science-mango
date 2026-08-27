import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWideSourceFirstHitGeometryV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedWideSourceFirstHitOwnerCapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteOccupiedCodeWideSourceFirstHitOwnerCapV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Lemma55FirstHitLabelWeightOwnerClusterCapV1
open FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWideSourceFirstHitGeometryV1
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
# Weighted actual wide-source owner-cluster cap

The selected carrier is the honest weighted V2 carrier.  The source weight is
defined once on the global fine-label first-hit partition and then pulled back
to every occupied code.  No conversion to the older cardinal package occurs.
-/

/-- The literal global first-hit weight used by both weighted sampling and
local occupied-code clustering. -/
noncomputable def actualGPrimeWideSourceFirstHitLabelWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (source : Set (Real × Real)) (r : fineLabel) : ENNReal :=
  volume (firstHitFineRectangleY2 source D.fineLabels D.fineRectangleAt
    (radius : Real) r)

/-- Actual specialization of the package-free wide-source cap.  The only
code-specific assumption is that each raw code fibre is contained in the
weighted V2 final carrier; all label, source-rectangle, and exact-local
interfaces are discharged here. -/
theorem actualGPrimeThreeShiftCGridWeighted_clusterWeightAt_le_wideSourceArea
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
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (source : Set (Real × Real)) (hsource : MeasurableSet source)
    (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep left right ballRadius omega
        (actualGPrimeWideSourceFirstHitLabelWeight D source)
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
        (fun _ a => actualGPrimeWideSourceFirstHitLabelWeight D source
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
  let labelAt : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> fineLabel :=
    actualGPrimeLabelFirstLabel N D keep left right ballRadius omega
  let rectangleAt :=
    actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D keep left right
      ballRadius omega globalDelta tGlobal
  apply finiteOccupiedCodeLocalCompactClusterWeightAt_le_wideSourceFirstHitArea
    rawAt rectangleAt (Icc outerA outerB) localCenterAt globalCenter codeBound
      source D.fineLabels D.fineRectangleAt labelAt
        (radius : Real) fineT G hsource
  · intro _k i _hi
    exact actualGPrimeLabelFirstLabel_mem_fineLabels
      N D keep left right ballRadius omega i
  · exact P.label_injective
  · intro _k i _hi
    exact actualPaperFineRectangle_length fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real) fineT coarseDelta coarseT D hD
        (labelAt i)
  · intro k' i hi
    exact perturbationReadyPairLocal_sourceBase_subset _ _ _ _ _ _ _ _ _ _
      hOuter (P.data i (hrawSubset k' hi))
  · intro _k i _hi
    exact actualGPrimeThreeShiftCGridLocalCompactRectangleAt_eq_exactLocal
      N D keep left right ballRadius omega globalDelta tGlobal i

#print axioms actualGPrimeWideSourceFirstHitLabelWeight
#print axioms actualGPrimeThreeShiftCGridWeighted_clusterWeightAt_le_wideSourceArea

end

end FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWeightedWideSourceFirstHitOwnerCapV1
