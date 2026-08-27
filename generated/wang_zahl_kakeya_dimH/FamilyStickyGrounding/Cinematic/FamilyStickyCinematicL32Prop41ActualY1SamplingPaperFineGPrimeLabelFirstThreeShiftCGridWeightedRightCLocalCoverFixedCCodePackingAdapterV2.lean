import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverTwoCenterBridgeV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFixedCCodePackingAdapterV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverTwoCenterBridgeV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41GlobalScaleNearFiberPackingV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-- Exact source-cover code set inside one literal normalized-C fibre of the
actual shifted-grid package. -/
noncomputable def actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2 fine N D
      keep left right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real) :
    Finset (Tube radius) :=
  actualY1GridRightCLocalCoverSourceCodesAtC P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel)
    pointAt tubeAt ballRadius c

/-- Actual fixed-C source-cover code packing cap.  The code family is built
from source tubes, while the C filter uses the final normalized right tubes. -/
theorem actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC_card_lt_packingCap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal : Real)
    (pointSource : ActualCenteredHalfPointRectangleSource E globalCenter
      tubeAt f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (fineDelta fineScale coarseDelta coarseScale : Real)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (hballRadius : 0 < ballRadius)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal)
    (globalDelta : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2 fine N D
      keep left right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal)
    (hpositive : 0 < ballRadius + 6 * tGlobal) (c : Real) :
    (actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC fine N D keep
      left right ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
        pointAt tubeAt c).card <
      projectedCoefficientPackingCap ballRadius
        (2 * (ballRadius + 6 * tGlobal)) := by
  have hsource :
      forall a : ActualY1GridRightCLocalCoverSelectedItem P.selected,
        tubePairCoefficientDistance
          (actualY1GridRightCLocalCoverSourceTube P.selected
            (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
            pointAt tubeAt a) globalCenter <= 6 * tGlobal := by
    intro a
    exact
      actualGPrimeThreeShiftCGridRightCLocalCoverSourceTube_distance_globalCenter_le
        fine E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2 outerA
          outerB hfDeriv hf1Deriv tGlobal pointSource hpointE fineDelta
            fineScale coarseDelta coarseScale N D hD keep left right
              ballRadius omega labelWeight globalDelta P a
  simpa only [actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC] using
    actualY1GridRightCLocalCoverSourceCodesAtC_card_lt_packingCap_six_mul
      P.selected
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega P.gridLabel)
      pointAt tubeAt ballRadius hballRadius globalCenter tGlobal hsource
        hpositive c

#print axioms actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC_card_lt_packingCap

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFixedCCodePackingAdapterV2
