import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCThirdStageVerticesNonemptyV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverFixedCCodePackingV1
open FamilyStickyCinematicL32Prop41ActualY1GridRightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCMassPartitionV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFiniteOccupiedCodeCurvatureDataV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedRightCLocalCoverFixedCCodePackingAdapterV2
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

/-!
# Nonempty third-stage candidates on an occupied exact-C fibre

An occupied outer C fibre contains an item.  Its canonical source-cover code
therefore gives an occupied raw code fibre.  The local two-stage outcome keeps
at least one selected pivot from every nonempty raw fibre, so the tagged union
of selected pivots is nonempty.
-/

/-- Package-free last step: one nonempty raw code fibre makes the tagged union
of local selected sets nonempty. -/
theorem codeSelectedCandidates_finiteOccupiedCodeLocalCompactSelectedAt_nonempty_of_exists_raw
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound)
    (hraw : ∃ k, (rawAt k).Nonempty) :
    (codeSelectedCandidates (Finset.univ : Finset code)
      (finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
        localCenterAt globalCenter codeBound weightAt G)).Nonempty := by
  rcases hraw with ⟨k, hk⟩
  have hselected :=
    (finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G k).selected_nonempty hk
  rcases hselected with ⟨a, ha⟩
  refine ⟨⟨k, a⟩, ?_⟩
  exact (mem_codeSelectedCandidates_iff (Finset.univ : Finset code)
    (finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G) ⟨k, a⟩).2
        ⟨Finset.mem_univ k, ha⟩


section Actual

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
variable {fine : UniformTubeFamily radius iota}
variable {N : CanonicalNormNonconcentrationData iota}
variable {D : CoarseRectangleIncidenceData (point := Real × Real)
  (radius := radius) (iota := iota) fineLabel}
variable {keep : iota -> fineLabel -> Prop} {left right : iota}
variable {ballRadius : Real}
variable {omega : (N.family -> Fin 1) × (N.family -> Fin 1)}
variable {labelWeight : fineLabel -> ENNReal}
variable {f : Real -> Real} {outerA outerB globalDelta tGlobal : Real}
variable (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
  fine N D keep left right ballRadius omega labelWeight f outerA outerB
    globalDelta tGlobal)
variable (pointAt : fineLabel -> Real × Real)
variable (tubeAt : Real × Real -> Tube radius)

/-- Every occupied outer C has at least one occupied source-code raw fibre. -/
theorem exists_actualGPrimeThreeShiftCGridWeighted_fixedCCode_rawAt_nonempty
    (c : Real)
    (hc : c ∈ actualGPrimeThreeShiftCGridWeightedOccupiedCValues P) :
    ∃ k : ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c,
      (actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c k).Nonempty := by
  have hc' : c ∈ actualThreeShiftCGridRestrictedOccupiedValues P.gridSelection
      P.selected (actualGPrimeThreeShiftCGridWeightedFinalTraceShift P) := by
    simpa only [actualGPrimeThreeShiftCGridWeightedOccupiedCValues] using hc
  rcases actualThreeShiftCGridRestrictedFiber_nonempty P.gridSelection hc' with
    ⟨a, ha⟩
  have haSelected : a ∈ P.selected :=
    actualThreeShiftCGridRestrictedFiber_subset P.gridSelection P.selected
      (actualGPrimeThreeShiftCGridWeightedFinalTraceShift P) c ha
  let b : ActualY1GridRightCLocalCoverSelectedItem P.selected :=
    ⟨a, haSelected⟩
  let coverCenter : Tube radius :=
    actualY1GridRightCLocalCoverCode P.selected
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      pointAt tubeAt ballRadius b
  have haData := (mem_finiteValueFiber_iff P.selected
    (actualThreeShiftCGridRestrictedValueAt P.gridSelection
      (actualGPrimeThreeShiftCGridWeightedFinalTraceShift P)) c a).mp ha
  have hright : tubeGraphC
        (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
          ballRadius omega P.gridLabel a) = c := by
    rw [P.rightTube_eq_restricted]
    exact (actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
      P.gridSelection P.selected_subset_grid
        (actualGPrimeThreeShiftCGridWeightedFinalTraceShift P) haSelected).trans
          haData.2
  have hvalue : (c, coverCenter) ∈
      actualY1GridRightCLocalCoverValues P.selected
        (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
        (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
          ballRadius omega P.gridLabel)
        pointAt tubeAt ballRadius := by
    rw [actualY1GridRightCLocalCoverValues, mem_finiteOccupiedValues_iff]
    refine ⟨b, Finset.mem_univ b, ?_⟩
    apply Prod.ext
    · simpa only [actualY1GridRightCLocalCoverValue, b] using hright
    · rfl
  have hcoverCenter : coverCenter ∈
      actualGPrimeThreeShiftCGridRightCLocalCoverSourceCodesAtC fine N D keep
        left right ballRadius omega labelWeight f outerA outerB globalDelta
          tGlobal P pointAt tubeAt c := by
    exact (mem_actualY1GridRightCLocalCoverSourceCodesAtC_iff P.selected
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
        ballRadius omega P.gridLabel)
      pointAt tubeAt ballRadius c coverCenter).2 hvalue
  let k : ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
      ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
        pointAt tubeAt c := ⟨coverCenter, hcoverCenter⟩
  refine ⟨k, ?_⟩
  have hraw := actualY1GridRightCLocalCoverUnderlyingFiber_nonempty P.selected
    (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
    (actualGPrimeLabelFirstThreeShiftCGridRightTube N D keep left right
      ballRadius omega P.gridLabel)
    pointAt tubeAt ballRadius (c, coverCenter) hvalue
  simpa only [actualGPrimeThreeShiftCGridFixedCRawAt, k] using hraw

/-- The exact `hvertices` interface required by the V2 sampled-lens theorem. -/
theorem actualGPrimeThreeShiftCGridWeighted_codeSelectedCandidates_nonempty
    (c : Real)
    (hc : c ∈ actualGPrimeThreeShiftCGridWeightedOccupiedCValues P)
    (rectangleAt : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt :
      ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal)
    (weightAt :
      ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c ->
      ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData
      (actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c)
      rectangleAt domain localCenterAt globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap externalRatio
          codeBound) :
    (codeSelectedCandidates
      (Finset.univ : Finset
        (ActualGPrimeThreeShiftCGridFixedCCode fine N D keep left right
          ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
            pointAt tubeAt c))
      (finiteOccupiedCodeLocalCompactSelectedAt
        (actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
          ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
            pointAt tubeAt c)
        rectangleAt domain localCenterAt globalCenter codeBound weightAt G)).Nonempty := by
  apply
    codeSelectedCandidates_finiteOccupiedCodeLocalCompactSelectedAt_nonempty_of_exists_raw
      (actualGPrimeThreeShiftCGridFixedCRawAt fine N D keep left right
        ballRadius omega labelWeight f outerA outerB globalDelta tGlobal P
          pointAt tubeAt c)
      rectangleAt domain localCenterAt globalCenter codeBound weightAt G
  exact exists_actualGPrimeThreeShiftCGridWeighted_fixedCCode_rawAt_nonempty
    P pointAt tubeAt c hc

#print axioms codeSelectedCandidates_finiteOccupiedCodeLocalCompactSelectedAt_nonempty_of_exists_raw
#print axioms exists_actualGPrimeThreeShiftCGridWeighted_fixedCCode_rawAt_nonempty
#print axioms actualGPrimeThreeShiftCGridWeighted_codeSelectedCandidates_nonempty

end Actual

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedExactCThirdStageVerticesNonemptyV2
