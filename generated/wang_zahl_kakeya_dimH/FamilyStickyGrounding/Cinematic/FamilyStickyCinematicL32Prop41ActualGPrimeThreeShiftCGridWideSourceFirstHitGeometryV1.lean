import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteOccupiedCodeWideSourceFirstHitOwnerCapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstLabelInjectivityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWideSourceFirstHitGeometryV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstLabelInjectivityV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRightCLocalCoverFiniteOccupiedCodeCurvatureDataV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridUniformPackageV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1

noncomputable section

universe u v

/-!
# Actual wide-source geometry fields

These lemmas discharge the non-clustering hypotheses of the package-free
wide-source owner cap.  In particular they keep the source paper-fine
rectangle separate from its exact-local restriction.
-/

/-- The actual paper-fine rectangle has its source (not local harmonic)
length. -/
theorem actualPaperFineRectangle_length
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (fineDelta fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 fineDelta fineT coarseDelta coarseT)
    (r : fineLabel) :
    (D.fineRectangleAt r).rectangle.right -
        (D.fineRectangleAt r).rectangle.left =
      Real.sqrt (fineDelta / fineT) := by
  subst D
  exact centeredTubeC2GraphRectangle_length
    (tubeAt (pointAt r)) f f1 f2 hf hf1 (pointAt r).2 fineDelta fineT

/-- A label-first survivor's literal label belongs to the source fine-label
carrier. -/
theorem actualGPrimeLabelFirstLabel_mem_fineLabels
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a ∈
      D.fineLabels := by
  exact ((mem_actualGPrimeBilateralRetainedFineLabels_iff
    N D keep left right ballRadius
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega a)).mp
        a.1.2).1

/-- The base containment used by the wide-source cap depends only on the
literal pair-local datum.  In particular it is independent of any cardinal
or weighted sampling package. -/
theorem perturbationReadyPairLocal_sourceBase_subset
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (R : C2GraphRectangle) (outerA outerB delta t lambda0 lambda1 : Real)
    (hOuter : outerA <= outerB)
    (H : PerturbationReadyPairLocalActualLensRectangleData
      T U f R outerA outerB delta t lambda0 lambda1) :
    R.rectangle.base ⊆ Icc outerA outerB := by
  intro z hz
  have hleft := H.data.left_mem_quarter
  have hright := H.data.right_mem_quarter
  change z ∈ Icc R.rectangle.left R.rectangle.right at hz
  rcases hz with ⟨hzLeft, hzRight⟩
  rcases hleft with ⟨hquarterLeft, _hleftUpper⟩
  rcases hright with ⟨_hrightLower, hquarterRight⟩
  simp only [centeredFractionLeft, centeredFractionRight] at hquarterLeft hquarterRight
  constructor <;> linarith

/-- On every finally selected grid item, the wide source base lies in the
ambient parameter interval. -/
theorem actualGPrimeThreeShiftCGrid_selected_sourceBase_subset
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstThreeShiftCGridPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (hOuter : outerA <= outerB)
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) (ha : a ∈ P.selected) :
    (D.fineRectangleAt (actualGPrimeLabelFirstLabel N D keep left right
      ballRadius omega a)).rectangle.base ⊆ Icc outerA outerB := by
  exact perturbationReadyPairLocal_sourceBase_subset
    (hOuter := hOuter) (H := P.data a ha)

/-- The local clustering rectangle is definitionally the exact-local
restriction of the wide source paper-fine rectangle. -/
theorem actualGPrimeThreeShiftCGridLocalCompactRectangleAt_eq_exactLocal
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (globalDelta tGlobal : Real)
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    actualGPrimeThreeShiftCGridLocalCompactRectangleAt N D keep left right
        ballRadius omega globalDelta tGlobal a =
      exactLocalC2GraphRectangle
        (D.fineRectangleAt (actualGPrimeLabelFirstLabel N D keep left right
          ballRadius omega a))
        (actualY1PaperFineCNormalizedChoiceLocalDelta
          (radius : Real) globalDelta tGlobal (4 * ballRadius))
        (4 * ballRadius) := by
  rfl

#print axioms actualPaperFineRectangle_length
#print axioms actualGPrimeLabelFirstLabel_mem_fineLabels
#print axioms perturbationReadyPairLocal_sourceBase_subset
#print axioms actualGPrimeThreeShiftCGrid_selected_sourceBase_subset
#print axioms actualGPrimeThreeShiftCGridLocalCompactRectangleAt_eq_exactLocal

end

end FamilyStickyCinematicL32Prop41ActualGPrimeThreeShiftCGridWideSourceFirstHitGeometryV1
