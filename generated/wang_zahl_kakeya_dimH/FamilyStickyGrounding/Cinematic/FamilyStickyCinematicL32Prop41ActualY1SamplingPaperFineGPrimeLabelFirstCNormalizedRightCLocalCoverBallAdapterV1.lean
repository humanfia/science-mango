import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedUniformPackageV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverBallAdapterV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u v

/-!
# C-normalized label-first adapter to the package-free local cover

The fibre key is the literal graph-C of the ordinary right endpoint together
with the finite reduced-coefficient cover code of the fine rectangle's source
tube.  All definitions use P.selected directly, so the refinement is lossless.
-/

def actualGPrimeCNormalizedLabelAt
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      fineLabel :=
  actualGPrimeLabelFirstLabel N D keep left right ballRadius omega

def actualGPrimeCNormalizedRightIndex
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      iota :=
  actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega

def actualGPrimeCNormalizedLeftTube
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      Tube radius :=
  fun a => traceTranslateTube
    (normalizeTubeCTo
      (fine.tubes (actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega a))
      (fine.tubes (actualGPrimeCNormalizedRightIndex
        N D keep left right ballRadius omega a)))
    (P.eta *
      (actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius) *
        actualY1PaperFineCNormalizedChoiceLocalDelta
          (radius : Real) globalDelta tGlobal (4 * ballRadius)))

/-- Definitional transport of the package's perturbation-ready pair data to
the adapter's left-tube, right-index, and label maps. -/
def actualGPrimeCNormalizedSelected_data
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal) :
    forall a, a ∈ P.selected ->
      PerturbationReadyPairLocalActualLensRectangleData
          (actualGPrimeCNormalizedLeftTube fine N D keep left right ballRadius
            omega f outerA outerB globalDelta tGlobal P a)
          (fine.tubes (actualGPrimeCNormalizedRightIndex
            N D keep left right ballRadius omega a))
          f
          (D.fineRectangleAt (actualGPrimeCNormalizedLabelAt
            N D keep left right ballRadius omega a))
          outerA outerB
          (actualY1PaperFineCNormalizedChoiceLocalDelta
            (radius : Real) globalDelta tGlobal (4 * ballRadius))
          (4 * ballRadius)
          (actualY1PaperFineCNormalizedChoiceLambda
            (radius : Real) globalDelta tGlobal (4 * ballRadius))
          (2 * actualY1PaperFineCNormalizedChoiceLambda
            (radius : Real) globalDelta tGlobal (4 * ballRadius)) := by
  intro a ha
  exact P.data a ha
noncomputable def actualGPrimeCNormalizedRightCLocalCoverValues
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) : Finset (Real × Tube radius) :=
  actualY1RightCLocalCoverValues fine P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius

noncomputable def actualGPrimeCNormalizedRightCLocalCoverFiber
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (value : Real × Tube radius) :=
  actualY1RightCLocalCoverFiber fine P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius value

noncomputable def actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (value : Real × Tube radius) :
    Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :=
  actualY1RightCLocalCoverUnderlyingFiber fine P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius value

def actualGPrimeCNormalizedRightCLocalCoverExactLocalRectangle
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (globalDelta tGlobal : Real) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      C2GraphRectangle :=
  actualY1RightCLocalCoverExactLocalRectangle D
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualY1PaperFineCNormalizedChoiceLocalDelta
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (4 * ballRadius)

/-- The normalized paper smallness automatically supplies the source-cover
C-error budget. -/
theorem radius_half_le_eight_ballRadius_of_cNormalizedThreeShiftSmall
    {radius : NNReal} {globalDelta tGlobal ballRadius A B : Real}
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (B - A))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    (radius : Real) / 2 <= 8 * ballRadius := by
  have scales :=
    actualY1PaperFineCNormalizedAutomaticThreeShiftNumerics_of_pairScaleSmall
      sharp hsmall
  have hfactor := q_le_prop41TangencyScaleFactor_of_one_le scales.traceQ_one
  have hfactorOne : 1 <=
      prop41TangencyScaleFactor
        (actualY1PaperFineCNormalizedChoiceTraceQ
          (radius : Real) globalDelta tGlobal (4 * ballRadius)) :=
    scales.traceQ_one.trans hfactor
  have hsum : 10 <=
      10 * prop41TangencyScaleFactor
          (actualY1PaperFineCNormalizedChoiceTraceQ
            (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
        actualY1PaperFineCNormalizedChoiceLambda
          (radius : Real) globalDelta tGlobal (4 * ballRadius) := by
    nlinarith [scales.lambda_pos]
  have hlarge : 1 <=
      46080 *
        (10 * prop41TangencyScaleFactor
            (actualY1PaperFineCNormalizedChoiceTraceQ
              (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
          actualY1PaperFineCNormalizedChoiceLambda
            (radius : Real) globalDelta tGlobal (4 * ballRadius)) := by
    nlinarith
  have hradius : 0 <= (radius : Real) := NNReal.coe_nonneg radius
  have hsmall' :
      46080 *
          (10 * prop41TangencyScaleFactor
              (actualY1PaperFineCNormalizedChoiceTraceQ
                (radius : Real) globalDelta tGlobal (4 * ballRadius)) +
            actualY1PaperFineCNormalizedChoiceLambda
              (radius : Real) globalDelta tGlobal (4 * ballRadius)) *
        (radius : Real) < 4 * ballRadius := by
    simpa only [ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness] using
      hsmall
  have hradiusLt : (radius : Real) < 4 * ballRadius := by
    nlinarith
  nlinarith

theorem actualGPrimeCNormalizedRightCLocalCover_selected_card_eq_sum_fiber_card
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) :
    P.selected.card =
      ∑ value ∈ actualGPrimeCNormalizedRightCLocalCoverValues fine N D keep
        left right ballRadius omega f outerA outerB globalDelta tGlobal P
          pointAt tubeAt,
        (actualGPrimeCNormalizedRightCLocalCoverFiber fine N D keep left right
          ballRadius omega f outerA outerB globalDelta tGlobal P pointAt tubeAt
            value).card := by
  exact actualY1RightCLocalCover_selected_card_eq_sum_fiber_card fine
    P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius

theorem actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_subset
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (value : Real × Tube radius) :
    actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt value ⊆ P.selected := by
  exact actualY1RightCLocalCoverUnderlyingFiber_subset fine P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius value

/-- Every occupied joint right-C/source-cover value has a nonempty fibre on
the original label-first survivor carrier. -/
theorem actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_nonempty
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (value : Real × Tube radius)
    (hvalue : value ∈ actualGPrimeCNormalizedRightCLocalCoverValues fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt) :
    (actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt value).Nonempty := by
  exact actualY1RightCLocalCoverUnderlyingFiber_nonempty fine P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius value hvalue

/-- Forgetting the membership proof from a joint fibre preserves its exact
cardinality. -/
theorem actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_card
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (value : Real × Tube radius) :
    (actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt value).card =
      (actualGPrimeCNormalizedRightCLocalCoverFiber fine N D keep left right
        ballRadius omega f outerA outerB globalDelta tGlobal P pointAt tubeAt
          value).card := by
  exact actualY1RightCLocalCoverUnderlyingFiber_card fine P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius value
theorem actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_leftGraphC
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
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius) (c : Real)
    (coverCenter : Tube radius) :
    forall a, a ∈ actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber fine
      N D keep left right ballRadius omega f outerA outerB globalDelta tGlobal
        P pointAt tubeAt (c, coverCenter) ->
      tubeGraphC
        (actualGPrimeCNormalizedLeftTube fine N D keep left right ballRadius
          omega f outerA outerB globalDelta tGlobal P a) = c := by
  apply actualY1RightCLocalCoverUnderlyingFiber_leftGraphC_of_pair fine
    P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    pointAt tubeAt ballRadius c coverCenter
    (actualGPrimeCNormalizedLeftTube fine N D keep left right ballRadius omega
      f outerA outerB globalDelta tGlobal P)
  intro a _ha
  simp only [actualGPrimeCNormalizedLeftTube,
    actualGPrimeCNormalizedRightIndex, tubeGraphC_traceTranslateTube,
    tubeGraphC_normalizeTubeCTo]

/-- The C-normalized package supplies the package-free local-cover ball
premise with no external callback and no comparison with tGlobal.

The fibre key fixes the right graph-C exactly.  The active C-bucket controls
the source tube's C error by radius / 2, while normalized paper smallness
turns that error into the explicit 12 * ballRadius budget. -/
theorem actualGPrimeCNormalizedRightCLocalCoverFiber_hballLocal
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hfDeriv hf1Deriv
      tGlobal globalDelta)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (c : Real) (coverCenter : Tube radius) :
    forall a,
      a ∈ actualGPrimeCNormalizedRightCLocalCoverFiber fine N D keep left
        right ballRadius omega f outerA outerB globalDelta tGlobal P pointAt
          tubeAt (c, coverCenter) ->
      InPointwiseC2BallOn (Icc outerA outerB)
        (globalCenterFixedCommonCReference coverCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter)
        (actualGPrimeCNormalizedRightCLocalCoverExactLocalRectangle N D keep
          left right ballRadius omega globalDelta tGlobal a.1)
        (3 * (4 * ballRadius)) := by
  have hpairScale : 0 < 4 * ballRadius := hsmall.pairScale_pos sharp
  have hballRadius : 0 < ballRadius := by nlinarith
  have hcBudget : (radius : Real) / 2 <= 8 * ballRadius :=
    radius_half_le_eight_ballRadius_of_cNormalizedThreeShiftSmall sharp hsmall
  exact actualY1RightCLocalCoverFiber_hballLocal fine physical E Y1
    fineLabels pointAt tubeAt f f1 f2 outerA outerB hOuter hfDeriv hf1Deriv
    tGlobal globalDelta facts hpointE (radius : Real)
    (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
    globalDelta tGlobal D hD keep P.selected
    (actualGPrimeCNormalizedLabelAt N D keep left right ballRadius omega)
    (actualGPrimeCNormalizedRightIndex N D keep left right ballRadius omega)
    P.right_retained
    (actualY1PaperFineCNormalizedChoiceLocalDelta
      (radius : Real) globalDelta tGlobal (4 * ballRadius))
    ballRadius hballRadius hcBudget hparameter hfunction hfirst hsecond c
    coverCenter

#print axioms radius_half_le_eight_ballRadius_of_cNormalizedThreeShiftSmall
#print axioms actualGPrimeCNormalizedRightCLocalCover_selected_card_eq_sum_fiber_card
#print axioms actualGPrimeCNormalizedRightCLocalCoverUnderlyingFiber_leftGraphC
#print axioms actualGPrimeCNormalizedRightCLocalCoverFiber_hballLocal
#print axioms actualGPrimeCNormalizedSelected_data
end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverBallAdapterV1
