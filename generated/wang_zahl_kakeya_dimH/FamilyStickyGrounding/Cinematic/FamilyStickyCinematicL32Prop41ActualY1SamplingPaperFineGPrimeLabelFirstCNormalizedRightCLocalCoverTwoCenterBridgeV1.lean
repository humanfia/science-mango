import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverBallAdapterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SharpCommonCReferenceTwoCenterBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32Prop41ActualY1ApproxCommonCLocalCoverGeometryV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RightCLocalCoverSelectedGenericV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverBallAdapterV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceTwoCenterBridgeV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

/-!
# Two-center bridge for C-normalized right-C/local-cover fibres

The source-cover code is within ballRadius of its actual source tube, while
the centered-half point source places that tube within 6*tGlobal of the
literal global center.  The triangle inequality therefore gives the exact
local-to-global second-jet bridge without fixed-C provenance.
-/

/-- On an occupied C-normalized right-C/local-cover fibre, the local cover
center is within ballRadius + 6*tGlobal of the literal global center. -/
theorem actualGPrimeCNormalizedRightCLocalCoverFiber_coverCenter_distance_globalCenter_le
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
    (globalDelta : Real)
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (c : Real) (coverCenter : Tube radius)
    (a : ActualY1RightCLocalCoverSelectedItem P.selected)
    (ha : a ∈ actualGPrimeCNormalizedRightCLocalCoverFiber fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt (c, coverCenter)) :
    tubePairCoefficientDistance coverCenter globalCenter <=
      ballRadius + 6 * tGlobal := by
  subst D
  let r := actualGPrimeCNormalizedLabelAt N
    (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    keep left right ballRadius omega a.1
  let i := actualGPrimeCNormalizedRightIndex N
    (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
    keep left right ballRadius omega a.1
  have hretained := P.right_retained a.1 a.2
  have hactiveData := y1FineCoarseRectangleData_retainedPair_active fine Y1
    fineLabels pointAt tubeAt f f1 f2 hfDeriv hf1Deriv fineDelta fineScale
      coarseDelta coarseScale keep i r hretained
  have hqE : pointAt r ∈ E := hpointE r hactiveData.1
  have hsource :
      tubePairCoefficientDistance (tubeAt (pointAt r)) globalCenter <=
        6 * tGlobal := by
    rw [tubePairCoefficientDistance_comm]
    exact pointSource.hcoefficientUpper (pointAt r) hqE
  have hcoverEq :
      actualY1RightCLocalCoverCode P.selected
        (actualGPrimeCNormalizedLabelAt N
          (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
            f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta
              coarseScale)
          keep left right ballRadius omega)
        pointAt tubeAt ballRadius a = coverCenter := by
    exact actualY1RightCLocalCoverFiber_coverCode_eq fine P.selected
      (actualGPrimeCNormalizedLabelAt N
        (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
          f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
        keep left right ballRadius omega)
      (actualGPrimeCNormalizedRightIndex N
        (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
          f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
        keep left right ballRadius omega)
      pointAt tubeAt ballRadius c coverCenter a ha
  have hcoverRaw := sourceTube_distance_coverCode_lt
    (actualY1RightCLocalCoverSourceTube P.selected
      (actualGPrimeCNormalizedLabelAt N
        (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
          f f1 f2 hfDeriv hf1Deriv fineDelta fineScale coarseDelta coarseScale)
        keep left right ballRadius omega)
      pointAt tubeAt)
    ballRadius hballRadius a
  have hcover :
      tubePairCoefficientDistance coverCenter (tubeAt (pointAt r)) <
        ballRadius := by
    rw [← hcoverEq, tubePairCoefficientDistance_comm]
    simpa only [actualY1RightCLocalCoverCode,
      actualY1RightCLocalCoverSourceTube, r] using hcoverRaw
  have htriangle := tubePairCoefficientDistance_triangle coverCenter
    globalCenter (tubeAt (pointAt r))
  linarith

/-- Exact second-jet bridge between the local cover reference and the global
reference sharing the fibre's literal right-C value. -/
theorem actualGPrimeCNormalizedRightCLocalCoverFiber_second_bridge
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (globalCenter : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
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
    (globalDelta : Real)
    (P : ActualGPrimeLabelFirstCNormalizedPaperFineUniformPackage fine N D
      keep left right ballRadius omega f outerA outerB globalDelta tGlobal)
    (c : Real) (coverCenter : Tube radius)
    (hfiber : (actualGPrimeCNormalizedRightCLocalCoverFiber fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal P
        pointAt tubeAt (c, coverCenter)).Nonempty)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100) :
    forall z, z ∈ Icc outerA outerB ->
      |(globalCenterFixedCommonCReference coverCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter).second z -
        (globalCenterFixedCommonCReference globalCenter c f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter).second z| <=
        (401 / 100 : Real) * (ballRadius + 6 * tGlobal) := by
  rcases hfiber with ⟨a, ha⟩
  have hdistance :=
    actualGPrimeCNormalizedRightCLocalCoverFiber_coverCenter_distance_globalCenter_le
      fine E Y1 fineLabels pointAt globalCenter tubeAt f f1 f2 outerA outerB
        hfDeriv hf1Deriv tGlobal pointSource hpointE fineDelta fineScale
          coarseDelta coarseScale N D hD keep left right ballRadius
            hballRadius omega globalDelta P c coverCenter a ha
  exact globalCenterFixedCommonCReference_second_dist_le coverCenter
    globalCenter c f f1 f2 hfDeriv hf1Deriv outerA outerB hOuter
      (ballRadius + 6 * tGlobal) hdistance hparameter hfunction hfirst hsecond

#print axioms actualGPrimeCNormalizedRightCLocalCoverFiber_coverCenter_distance_globalCenter_le
#print axioms actualGPrimeCNormalizedRightCLocalCoverFiber_second_bridge

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstCNormalizedRightCLocalCoverTwoCenterBridgeV1
