import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualBoundarySharedTubeExtractionGlobalCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualLensDynamicSharedTubeComparabilityTwoScaleRepoV2V1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualLensBoundaryNonOverlapTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualBoundarySharedTubeExtractionGlobalCleanV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
open FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensDynamicSharedTubeComparabilityTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Pair-local boundary non-overlap at independent scales

The shared-side extraction and all pair localization stay at `localScale`.
Only the common pointwise C2 family uses `referenceScale`.
-/

private theorem tangent_to_pairLocalTubeReference_of_tangent_twoScale
    {radius : NNReal} (V : Tube radius)
    (f f1 f2 : Real -> Real) (R : C2GraphRectangle)
    {A B delta lambda0 lambda : Real}
    (hAB : A <= B)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (htangent : R.carrier delta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f (tubeGraphA V) (tubeGraphB V)
          (tubeGraphC V) (tubeGraphD V))
        R.rectangle.base (2 * lambda0 * delta))
    (henlarge : 2 * lambda0 * delta <= lambda * delta) :
    R.carrier delta ⊆
      cinematicVerticalNeighborhood
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).rectangle.graph
        R.rectangle.base (lambda * delta) := by
  intro q hq
  have hqTrace := htangent hq
  refine ⟨hqTrace.1, ?_⟩
  simpa [pairLocalTubeReference, tubeC2GraphRectangle] using
    hqTrace.2.trans henlarge

/-- Positive boundary-segment overlap forces the two-scale compact-C2
comparability relation. -/
theorem compactC2ComparableAtScales_of_pairLocalActualBoundariesSharePositiveSegment_global
    {radius : NNReal} (curves : Finset (Tube radius))
    (T1 U1 T2 U2 : Tube radius)
    (hT1 : T1 ∈ curves) (hU1 : U1 ∈ curves)
    (hT2 : T2 ∈ curves) (hU2 : U2 ∈ curves)
    (f f1 f2 : Real -> Real) (center R S : C2GraphRectangle)
    {domain : Set Real}
    {A B delta localScale referenceScale lambda0 lambda : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcommonC : forall V, V ∈ curves -> forall W, W ∈ curves ->
      tubeGraphC V = tubeGraphC W)
    (hcoefficient : forall V, V ∈ curves -> forall W, W ∈ curves ->
      V ≠ W -> 0 < tubePairCoefficientDistance V W)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (D1 : PairLocalActualLensRectangleData T1 U1 f R
      A B delta localScale lambda0)
    (D2 : PairLocalActualLensRectangleData T2 U2 f S
      A B delta localScale lambda0)
    (hoverlap : sharePositiveGraphSegment
      (actualPairGraphBoundary T1 U1 f D1.thetaLeft D1.thetaRight)
      (actualPairGraphBoundary T2 U2 f D2.thetaLeft D2.thetaRight))
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <=
      Real.sqrt (lambda * delta / localScale))
    (hreference : forall V, V ∈ curves ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
        (3 * referenceScale)) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda := by
  have hsupport : (D1.lensSupport ∩ D2.lensSupport).Nonempty := by
    have h := rootSupports_overlap_of_boundaryArcs_sharePositiveGraphSegment
      (cinematicTraceValue f (tubeGraphA T1) (tubeGraphB T1)
        (tubeGraphC T1) (tubeGraphD T1))
      (cinematicTraceValue f (tubeGraphA U1) (tubeGraphB U1)
        (tubeGraphC U1) (tubeGraphD U1))
      (cinematicTraceValue f (tubeGraphA T2) (tubeGraphB T2)
        (tubeGraphC T2) (tubeGraphD T2))
      (cinematicTraceValue f (tubeGraphA U2) (tubeGraphB U2)
        (tubeGraphC U2) (tubeGraphD U2))
      D1.thetaLeft D1.thetaRight D2.thetaLeft D2.thetaRight
      (by simpa [actualPairGraphBoundary] using hoverlap)
    simpa [PairLocalActualLensRectangleData.lensSupport,
      prop41PairRootSupport] using h
  have hshared :=
    exists_equal_cross_side_tubes_of_actualPairBoundaries_sharePositiveSegment_global
      curves f f1 f2 hAB hcommonC hcoefficient hparameter hft
      hf1Lower hf1Upper hf2 (fun z _ => hfDeriv z)
      (fun z _ => hf1Deriv z)
      T1 hT1 U1 hU1 T2 hT2 U2 hU2
      D1.thetaLeft_mem D1.thetaRight_mem
      D2.thetaLeft_mem D2.thetaRight_mem hoverlap
  rcases hshared with hshared | hshared | hshared | hshared
  · subst T2
    exact compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube
      T1 U1 T1 U2 T1 f f1 f2 center R S hAB hdelta ht hlambda0
      hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous D1 D2 hsupport hscale
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        T1 f f1 f2 R hAB hfDeriv hf1Deriv D1.tangent_first henlarge)
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        T1 f f1 f2 S hAB hfDeriv hf1Deriv D2.tangent_first henlarge)
      (hreference T1 hT1)
  · subst U2
    exact compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube
      T1 U1 T2 T1 T1 f f1 f2 center R S hAB hdelta ht hlambda0
      hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous D1 D2 hsupport hscale
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        T1 f f1 f2 R hAB hfDeriv hf1Deriv D1.tangent_first henlarge)
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        T1 f f1 f2 S hAB hfDeriv hf1Deriv D2.tangent_second henlarge)
      (hreference T1 hT1)
  · subst T2
    exact compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube
      T1 U1 U1 U2 U1 f f1 f2 center R S hAB hdelta ht hlambda0
      hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous D1 D2 hsupport hscale
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        U1 f f1 f2 R hAB hfDeriv hf1Deriv D1.tangent_second henlarge)
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        U1 f f1 f2 S hAB hfDeriv hf1Deriv D2.tangent_first henlarge)
      (hreference U1 hU1)
  · subst U2
    exact compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube
      T1 U1 T2 U1 U1 f f1 f2 center R S hAB hdelta ht hlambda0
      hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous D1 D2 hsupport hscale
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        U1 f f1 f2 R hAB hfDeriv hf1Deriv D1.tangent_second henlarge)
      (tangent_to_pairLocalTubeReference_of_tangent_twoScale
        U1 f f1 f2 S hAB hfDeriv hf1Deriv D2.tangent_second henlarge)
      (hreference U1 hU1)

/-- Two-scale incomparability rules out a positive common boundary
segment. -/
theorem not_sharePositiveSegment_of_pairLocalActualData_and_incomparableAtScales_global
    {radius : NNReal} (curves : Finset (Tube radius))
    (T1 U1 T2 U2 : Tube radius)
    (hT1 : T1 ∈ curves) (hU1 : U1 ∈ curves)
    (hT2 : T2 ∈ curves) (hU2 : U2 ∈ curves)
    (f f1 f2 : Real -> Real) (center R S : C2GraphRectangle)
    {domain : Set Real}
    {A B delta localScale referenceScale lambda0 lambda : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcommonC : forall V, V ∈ curves -> forall W, W ∈ curves ->
      tubeGraphC V = tubeGraphC W)
    (hcoefficient : forall V, V ∈ curves -> forall W, W ∈ curves ->
      V ≠ W -> 0 < tubePairCoefficientDistance V W)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (D1 : PairLocalActualLensRectangleData T1 U1 f R
      A B delta localScale lambda0)
    (D2 : PairLocalActualLensRectangleData T2 U2 f S
      A B delta localScale lambda0)
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <=
      Real.sqrt (lambda * delta / localScale))
    (hreference : forall V, V ∈ curves ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
        (3 * referenceScale))
    (hincomparable : Not
      (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center R S delta localScale referenceScale lambda)) :
    Not (sharePositiveGraphSegment
      (actualPairGraphBoundary T1 U1 f D1.thetaLeft D1.thetaRight)
      (actualPairGraphBoundary T2 U2 f D2.thetaLeft D2.thetaRight)) := by
  intro hoverlap
  apply hincomparable
  exact compactC2ComparableAtScales_of_pairLocalActualBoundariesSharePositiveSegment_global
    curves T1 U1 T2 U2 hT1 hU1 hT2 hU2 f f1 f2 center R S
    hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient
    hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower hf1Upper
    hf2 hf2Continuous D1 D2 hoverlap henlarge hscale hreference

#print axioms compactC2ComparableAtScales_of_pairLocalActualBoundariesSharePositiveSegment_global
#print axioms not_sharePositiveSegment_of_pairLocalActualData_and_incomparableAtScales_global

end

end FamilyStickyCinematicL32Prop41PairLocalActualLensBoundaryNonOverlapTwoScaleRepoV2V1
