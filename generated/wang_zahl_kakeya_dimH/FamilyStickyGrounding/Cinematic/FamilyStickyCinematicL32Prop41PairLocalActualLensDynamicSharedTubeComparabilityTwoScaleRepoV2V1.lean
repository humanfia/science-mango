import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1RepoV2

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualLensDynamicSharedTubeComparabilityTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Dynamic shared-tube comparability at independent scales

This is the first analytic consumer above the common-reference adapter.
All root-support localization remains at `localScale`; the selected shared
tube is required only to lie in the `3 * referenceScale` C2 ball.
-/

/-- Two pair-local lens records become two-scale comparable once one of
their cross-side tubes is selected as the common reference. -/
theorem compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube
    {radius : NNReal} (T1 U1 T2 U2 V : Tube radius)
    (f f1 f2 : Real -> Real) (center R S : C2GraphRectangle)
    {domain : Set Real}
    {A B delta localScale referenceScale lambda0 lambda : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
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
    (hoverlap : (D1.lensSupport ∩ D2.lensSupport).Nonempty)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <=
      Real.sqrt (lambda * delta / localScale))
    (htangentR : R.carrier delta ⊆
      cinematicVerticalNeighborhood
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).rectangle.graph
        R.rectangle.base (lambda * delta))
    (htangentS : S.carrier delta ⊆
      cinematicVerticalNeighborhood
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).rectangle.graph
        S.rectangle.base (lambda * delta))
    (hreference : InPointwiseC2BallOn domain center
      (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
      (3 * referenceScale)) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda := by
  have hfirst1 :
      cinematicVerticalNeighborhood R.rectangle.graph
          (Icc R.rectangle.left R.rectangle.right) delta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f (tubeGraphA T1) (tubeGraphB T1)
            (tubeGraphC T1) (tubeGraphD T1))
          (Icc R.rectangle.left R.rectangle.right)
          (2 * lambda0 * delta) := by
    simpa [C2GraphRectangle.carrier, GraphRectangle.carrier,
      GraphRectangle.base] using D1.tangent_first
  have hsecond1 :
      cinematicVerticalNeighborhood R.rectangle.graph
          (Icc R.rectangle.left R.rectangle.right) delta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f (tubeGraphA U1) (tubeGraphB U1)
            (tubeGraphC U1) (tubeGraphD U1))
          (Icc R.rectangle.left R.rectangle.right)
          (2 * lambda0 * delta) := by
    simpa [C2GraphRectangle.carrier, GraphRectangle.carrier,
      GraphRectangle.base] using D1.tangent_second
  obtain ⟨critical1, _hcritical1Mem, _hcritical1,
      _hcritical1Unique, hlens1Abs, hbase1Abs⟩ :=
    actualTubePair_twoLambdaTangent_rectangleBase_and_rootSupport_localized
      T1 U1 f f1 f2 R.rectangle.graph hAB hdelta ht hlambda0 hwidth
      R.rectangle.left_le_right D1.left_mem_quarter
      D1.right_mem_quarter D1.rectangle_width D1.theta_order
      D1.thetaLeft_mem D1.thetaRight_mem D1.common_c D1.root_left
      D1.root_right D1.coefficient_lower
      (fun z _ => hfDeriv z) (fun z _ => hf1Deriv z) hsmallScale
      hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hdelta.le hfirst1 hsecond1
  have hfirst2 :
      cinematicVerticalNeighborhood S.rectangle.graph
          (Icc S.rectangle.left S.rectangle.right) delta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f (tubeGraphA T2) (tubeGraphB T2)
            (tubeGraphC T2) (tubeGraphD T2))
          (Icc S.rectangle.left S.rectangle.right)
          (2 * lambda0 * delta) := by
    simpa [C2GraphRectangle.carrier, GraphRectangle.carrier,
      GraphRectangle.base] using D2.tangent_first
  have hsecond2 :
      cinematicVerticalNeighborhood S.rectangle.graph
          (Icc S.rectangle.left S.rectangle.right) delta ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f (tubeGraphA U2) (tubeGraphB U2)
            (tubeGraphC U2) (tubeGraphD U2))
          (Icc S.rectangle.left S.rectangle.right)
          (2 * lambda0 * delta) := by
    simpa [C2GraphRectangle.carrier, GraphRectangle.carrier,
      GraphRectangle.base] using D2.tangent_second
  obtain ⟨critical2, _hcritical2Mem, _hcritical2,
      _hcritical2Unique, hlens2Abs, hbase2Abs⟩ :=
    actualTubePair_twoLambdaTangent_rectangleBase_and_rootSupport_localized
      T2 U2 f f1 f2 S.rectangle.graph hAB hdelta ht hlambda0 hwidth
      S.rectangle.left_le_right D2.left_mem_quarter
      D2.right_mem_quarter D2.rectangle_width D2.theta_order
      D2.thetaLeft_mem D2.thetaRight_mem D2.common_c D2.root_left
      D2.root_right D2.coefficient_lower
      (fun z _ => hfDeriv z) (fun z _ => hf1Deriv z) hsmallScale
      hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hdelta.le hfirst2 hsecond2
  have hbase1 : forall theta, theta ∈ R.rectangle.base ->
      dist theta critical1 <=
        prop41ActualPairLocalizationRadius
          (4 * lambda0) delta localScale := by
    intro theta htheta
    simpa [GraphRectangle.base, Real.dist_eq] using
      hbase1Abs theta htheta
  have hbase2 : forall theta, theta ∈ S.rectangle.base ->
      dist theta critical2 <=
        prop41ActualPairLocalizationRadius
          (4 * lambda0) delta localScale := by
    intro theta htheta
    simpa [GraphRectangle.base, Real.dist_eq] using
      hbase2Abs theta htheta
  have hlens1 : forall theta, theta ∈ D1.lensSupport ->
      dist theta critical1 <=
        prop41ActualPairLocalizationRadius
          (4 * lambda0) delta localScale := by
    intro theta htheta
    simpa [PairLocalActualLensRectangleData.lensSupport,
      Real.dist_eq] using hlens1Abs theta htheta
  have hlens2 : forall theta, theta ∈ D2.lensSupport ->
      dist theta critical2 <=
        prop41ActualPairLocalizationRadius
          (4 * lambda0) delta localScale := by
    intro theta htheta
    simpa [PairLocalActualLensRectangleData.lensSupport,
      Real.dist_eq] using hlens2Abs theta htheta
  have hradius : 0 <= prop41ActualPairLocalizationRadius
      (4 * lambda0) delta localScale := by
    dsimp [prop41ActualPairLocalizationRadius,
      FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1.prop41CriticalLocalizationFactor]
    positivity
  exact compactC2ComparableAtScales_of_lensSupport_overlap
    hradius hbase1 hbase2 hlens1 hlens2 hoverlap hscale
    htangentR htangentS hreference

#print axioms compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube

end

end FamilyStickyCinematicL32Prop41PairLocalActualLensDynamicSharedTubeComparabilityTwoScaleRepoV2V1
