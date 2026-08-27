import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensTwoScaleMoonCoreRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleConsumerRepoV2V1

open Set
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensTwoScaleMoonCoreRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleTieOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Selected-subfamily two-scale consumer on the RepoV2 branch

This package removes only the source-pairwise field.  All local geometry
continues to use `localScale`; common-reference membership and compact
comparability use the independent `referenceScale`.  The RepoV2 two-scale
Moon chain constructs the analytic core internally.
-/

/-- All finite-general-position data needed to construct and count the
selected endpoint family, except its source `Pairwise` proof. -/
structure SelectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    (A B delta localScale referenceScale lambda1 depth : Real)
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z) where
  weight : Tube radius -> Real
  externalTolerance : Real
  graphBound : Real
  externalTolerance_pos : 0 < externalTolerance
  interval_strict : A < B
  delta_pos : 0 < delta
  localScale_pos : 0 < localScale
  lambda1_ge_one : 1 <= lambda1
  interval_width : (1 / 2 : Real) <= B - A
  small_scale : prop41TangencyScaleFactor (4 * lambda1) * delta <
    localScale / 1200
  parameter_bound : forall z, z ∈ Icc A B -> |z| <= 1
  graph_function_bound : forall z, z ∈ Icc A B -> |f z| <= 2
  first_derivative_lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|
  first_derivative_upper : forall z, z ∈ Icc A B -> |f1 z| <= 2
  second_derivative_bound : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100
  second_derivative_continuous : ContinuousOn f2 (Icc A B)
  common_c : forall V, V ∈ retainedPairTubeFamily fiber T U -> forall W,
    W ∈ retainedPairTubeFamily fiber T U -> tubeGraphC V = tubeGraphC W
  weight_injective : Set.InjOn weight
    (retainedPairTubeFamily fiber T U : Set (Tube radius))
  critical_finite : forall V, V ∈ retainedPairTubeFamily fiber T U ->
    forall W, W ∈ retainedPairTubeFamily fiber T U -> V ≠ W ->
      (criticalHeightDifferenceSet
        (fun X => actualTubeGraph X f)
        (fun X => actualTubeGraphFirst X f f1) A B V W).Finite
  comparison_enlarges : 2 * lambda1 * delta <= comparisonLambda * delta
  localization_scale : 4 * prop41ActualPairLocalizationRadius
      (4 * lambda1) delta localScale <=
    Real.sqrt (comparisonLambda * delta / localScale)
  reference : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B
          interval_strict.le) (3 * referenceScale)
  depth_bound :
    (canonicalDepth (FirstGenerationCurve
      (retainedPairTubeFamily fiber T U)) : Real) <= depth
  perturbed_graph_bound : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      forall theta, theta ∈ Icc A B ->
        |actualTubeGraph V f theta| <= graphBound

/-- A perturbation-ready selected subfamily satisfies the usual sampled
lens bound while using an independent common-reference scale. -/
theorem selectedSubfamily_card_le_sampledLensBoundAtScales_of_perturbationReady
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (hfiber : fiber.Nonempty)
    (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    {A B delta localScale referenceScale lambda0 lambda1 depth : Real}
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : forall i, i ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T i) (U i) f (sourceRectangles i)
          A B delta localScale lambda0 lambda1)
    (G : SelectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage
      fiber T U sourceRectangles f f1 f2 A B delta localScale
        referenceScale lambda1 depth center domain comparisonLambda
          hfDeriv hf1Deriv)
    (hsource : Set.Pairwise (fiber : Set alpha)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (sourceRectangles i) (sourceRectangles j)
          delta localScale referenceScale comparisonLambda))) :
    (fiber.card : Real) <= sampledLensBound depth
      ((retainedPairTubeFamily fiber T U).card : Real) := by
  obtain ⟨S⟩ :=
    exists_perturbedRetainedPairEndpointAssemblyAtScales_of_perturbationReady
      fiber hfiber T U sourceRectangles G.weight f f1 f2 center
      G.externalTolerance_pos G.interval_strict G.delta_pos G.localScale_pos
      G.lambda1_ge_one G.interval_width P hfDeriv hf1Deriv G.small_scale
      G.parameter_bound G.graph_function_bound G.first_derivative_lower
      G.first_derivative_upper G.second_derivative_bound
      G.second_derivative_continuous G.common_c G.weight_injective
      G.critical_finite G.comparison_enlarges G.localization_scale
      G.reference hsource
  let curves := perturbedRetainedTubeFamily fiber T U G.weight S.epsilon
  let E := S.endpointInterface
  have hmoonCore : forall hpair : forall p : FirstGenerationCurvePair curves,
      p.1 = s(pairLocalActualItemSelectedFirstCurve E.firstTube E.first_mem p,
        pairLocalActualItemSelectedSecondCurve E.secondTube E.second_mem p),
      forall localDepth : FirstGenerationCurve curves -> Real,
        PairLocalActualSelectedLensTwoScaleMoonCore curves E.items E.firstTube
          E.secondTube E.first_mem E.second_mem hpair E.rectangles f f1 f2
            A B G.graphBound localDepth center domain delta localScale
              referenceScale lambda1 comparisonLambda E.data
                G.interval_strict.le hfDeriv hf1Deriv := by
    intro hpair localDepth
    exact pairLocalActualSelectedLensTwoScaleMoonCore_of_geometry
      curves E.items E.firstTube E.secondTube E.first_mem E.second_mem hpair
      E.rectangles f f1 f2 A B G.graphBound localDepth center domain E.data
      G.interval_strict G.delta_pos G.localScale_pos G.lambda1_ge_one
      G.interval_width S.common_c S.coefficient_pos hfDeriv hf1Deriv
      G.small_scale G.parameter_bound G.graph_function_bound
      G.first_derivative_lower G.first_derivative_upper
      G.second_derivative_bound G.second_derivative_continuous
      S.endpoint_distinct S.no_tangential_intersections
      G.comparison_enlarges G.localization_scale
  have hcount : (fiber.card : Real) <=
      sampledLensBound
        (canonicalDepth (FirstGenerationCurve curves) : Real)
        (curves.card : Real) := by
    simpa only [sampledLensBound, curves] using
      pairLocalActualSelectedLens_card_le_explicitAtScales_global_of_endpointAssembly
        fiber T U sourceRectangles G.weight f f1 f2 center S
        G.interval_strict G.graphBound G.delta_pos G.localScale_pos
        G.lambda1_ge_one G.interval_width hfDeriv hf1Deriv G.small_scale
        G.parameter_bound G.graph_function_bound G.first_derivative_lower
        G.first_derivative_upper G.second_derivative_bound
        G.second_derivative_continuous
        (G.perturbed_graph_bound S.epsilon S.epsilon_pos
          S.epsilon_lt_external)
        G.comparison_enlarges G.localization_scale
        (G.reference S.epsilon S.epsilon_pos S.epsilon_lt_external)
        hmoonCore
  have hcanonical : canonicalDepth (FirstGenerationCurve curves) =
      canonicalDepth (FirstGenerationCurve
        (retainedPairTubeFamily fiber T U)) := by
    unfold canonicalDepth
    simp only [Fintype.card_coe, curves, S.family_card_eq]
  have hdepth :
      (canonicalDepth (FirstGenerationCurve curves) : Real) <= depth := by
    simpa only [hcanonical] using G.depth_bound
  have hmono := sampledLensBound_mono_depth hdepth
    (show 0 <= (curves.card : Real) by positivity)
  rw [S.family_card_eq] at hmono
  rw [S.family_card_eq] at hcount
  exact hcount.trans hmono

#print axioms SelectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage
#print axioms selectedSubfamily_card_le_sampledLensBoundAtScales_of_perturbationReady

end

end FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleConsumerRepoV2V1
