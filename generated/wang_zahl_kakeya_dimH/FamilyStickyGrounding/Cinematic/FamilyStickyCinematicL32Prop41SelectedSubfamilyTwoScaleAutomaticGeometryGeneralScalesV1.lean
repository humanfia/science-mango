import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticGeometryRepoV2V1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticGeometryGeneralScalesV1

open Set
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
open FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
open FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
open FamilyStickyCinematicL32Prop41CommonReferenceIndependentScaleV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleConsumerRepoV2V1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Carrier-generic automatic two-scale geometry at arbitrary proved scales

The existing automatic constructor hard-codes the five-radius paper-fine
choice. This variant exposes the scalar fields actually consumed by the
finite-general-position package. It therefore accepts the six-radius
C-normalized lambda without changing any geometric or counting theorem.
-/

/-- Automatic finite-general-position geometry from literal scalar facts.
No formula for the four scale and comparison parameters is assumed. -/
theorem exists_selectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage_of_scalars
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (source : alpha -> C2GraphRectangle)
    (globalCenter : Tube radius) (commonC rho : Real)
    (f f1 f2 : Real -> Real)
    (A B delta localScale referenceScale lambda1 depth comparisonLambda :
      Real)
    (hOuter : A <= B)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hintervalStrict : A < B)
    (hdelta : 0 < delta)
    (hlocalScale : 0 < localScale)
    (hlambda1 : 1 <= lambda1)
    (hintervalWidth : (1 / 2 : Real) <= B - A)
    (hsmallScale :
      prop41TangencyScaleFactor (4 * lambda1) * delta <
        localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hfirstUpper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc A B))
    (hcommon : forall V, V ∈ retainedPairTubeFamily fiber T U ->
      tubeGraphC V = commonC)
    (hdistance : forall V, V ∈ retainedPairTubeFamily fiber T U ->
      tubePairCoefficientDistance V globalCenter <= rho)
    (hdepth :
      (canonicalDepth (FirstGenerationCurve
        (retainedPairTubeFamily fiber T U)) : Real) <= depth)
    (hreferenceMargin :
      max ((401 / 100 : Real) * rho) (2 * rho + 0) <
        3 * referenceScale)
    (hcomparisonEnlarges :
      2 * lambda1 * delta <= comparisonLambda * delta)
    (hlocalization :
      4 * prop41ActualPairLocalizationRadius
          (4 * lambda1) delta localScale <=
        Real.sqrt (comparisonLambda * delta / localScale)) :
    Nonempty
      (SelectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage
        fiber T U source f f1 f2 A B delta localScale referenceScale
          lambda1 depth
          (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
            hfDeriv hf1Deriv A B hOuter)
          (Icc A B) comparisonLambda hfDeriv hf1Deriv) := by
  let family := retainedPairTubeFamily fiber T U
  let weight := finiteActualTubeWeight family
  let weightEnvelope := finiteActualTubeFamilyWeightEnvelope family weight
  have hweightEnvelope : 0 <= weightEnvelope :=
    finiteActualTubeFamilyWeightEnvelope_nonneg family weight
  obtain ⟨externalTolerance, hexternalTolerance, hreference⟩ :=
    exists_positive_tolerance_fixedCommonC_family_reference family id
      (fun _ => 0) weight globalCenter commonC f f1 f2 hfDeriv hf1Deriv
      A B hOuter rho 0 weightEnvelope referenceScale hweightEnvelope
      hreferenceMargin
      (by
        intro V hV
        exact hcommon V (by simpa only [family] using hV))
      (by
        intro V hV
        exact hdistance V (by simpa only [family] using hV))
      (by
        intro V _hV
        norm_num)
      (by
        intro V hV
        exact abs_weight_le_finiteFamilyWeightEnvelope weight hV)
      hparameter hfunction hfirstUpper hsecond
  refine ⟨{
    weight := weight
    externalTolerance := externalTolerance
    graphBound :=
      retainedPairPerturbedGraphBound fiber T U weight externalTolerance
    externalTolerance_pos := hexternalTolerance
    interval_strict := hintervalStrict
    delta_pos := hdelta
    localScale_pos := hlocalScale
    lambda1_ge_one := hlambda1
    interval_width := hintervalWidth
    small_scale := hsmallScale
    parameter_bound := hparameter
    graph_function_bound := hfunction
    first_derivative_lower := hfirstLower
    first_derivative_upper := hfirstUpper
    second_derivative_bound := hsecond
    second_derivative_continuous := hsecondContinuous
    common_c := ?_
    weight_injective := ?_
    critical_finite := ?_
    comparison_enlarges := hcomparisonEnlarges
    localization_scale := hlocalization
    reference := ?_
    depth_bound := hdepth
    perturbed_graph_bound := ?_ }⟩
  · intro V hV W hW
    exact (hcommon V (by simpa only [family] using hV)).trans
      (hcommon W (by simpa only [family] using hW)).symm
  · simpa only [weight, family] using finiteActualTubeWeight_injOn family
  · apply actualTube_family_criticalHeightDifferenceSet_finite
      family f f1 f2 hintervalStrict.le
    · intro V hV W hW
      exact (hcommon V (by simpa only [family] using hV)).trans
        (hcommon W (by simpa only [family] using hW)).symm
    · exact hparameter
    · exact hfunction
    · exact hfirstLower
    · exact hfirstUpper
    · exact hsecond
    · intro z _hz
      exact hfDeriv z
    · intro z _hz
      exact hf1Deriv z
    · exact hsecondContinuous
  · intro epsilon hepsilon hepsilon_lt V hV
    rw [FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1.perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily]
      at hV
    simp only [individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV
    obtain ⟨W, hW, rfl⟩ := hV
    simpa only [individuallyTracePerturbedTube, id_eq, zero_add] using
      hreference epsilon hepsilon hepsilon_lt W
        (by simpa only [family] using hW)
  · intro epsilon hepsilon hepsilon_lt V hV theta htheta
    exact perturbedRetainedTubeFamily_graph_le_automatic_bound fiber T U
      weight f hexternalTolerance hepsilon hepsilon_lt hV theta
        (hparameter theta htheta) (hfunction theta htheta)

#print axioms exists_selectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage_of_scalars

end

end FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticGeometryGeneralScalesV1
