import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleAutomaticGeometryRepoV2V1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticGeometryRepoV2V1

open Set
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedBasicNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleAutomaticGeometryRepoV2V1
open FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
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

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Carrier-generic automatic two-scale geometry

This is the carrier-independent core of the actual selected construction.
It requires exact common-`c`, coefficient-radius and depth facts only on the
literal selected tube family.  In particular it does not require a global
fixed-`c` provenance object, so an exact-`c` cell may supply these facts
locally.
-/

theorem exists_selectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage_automatic
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (source : alpha -> C2GraphRectangle)
    (globalCenter : Tube radius) (commonC rho : Real)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale depth : Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (N : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hthree : ActualY1PaperFineThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal pairScale)
    (hcount : ActualY1PaperFineSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal pairScale)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hfirstUpper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc outerA outerB))
    (hcommon : forall V, V ∈ retainedPairTubeFamily fiber T U ->
      tubeGraphC V = commonC)
    (hdistance : forall V, V ∈ retainedPairTubeFamily fiber T U ->
      tubePairCoefficientDistance V globalCenter <= rho)
    (hdepth :
      (canonicalDepth (FirstGenerationCurve
        (retainedPairTubeFamily fiber T U)) : Real) <= depth)
    (hreferenceMargin :
      max ((401 / 100 : Real) * rho) (2 * rho + 0) <
        3 * referenceScale) :
    Nonempty
      (SelectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage
        fiber T U source f f1 f2 outerA outerB
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale referenceScale
          (2 * actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal pairScale)
          depth
          (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
            hfDeriv hf1Deriv outerA outerB hOuter)
          (Icc outerA outerB)
          (actualY1PaperFineSelectedAutomaticComparisonLambda
            (radius := radius) globalDelta tGlobal pairScale)
          hfDeriv hf1Deriv) := by
  let family := retainedPairTubeFamily fiber T U
  let weight := finiteActualTubeWeight family
  let weightEnvelope := finiteActualTubeFamilyWeightEnvelope family weight
  have hweightEnvelope : 0 <= weightEnvelope :=
    finiteActualTubeFamilyWeightEnvelope_nonneg family weight
  obtain ⟨externalTolerance, hexternalTolerance, hreference⟩ :=
    exists_positive_tolerance_fixedCommonC_family_reference family id
      (fun _ => 0) weight globalCenter commonC f f1 f2 hfDeriv hf1Deriv
      outerA outerB hOuter rho 0 weightEnvelope referenceScale
      hweightEnvelope hreferenceMargin
      (by intro V hV; exact hcommon V (by simpa only [family] using hV))
      (by intro V hV; exact hdistance V (by simpa only [family] using hV))
      (by intro V hV; norm_num)
      (by intro V hV; exact abs_weight_le_finiteFamilyWeightEnvelope weight hV)
      hparameter hfunction hfirstUpper hsecond
  let numerics := actualY1PaperFineSelectedCountingNumerics_of_pairScaleSmall
    N hthree hcount
  let comparisonLambda := actualY1PaperFineSelectedAutomaticComparisonLambda
    (radius := radius) globalDelta tGlobal pairScale
  refine ⟨{
    weight := weight
    externalTolerance := externalTolerance
    graphBound := retainedPairPerturbedGraphBound fiber T U weight
      externalTolerance
    externalTolerance_pos := hexternalTolerance
    interval_strict := numerics.interval_strict
    delta_pos := numerics.delta_pos
    localScale_pos := numerics.t_pos
    lambda1_ge_one := numerics.lambda1_ge_one
    interval_width := numerics.interval_width
    small_scale := numerics.small_scale
    parameter_bound := hparameter
    graph_function_bound := hfunction
    first_derivative_lower := hfirstLower
    first_derivative_upper := hfirstUpper
    second_derivative_bound := hsecond
    second_derivative_continuous := hsecondContinuous
    common_c := ?_
    weight_injective := ?_
    critical_finite := ?_
    comparison_enlarges := ?_
    localization_scale := ?_
    reference := ?_
    depth_bound := hdepth
    perturbed_graph_bound := ?_ }⟩
  · intro V hV W hW
    exact (hcommon V (by simpa only [family] using hV)).trans
      (hcommon W (by simpa only [family] using hW)).symm
  · simpa only [weight, family] using finiteActualTubeWeight_injOn family
  · apply actualTube_family_criticalHeightDifferenceSet_finite
      family f f1 f2 numerics.interval_strict.le
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
  · exact prop41AutomaticComparisonLambda_enlarges
      numerics.lambda1_ge_one numerics.delta_pos numerics.t_pos
  · exact prop41AutomaticComparisonLambda_localization
      numerics.lambda1_ge_one numerics.delta_pos numerics.t_pos
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

#print axioms exists_selectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage_automatic

end

end FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticGeometryRepoV2V1
