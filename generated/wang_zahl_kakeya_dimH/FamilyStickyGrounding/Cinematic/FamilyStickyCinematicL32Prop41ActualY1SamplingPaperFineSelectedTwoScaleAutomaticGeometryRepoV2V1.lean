import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleOutcomeRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticToleranceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedBasicNumericsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedDepthProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CommonReferenceIndependentScaleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleAutomaticGeometryRepoV2V1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticToleranceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedBasicNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedDepthProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleOutcomeRepoV2V1
open FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
open FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
open FamilyStickyCinematicL32Prop41CommonReferenceIndependentScaleV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic ordinary geometry for the RepoV2 two-scale selected outcome

The selected family still uses `pairScale` for tangency and localization,
while the synthetic common reference uses the independent `referenceScale`.
All finite general-position data, the logarithmic depth, the comparison
enlargement, the perturbation tolerance and the graph bound are canonical.
-/

/-- A uniform, outcome-independent coefficient radius for both the selected
shifted left tubes and the unshifted right tubes. -/
def actualY1PaperFineSelectedUniformCoefficientRadius
    {radius : NNReal}
    (globalScale globalDelta tGlobal pairScale : Real) : Real :=
  3 * (globalScale +
    |actualY1PaperFineChoiceLambda (radius : Real) globalDelta tGlobal
        pairScale *
      actualY1PaperFineChoiceLocalDelta (radius : Real) globalDelta tGlobal
        pairScale|)

/-- The canonical comparison enlargement used for every selected outcome. -/
def actualY1PaperFineSelectedAutomaticComparisonLambda
    {radius : NNReal} (globalDelta tGlobal pairScale : Real) : Real :=
  prop41AutomaticComparisonLambda
    (2 * actualY1PaperFineChoiceLambda
      (radius : Real) globalDelta tGlobal pairScale)
    (actualY1PaperFineChoiceLocalDelta
      (radius : Real) globalDelta tGlobal pairScale)
    pairScale

/-- The callback-free ordinary geometry package at the canonical center,
domain, comparison enlargement and ambient logarithmic depth. -/
structure ActualSharedGlobalPaperFineSelectedTwoScaleAutomaticGeometry
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale commonC : Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) where
  counting :
    ActualSharedGlobalPaperFineSelectedTwoScaleCountingNoSourcePairwisePackage
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
          tGlobal pairScale referenceScale
          (actualSharedGlobalPaperFineSelectedAutomaticDepth fine physical
            globalScale globalCenter)
          (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
            hfDeriv hf1Deriv outerA outerB hOuter)
          (Icc outerA outerB)
          (actualY1PaperFineSelectedAutomaticComparisonLambda
            (radius := radius) globalDelta tGlobal pairScale)
          hfDeriv hf1Deriv P

/-- All ordinary geometry fields of one already-produced uniform outcome are
automatic.  The strict independent-reference margin is outcome-independent;
the finite weight envelope is absorbed by the canonical positive tolerance. -/
theorem exists_actualSharedGlobalPaperFineSelectedTwoScaleAutomaticGeometry
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale commonC : Real)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (N : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hthree : ActualY1PaperFineThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal pairScale)
    (hcount : ActualY1PaperFineSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal pairScale)
    (hDfine : D.fine = fine)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical globalScale
      globalCenter D commonC)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hfirstUpper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc outerA outerB))
    (hreferenceMargin :
      max ((401 / 100 : Real) *
          actualY1PaperFineSelectedUniformCoefficientRadius
            (radius := radius) globalScale globalDelta tGlobal pairScale)
        (2 * actualY1PaperFineSelectedUniformCoefficientRadius
            (radius := radius) globalScale globalDelta tGlobal pairScale + 0) <
      3 * referenceScale) :
    Nonempty (ActualSharedGlobalPaperFineSelectedTwoScaleAutomaticGeometry
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
          tGlobal pairScale referenceScale commonC hOuter hfDeriv hf1Deriv P) := by
  let T := actualSharedGlobalPaperFineSelectedLeftTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let U := actualSharedGlobalPaperFineSelectedRightTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let family := retainedPairTubeFamily P.selected T U
  let weight := finiteActualTubeWeight family
  let weightEnvelope := finiteActualTubeFamilyWeightEnvelope family weight
  let rho := actualY1PaperFineSelectedUniformCoefficientRadius
    (radius := radius) globalScale globalDelta tGlobal pairScale
  have hweightEnvelope : 0 <= weightEnvelope := by
    exact finiteActualTubeFamilyWeightEnvelope_nonneg family weight
  have hcommon : forall V, V ∈ family -> tubeGraphC V = commonC := by
    intro V hV
    apply actualSharedGlobalPaperFineSelectedRetainedTube_fixed_c fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale P hDfine
          commonC C V
    simpa only [family, T, U] using hV
  have hdistance : forall V, V ∈ family ->
      tubePairCoefficientDistance V globalCenter <= rho := by
    intro V hV
    have hselected :=
      actualSharedGlobalPaperFineSelectedRetainedTube_distance_le fine physical
        globalScale globalCenter D keep rectangles left right ballRadius mu nu
          omega labelAt f outerA outerB globalDelta tGlobal pairScale P V
          (by simpa only [family, T, U] using hV)
    have hscale := actualY1PaperFineSelectedReferenceScale_le_uniform fine
      physical globalScale globalCenter D keep rectangles left right ballRadius
        mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale P
    dsimp only [rho, actualY1PaperFineSelectedUniformCoefficientRadius]
    exact hselected.trans (mul_le_mul_of_nonneg_left hscale (by norm_num))
  obtain ⟨externalTolerance, hexternalTolerance, hreference⟩ :=
    exists_positive_tolerance_fixedCommonC_family_reference family id
      (fun _ => 0) weight globalCenter commonC f f1 f2 hfDeriv hf1Deriv
      outerA outerB hOuter rho 0 weightEnvelope referenceScale
      hweightEnvelope (by simpa only [rho] using hreferenceMargin)
      (by intro V hV; exact hcommon V hV) hdistance
      (by intro V hV; norm_num)
      (by intro V hV; exact abs_weight_le_finiteFamilyWeightEnvelope weight hV)
      hparameter hfunction hfirstUpper hsecond
  let numerics := actualY1PaperFineSelectedCountingNumerics_of_pairScaleSmall
    N hthree hcount
  let comparisonLambda := actualY1PaperFineSelectedAutomaticComparisonLambda
    (radius := radius) globalDelta tGlobal pairScale
  refine ⟨{ counting := {
    weight := weight
    externalTolerance := externalTolerance
    graphBound := retainedPairPerturbedGraphBound P.selected T U weight
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
    common_c := by
      intro V hV W hW
      exact (hcommon V (by simpa only [family, T, U] using hV)).trans
        (hcommon W (by simpa only [family, T, U] using hW)).symm
    weight_injective := by
      simpa only [weight, family, T, U] using
        finiteActualTubeWeight_injOn family
    critical_finite := by
      apply actualTube_family_criticalHeightDifferenceSet_finite
        (retainedPairTubeFamily P.selected T U) f f1 f2
          numerics.interval_strict.le
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
    comparison_enlarges := by
      exact prop41AutomaticComparisonLambda_enlarges
        numerics.lambda1_ge_one numerics.delta_pos numerics.t_pos
    localization_scale := by
      exact prop41AutomaticComparisonLambda_localization
        numerics.lambda1_ge_one numerics.delta_pos numerics.t_pos
    reference := by
      intro epsilon hepsilon hepsilon_lt V hV
      rw [FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1.perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily]
        at hV
      simp only [individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV
      obtain ⟨W, hW, rfl⟩ := hV
      simpa only [individuallyTracePerturbedTube, id_eq, zero_add] using
        hreference epsilon hepsilon hepsilon_lt W
          (by simpa only [family, T, U] using hW)
    depth_bound := by
      exact actualSharedGlobalPaperFineSelected_depth_bound_automatic fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale P
    perturbed_graph_bound := by
      intro epsilon hepsilon hepsilon_lt V hV theta htheta
      exact perturbedRetainedTubeFamily_graph_le_automatic_bound P.selected
        T U weight f hexternalTolerance hepsilon hepsilon_lt hV theta
          (hparameter theta htheta) (hfunction theta htheta)
  } }⟩

#print axioms actualY1PaperFineSelectedUniformCoefficientRadius
#print axioms actualY1PaperFineSelectedAutomaticComparisonLambda
#print axioms ActualSharedGlobalPaperFineSelectedTwoScaleAutomaticGeometry
#print axioms exists_actualSharedGlobalPaperFineSelectedTwoScaleAutomaticGeometry

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleAutomaticGeometryRepoV2V1
