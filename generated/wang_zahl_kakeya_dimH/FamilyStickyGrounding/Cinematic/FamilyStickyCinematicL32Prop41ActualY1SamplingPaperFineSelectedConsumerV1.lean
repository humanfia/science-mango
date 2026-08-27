import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SampledLensPaperShapeNumericsV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v w

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Consuming the retained paper-fine one-third subfamily

The three-shift package is counted on its literal selected subfamily.  Its
left endpoint is the common translated tube and its source rectangle is the
fine rectangle.  The resulting bound is transferred back only at the level
of cardinality, with the recorded factor three.
-/

/-- Residual finite-general-position and counting geometry for an arbitrary
perturbation-ready selected subfamily.  Pair-local data is deliberately an
argument of the consumer theorem rather than duplicated in this package. -/
structure SelectedSubfamilyFiniteGeneralPositionCountingPackage
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    (A B delta t lambda1 depth : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z) where
  weight : Tube radius -> Real
  center : C2GraphRectangle
  domain : Set Real
  comparisonLambda : Real
  externalTolerance : Real
  graphBound : Real
  externalTolerance_pos : 0 < externalTolerance
  interval_strict : A < B
  delta_pos : 0 < delta
  t_pos : 0 < t
  lambda1_ge_one : 1 <= lambda1
  interval_width : (1 / 2 : Real) <= B - A
  small_scale : prop41TangencyScaleFactor (4 * lambda1) * delta < t / 1200
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
      (4 * lambda1) delta t <= Real.sqrt (comparisonLambda * delta / t)
  reference : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B
          interval_strict.le) (3 * t)
  source_pairwise : Set.Pairwise (fiber : Set alpha)
    (fun i j => Not (compactC2SymmetricGraphLambdaComparableOn
      domain center (sourceRectangles i) (sourceRectangles j)
        delta t comparisonLambda))
  depth_bound :
    (canonicalDepth (FirstGenerationCurve
      (retainedPairTubeFamily fiber T U)) : Real) <= depth
  perturbed_graph_bound : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      forall theta, theta ∈ Icc A B ->
        |actualTubeGraph V f theta| <= graphBound

/-- A perturbation-ready selected subfamily satisfies the explicit lens
bound with its unperturbed retained endpoint-family cardinality. -/
theorem selectedSubfamily_card_le_sampledLensBound_of_perturbationReady
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (hfiber : fiber.Nonempty)
    (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    {A B delta t lambda0 lambda1 depth : Real}
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : forall i, i ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T i) (U i) f (sourceRectangles i)
          A B delta t lambda0 lambda1)
    (G : SelectedSubfamilyFiniteGeneralPositionCountingPackage
      fiber T U sourceRectangles f f1 f2 A B delta t lambda1 depth
        hfDeriv hf1Deriv) :
    (fiber.card : Real) <= sampledLensBound depth
      ((retainedPairTubeFamily fiber T U).card : Real) := by
  obtain ⟨S⟩ :=
    exists_perturbedRetainedPairEndpointAssembly_of_perturbationReady
      fiber hfiber T U sourceRectangles G.weight f f1 f2 G.center
      G.externalTolerance_pos G.interval_strict G.delta_pos G.t_pos
      G.lambda1_ge_one G.interval_width P hfDeriv hf1Deriv G.small_scale
      G.parameter_bound G.graph_function_bound G.first_derivative_lower
      G.first_derivative_upper G.second_derivative_bound
      G.second_derivative_continuous G.common_c G.weight_injective
      G.critical_finite G.comparison_enlarges G.localization_scale
      G.reference G.source_pairwise
  let curves := perturbedRetainedTubeFamily fiber T U G.weight S.epsilon
  have hcount : (fiber.card : Real) <=
      sampledLensBound
        (canonicalDepth (FirstGenerationCurve curves) : Real)
        (curves.card : Real) := by
    simpa only [sampledLensBound, curves] using
      pairLocalActualSelectedLens_card_le_explicit_global_of_endpointAssembly
        fiber T U sourceRectangles G.weight f f1 f2 G.center S
        G.interval_strict G.graphBound G.delta_pos G.t_pos G.lambda1_ge_one
        G.interval_width hfDeriv hf1Deriv G.small_scale G.parameter_bound
        G.graph_function_bound G.first_derivative_lower
        G.first_derivative_upper G.second_derivative_bound
        G.second_derivative_continuous
        (G.perturbed_graph_bound S.epsilon S.epsilon_pos
          S.epsilon_lt_external)
        G.comparison_enlarges G.localization_scale
        (G.reference S.epsilon S.epsilon_pos S.epsilon_lt_external)
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

/-! ## Literal paper-fine selected objects -/

/-- The selected left tube, including the common three-shift translation. -/
noncomputable def actualSharedGlobalPaperFineSelectedLeftTube
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :
    ActualSharedGlobalSurvivorItem fine physical globalScale globalCenter D
      keep rectangles left right ballRadius mu nu omega -> Tube radius :=
  fun a => traceTranslateTube
    (fine.tubes (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega a))
    (P.eta *
      (actualY1PaperFineChoiceLambda (radius : Real) globalDelta tGlobal
          pairScale *
        actualY1PaperFineChoiceLocalDelta (radius : Real) globalDelta tGlobal
          pairScale))

/-- The selected right tube is the literal sampled fine tube and is not
translated. -/
noncomputable def actualSharedGlobalPaperFineSelectedRightTube
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (_P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :
    ActualSharedGlobalSurvivorItem fine physical globalScale globalCenter D
      keep rectangles left right ballRadius mu nu omega -> Tube radius :=
  fun a => fine.tubes
    (actualSharedGlobalSurvivorRightIndex fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega a)

/-- The source rectangle used by the selected consumer is the actual fine
rectangle retained by the producer. -/
noncomputable def actualSharedGlobalPaperFineSelectedRectangle
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (_P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :
    ActualSharedGlobalSurvivorItem fine physical globalScale globalCenter D
      keep rectangles left right ballRadius mu nu omega -> C2GraphRectangle :=
  fun a => D.fineRectangleAt (labelAt a)

/-- The literal curve family counted on the selected paper-fine subfamily. -/
noncomputable def actualSharedGlobalPaperFineSelectedRetainedTubeFamily
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :
    Finset (Tube radius) :=
  retainedPairTubeFamily P.selected
    (actualSharedGlobalPaperFineSelectedLeftTube fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)
    (actualSharedGlobalPaperFineSelectedRightTube fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)


/-- Although the selected left endpoints are uniformly translated, their
literal retained family is still controlled by the two sampled index sets.
The proof counts the image of the left zero-colour sample under the translated
tube map and the image of the right sample under the unshifted tube map; it
does not identify either image with the original survivor tube family. -/
theorem actualSharedGlobalPaperFineSelectedRetainedTubeFamily_card_cast_le_load
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :
    ((actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale P).card :
          Real) <= twoSidedZeroColorLoad mu nu omega := by
  let T := actualSharedGlobalPaperFineSelectedLeftTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let U := actualSharedGlobalPaperFineSelectedRightTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let shift := P.eta *
    (actualY1PaperFineChoiceLambda (radius : Real) globalDelta tGlobal
        pairScale *
      actualY1PaperFineChoiceLocalDelta (radius : Real) globalDelta tGlobal
        pairScale)
  let leftFamily := (zeroColorSample mu omega.1).image
    (fun i : actualGlobalNormIndexFamily fine physical globalScale
      globalCenter => traceTranslateTube (fine.tubes i.1) shift)
  let rightFamily := (zeroColorSample nu omega.2).image
    (fun i : actualGlobalNormIndexFamily fine physical globalScale
      globalCenter => fine.tubes i.1)
  have hleft : forall a, a ∈ P.selected -> T a ∈ leftFamily := by
    intro a _ha
    apply Finset.mem_image.mpr
    refine ⟨(survivorLeftHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega a).1, ?_, ?_⟩
    · simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact (survivorLeftHitWitness mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega a).2.2
    · rfl
  have hright : forall a, a ∈ P.selected -> U a ∈ rightFamily := by
    intro a _ha
    apply Finset.mem_image.mpr
    refine ⟨(survivorRightHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega a).1, ?_, ?_⟩
    · simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact (survivorRightHitWitness mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega a).2.2
    · rfl
  have hcard :
      (retainedPairTubeFamily P.selected T U).card <=
        (zeroColorSample mu omega.1).card +
          (zeroColorSample nu omega.2).card := by
    calc
      (retainedPairTubeFamily P.selected T U).card <=
          leftFamily.card + rightFamily.card :=
        retainedPairTubeFamily_card_le_of_mem P.selected T U leftFamily
          rightFamily hleft hright
      _ <= (zeroColorSample mu omega.1).card +
          (zeroColorSample nu omega.2).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
  unfold twoSidedZeroColorLoad
  change ((retainedPairTubeFamily P.selected T U).card : Real) <=
    ((zeroColorSample mu omega.1).card : Real) +
      ((zeroColorSample nu omega.2).card : Real)
  exact_mod_cast hcard
/-- Short name for the exact residual geometry package on the selected
paper-fine objects. -/
abbrev ActualSharedGlobalPaperFineSelectedCountingPackage
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
    (outerA outerB globalDelta tGlobal pairScale depth : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :=
  SelectedSubfamilyFiniteGeneralPositionCountingPackage P.selected
    (actualSharedGlobalPaperFineSelectedLeftTube fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)
    (actualSharedGlobalPaperFineSelectedRightTube fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)
    (actualSharedGlobalPaperFineSelectedRectangle fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)
    f f1 f2 outerA outerB
    (actualY1PaperFineChoiceLocalDelta
      (radius : Real) globalDelta tGlobal pairScale)
    pairScale
    (2 * actualY1PaperFineChoiceLambda
      (radius : Real) globalDelta tGlobal pairScale)
    depth hfDeriv hf1Deriv


/-- Outcome-local consumer package.  It binds the dependent fine label map,
the literal one-third/three-shift producer, and exactly the residual finite
general-position geometry needed to count that selected family. -/
structure ActualSharedGlobalPaperFineSelectedOutcomePackage
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
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale depth : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z) where
  labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega ->
      fineLabel
  uniform : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale
  counting : ActualSharedGlobalPaperFineSelectedCountingPackage fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f f1 f2 outerA outerB globalDelta tGlobal pairScale depth
        hfDeriv hf1Deriv uniform
/-- Honest factor-three certificate: it bounds the original survivor count
using the literal selected, shifted, fine-rectangle curve family. -/
def ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (depth : Real) : Prop :=
  ((twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).card : Real) <=
    3 * sampledLensBound depth
      ((actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
        globalScale globalCenter D keep rectangles left right ballRadius mu nu
          omega labelAt f outerA outerB globalDelta tGlobal pairScale P).card :
            Real)
/-- The uniform paper-fine package plus residual selected-family geometry
produces the factor-three certificate for the original survivor count. -/
theorem actualSharedGlobalSurvivorPaperFineSelectedLensCertificate_of_uniformPackage
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
    (outerA outerB globalDelta tGlobal pairScale depth : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (G : ActualSharedGlobalPaperFineSelectedCountingPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f f1 f2 outerA outerB globalDelta tGlobal pairScale
          depth hfDeriv hf1Deriv P) :
    ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale P depth := by
  let T := actualSharedGlobalPaperFineSelectedLeftTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let U := actualSharedGlobalPaperFineSelectedRightTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let source := actualSharedGlobalPaperFineSelectedRectangle fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  have hdata : forall a, a ∈ P.selected ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T a) (U a) f (source a) outerA outerB
        (actualY1PaperFineChoiceLocalDelta
          (radius : Real) globalDelta tGlobal pairScale)
        pairScale
        (actualY1PaperFineChoiceLambda
          (radius : Real) globalDelta tGlobal pairScale)
        (2 * actualY1PaperFineChoiceLambda
          (radius : Real) globalDelta tGlobal pairScale) := by
    intro a ha
    simpa only [T, U, source, actualSharedGlobalPaperFineSelectedLeftTube,
      actualSharedGlobalPaperFineSelectedRightTube,
      actualSharedGlobalPaperFineSelectedRectangle] using P.data a ha
  have hselected :=
    selectedSubfamily_card_le_sampledLensBound_of_perturbationReady
      P.selected P.selected_nonempty T U source f f1 f2 hfDeriv hf1Deriv
        hdata G
  have hretention :
      ((actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega).card : Real) <=
        3 * (P.selected.card : Real) := by
    exact_mod_cast P.cardinal_retention
  unfold ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate
  rw [← actualSharedGlobalSurvivorFiber_card fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega]
  calc
    ((actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega).card : Real) <=
        3 * (P.selected.card : Real) := hretention
    _ <= 3 * sampledLensBound depth
        ((actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P).card : Real) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [actualSharedGlobalPaperFineSelectedRetainedTubeFamily,
        T, U] using hselected


/-- Load-valued form of the selected certificate.  This is the honest
consumer adapter used by random sampling: the factor three remains explicit,
while the shifted selected curve family is bounded by the literal two-sided
zero-colour load. -/
theorem ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate.card_le_three_mul_sampledLensBound_load
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (depth : Real) (hdepth : 0 <= depth)
    (C : ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate fine
      physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
        pairScale P depth) :
    ((twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).card : Real) <=
      3 * sampledLensBound depth (twoSidedZeroColorLoad mu nu omega) := by
  have hfamilyLoad :=
    actualSharedGlobalPaperFineSelectedRetainedTubeFamily_card_cast_le_load
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
          pairScale P
  have hmono := sampledLensBound_mono_curveCount hdepth
    (show 0 <=
      ((actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
        globalScale globalCenter D keep rectangles left right ballRadius mu nu
          omega labelAt f outerA outerB globalDelta tGlobal pairScale P).card :
            Real) by positivity) hfamilyLoad
  exact C.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))

/-- Zero-manual-connector form: the paper-fine uniform producer together with
its residual selected-family general-position package directly bounds the
original survivor count at the sampled load, with the exact retention factor
three. -/
theorem actualSharedGlobalSurvivor_card_le_three_mul_sampledLensBound_load_of_paperFineUniformPackage
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
    (outerA outerB globalDelta tGlobal pairScale depth : Real)
    (hdepth : 0 <= depth)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (G : ActualSharedGlobalPaperFineSelectedCountingPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f f1 f2 outerA outerB globalDelta tGlobal pairScale
          depth hfDeriv hf1Deriv P) :
    ((twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).card : Real) <=
      3 * sampledLensBound depth (twoSidedZeroColorLoad mu nu omega) := by
  let C :=
    actualSharedGlobalSurvivorPaperFineSelectedLensCertificate_of_uniformPackage
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
          tGlobal pairScale depth hfDeriv hf1Deriv P G
  exact C.card_le_three_mul_sampledLensBound_load fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega labelAt f
      outerA outerB globalDelta tGlobal pairScale P depth hdepth
/-- Exact adapter back to the former lossless sampling certificate.  Its
single additional premise is the missing numerical domination; no equality
between selected/fine/shifted and full/coarse/unshifted objects is asserted. -/
theorem ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate.toFullCertificate
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (depth : Real)
    (C : ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate fine
      physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
        pairScale P depth)
    (hdomination : 3 * sampledLensBound depth
      ((actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
        globalScale globalCenter D keep rectangles left right ballRadius mu nu
          omega labelAt f outerA outerB globalDelta tGlobal pairScale P).card :
            Real) <=
      sampledLensBound depth
        ((actualSharedGlobalSurvivorRetainedTubeFamily fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega).card : Real)) :
    ActualSharedGlobalSurvivorLensCertificate fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu depth omega := by
  exact C.trans hdomination


/-- At a nontrivial load, the one-third retention loss can be absorbed by an
explicit depth inflation.  No comparison of shifted and unshifted tube
objects is involved. -/
theorem three_mul_sampledLensBound_le_sampledLensBound_threeDepth_add_fourteen
    {depth load : Real} (hload : 1 <= load) :
    3 * sampledLensBound depth load <=
      sampledLensBound (3 * depth + 14) load := by
  have hloadNonneg : 0 <= load := by linarith
  have hsqrtOne : 1 <= Real.sqrt load := Real.one_le_sqrt.mpr hload
  have hlinear : load <= load * Real.sqrt load := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtOne hloadNonneg
    simpa using hmul
  unfold sampledLensBound
  nlinarith

/-- A nonempty two-sided survivor outcome has a nontrivial sampled load.
One genuine left zero-colour witness already suffices. -/
theorem one_le_twoSidedZeroColorLoad_of_survivors_nonempty
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (omega : (alpha -> Fin mu) × (beta -> Fin nu))
    (hsurvivor : (twoSidedZeroColorSurvivors mu nu leftNeighbors
      rightNeighbors omega).Nonempty) :
    1 <= twoSidedZeroColorLoad mu nu omega := by
  obtain ⟨R, hR⟩ := hsurvivor
  let S : TwoSidedZeroColorSurvivor mu nu leftNeighbors rightNeighbors omega :=
    ⟨R, hR⟩
  let w := survivorLeftHitWitness mu nu leftNeighbors rightNeighbors omega S
  have hw : w.1 ∈ zeroColorSample mu omega.1 := by
    simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ, true_and]
    exact w.2.2
  have hpositive : 0 < (zeroColorSample mu omega.1).card :=
    Finset.card_pos.mpr ⟨w.1, hw⟩
  have hnat : 1 <= (zeroColorSample mu omega.1).card +
      (zeroColorSample nu omega.2).card := by omega
  unfold twoSidedZeroColorLoad
  exact_mod_cast hnat

/-- Abstract random-sampling endpoint for a one-third retained lens callback.
The callback keeps its honest factor three; on nonempty outcomes it is
absorbed into `depth ↦ 3 * depth + 14`, while empty outcomes are closed by
nonnegativity. -/
theorem rectangleCard_le_eight_mul_sampledLensBound_threeDepth_add_fourteen_of_twoSidedSampling_factorThree
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleft : forall R, mu <= (leftNeighbors R).card)
    (hright : forall R, nu <= (rightNeighbors R).card)
    (depth : Real) (hdepth : 0 <= depth)
    (hsampledLens : forall omega :
        (alpha -> Fin mu) × (beta -> Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
          omega).card : Real) <=
        3 * sampledLensBound depth (twoSidedZeroColorLoad mu nu omega)) :
    (Fintype.card Rectangle : Real) <=
      8 * sampledLensBound (3 * depth + 14)
        (7 * ((Fintype.card alpha : Real) / (mu : Real) +
          (Fintype.card beta : Real) / (nu : Real))) := by
  have hinflated : 0 <= 3 * depth + 14 := by nlinarith
  apply rectangleCard_le_eight_mul_sampledLensBound_of_twoSidedSampling
    mu nu leftNeighbors rightNeighbors hleft hright (3 * depth + 14)
      hinflated
  intro omega
  by_cases hsurvivor : (twoSidedZeroColorSurvivors mu nu leftNeighbors
      rightNeighbors omega).Nonempty
  · exact (hsampledLens omega).trans
      (three_mul_sampledLensBound_le_sampledLensBound_threeDepth_add_fourteen
        (one_le_twoSidedZeroColorLoad_of_survivors_nonempty mu nu
          leftNeighbors rightNeighbors omega hsurvivor))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hsurvivor]
    norm_num only [Finset.card_empty, Nat.cast_zero]
    have hload : 0 <= twoSidedZeroColorLoad mu nu omega :=
      twoSidedZeroColorLoad_nonneg mu nu omega
    unfold sampledLensBound
    positivity

/-- Paper-shaped automatic-budget form of the preceding factor-three
sampling endpoint.  The leading sampling constant remains eight; the
one-third selection loss appears only in the explicit inflated depth. -/
theorem rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen_of_twoSidedSampling_factorThree_automaticBudget
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleft : forall R, mu <= (leftNeighbors R).card)
    (hright : forall R, nu <= (rightNeighbors R).card)
    (depth : Real) (hdepth : 0 <= depth)
    (hsampledLens : forall omega :
        (alpha -> Fin mu) × (beta -> Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
          omega).card : Real) <=
        3 * sampledLensBound depth (twoSidedZeroColorLoad mu nu omega)) :
    (Fintype.card Rectangle : Real) <=
      8 * (316 + 48 * (3 * depth + 14)) *
        (7 * ((Fintype.card alpha : Real) / (mu : Real) +
          (Fintype.card beta : Real) / (nu : Real))) *
        Real.sqrt
          (7 * ((Fintype.card alpha : Real) / (mu : Real) +
            (Fintype.card beta : Real) / (nu : Real))) := by
  have hinflated : 0 <= 3 * depth + 14 := by nlinarith
  apply rectangleCard_le_sampledLensPaperShape_of_twoSidedSampling_automaticBudget
    mu nu leftNeighbors rightNeighbors hleft hright (3 * depth + 14)
      hinflated
  intro omega
  by_cases hsurvivor : (twoSidedZeroColorSurvivors mu nu leftNeighbors
      rightNeighbors omega).Nonempty
  · exact (hsampledLens omega).trans
      (three_mul_sampledLensBound_le_sampledLensBound_threeDepth_add_fourteen
        (one_le_twoSidedZeroColorLoad_of_survivors_nonempty mu nu
          leftNeighbors rightNeighbors omega hsurvivor))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hsurvivor]
    norm_num only [Finset.card_empty, Nat.cast_zero]
    have hload : 0 <= twoSidedZeroColorLoad mu nu omega :=
      twoSidedZeroColorLoad_nonneg mu nu omega
    unfold sampledLensBound
    positivity

/-- Actual selected-paper-fine sampling endpoint with no bare lens inequality.
For each nonempty outcome it asks only for the dependent producer/counting
package above; empty outcomes are discharged automatically. -/
theorem actualSharedGlobalPaperFineSelected_rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen
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
    (hleft : forall R : rectangles,
      mu <= (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left R).card)
    (hright : forall R : rectangles,
      nu <= (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right R).card)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale depth : Real)
    (hdepth : 0 <= depth)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hgeometry : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu),
      (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).Nonempty ->
      ActualSharedGlobalPaperFineSelectedOutcomePackage fine physical
        globalScale globalCenter D keep rectangles left right ballRadius mu nu
          omega f f1 f2 outerA outerB globalDelta tGlobal pairScale depth
            hfDeriv hf1Deriv) :
    let ambient :=
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    let load := 7 * ((ambient.card : Real) / (mu : Real) +
      (ambient.card : Real) / (nu : Real))
    ((rectangles.card : Nat) : Real) <=
      8 * (316 + 48 * (3 * depth + 14)) * load * Real.sqrt load := by
  dsimp only
  let leftNeighbors :=
    actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left
  let rightNeighbors :=
    actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right
  have hsampledLens : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
        omega).card : Real) <=
        3 * sampledLensBound depth (twoSidedZeroColorLoad mu nu omega) := by
    intro omega
    by_cases hsurvivor : (twoSidedZeroColorSurvivors mu nu leftNeighbors
        rightNeighbors omega).Nonempty
    · let O := hgeometry omega hsurvivor
      exact
        actualSharedGlobalSurvivor_card_le_three_mul_sampledLensBound_load_of_paperFineUniformPackage
          fine physical globalScale globalCenter D keep rectangles left right
            ballRadius mu nu omega O.labelAt f f1 f2 outerA outerB globalDelta
              tGlobal pairScale depth hdepth hfDeriv hf1Deriv O.uniform
                O.counting
    · rw [Finset.not_nonempty_iff_eq_empty.mp hsurvivor]
      norm_num only [Finset.card_empty, Nat.cast_zero]
      have hload : 0 <= twoSidedZeroColorLoad mu nu omega :=
        twoSidedZeroColorLoad_nonneg mu nu omega
      unfold sampledLensBound
      positivity
  simpa only [leftNeighbors, rightNeighbors, Fintype.card_coe] using
    (rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen_of_twoSidedSampling_factorThree_automaticBudget
      mu nu leftNeighbors rightNeighbors hleft hright depth hdepth
        hsampledLens)
/-- A factor three cannot be absorbed merely by identifying the two curve
counts when the sampled lens bound is positive. -/
theorem factorThree_not_absorbed_at_same_positive_sampledLensBound
    {depth curveCount : Real}
    (hpositive : 0 < sampledLensBound depth curveCount) :
    ¬ 3 * sampledLensBound depth curveCount <=
      sampledLensBound depth curveCount := by
  nlinarith

#print axioms actualSharedGlobalPaperFineSelectedLeftTube
#print axioms actualSharedGlobalPaperFineSelectedRightTube
#print axioms actualSharedGlobalPaperFineSelectedRectangle
#print axioms actualSharedGlobalPaperFineSelectedRetainedTubeFamily
#print axioms actualSharedGlobalPaperFineSelectedRetainedTubeFamily_card_cast_le_load
#print axioms ActualSharedGlobalPaperFineSelectedCountingPackage
#print axioms ActualSharedGlobalPaperFineSelectedOutcomePackage
#print axioms ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate
#print axioms actualSharedGlobalSurvivorPaperFineSelectedLensCertificate_of_uniformPackage
#print axioms ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate.card_le_three_mul_sampledLensBound_load
#print axioms actualSharedGlobalSurvivor_card_le_three_mul_sampledLensBound_load_of_paperFineUniformPackage
#print axioms ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate.toFullCertificate
#print axioms three_mul_sampledLensBound_le_sampledLensBound_threeDepth_add_fourteen
#print axioms one_le_twoSidedZeroColorLoad_of_survivors_nonempty
#print axioms rectangleCard_le_eight_mul_sampledLensBound_threeDepth_add_fourteen_of_twoSidedSampling_factorThree
#print axioms rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen_of_twoSidedSampling_factorThree_automaticBudget
#print axioms actualSharedGlobalPaperFineSelected_rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen
#print axioms factorThree_not_absorbed_at_same_positive_sampledLensBound
#print axioms SelectedSubfamilyFiniteGeneralPositionCountingPackage
#print axioms selectedSubfamily_card_le_sampledLensBound_of_perturbationReady

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
