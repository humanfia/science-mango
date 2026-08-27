import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingSourcePairwiseProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedSourcePairwiseV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
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
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingSourcePairwiseProducerV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v w

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Source-pairwise automation for the selected paper-fine family

The selected three-shift producer records that every fine label maps back to
the survivor's literal coarse source rectangle.  Since the survivor source
map is injective, the label map is injective on the selected subfamily.  A
single pairwise noncomparability statement on all fine labels can therefore
be pulled back to the outcome-local selected source rectangles.
-/

/-- If an injective source is recovered from a label through a coarse map,
then the label is injective on the same finite fiber. -/
theorem labelAt_injOn_of_source_injOn_of_identification
    {alpha : Type u} {label : Type v} {sourceType : Type w}
    (fiber : Finset alpha) (labelAt : alpha -> label)
    (coarseAt : label -> sourceType) (source : alpha -> sourceType)
    (hsource : Set.InjOn source (fiber : Set alpha))
    (hidentification : forall a, a ∈ fiber ->
      coarseAt (labelAt a) = source a) :
    Set.InjOn labelAt (fiber : Set alpha) := by
  intro a ha b hb hab
  apply hsource ha hb
  calc
    source a = coarseAt (labelAt a) := (hidentification a ha).symm
    _ = coarseAt (labelAt b) := by rw [hab]
    _ = source b := hidentification b hb

/-- Pairwise data on all labels pulls back along a label map that is
injective on the selected fiber. -/
theorem pairwise_pullback_of_labelAt_injOn
    {alpha : Type u} {label : Type v} {sourceType : Type w}
    (fiber : Finset alpha) (labelAt : alpha -> label)
    (sourceAt : label -> sourceType) (relation : sourceType -> sourceType -> Prop)
    (hinjective : Set.InjOn labelAt (fiber : Set alpha))
    (hlabels : Set.Pairwise (Set.univ : Set label)
      (fun r s => relation (sourceAt r) (sourceAt s))) :
    Set.Pairwise (fiber : Set alpha)
      (fun a b => relation (sourceAt (labelAt a))
        (sourceAt (labelAt b))) := by
  intro a ha b hb hab
  apply hlabels (Set.mem_univ _) (Set.mem_univ _)
  intro hlabel
  exact hab (hinjective ha hb hlabel)


/-- All selected-family counting geometry except source pairwise data.  The
comparison context is an external parameter, so one global fine-label
pairwise statement can serve every outcome using this same context. -/
structure SelectedSubfamilyFiniteGeneralPositionCountingNoSourcePairwisePackage
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    (A B delta t lambda1 depth : Real)
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
  depth_bound :
    (canonicalDepth (FirstGenerationCurve
      (retainedPairTubeFamily fiber T U)) : Real) <= depth
  perturbed_graph_bound : forall epsilon, 0 < epsilon ->
    epsilon < externalTolerance -> forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      forall theta, theta ∈ Icc A B ->
        |actualTubeGraph V f theta| <= graphBound

/-- Restore the full selected counting package from one source-pairwise
proof; every other field is copied definitionally. -/
def SelectedSubfamilyFiniteGeneralPositionCountingNoSourcePairwisePackage.toCountingPackage
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    {fiber : Finset alpha} {T U : alpha -> Tube radius}
    {sourceRectangles : alpha -> C2GraphRectangle}
    {f f1 f2 : Real -> Real}
    {A B delta t lambda1 depth : Real}
    {center : C2GraphRectangle} {domain : Set Real}
    {comparisonLambda : Real}
    {hfDeriv : forall z, HasDerivAt f (f1 z) z}
    {hf1Deriv : forall z, HasDerivAt f1 (f2 z) z}
    (G : SelectedSubfamilyFiniteGeneralPositionCountingNoSourcePairwisePackage
      fiber T U sourceRectangles f f1 f2 A B delta t lambda1 depth center
        domain comparisonLambda hfDeriv hf1Deriv)
    (hsource : Set.Pairwise (fiber : Set alpha)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (sourceRectangles i) (sourceRectangles j)
          delta t comparisonLambda))) :
    SelectedSubfamilyFiniteGeneralPositionCountingPackage fiber T U
      sourceRectangles f f1 f2 A B delta t lambda1 depth hfDeriv hf1Deriv where
  weight := G.weight
  center := center
  domain := domain
  comparisonLambda := comparisonLambda
  externalTolerance := G.externalTolerance
  graphBound := G.graphBound
  externalTolerance_pos := G.externalTolerance_pos
  interval_strict := G.interval_strict
  delta_pos := G.delta_pos
  t_pos := G.t_pos
  lambda1_ge_one := G.lambda1_ge_one
  interval_width := G.interval_width
  small_scale := G.small_scale
  parameter_bound := G.parameter_bound
  graph_function_bound := G.graph_function_bound
  first_derivative_lower := G.first_derivative_lower
  first_derivative_upper := G.first_derivative_upper
  second_derivative_bound := G.second_derivative_bound
  second_derivative_continuous := G.second_derivative_continuous
  common_c := G.common_c
  weight_injective := G.weight_injective
  critical_finite := G.critical_finite
  comparison_enlarges := G.comparison_enlarges
  localization_scale := G.localization_scale
  reference := G.reference
  source_pairwise := hsource
  depth_bound := G.depth_bound
  perturbed_graph_bound := G.perturbed_graph_bound
/-- The fine-label selector in a uniform selected package is injective on
the selected subfamily.  The proof uses only the recorded selected-subset
fact and the honest coarse-source identification. -/
theorem actualSharedGlobalPaperFineSelected_labelAt_injOn
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
    Set.InjOn labelAt (P.selected : Set _) := by
  let source := actualSharedGlobalSurvivorRectangle fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  have hsource : Set.InjOn source (P.selected : Set _) := by
    intro a ha b hb hab
    exact (actualSharedGlobalSurvivorRectangle_injOn_fiber fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega) (P.selected_subset ha) (P.selected_subset hb) hab
  exact labelAt_injOn_of_source_injOn_of_identification P.selected labelAt
    D.coarseRectangleAt source hsource P.coarse_rectangle_identification

/-- A single global fine-label noncomparability hypothesis supplies the
`source_pairwise` field for the literal selected fine rectangles. -/
theorem actualSharedGlobalPaperFineSelected_sourcePairwise_of_fineLabelsPairwise
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
    (domain : Set Real) (center : C2GraphRectangle)
    (delta t comparisonLambda : Real)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (D.fineRectangleAt r) (D.fineRectangleAt s)
          delta t comparisonLambda))) :
    Set.Pairwise (P.selected : Set _)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P i)
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P j)
        delta t comparisonLambda)) := by
  have hinjective := actualSharedGlobalPaperFineSelected_labelAt_injOn
    fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
        pairScale P
  simpa only [actualSharedGlobalPaperFineSelectedRectangle] using
    (pairwise_pullback_of_labelAt_injOn P.selected labelAt D.fineRectangleAt
      (fun R S => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center R S delta t comparisonLambda)) hinjective hfineLabels)


/-- Actual paper-fine specialization of the slim selected counting package. -/
abbrev ActualSharedGlobalPaperFineSelectedCountingNoSourcePairwisePackage
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
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :=
  SelectedSubfamilyFiniteGeneralPositionCountingNoSourcePairwisePackage
    P.selected
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
    depth center domain comparisonLambda hfDeriv hf1Deriv

/-- Convert the slim actual package using one global fine-label pairwise
hypothesis in the fixed comparison context. -/
def actualSharedGlobalPaperFineSelectedCountingPackage_of_fineLabelsPairwise
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    {fine : UniformTubeFamily radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {globalScale : Real} {globalCenter : Tube radius}
    {D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel}
    {keep : iota -> fineLabel -> Prop}
    {rectangles : Finset C2GraphRectangle}
    {left right : Tube radius} {ballRadius : Real}
    {mu nu : Nat} [NeZero mu] [NeZero nu]
    {omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)}
    {labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel}
    {f f1 f2 : Real -> Real}
    {outerA outerB globalDelta tGlobal pairScale depth : Real}
    {center : C2GraphRectangle} {domain : Set Real}
    {comparisonLambda : Real}
    {hfDeriv : forall z, HasDerivAt f (f1 z) z}
    {hf1Deriv : forall z, HasDerivAt f1 (f2 z) z}
    {P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale}
    (G : ActualSharedGlobalPaperFineSelectedCountingNoSourcePairwisePackage
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
          tGlobal pairScale depth center domain comparisonLambda hfDeriv
            hf1Deriv P)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (D.fineRectangleAt r) (D.fineRectangleAt s)
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale comparisonLambda))) :
    ActualSharedGlobalPaperFineSelectedCountingPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f f1 f2 outerA outerB globalDelta tGlobal pairScale
          depth hfDeriv hf1Deriv P := by
  apply G.toCountingPackage
  exact actualSharedGlobalPaperFineSelected_sourcePairwise_of_fineLabelsPairwise
    fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
        pairScale P domain center
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale comparisonLambda hfineLabels

/-- Outcome-local selected producer and residual counting geometry with the
source-pairwise field removed.  The comparison context is fixed externally. -/
structure ActualSharedGlobalPaperFineSelectedOutcomeNoSourcePairwisePackage
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
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z) where
  labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega ->
      fineLabel
  uniform : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale
  counting : ActualSharedGlobalPaperFineSelectedCountingNoSourcePairwisePackage
    fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta tGlobal
        pairScale depth center domain comparisonLambda hfDeriv hf1Deriv uniform

/-- Insert the globally supplied fine-label pairwise fact and recover the
former full outcome package. -/
def ActualSharedGlobalPaperFineSelectedOutcomeNoSourcePairwisePackage.toOutcomePackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    {fine : UniformTubeFamily radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {globalScale : Real} {globalCenter : Tube radius}
    {D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel}
    {keep : iota -> fineLabel -> Prop}
    {rectangles : Finset C2GraphRectangle}
    {left right : Tube radius} {ballRadius : Real}
    {mu nu : Nat} [NeZero mu] [NeZero nu]
    {omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu)}
    {f f1 f2 : Real -> Real}
    {outerA outerB globalDelta tGlobal pairScale depth : Real}
    {center : C2GraphRectangle} {domain : Set Real}
    {comparisonLambda : Real}
    {hfDeriv : forall z, HasDerivAt f (f1 z) z}
    {hf1Deriv : forall z, HasDerivAt f1 (f2 z) z}
    (O : ActualSharedGlobalPaperFineSelectedOutcomeNoSourcePairwisePackage
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega f f1 f2 outerA outerB globalDelta tGlobal
          pairScale depth center domain comparisonLambda hfDeriv hf1Deriv)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (D.fineRectangleAt r) (D.fineRectangleAt s)
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale comparisonLambda))) :
    ActualSharedGlobalPaperFineSelectedOutcomePackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega f f1 f2 outerA outerB globalDelta tGlobal pairScale depth
          hfDeriv hf1Deriv where
  labelAt := O.labelAt
  uniform := O.uniform
  counting := actualSharedGlobalPaperFineSelectedCountingPackage_of_fineLabelsPairwise
    O.counting hfineLabels

/-- Final selected paper-fine endpoint with one global pairwise hypothesis on
all fine labels and no outcome-local `source_pairwise` callback.  All other
finite-general-position and counting fields remain in the slim outcome
package. -/
theorem actualSharedGlobalPaperFineSelected_rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen_of_globalFineLabelsPairwise
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
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
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
      ActualSharedGlobalPaperFineSelectedOutcomeNoSourcePairwisePackage
        fine physical globalScale globalCenter D keep rectangles left right
          ballRadius mu nu omega f f1 f2 outerA outerB globalDelta tGlobal
            pairScale depth center domain comparisonLambda hfDeriv hf1Deriv)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (D.fineRectangleAt r) (D.fineRectangleAt s)
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale comparisonLambda))) :
    let ambient :=
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    let load := 7 * ((ambient.card : Real) / (mu : Real) +
      (ambient.card : Real) / (nu : Real))
    ((rectangles.card : Nat) : Real) <=
      8 * (316 + 48 * (3 * depth + 14)) * load * Real.sqrt load := by
  apply
    actualSharedGlobalPaperFineSelected_rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu hleft hright f f1 f2 outerA outerB globalDelta
          tGlobal pairScale depth hdepth hfDeriv hf1Deriv
  intro omega hsurvivor
  exact (hgeometry omega hsurvivor).toOutcomePackage hfineLabels
#print axioms labelAt_injOn_of_source_injOn_of_identification
#print axioms pairwise_pullback_of_labelAt_injOn
#print axioms SelectedSubfamilyFiniteGeneralPositionCountingNoSourcePairwisePackage
#print axioms SelectedSubfamilyFiniteGeneralPositionCountingNoSourcePairwisePackage.toCountingPackage
#print axioms actualSharedGlobalPaperFineSelected_labelAt_injOn
#print axioms actualSharedGlobalPaperFineSelected_sourcePairwise_of_fineLabelsPairwise
#print axioms ActualSharedGlobalPaperFineSelectedCountingNoSourcePairwisePackage
#print axioms actualSharedGlobalPaperFineSelectedCountingPackage_of_fineLabelsPairwise
#print axioms ActualSharedGlobalPaperFineSelectedOutcomeNoSourcePairwisePackage
#print axioms ActualSharedGlobalPaperFineSelectedOutcomeNoSourcePairwisePackage.toOutcomePackage
#print axioms actualSharedGlobalPaperFineSelected_rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen_of_globalFineLabelsPairwise

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedSourcePairwiseV1
