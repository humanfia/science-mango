import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedSourcePairwiseV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleSourcePairwiseV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1
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
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedSourcePairwiseV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

/-!
# Two-scale source-pairwise connector for the selected paper-fine family

The old fine-label hypothesis rules out compact comparability whose common
container lies in the `3 * localScale` C2 ball.  It does not in general rule
out the two-scale relation when `referenceScale` is larger: enlarging the C2
ball only makes comparability easier.

There are two honest bridges below.  The preferred one assumes the
reference-free graph-rectangle incomparability.  Since every compact
two-scale witness forgets to such a graph-rectangle witness, this works for
an arbitrary independent reference scale.  The compatibility bridge from
the old compact hypothesis is available under `referenceScale <= localScale`.
-/

/-- Forgetting the C2-ball field of a two-scale compact witness gives the
reference-free common graph-container relation. -/
theorem symmetricGraphLambdaComparable_of_compactC2AtScales
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale comparisonLambda : Real}
    (h : compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale comparisonLambda) :
    symmetricGraphLambdaComparable R.rectangle S.rectangle
      delta localScale comparisonLambda := by
  rcases h with ⟨container, hlength, hcontain, _hball⟩
  exact ⟨container.rectangle, hlength, hcontain⟩

/-- Reference-free incomparability implies compact-C2 two-scale
incomparability for every center, domain and reference scale. -/
theorem not_compactC2AtScales_of_not_symmetricGraphLambdaComparable
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale comparisonLambda : Real}
    (h : Not (symmetricGraphLambdaComparable R.rectangle S.rectangle
      delta localScale comparisonLambda)) :
    Not (compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale comparisonLambda) := by
  exact fun hcompact => h
    (symmetricGraphLambdaComparable_of_compactC2AtScales hcompact)

/-- A two-scale witness with a no-larger reference scale is also an old
single-scale witness at the local scale. -/
theorem compactC2On_of_compactC2AtScales_of_referenceScale_le
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale comparisonLambda : Real}
    (hscale : referenceScale <= localScale)
    (h : compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale comparisonLambda) :
    compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta localScale comparisonLambda := by
  rcases h with ⟨container, hlength, hcontain, hball⟩
  refine ⟨container, hlength, hcontain, ?_⟩
  apply inPointwiseC2BallOn_mono_radius
    (r := 3 * referenceScale) (s := 3 * localScale)
  · gcongr
  · exact hball

/-- Consequently, the old fine-label relation is sufficient in the
restricted regime `referenceScale <= localScale`. -/
theorem not_compactC2AtScales_of_not_compactC2On_of_referenceScale_le
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale comparisonLambda : Real}
    (hscale : referenceScale <= localScale)
    (h : Not (compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta localScale comparisonLambda)) :
    Not (compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale comparisonLambda) := by
  exact fun htwo => h
    (compactC2On_of_compactC2AtScales_of_referenceScale_le hscale htwo)

/-- A global two-scale fine-label statement pulls back to the literal
selected fine rectangles. -/
theorem actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_fineLabelsPairwiseAtScales
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
    (delta localScale referenceScale comparisonLambda : Real)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (D.fineRectangleAt r) (D.fineRectangleAt s)
          delta localScale referenceScale comparisonLambda))) :
    Set.Pairwise (P.selected : Set _)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P i)
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P j)
        delta localScale referenceScale comparisonLambda)) := by
  have hinjective := actualSharedGlobalPaperFineSelected_labelAt_injOn
    fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
        pairScale P
  simpa only [actualSharedGlobalPaperFineSelectedRectangle] using
    (pairwise_pullback_of_labelAt_injOn P.selected labelAt D.fineRectangleAt
      (fun R S => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center R S delta localScale referenceScale comparisonLambda))
      hinjective hfineLabels)

/-- Preferred arbitrary-reference-scale connector.  A single global
reference-free fine-label incomparability statement supplies the two-scale
`source_pairwise` relation on every selected outcome. -/
theorem actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_referenceFreeFineLabelsPairwise
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
    (delta localScale referenceScale comparisonLambda : Real)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (symmetricGraphLambdaComparable
        (D.fineRectangleAt r).rectangle (D.fineRectangleAt s).rectangle
          delta localScale comparisonLambda))) :
    Set.Pairwise (P.selected : Set _)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P i)
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P j)
        delta localScale referenceScale comparisonLambda)) := by
  apply actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_fineLabelsPairwiseAtScales
    fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
        pairScale P domain center delta localScale referenceScale
          comparisonLambda
  intro r _hr s _hs hrs
  exact not_compactC2AtScales_of_not_symmetricGraphLambdaComparable
    (hfineLabels (Set.mem_univ r) (Set.mem_univ s) hrs)

/-- Compatibility connector from the old one-scale global fine-label
hypothesis.  The scale order is necessary for this implication. -/
theorem actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_oldFineLabelsPairwise
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
    (delta localScale referenceScale comparisonLambda : Real)
    (hscale : referenceScale <= localScale)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (D.fineRectangleAt r) (D.fineRectangleAt s)
          delta localScale comparisonLambda))) :
    Set.Pairwise (P.selected : Set _)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P i)
        (actualSharedGlobalPaperFineSelectedRectangle fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P j)
        delta localScale referenceScale comparisonLambda)) := by
  apply actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_fineLabelsPairwiseAtScales
    fine physical globalScale globalCenter D keep rectangles left right
      ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
        pairScale P domain center delta localScale referenceScale
          comparisonLambda
  intro r _hr s _hs hrs
  exact not_compactC2AtScales_of_not_compactC2On_of_referenceScale_le hscale
    (hfineLabels (Set.mem_univ r) (Set.mem_univ s) hrs)

#print axioms symmetricGraphLambdaComparable_of_compactC2AtScales
#print axioms not_compactC2AtScales_of_not_symmetricGraphLambdaComparable
#print axioms compactC2On_of_compactC2AtScales_of_referenceScale_le
#print axioms not_compactC2AtScales_of_not_compactC2On_of_referenceScale_le
#print axioms actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_fineLabelsPairwiseAtScales
#print axioms actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_referenceFreeFineLabelsPairwise
#print axioms actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_oldFineLabelsPairwise

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleSourcePairwiseV1
