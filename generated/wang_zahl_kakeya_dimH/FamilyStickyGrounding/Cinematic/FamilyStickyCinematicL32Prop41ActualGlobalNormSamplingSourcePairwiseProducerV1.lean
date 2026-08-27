import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingAutomaticGeneralPositionConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingSourcePairwiseProducerV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41ActualFiniteGeneralPositionDataProducerV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingAutomaticGeneralPositionConnectorV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Restricting global rectangle noncomparability to sampling survivors

A survivor is a subtype of the finite rectangle subtype.  Its source map is
therefore membership-preserving and injective before any geometry is used.
This lets one global pairwise hypothesis on `rectangles` discharge every
outcome-local endpoint `source_pairwise` premise.
-/

/-- Every actual survivor carries a literal member of the input rectangle
finset. -/
theorem actualSharedGlobalSurvivorRectangle_mem
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
    (R : TwoSidedZeroColorSurvivor mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega) :
    actualSharedGlobalSurvivorRectangle fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega R ∈ rectangles := by
  exact R.1.2

/-- Forgetting the two subtype proofs loses no survivor identity. -/
theorem actualSharedGlobalSurvivorRectangle_injective
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
          Fin nu)) :
    Function.Injective
      (actualSharedGlobalSurvivorRectangle fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega) := by
  intro R S hRS
  apply Subtype.ext
  apply Subtype.ext
  exact hRS

/-- Fiber-local form consumed by endpoint bookkeeping. -/
theorem actualSharedGlobalSurvivorRectangle_injOn_fiber
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
          Fin nu)) :
    Set.InjOn
      (actualSharedGlobalSurvivorRectangle fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega : Set _) := by
  exact (actualSharedGlobalSurvivorRectangle_injective fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega).injOn

/-- A single pairwise noncomparability statement on all source rectangles
restricts automatically to the survivor fiber of every outcome. -/
theorem actualSharedGlobalSurvivor_sourcePairwise_of_rectanglesPairwise
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
    (domain : Set Real) (center : C2GraphRectangle)
    (delta t comparisonLambda : Real)
    (hrectanglesPairwise : Set.Pairwise
      (rectangles : Set C2GraphRectangle)
      (fun R S => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center R S delta t comparisonLambda))) :
    Set.Pairwise
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega : Set _)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center
        (actualSharedGlobalSurvivorRectangle fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega i)
        (actualSharedGlobalSurvivorRectangle fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega j)
        delta t comparisonLambda)) := by
  intro i hi j hj hij
  apply hrectanglesPairwise
  · exact actualSharedGlobalSurvivorRectangle_mem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega i
  · exact actualSharedGlobalSurvivorRectangle_mem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega j
  · intro hsource
    exact hij ((actualSharedGlobalSurvivorRectangle_injOn_fiber fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega) hi hj hsource)

#print axioms actualSharedGlobalSurvivorRectangle_mem
#print axioms actualSharedGlobalSurvivorRectangle_injective
#print axioms actualSharedGlobalSurvivorRectangle_injOn_fiber
#print axioms actualSharedGlobalSurvivor_sourcePairwise_of_rectanglesPairwise

end

end FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingSourcePairwiseProducerV1
