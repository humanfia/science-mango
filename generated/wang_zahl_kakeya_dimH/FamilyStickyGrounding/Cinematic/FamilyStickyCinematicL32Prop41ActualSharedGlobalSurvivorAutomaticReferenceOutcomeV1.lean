import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceOutcomeV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticBoundsV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Actual sampling-outcome automatic common reference

The neighbour hit witnesses are already elements of the global-norm index
subtype.  The sole identification needed to turn that fact into a statement
about the literal tubes stored in the sampling endpoint is `D.fine = fine`.
For the actual rectangle producer this equality follows by rewriting its
existing `D = actualCenteredHalfY1FineCoarseRectangleData ...` certificate.
-/

/-- Every literal tube retained by one actual sampling outcome belongs to
the same coefficient ball of radius `3 * globalScale` about `globalCenter`. -/
theorem actualSharedGlobalSurvivorRetainedTube_distance_le_three_mul
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
    (hDfine : D.fine = fine) (V : Tube radius)
    (hV : V ∈ actualSharedGlobalSurvivorRetainedTubeFamily fine physical
      globalScale globalCenter D keep rectangles left right ballRadius
        mu nu omega) :
    tubePairCoefficientDistance V globalCenter <= 3 * globalScale := by
  rw [← actualSharedGlobalSurvivorRetainedTubeFamily_eq fine physical
    globalScale globalCenter D keep rectangles left right ballRadius
      mu nu omega] at hV
  simp only [retainedPairTubeFamily, Finset.mem_union,
    Finset.mem_image] at hV
  rcases hV with ⟨S, _hS, rfl⟩ | ⟨S, _hS, rfl⟩
  · simpa only [actualSharedGlobalSurvivorLeftTube, hDfine] using
      actualGlobalNormIndex_tube_distance_le_three_mul fine physical
        globalScale globalCenter
        (survivorLeftHitWitness mu nu
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius left)
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius right) omega S).1
  · simpa only [actualSharedGlobalSurvivorRightTube, hDfine] using
      actualGlobalNormIndex_tube_distance_le_three_mul fine physical
        globalScale globalCenter
        (survivorRightHitWitness mu nu
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius left)
          (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
            globalCenter D keep rectangles ballRadius right) omega S).1

/-- A nonempty literal survivor outcome automatically produces exactly the
`center`, `domain`, and `reference` data required by the shared-global
geometry package.  No graph bound, depth, or source-pairwise field is bundled
here, so this result composes directly with the independent producers. -/
theorem exists_actualSharedGlobalSurvivorAutomaticReferenceData
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
    (hsurvivor :
      (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).Nonempty)
    (hDfine : D.fine = fine)
    (weight : Tube radius -> Real) (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) (externalTolerance t : Real)
    (hexternalTolerance : 0 < externalTolerance)
    (hcommonC : forall V, V ∈ retainedPairTubeFamily
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega) -> forall W,
      W ∈ retainedPairTubeFamily
        (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
          D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorLeftTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega)
        (actualSharedGlobalSurvivorRightTube fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega) ->
        tubeGraphC V = tubeGraphC W)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirst : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hbudget : 30 * globalScale + externalTolerance *
      finiteActualTubeFamilyWeightEnvelope
        (actualSharedGlobalSurvivorRetainedTubeFamily fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega) weight <= 3 * t) :
    Nonempty (RetainedPairAutomaticReferenceData
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      weight f f1 f2 hfDeriv hf1Deriv A B hAB externalTolerance t) := by
  let fiber := actualSharedGlobalSurvivorFiber fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let T := actualSharedGlobalSurvivorLeftTube fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  let U := actualSharedGlobalSurvivorRightTube fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega
  have hfiber : fiber.Nonempty := by
    obtain ⟨R, hR⟩ := hsurvivor
    exact ⟨⟨R, hR⟩, by simp only [fiber,
      actualSharedGlobalSurvivorFiber, Finset.mem_univ]⟩
  have hglobal : forall V, V ∈ retainedPairTubeFamily fiber T U ->
      tubePairCoefficientDistance V globalCenter <= 3 * globalScale := by
    intro V hV
    apply actualSharedGlobalSurvivorRetainedTube_distance_le_three_mul
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega hDfine V
    rw [← actualSharedGlobalSurvivorRetainedTubeFamily_eq fine physical
      globalScale globalCenter D keep rectangles left right ballRadius
        mu nu omega]
    simpa only [fiber, T, U] using hV
  have hbudget' : 30 * globalScale + externalTolerance *
      finiteActualTubeFamilyWeightEnvelope
        (retainedPairTubeFamily fiber T U) weight <= 3 * t := by
    rw [actualSharedGlobalSurvivorRetainedTubeFamily_eq fine physical
      globalScale globalCenter D keep rectangles left right ballRadius
        mu nu omega]
    simpa only [fiber, T, U] using hbudget
  exact exists_retainedPairAutomaticReferenceData_of_globalNorm
    fiber hfiber T U weight f f1 f2 hfDeriv hf1Deriv A B hAB
      globalScale globalCenter externalTolerance t hexternalTolerance hglobal
      (by simpa only [fiber, T, U] using hcommonC) hparameter hfunction
        hfirst hsecond hbudget'

#print axioms actualSharedGlobalSurvivorRetainedTube_distance_le_three_mul
#print axioms exists_actualSharedGlobalSurvivorAutomaticReferenceData

end

end FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceOutcomeV1
