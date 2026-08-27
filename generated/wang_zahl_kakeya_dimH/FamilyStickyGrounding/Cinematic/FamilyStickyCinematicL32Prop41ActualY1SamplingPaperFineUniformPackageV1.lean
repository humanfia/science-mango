import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# A paper-fine uniform three-shift package on actual sampling survivors

The fixed-common-`c` connector supplies the exact selection record needed by
the automatic paper-fine three-shift producer.  This module specializes that
producer to one literal shared-global sampling outcome.

The output is deliberately a uniform package rather than a false direct call
to `actualSharedGlobalSurvivorLensCertificate_of_perturbationReady`.  The
three-shift theorem keeps a one-third subfiber, translates its left tubes by
one common shift, and uses the actual fine rectangles.  The current sampling
consumer is hard-wired to all survivors, the untranslated left tubes, and the
coarse survivor rectangles.  Those objects are not definitionally equal.
The package below records all identifications that are genuinely available
and exposes precisely the remaining consumer-adapter gap.
-/

/-- One uniform paper-fine three-shift output on a nonempty subfamily of the
literal survivor fibre.  All scalar choices are the automatic harmonic ones.
-/
structure ActualSharedGlobalSurvivorPaperFineUniformPackage
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
    (f : Real -> Real) (outerA outerB globalDelta tGlobal pairScale : Real) where
  shiftLabel : Fin 3
  eta : Real
  selected : Finset (ActualSharedGlobalSurvivorItem fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega)
  data : forall a, a ∈ selected ->
    PerturbationReadyPairLocalActualLensRectangleData
      (traceTranslateTube
        (fine.tubes (actualSharedGlobalSurvivorLeftIndex fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega a))
        (eta *
          (actualY1PaperFineChoiceLambda (radius : Real) globalDelta tGlobal
              pairScale *
            actualY1PaperFineChoiceLocalDelta (radius : Real) globalDelta
              tGlobal pairScale)))
      (fine.tubes (actualSharedGlobalSurvivorRightIndex fine physical
        globalScale globalCenter D keep rectangles left right ballRadius
          mu nu omega a))
      f (D.fineRectangleAt (labelAt a)) outerA outerB
      (actualY1PaperFineChoiceLocalDelta
        (radius : Real) globalDelta tGlobal pairScale)
      pairScale
      (actualY1PaperFineChoiceLambda
        (radius : Real) globalDelta tGlobal pairScale)
      (2 * actualY1PaperFineChoiceLambda
        (radius : Real) globalDelta tGlobal pairScale)
  eta_eq : eta = threeShiftValue shiftLabel
  eta_mem : eta ∈ ({(-1 : Real), 0, 1} : Set Real)
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆
    actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega
  cardinal_retention :
    (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega).card <=
      3 * selected.card
  left_retained : forall a, a ∈ selected ->
    (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega a,
      labelAt a) ∈ D.retainedGoodPairs keep
  right_retained : forall a, a ∈ selected ->
    (actualSharedGlobalSurvivorRightIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega a,
      labelAt a) ∈ D.retainedGoodPairs keep
  fine_subset_coarse : forall a, a ∈ selected ->
    (D.fineRectangleAt (labelAt a)).carrier (radius : Real) ⊆
      (D.coarseRectangleAt (labelAt a)).carrier globalDelta
  left_tube_identification : forall a, a ∈ selected ->
    actualSharedGlobalSurvivorLeftTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega a =
      fine.tubes (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega a)
  right_tube_identification : forall a, a ∈ selected ->
    actualSharedGlobalSurvivorRightTube fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega a =
      fine.tubes (actualSharedGlobalSurvivorRightIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega a)
  coarse_rectangle_identification : forall a, a ∈ selected ->
    D.coarseRectangleAt (labelAt a) =
      actualSharedGlobalSurvivorRectangle fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega a

/-- A fixed-common-`c` actual survivor selection feeds the automatic
paper-fine three-shift theorem.  Retained membership, exact common `c`, and
coefficient separation are supplied by the preceding connector; all literal
tangencies and fine-to-coarse carrier containment are produced by the
paper-fine geometry theorem.

The only scalar smallness input is
`ActualY1PaperFineThreeShiftPairScaleSmallness`.
-/
theorem exists_actualSharedGlobalSurvivorPaperFineUniformPackage_of_fixedCommonC
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (N : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (commonC pairScale : Real)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical globalScale
      globalCenter D commonC)
    (L : ActualSharedGlobalSurvivorCommonFineRefinement fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega)
    (hseparated : forall a : ActualSharedGlobalSurvivorItem fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega,
      2 * pairScale <= tubePairCoefficientDistance
        (D.fine.tubes (actualSharedGlobalSurvivorLeftIndex fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega a))
        (D.fine.tubes (actualSharedGlobalSurvivorRightIndex fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega a)))
    (hsurvivor : (twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).Nonempty)
    (hsmall : ActualY1PaperFineThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal pairScale) :
    Nonempty (ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega L.labelAt f outerA outerB globalDelta tGlobal pairScale) := by
  subst D
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 (radius : Real)
    (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
    globalDelta tGlobal
  have selection : ActualRetainedY1PairSelection D
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      L.labelAt keep pairScale := by
    exact actualSharedGlobalSurvivor_fixedCommonC_selection fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega commonC pairScale C L hseparated
  have hitems : (actualSharedGlobalSurvivorFiber fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega).Nonempty := by
    obtain ⟨R, hR⟩ := hsurvivor
    exact ⟨⟨R, hR⟩, Finset.mem_univ _⟩
  obtain ⟨k, eta, fiber, P, heta, hetaMem, hfiber, hsubset, hcard,
      hactual⟩ :=
    exists_uniform_threeShift_perturbationReady_of_actualRetainedY1Pairs_of_pairScaleSmall
      fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
      outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
      hpointE N hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      L.labelAt keep pairScale selection hitems hsmall
  refine ⟨{
    shiftLabel := k
    eta := eta
    selected := fiber
    data := P
    eta_eq := heta
    eta_mem := hetaMem
    selected_nonempty := hfiber
    selected_subset := hsubset
    cardinal_retention := hcard
    left_retained := ?_
    right_retained := ?_
    fine_subset_coarse := ?_
    left_tube_identification := ?_
    right_tube_identification := ?_
    coarse_rectangle_identification := ?_ }⟩
  · intro a ha
    exact (hactual a ha).1
  · intro a ha
    exact (hactual a ha).2.1
  · intro a ha
    exact (hactual a ha).2.2
  · intro _a _ha
    rfl
  · intro _a _ha
    rfl
  · intro a _ha
    exact L.coarse_at a

#print axioms ActualSharedGlobalSurvivorPaperFineUniformPackage
#print axioms exists_actualSharedGlobalSurvivorPaperFineUniformPackage_of_fixedCommonC

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
