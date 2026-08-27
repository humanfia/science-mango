import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1ExactCFiberPairSelectionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualY1ExactCFiberPairSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v w x

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Fixed common-c provenance and lossless retained-pair connectors

An approximate positive-width graph-`c` bucket cannot discharge the literal
`common_c` field of `ActualRetainedY1PairSelection`.  This module instead
records exact fixed-`c` provenance and transports it without any further
`c`-refinement.

There are three layers:

* a generic retained-pair provenance record and its lossless connector;
* a fixed fine-fibre specialization, identified with the exact fibre from
  `ActualY1ExactCFiberPairSelectionV1`;
* the actual shared-global sampling survivor specialization.  The sampling
  construction automatically supplies retained incidences over the same
  coarse rectangle, but not a common fine label.  Consequently the latter is
  isolated as one explicit refinement datum.  Coefficient separation is also
  an explicit quantitative input.
-/

/-! ## Generic fixed-common-c retained pairs -/

/-- Exact upstream provenance for an arbitrary finite family of actual
retained pairs.  Both incidences use the single displayed `labelAt`; exact
fixed-`c` facts are stated separately for the two endpoints. -/
structure ActualFixedCommonCRetainedPairProvenance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type x}
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (items : Finset alpha)
    (leftIndex rightIndex : alpha -> iota)
    (labelAt : alpha -> fineLabel)
    (keep : iota -> fineLabel -> Prop) (commonC : Real) : Prop where
  left_retained : forall a, a ∈ items ->
    (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep
  right_retained : forall a, a ∈ items ->
    (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep
  left_fixed_c : forall a, a ∈ items ->
    tubeGraphC (D.fine.tubes (leftIndex a)) = commonC
  right_fixed_c : forall a, a ∈ items ->
    tubeGraphC (D.fine.tubes (rightIndex a)) = commonC

/-- Adding the literal coefficient lower bound turns fixed-common-`c`
provenance into `ActualRetainedY1PairSelection` on exactly the same item
family.  Thus this connector has no cardinality loss. -/
theorem ActualFixedCommonCRetainedPairProvenance.toSelection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type x}
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha}
    {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel}
    {keep : iota -> fineLabel -> Prop} {commonC pairScale : Real}
    (P : ActualFixedCommonCRetainedPairProvenance D items
      leftIndex rightIndex labelAt keep commonC)
    (hseparated : forall a, a ∈ items ->
      2 * pairScale <= tubePairCoefficientDistance
        (D.fine.tubes (leftIndex a)) (D.fine.tubes (rightIndex a))) :
    ActualRetainedY1PairSelection D items leftIndex rightIndex labelAt
      keep pairScale := by
  constructor
  · exact P.left_retained
  · exact P.right_retained
  · intro a ha
    exact (P.left_fixed_c a ha).trans (P.right_fixed_c a ha).symm
  · exact hseparated

/-! ## A genuinely fixed retained fine fibre -/

/-- Upstream provenance saying that every retained incidence at one literal
fine label has the same exact graph-`c` value. -/
structure ActualRetainedFineFiberFixedCProvenance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel)
    (commonC : Real) : Prop where
  fixed_c : forall i, i ∈ retainedY1IndicesAtFine D keep r ->
    tubeGraphC (D.fine.tubes i) = commonC

/-- Under exact fixed-`c` provenance, the exact fibre is the whole retained
fine fibre.  This is the formal no-loss statement. -/
theorem ActualRetainedFineFiberFixedCProvenance.exactFiber_eq_source
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {keep : iota -> fineLabel -> Prop} {r : fineLabel} {commonC : Real}
    (P : ActualRetainedFineFiberFixedCProvenance D keep r commonC) :
    retainedY1ExactCFiberAtFine D keep r commonC =
      retainedY1IndicesAtFine D keep r := by
  unfold retainedY1ExactCFiberAtFine
  exact exactValueFiber_eq_source_of_constant
    (retainedY1IndicesAtFine D keep r)
    (fun i => tubeGraphC (D.fine.tubes i)) commonC P.fixed_c

/-- All coefficient-separated ordered pairs in the retained fine fibre.
There is no graph-`c` filter in this definition. -/
noncomputable def retainedY1FixedCSeparatedPairsAtFine
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel)
    (pairScale : Real) : Finset (iota × iota) := by
  classical
  exact ((retainedY1IndicesAtFine D keep r).product
    (retainedY1IndicesAtFine D keep r)).filter fun pair =>
      2 * pairScale <= tubePairCoefficientDistance
        (D.fine.tubes pair.1) (D.fine.tubes pair.2)

/-- The no-`c`-filter pair family is definitionally the earlier exact-fibre
pair family once fixed-`c` provenance is supplied. -/
theorem ActualRetainedFineFiberFixedCProvenance.fixedPairs_eq_exactPairs
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {keep : iota -> fineLabel -> Prop} {r : fineLabel} {commonC pairScale : Real}
    (P : ActualRetainedFineFiberFixedCProvenance D keep r commonC) :
    retainedY1FixedCSeparatedPairsAtFine D keep r pairScale =
      retainedY1ExactCSeparatedPairsAtFine D keep r commonC pairScale := by
  unfold retainedY1FixedCSeparatedPairsAtFine
  unfold retainedY1ExactCSeparatedPairsAtFine
  rw [P.exactFiber_eq_source]

/-- Direct lossless connector for a genuinely fixed retained fine fibre.
The earlier exact-fibre producer supplies both common `c` and coefficient
separation after the no-loss identification. -/
theorem ActualRetainedFineFiberFixedCProvenance.toSelection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {keep : iota -> fineLabel -> Prop} {r : fineLabel} {commonC pairScale : Real}
    (P : ActualRetainedFineFiberFixedCProvenance D keep r commonC) :
    ActualRetainedY1PairSelection D
      (retainedY1FixedCSeparatedPairsAtFine D keep r pairScale)
      Prod.fst Prod.snd (fun _ : iota × iota => r) keep pairScale := by
  rw [P.fixedPairs_eq_exactPairs]
  exact retainedY1ExactCSeparatedPairsAtFine_selection
    D keep r commonC pairScale

/-! ## Actual shared-global sampling survivors -/

/-- Short name for the literal actual shared-global survivor item type. -/
abbrev ActualSharedGlobalSurvivorItem
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
          Fin nu)) :=
  TwoSidedZeroColorSurvivor mu nu
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left)
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right) omega

/-- The actual index underlying the selected left hit of a survivor. -/
noncomputable def actualSharedGlobalSurvivorLeftIndex
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
    ActualSharedGlobalSurvivorItem fine physical globalScale globalCenter D
      keep rectangles left right ballRadius mu nu omega -> iota :=
  fun S => (survivorLeftHitWitness mu nu
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left)
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right) omega S).1.1

/-- The actual index underlying the selected right hit of a survivor. -/
noncomputable def actualSharedGlobalSurvivorRightIndex
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
    ActualSharedGlobalSurvivorItem fine physical globalScale globalCenter D
      keep rectangles left right ballRadius mu nu omega -> iota :=
  fun S => (survivorRightHitWitness mu nu
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left)
    (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right) omega S).1.1

/-- Sampling automatically supplies one retained fine incidence on each side
over the survivor's coarse rectangle.  The two fine labels in this conclusion
are intentionally not asserted equal. -/
theorem actualSharedGlobalSurvivor_exists_retainedCoarseIncidences
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
    (S : ActualSharedGlobalSurvivorItem fine physical globalScale globalCenter
      D keep rectangles left right ballRadius mu nu omega) :
    (exists leftFine,
      (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega S,
        leftFine) ∈ D.retainedGoodPairs keep ∧
      D.coarseRectangleAt leftFine = S.1.1) ∧
    (exists rightFine,
      (actualSharedGlobalSurvivorRightIndex fine physical globalScale
          globalCenter D keep rectangles left right ballRadius mu nu omega S,
        rightFine) ∈ D.retainedGoodPairs keep ∧
      D.coarseRectangleAt rightFine = S.1.1) := by
  have hleftBall :=
    actualSharedGlobal_survivorLeftHit_mem_coarseCurveMetricBall
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega S
  have hrightBall :=
    actualSharedGlobal_survivorRightHit_mem_coarseCurveMetricBall
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega S
  have hleftFiber := ((D.mem_coarseCurveMetricBall_iff keep).mp hleftBall).1
  have hrightFiber := ((D.mem_coarseCurveMetricBall_iff keep).mp hrightBall).1
  obtain ⟨leftFine, hleftGood, hleftKeep, hleftCoarse⟩ :=
    (D.mem_coarseCurveIndexFiber_iff keep).mp hleftFiber
  obtain ⟨rightFine, hrightGood, hrightKeep, hrightCoarse⟩ :=
    (D.mem_coarseCurveIndexFiber_iff keep).mp hrightFiber
  constructor
  · refine ⟨leftFine, ?_, hleftCoarse⟩
    simpa only [actualSharedGlobalSurvivorLeftIndex] using
      (D.mem_retainedGoodPairs_iff keep).mpr ⟨hleftGood, hleftKeep⟩
  · refine ⟨rightFine, ?_, hrightCoarse⟩
    simpa only [actualSharedGlobalSurvivorRightIndex] using
      (D.mem_retainedGoodPairs_iff keep).mpr ⟨hrightGood, hrightKeep⟩

/-- The genuinely additional refinement required to identify one common
fine rectangle for both survivor endpoints. -/
structure ActualSharedGlobalSurvivorCommonFineRefinement
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
          Fin nu)) where
  labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega ->
      fineLabel
  left_retained : forall S,
    (actualSharedGlobalSurvivorLeftIndex fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega S, labelAt S) ∈
      D.retainedGoodPairs keep
  right_retained : forall S,
    (actualSharedGlobalSurvivorRightIndex fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega S, labelAt S) ∈
      D.retainedGoodPairs keep
  coarse_at : forall S, D.coarseRectangleAt (labelAt S) = S.1.1

/-- A pointwise common-fine-label witness builds the refinement data. -/
theorem exists_actualSharedGlobalSurvivorCommonFineRefinement
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
    (hcommonFine : forall S : ActualSharedGlobalSurvivorItem fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega,
      exists r,
        (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
            globalCenter D keep rectangles left right ballRadius mu nu omega S,
          r) ∈ D.retainedGoodPairs keep ∧
        (actualSharedGlobalSurvivorRightIndex fine physical globalScale
            globalCenter D keep rectangles left right ballRadius mu nu omega S,
          r) ∈ D.retainedGoodPairs keep ∧
        D.coarseRectangleAt r = S.1.1) :
    Nonempty (ActualSharedGlobalSurvivorCommonFineRefinement fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega) := by
  classical
  let labelAt := fun S : ActualSharedGlobalSurvivorItem fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega => Classical.choose (hcommonFine S)
  refine ⟨{
    labelAt := labelAt
    left_retained := ?_
    right_retained := ?_
    coarse_at := ?_ }⟩
  · intro S
    exact (Classical.choose_spec (hcommonFine S)).1
  · intro S
    exact (Classical.choose_spec (hcommonFine S)).2.1
  · intro S
    exact (Classical.choose_spec (hcommonFine S)).2.2

/-- Exact fixed-`c` provenance for the whole actual shared-global index
family.  This is stronger than membership in any positive-width `c` bucket. -/
structure ActualGlobalNormIndexFamilyFixedCProvenance
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (commonC : Real) : Prop where
  fixed_c : forall i,
    i ∈ actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
      tubeGraphC (D.fine.tubes i) = commonC

/-- The common-fine refinement and exact global fixed-`c` provenance combine
to give generic fixed-common-`c` pair provenance on the entire literal
survivor fibre. -/
theorem actualSharedGlobalSurvivor_fixedCommonCProvenance
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
    (commonC : Real)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical globalScale
      globalCenter D commonC)
    (L : ActualSharedGlobalSurvivorCommonFineRefinement fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega) :
    ActualFixedCommonCRetainedPairProvenance D
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      L.labelAt keep commonC := by
  constructor
  · intro S _hS
    exact L.left_retained S
  · intro S _hS
    exact L.right_retained S
  · intro S _hS
    apply C.fixed_c
    exact (survivorLeftHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega S).1.2
  · intro S _hS
    apply C.fixed_c
    exact (survivorRightHitWitness mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega S).1.2

/-- Final lossless sampling connector.  It keeps every survivor item; the
only extra quantitative input is the pairwise coefficient lower bound. -/
theorem actualSharedGlobalSurvivor_fixedCommonC_selection
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
    (commonC pairScale : Real)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical globalScale
      globalCenter D commonC)
    (L : ActualSharedGlobalSurvivorCommonFineRefinement fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega)
    (hseparated : forall S : ActualSharedGlobalSurvivorItem fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega,
      2 * pairScale <= tubePairCoefficientDistance
        (D.fine.tubes (actualSharedGlobalSurvivorLeftIndex fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega S))
        (D.fine.tubes (actualSharedGlobalSurvivorRightIndex fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega S))) :
    ActualRetainedY1PairSelection D
      (actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorLeftIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      (actualSharedGlobalSurvivorRightIndex fine physical globalScale
        globalCenter D keep rectangles left right ballRadius mu nu omega)
      L.labelAt keep pairScale := by
  apply (actualSharedGlobalSurvivor_fixedCommonCProvenance fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega commonC C L).toSelection
  intro S _hS
  exact hseparated S

#print axioms ActualFixedCommonCRetainedPairProvenance.toSelection
#print axioms ActualRetainedFineFiberFixedCProvenance.exactFiber_eq_source
#print axioms ActualRetainedFineFiberFixedCProvenance.toSelection
#print axioms actualSharedGlobalSurvivor_exists_retainedCoarseIncidences
#print axioms exists_actualSharedGlobalSurvivorCommonFineRefinement
#print axioms actualSharedGlobalSurvivor_fixedCommonCProvenance
#print axioms actualSharedGlobalSurvivor_fixedCommonC_selection

end

end FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
