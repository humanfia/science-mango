import Family8Grounding.Family8QFreshNextActiveFinePaperStateTransportV1
import Mathlib.Tactic

/-!
# Core finite reindexing for q-fresh next-active readiness

This file contains only the finite-index and per-scale transports.  The
coherent hierarchy and final `PaperFactorAtomReadiness` are assembled in the
downstream producer module.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8QFreshNextActiveReadinessProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoublyBufferedDef212GroundedOneStepRunV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8QFreshNextActiveFinePaperStateTransportV1
open Family8SelectedFiberDoublyBufferedPaperFactorConnectorV1
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
open Family8SourceDef212BoundCrossingTransitionV2
open Family8SourceDef212BoundCrossingTransitionV2.SourceDef212CrossingIntegratedSuccessor
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}
  {depth : Nat}
  {Csource : CoherentStickyMultiscaleCover source}
  {hdeltaTau : delta ≤ tau} {hTauOne : tau ≤ 1}
  {Ysource : Shading
    (Csource.base.cover tau hdeltaTau hTauOne).coarse.bodyFamily}
  {hDtau : (rerootedPaperSourceDatum Csource tau hdeltaTau
    hTauOne Ysource).IsAdmissible}
  {S : FiniteScaleSequence tau depth}
  {epsilon : Real} {hepsilon : 0 ≤ epsilon}
  {eta : Nat → Real} {N : Nat}
  {W : FirstParentwiseNormalizedCrossingWitness
    (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
    hDtau (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
    S epsilon hepsilon eta N}
  {R : SourceDef212CrossingSuccessorReadiness W}
  {X : SourceDef212CrossingIntegratedSuccessor W R}

/-
/-- Canonical active-subtype equivalence in the exact index type owned by
the genuine q-fresh hierarchy. -/
noncomputable def qFreshNextActiveHierarchyIndexEquiv
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    {i // i ∈ (crossingBaseCover Y.destination).activeFine} ≃
      {i // i ∈
        X.toParentwiseCrossingIntegratedSuccessor.dualChild.qFibreSelected} where
  toFun i := i.1
  invFun i := ⟨i, by
    rw [nextCrossingBaseCover_activeFine_eq_univ H Y]
    exact Finset.mem_univ _⟩
  left_inv i := by
    apply Subtype.ext
    rfl
  right_inv i := rfl

@[simp] theorem qFreshNextActiveHierarchyIndexEquiv_tube
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (i : {i // i ∈ (crossingBaseCover Y.destination).activeFine}) :
    (qFreshNextActiveSourceDatum Y).family.tubes i =
      X.toParentwiseCrossingIntegratedSuccessor.dualChild.qFibreChildDatum.family.tubes
        (qFreshNextActiveHierarchyIndexEquiv H Y i) :=
  rfl

-/

abbrev qFreshFullScaleCover
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :=
  H.readiness.qFreshCover.base.cover rho hChildRho hRhoOne

theorem qFreshFullScaleCover_activeFine_eq_univ
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    (qFreshFullScaleCover H rho hChildRho hRhoOne).activeFine =
      Finset.univ := by
  rw [(qFreshFullScaleCover H rho hChildRho hRhoOne).activeFine_eq_refined,
    H.readiness.qFreshExact.fine_refined_eq_univ]

/-
/-- Reindex only the fine side of one genuine q-fresh scale cover. -/
noncomputable def qFreshNextActiveScaleCover
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    StickyScaleCover (qFreshNextActiveSourceDatum Y).family rho :=
  Family8StickyScaleCoverFineEquivReindexV1.StickyScaleCover.reindexFineOfActiveUniv
      (qFreshFullScaleCover H rho hChildRho hRhoOne)
      (qFreshNextActiveSourceDatum Y).family
      (qFreshNextActiveHierarchyIndexEquiv H Y)
      (qFreshNextActiveHierarchyIndexEquiv_tube H Y)
      (qFreshFullScaleCover_activeFine_eq_univ H rho hChildRho hRhoOne)
      (by rfl)

@[simp] theorem qFreshNextActiveScaleCover_coarse
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).coarse =
      (qFreshFullScaleCover H rho hChildRho hRhoOne).coarse :=
  rfl

@[simp] theorem qFreshNextActiveScaleCover_activeCoarse
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).activeCoarse =
      (qFreshFullScaleCover H rho hChildRho hRhoOne).activeCoarse :=
  rfl

 -/
/-
noncomputable def qFreshNextActiveFiberEquiv
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : Fin (qFreshFullScaleCover H rho hChildRho hRhoOne).coarseCard) :
    {i // i ∈ (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiber k} ≃
      {j // j ∈ (qFreshFullScaleCover H rho hChildRho hRhoOne).fiber k} := by
  classical
  let T := qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne
  let A := qFreshFullScaleCover H rho hChildRho hRhoOne
  let e := qFreshNextActiveHierarchyIndexEquiv H Y
  have hAactive : A.activeFine = Finset.univ := by
    rw [A.activeFine_eq_refined,
      H.readiness.qFreshExact.fine_refined_eq_univ]
  refine
    { toFun := fun i => ⟨e i.1, ?_⟩
      invFun := fun j => ⟨e.symm j.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hi := (T.mem_fiber i.1 k).mp i.2
    apply (A.mem_fiber (e i.1) k).mpr
    refine ⟨?_, hi.2⟩
    rw [hAactive]
    exact Finset.mem_univ _
  · have hj := (A.mem_fiber j.1 k).mp j.2
    apply (T.mem_fiber (e.symm j.1) k).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change A.parent (e (e.symm j.1)) = k
    rw [e.apply_symm_apply]
    exact hj.2
  · intro i
    apply Subtype.ext
    exact e.symm_apply_apply i.1
  · intro j
    apply Subtype.ext
    exact e.apply_symm_apply j.1

@[simp] theorem qFreshNextActiveFiberEquiv_body
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : Fin (qFreshFullScaleCover H rho hChildRho hRhoOne).coarseCard)
    (i : {i // i ∈
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiber k}) :
    (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiberFamily k i =
      (qFreshFullScaleCover H rho hChildRho hRhoOne).fiberFamily k
        (qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k i) :=
  rfl

theorem qFreshNextActive_fiber_card_eq
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : Fin (qFreshFullScaleCover H rho hChildRho hRhoOne).coarseCard) :
    ((qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).fiber k).card =
      ((qFreshFullScaleCover H rho hChildRho hRhoOne).fiber k).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k)

theorem qFreshNextActive_isCUniform
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    IsCUniform (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne)
      (H.readiness.qFreshK : ENNReal) := by
  intro k hk l hl
  rw [qFreshNextActive_fiber_card_eq H Y rho hChildRho hRhoOne k,
    qFreshNextActive_fiber_card_eq H Y rho hChildRho hRhoOne l]
  exact H.readiness.qFreshExact.c_uniform rho hChildRho hRhoOne
    k hk l hl

/-
theorem qFreshNextActive_mem_doubledFiber_iff
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (i : {i // i ∈ (crossingBaseCover Y.destination).activeFine})
    (k : Fin (qFreshFullScaleCover H rho hChildRho hRhoOne).coarseCard) :
    i ∈ doubledFiber
        (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne) k ↔
      qFreshNextActiveHierarchyIndexEquiv H Y i ∈
        doubledFiber (qFreshFullScaleCover H rho hChildRho hRhoOne) k := by
  let T := qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne
  let A := qFreshFullScaleCover H rho hChildRho hRhoOne
  have hparentCarrier :
      twoFoldTubeCarrier (T.coarse.tubes k) =
        twoFoldTubeCarrier (A.coarse.tubes k) := rfl
  have hAactive : A.activeFine = Finset.univ := by
    rw [A.activeFine_eq_refined,
      H.readiness.qFreshExact.fine_refined_eq_univ]
  constructor
  · intro hi
    have hiT := (mem_doubledFiber T i k).mp hi
    apply (mem_doubledFiber A
      (qFreshNextActiveHierarchyIndexEquiv H Y i) k).mpr
    refine ⟨?_, ?_⟩
    · rw [hAactive]
      exact Finset.mem_univ _
    · rw [← hparentCarrier]
      simpa only [qFreshNextActiveHierarchyIndexEquiv_tube] using hiT.2
  · intro hi
    have hiA := (mem_doubledFiber A
      (qFreshNextActiveHierarchyIndexEquiv H Y i) k).mp hi
    apply (mem_doubledFiber T i k).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hparentCarrier]
    simpa only [qFreshNextActiveHierarchyIndexEquiv_tube] using hiA.2

theorem qFreshNextActive_isDoubledParentPartitioning
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    IsDoubledParentPartitioning
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne) := by
  intro k hk l hl hkl
  rw [Finset.disjoint_left]
  intro i hik hil
  have hik' :=
    (qFreshNextActive_mem_doubledFiber_iff
      H Y rho hChildRho hRhoOne i k).mp hik
  have hil' :=
    (qFreshNextActive_mem_doubledFiber_iff
      H Y rho hChildRho hRhoOne i l).mp hil
  exact (Finset.disjoint_left.mp
    (H.readiness.qFreshExact.doubled_parent_partitioning
      rho hChildRho hRhoOne k hk l hl hkl)) hik' hil'

/-
/-- Convert an occupied target parent to the identical occupied source
parent without identifying fine index types. -/
def qFreshNextActiveOldParent
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : {k // k ∈
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).activeCoarse}) :
    {k // k ∈
      (qFreshFullScaleCover H rho hChildRho hRhoOne).activeCoarse} :=
  ⟨k.1, k.2⟩

noncomputable def qFreshNextActiveUnitRescalingGeometry
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    UnitRescalingGeometry
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne) := by
  let Old := H.readiness.qFreshExact.unitRescalingGeometry
    rho hChildRho hRhoOne
  exact
    { johnWitness := fun k =>
        Old.johnWitness
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)
      unitRescaling := fun k =>
        Old.unitRescaling
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)
      johnOuter_image_eq_unitBall := fun k =>
        Old.johnOuter_image_eq_unitBall
          (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k) }

/-- The new normalized fibre is exactly the old normalized fibre reindexed
by the explicit finite equivalence. -/
theorem qFreshNextActive_rescaledFiberFamily_eq_reindex
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1)
    (k : {k // k ∈
      (qFreshNextActiveScaleCover H Y rho hChildRho hRhoOne).activeCoarse}) :
    (qFreshNextActiveUnitRescalingGeometry H Y rho hChildRho hRhoOne).
        rescaledFiberFamily k =
      reindexConvexFamily
        (qFreshNextActiveFiberEquiv H Y rho hChildRho hRhoOne k.1)
        ((H.readiness.qFreshExact.unitRescalingGeometry
          rho hChildRho hRhoOne).rescaledFiberFamily
            (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)) := by
  funext i
  rfl

theorem qFreshNextActive_rescaledFibres_cwa
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (rho : NNReal)
    (hChildRho : badParentFreshChildRadius tau W.rho ≤ rho)
    (hRhoOne : rho ≤ 1) :
    (qFreshNextActiveUnitRescalingGeometry
      H Y rho hChildRho hRhoOne).FibresSatisfyCWA
        (H.readiness.qFreshK : ENNReal) := by
  intro k
  rw [qFreshNextActive_rescaledFiberFamily_eq_reindex]
  apply satisfiesConvexWolffAxioms_reindex
  exact H.readiness.qFreshExact.rescaled_fibres_cwa
    rho hChildRho hRhoOne
      (qFreshNextActiveOldParent H Y rho hChildRho hRhoOne k)

-/
theorem qFreshNextActive_pairwise_paperEssentiallyDistinct
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (Y : DoublyBufferedQFreshCrossingDestination H) :
    Set.Pairwise
      (Set.univ : Set {i // i ∈
        (crossingBaseCover Y.destination).activeFine})
      fun i j => PaperEssentiallyDistinct
        ((qFreshNextActiveSourceDatum Y).family.tubes i)
        ((qFreshNextActiveSourceDatum Y).family.tubes j) := by
  intro i _hi j _hj hij
  rw [qFreshNextActiveHierarchyIndexEquiv_tube H Y,
    qFreshNextActiveHierarchyIndexEquiv_tube H Y]
  apply H.readiness.qFreshExact.fine_pairwise_paperEssentiallyDistinct
    (Set.mem_univ _) (Set.mem_univ _)
  intro hval
  exact hij ((qFreshNextActiveHierarchyIndexEquiv H Y).injective hval)

-/
#print axioms qFreshNextActiveScaleCover
-/
#print axioms qFreshFullScaleCover_activeFine_eq_univ

end
end Family8QFreshNextActiveReadinessProducerV1
