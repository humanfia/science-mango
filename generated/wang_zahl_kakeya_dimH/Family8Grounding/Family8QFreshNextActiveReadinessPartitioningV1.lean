import Family8Grounding.Family8QFreshNextActiveReadinessFiberUniformV1
import Mathlib.Tactic

/-!
# Doubled-parent and pairwise transports for q-fresh next-active readiness

This module deliberately imports the finite scale/fibre transport core instead
of unfolding the later geometry and coherent hierarchy.
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

#print axioms qFreshNextActive_mem_doubledFiber_iff
#print axioms qFreshNextActive_isDoubledParentPartitioning
#print axioms qFreshNextActive_pairwise_paperEssentiallyDistinct

end
end Family8QFreshNextActiveReadinessProducerV1
