import Family8Grounding.Family8QFreshNextActiveReadinessTransportCoreV1
import Mathlib.Tactic

/-!
# Exact H-owned active-subtype equivalence for the q-fresh hierarchy
-/

set_option autoImplicit false
set_option warningAsError true

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

/-- Canonical active-subtype equivalence stated in the exact index type
owned by `H`, avoiding any semireducible projection bridge. -/
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

#print axioms qFreshNextActiveHierarchyIndexEquiv
#print axioms qFreshNextActiveHierarchyIndexEquiv_tube

end
end Family8QFreshNextActiveReadinessProducerV1
