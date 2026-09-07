import Family8Grounding.Family8SelectedFiberFaithfulBufferedCoherentSuccessorV1
import Family8Grounding.Family8SelectedFiberFaithfulActiveBufferedAxisGapV1
import Family8Grounding.Family8ContractedJohnEighthProxyAxisGapBufferPowerV1
import Mathlib.Tactic

/-!
# Doubly buffered faithful coherent successors

Both recursive children now use source-derived axis-gap estimates and genuine
buffered ancestor tubes.  The q-fresh route consumes the contracted-John gap;
the active-parent route consumes the literal eighth-normalized gap.  Thus the
readiness below has no axis-inclusion callback.  Its geometric seams are only
scalar buffer comparisons, scale-at-most-one budgets, and positive mapped
parent realizations in two externally supplied real coherent covers.

All parents and selected indices are inherited from the same crossing
successor.  No identity cover and no parent reselection is performed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnEighthProxyCarrierMonoV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8ContractedJohnEighthProxyAxisGapBufferPowerV1
open Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EighthNormalizedSelectedAncestorAxisGapV1
open Family8ExactDef212CompositionalParentsV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV1
open Family8SelectedFiberFaithfulCoherentSuccessorV1
open Family8SelectedFiberFaithfulActiveBufferedAxisGapV1
open Family8SelectedFiberJohnCanonicalCoherentFactorV1
open Family8StickyActiveCoarseAdmissibleChildV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}


/-- Final readiness for both faithful child hierarchies.  There is no
q-route or active-route normalized-axis field. -/
structure FaithfulDoublyBufferedCoherentSuccessorReadiness
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W) where
  sourceK : NNReal
  sourceExact : ExactScaleDef212Inputs C.base sourceK
  qFreshCover :
    CoherentStickyMultiscaleCover X.dualChild.qFibreChildDatum.family
  qFreshK : NNReal
  qFreshExact : ExactScaleDef212Inputs qFreshCover.base qFreshK
  activeParentCover :
    CoherentStickyMultiscaleCover X.dualChild.activeParentChildDatum.family
  activeParentK : NNReal
  activeParentExact :
    ExactScaleDef212Inputs activeParentCover.base activeParentK
  q_epsilon_pos : 0 < epsilon
  q_ratio_power : forall (tau : NNReal)
      (_hdeltaTau : delta <= tau) (_hTauRho : tau <= W.rho),
    tau / W.rho <= delta ^ (epsilon ^ 2)
  q_small_delta : delta <=
    contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon
  q_bufferedScale_le_one : forall (tau : NNReal)
      (_hTauRho : tau <= W.rho),
    qFreshBufferedProxyScale W tau
      contractedJohnEighthSelectedAncestorOneEighthBuffer <= 1
  activeBuffer : NNReal -> NNReal
  active_axisGap_le_buffer : forall (sigma : NNReal)
      (_hRhoSigma : W.rho <= sigma) (_hSigmaOne : sigma <= 1),
    eighthNormalizedSelectedAncestorAxisGap sigma <= activeBuffer sigma
  active_bufferedScale_le_one : forall (sigma : NNReal)
      (_hRhoSigma : W.rho <= sigma) (_hSigmaOne : sigma <= 1),
    activeParentBufferedProxyScale sigma (activeBuffer sigma) <= 1
  qFresh_parent_realizes_buffered_source : forall (tau : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= W.rho)
      (i : {j // j ∈ X.dualChild.qFibreSelected}),
    let A := qFreshCover.base.cover
      (qFreshBufferedProxyScale W tau
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (qFreshChildRadius_le_bufferedProxyScale W hdeltaTau
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (q_bufferedScale_le_one tau hTauRho)
    A.coarse.tubes (A.parent i) =
      contractedJohnEighthProxyContainingTube (crossingRootTube W)
        (crossingRhoPos W) (crossingRootJohnWitness W)
        (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)
        contractedJohnEighthSelectedAncestorOneEighthBuffer
  activeParent_parent_realizes_buffered_source : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    let A := activeParentCover.base.cover
      (activeParentBufferedProxyScale sigma (activeBuffer sigma))
      (activeParentChildRadius_le_bufferedProxyScale W hRhoSigma
        (activeBuffer sigma))
      (active_bufferedScale_le_one sigma hRhoSigma hSigmaOne)
    A.coarse.tubes (A.parent i) =
      eighthNormalizedContainingTube
        (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)
        (activeBuffer sigma)

/-- Both actual child covers, their exact parent composition, and their
source-derived buffered carrier ledgers. -/
structure SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W) where
  readiness : FaithfulDoublyBufferedCoherentSuccessorReadiness W X
  source_compositional : HasCompositionalParents C
  qFresh_compositional : HasCompositionalParents readiness.qFreshCover
  activeParent_compositional :
    HasCompositionalParents readiness.activeParentCover
  qFresh_buffered_steps : forall (tau : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= W.rho)
      (i : {j // j ∈ X.dualChild.qFibreSelected}),
    ContractedJohnEighthSelectedAncestorBufferedStep
      (crossingRootTube W) (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingRootJohnWitness W) (D.family.tubes i.1.1)
      (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)
      contractedJohnEighthSelectedAncestorOneEighthBuffer
  activeParent_buffered_steps : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    EighthNormalizedSelectedAncestorBufferedStep
      ((crossingBaseCover W).coarse.tubes i.1.1)
      (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)
      (readiness.activeBuffer sigma)

/-- Assemble the double-buffer connector exclusively from scalar and actual
mapped-parent readiness. -/
theorem exists_selectedFiberFaithfulDoublyBufferedCoherentSuccessor
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (R : FaithfulDoublyBufferedCoherentSuccessorReadiness W X) :
    Nonempty
      (SelectedFiberFaithfulDoublyBufferedCoherentSuccessor W X) := by
  exact ⟨
    { readiness := R
      source_compositional :=
        hasCompositionalParents_of_exactScaleDef212Inputs C R.sourceExact
      qFresh_compositional :=
        hasCompositionalParents_of_exactScaleDef212Inputs
          R.qFreshCover R.qFreshExact
      activeParent_compositional :=
        hasCompositionalParents_of_exactScaleDef212Inputs
          R.activeParentCover R.activeParentExact
      qFresh_buffered_steps := fun tau hdeltaTau hTauRho i =>
        qFresh_selectedAncestorBufferedStep_of_source W X R.sourceExact
          tau hdeltaTau hTauRho i
          contractedJohnEighthSelectedAncestorOneEighthBuffer
          (contractedJohnEighthSelectedAncestorAxisGap_le_oneEighthBuffer
            hD.delta_pos (crossingRhoPos W) R.q_epsilon_pos
            (R.q_ratio_power tau hdeltaTau hTauRho) R.q_small_delta)
      activeParent_buffered_steps := fun sigma hRhoSigma hSigmaOne i =>
        activeParent_selectedAncestorBufferedStep_of_source W X
          sigma hRhoSigma hSigmaOne i (R.activeBuffer sigma)
          (R.active_axisGap_le_buffer sigma hRhoSigma hSigmaOne) }⟩

namespace SelectedFiberFaithfulDoublyBufferedCoherentSuccessor

variable {W : FirstParentwiseNormalizedCrossingWitness
  D hD C S epsilon hepsilon eta N}
  {X : ParentwiseCrossingIntegratedSuccessor W}

/-- Automatic q-fresh fine-to-realized-parent carrier nesting. -/
theorem qFresh_fine_subset_realized_buffered_parent
    (Y : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor W X)
    (tau : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= W.rho)
    (i : {j // j ∈ X.dualChild.qFibreSelected}) :
    let A := Y.readiness.qFreshCover.base.cover
      (qFreshBufferedProxyScale W tau
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (qFreshChildRadius_le_bufferedProxyScale W hdeltaTau
        contractedJohnEighthSelectedAncestorOneEighthBuffer)
      (Y.readiness.q_bufferedScale_le_one tau hTauRho)
    (X.dualChild.qFibreChildDatum.family.tubes i).carrier ⊆
      (A.coarse.tubes (A.parent i)).carrier := by
  dsimp only
  rw [qFibreChildDatum_family_tubes]
  rw [Y.readiness.qFresh_parent_realizes_buffered_source
    tau hdeltaTau hTauRho i]
  exact (Y.qFresh_buffered_steps tau hdeltaTau hTauRho i).actual_proxy_subset_buffered_parent

/-- Automatic active-parent fine-to-realized-parent carrier nesting. -/
theorem activeParent_fine_subset_realized_buffered_parent
    (Y : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor W X)
    (sigma : NNReal) (hRhoSigma : W.rho <= sigma)
    (hSigmaOne : sigma <= 1)
    (i : {k // k ∈ X.dualChild.activeParentSelected}) :
    let A := Y.readiness.activeParentCover.base.cover
      (activeParentBufferedProxyScale sigma (Y.readiness.activeBuffer sigma))
      (activeParentChildRadius_le_bufferedProxyScale W hRhoSigma
        (Y.readiness.activeBuffer sigma))
      (Y.readiness.active_bufferedScale_le_one
        sigma hRhoSigma hSigmaOne)
    (X.dualChild.activeParentChildDatum.family.tubes i).carrier ⊆
      (A.coarse.tubes (A.parent i)).carrier := by
  dsimp only
  rw [activeParentChildDatum_family_tubes]
  rw [Y.readiness.activeParent_parent_realizes_buffered_source
    sigma hRhoSigma hSigmaOne i]
  exact (Y.activeParent_buffered_steps sigma hRhoSigma hSigmaOne i).actual_normalized_subset_buffered_parent

/-- Literal all-scale carrier nesting in the real q-fresh cover. -/
theorem qFresh_cover_carrier_subset
    (Y : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor W X)
    (r s : NNReal)
    (hchildR : badParentFreshChildRadius delta W.rho <= r)
    (hRS : r <= s) (hSOne : s <= 1)
    (i : Fin ((Y.readiness.qFreshCover.base.cover r hchildR
      (hRS.trans hSOne)).coarseCard))
    (hi : i ∈ (Y.readiness.qFreshCover.base.cover r hchildR
      (hRS.trans hSOne)).activeCoarse) :
    ((Y.readiness.qFreshCover.base.cover r hchildR
      (hRS.trans hSOne)).coarse.tubes i).carrier ⊆
    ((Y.readiness.qFreshCover.base.cover s (hchildR.trans hRS)
      hSOne).coarse.tubes
        (Y.readiness.qFreshCover.parent r s hchildR hRS hSOne i)).carrier :=
  Y.readiness.qFreshCover.carrier_subset r s hchildR hRS hSOne i hi

/-- Literal all-scale carrier nesting in the real active-parent cover. -/
theorem activeParent_cover_carrier_subset
    (Y : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor W X)
    (r s : NNReal) (hchildR : W.rho / 8 <= r)
    (hRS : r <= s) (hSOne : s <= 1)
    (i : Fin ((Y.readiness.activeParentCover.base.cover r hchildR
      (hRS.trans hSOne)).coarseCard))
    (hi : i ∈ (Y.readiness.activeParentCover.base.cover r hchildR
      (hRS.trans hSOne)).activeCoarse) :
    ((Y.readiness.activeParentCover.base.cover r hchildR
      (hRS.trans hSOne)).coarse.tubes i).carrier ⊆
    ((Y.readiness.activeParentCover.base.cover s
      (hchildR.trans hRS) hSOne).coarse.tubes
        (Y.readiness.activeParentCover.parent r s hchildR
          hRS hSOne i)).carrier :=
  Y.readiness.activeParentCover.carrier_subset
    r s hchildR hRS hSOne i hi

end SelectedFiberFaithfulDoublyBufferedCoherentSuccessor

#print axioms activeParentBufferedProxyScale
#print axioms activeParentChildRadius_le_bufferedProxyScale
#print axioms activeParent_selectedAncestorBufferedStep_of_source
#print axioms FaithfulDoublyBufferedCoherentSuccessorReadiness
#print axioms SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
#print axioms exists_selectedFiberFaithfulDoublyBufferedCoherentSuccessor
#print axioms SelectedFiberFaithfulDoublyBufferedCoherentSuccessor.qFresh_fine_subset_realized_buffered_parent
#print axioms SelectedFiberFaithfulDoublyBufferedCoherentSuccessor.activeParent_fine_subset_realized_buffered_parent
#print axioms SelectedFiberFaithfulDoublyBufferedCoherentSuccessor.qFresh_cover_carrier_subset
#print axioms SelectedFiberFaithfulDoublyBufferedCoherentSuccessor.activeParent_cover_carrier_subset

end
end Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
