import Family8Grounding.Family8SelectedFiberFaithfulCoherentSuccessorV1
import Family8Grounding.Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
import Mathlib.Tactic

/-!
# Buffered faithful coherent successors

The selected-ancestor axis-gap theorem removes the normalized-axis inclusion
from the q-fresh readiness.  At a source scale `tau`, the actual coherent
parent is required to be the genuine contracted-John/eighth ancestor proxy
with an explicit buffer.  Source carrier nesting and the scalar comparison
`axisGap tau rho <= buffer tau` then prove the whole fine-to-parent carrier
inclusion automatically.

The active-parent route is geometrically different and retains its earliest
honest normalized-axis input.  Both covers remain externally supplied real
coherent covers of the literal child families; this module neither constructs
an identity cover nor selects a new parent `q`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedFiberFaithfulBufferedCoherentSuccessorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyCarrierMonoV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8ExactDef212CompositionalParentsV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SelectedFiberFaithfulCoherentSuccessorV1
open Family8SelectedFiberJohnCanonicalCoherentFactorV1
open Family8StickyActiveCoarseAdmissibleChildV1
open Family8TubeJohnUnitRescalingGeometryLeOneV7
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

/-- The actual scale of a buffered q-fresh ancestor. -/
def qFreshBufferedProxyScale
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (tau buffer : NNReal) : NNReal :=
  qFreshProxyScale W tau + buffer

theorem qFreshChildRadius_le_bufferedProxyScale
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    {tau : NNReal} (hdeltaTau : delta <= tau) (buffer : NNReal) :
    badParentFreshChildRadius delta W.rho <=
      qFreshBufferedProxyScale W tau buffer := by
  calc
    badParentFreshChildRadius delta W.rho <= qFreshProxyScale W tau :=
      qFreshChildRadius_le_proxyScale W hdeltaTau
    _ <= qFreshProxyScale W tau + buffer := le_add_right (le_refl _)

/-- Exact source hierarchy data plus the scalar buffer comparison produces
the complete actual buffered q-fresh step.  No axis inclusion is an input. -/
theorem qFresh_selectedAncestorBufferedStep_of_source
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    {sourceK : NNReal} (H : ExactScaleDef212Inputs C.base sourceK)
    (tau : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= W.rho)
    (i : {j // j ∈ X.dualChild.qFibreSelected})
    (buffer : NNReal)
    (haxisGapBuffer :
      contractedJohnEighthSelectedAncestorAxisGap tau W.rho <= buffer) :
    ContractedJohnEighthSelectedAncestorBufferedStep
      (crossingRootTube W) (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingRootJohnWitness W) (D.family.tubes i.1.1)
      (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i) buffer := by
  let T := C.base.cover tau hdeltaTau
    (hTauRho.trans (crossingRhoLeOne W))
  let R := crossingBaseCover W
  have hfiber : i.1.1 ∈ R.fiber (crossingBaseQ W).1 := i.1.2
  have hiData := (R.mem_fiber i.1.1 (crossingBaseQ W).1).1 hfiber
  have hiT : i.1.1 ∈ T.activeFine := by
    rw [T.activeFine_eq_refined, ← R.activeFine_eq_refined]
    exact hiData.1
  have hTU :
      (D.family.tubes i.1.1).carrier ⊆
        (T.coarse.tubes (T.parent i.1.1)).carrier :=
    T.carrier_subset i.1.1 hiT
  have hparentMem : T.parent i.1.1 ∈ T.activeCoarse :=
    T.parent_mem i.1.1 hiT
  have hcompat :=
    fine_parent_compatible_of_doubledParentPartitioning
      C tau W.rho hdeltaTau hTauRho (crossingRhoLeOne W)
      (H.doubled_parent_partitioning W.rho
        (hdeltaTau.trans hTauRho) (crossingRhoLeOne W))
      i.1.1 hiT
  have hparent :
      C.parent tau W.rho hdeltaTau hTauRho (crossingRhoLeOne W)
          (T.parent i.1.1) = (crossingBaseQ W).1 :=
    hcompat.symm.trans hiData.2
  have hUP := C.carrier_subset tau W.rho hdeltaTau hTauRho
    (crossingRhoLeOne W) (T.parent i.1.1) hparentMem
  change (T.coarse.tubes (T.parent i.1.1)).carrier ⊆
    (R.coarse.tubes
      (C.parent tau W.rho hdeltaTau hTauRho
        (crossingRhoLeOne W) (T.parent i.1.1))).carrier at hUP
  rw [hparent] at hUP
  exact contractedJohnEighthSelectedAncestorBufferedStep_of_source
    (crossingRootTube W) (crossingRhoPos W) (crossingRhoLeOne W)
    (crossingRootJohnWitness W) (D.family.tubes i.1.1)
    (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i) buffer
    hdeltaTau hTauRho hTU hUP haxisGapBuffer

/-- Readiness after eliminating the q-route axis inclusion.  The q buffer
comparison and upper-scale budget are scalar fields.  Parent realization is
at the buffered scale and names the genuine containing tube from AxisGapV1. -/
structure FaithfulBufferedCoherentSuccessorReadiness
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
  qBuffer : NNReal -> NNReal
  q_axisGap_le_buffer : forall (tau : NNReal)
      (_hTauRho : tau <= W.rho),
    contractedJohnEighthSelectedAncestorAxisGap tau W.rho <= qBuffer tau
  q_bufferedScale_le_one : forall (tau : NNReal)
      (_hTauRho : tau <= W.rho),
    qFreshBufferedProxyScale W tau (qBuffer tau) <= 1
  activeParent_axis_subset : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    (eighthNormalizedTube
      ((crossingBaseCover W).coarse.tubes i.1.1)).axis.carrier ⊆
    (eighthNormalizedTube
      (activeParentSourceAncestorTube W X sigma hRhoSigma
        hSigmaOne i)).axis.carrier
  qFresh_parent_realizes_buffered_source : forall (tau : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= W.rho)
      (i : {j // j ∈ X.dualChild.qFibreSelected}),
    let A := qFreshCover.base.cover
      (qFreshBufferedProxyScale W tau (qBuffer tau))
      (qFreshChildRadius_le_bufferedProxyScale W hdeltaTau (qBuffer tau))
      (q_bufferedScale_le_one tau hTauRho)
    A.coarse.tubes (A.parent i) =
      contractedJohnEighthProxyContainingTube (crossingRootTube W)
        (crossingRhoPos W) (crossingRootJohnWitness W)
        (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)
        (qBuffer tau)
  activeParent_parent_realizes_source : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    let A := activeParentCover.base.cover (activeParentProxyScale sigma)
      (activeParentChildRadius_le_proxyScale W hRhoSigma)
      (activeParentProxyScale_le_one hSigmaOne)
    A.coarse.tubes (A.parent i) =
      eighthNormalizedTube
        (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)

/-- The faithful connector with q-axis geometry discharged by AxisGapV1. -/
structure SelectedFiberFaithfulBufferedCoherentSuccessor
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W) where
  readiness : FaithfulBufferedCoherentSuccessorReadiness W X
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
      (readiness.qBuffer tau)
  activeParent_source_steps : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    EighthNormalizedActualHierarchyStep
      ((crossingBaseCover W).coarse.tubes i.1.1)
      (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)

/-- Assemble the new connector.  The q step consumes only source ExactDef212
and scalar buffer data; the active axis input remains explicit. -/
theorem exists_selectedFiberFaithfulBufferedCoherentSuccessor
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (R : FaithfulBufferedCoherentSuccessorReadiness W X) :
    Nonempty (SelectedFiberFaithfulBufferedCoherentSuccessor W X) := by
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
          tau hdeltaTau hTauRho i (R.qBuffer tau)
          (R.q_axisGap_le_buffer tau hTauRho)
      activeParent_source_steps := fun sigma hRhoSigma hSigmaOne i =>
        activeParent_sourceHierarchyStep_of_axis_subset W X
          sigma hRhoSigma hSigmaOne i
          (R.activeParent_axis_subset sigma hRhoSigma hSigmaOne i) }⟩

namespace SelectedFiberFaithfulBufferedCoherentSuccessor

variable {W : FirstParentwiseNormalizedCrossingWitness
  D hD C S epsilon hepsilon eta N}
  {X : ParentwiseCrossingIntegratedSuccessor W}

/-- The literal q-fresh fine tube is contained in the actual coherent
parent realized by the selected ancestor and its scalar buffer. -/
theorem qFresh_fine_subset_realized_buffered_parent
    (Y : SelectedFiberFaithfulBufferedCoherentSuccessor W X)
    (tau : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= W.rho)
    (i : {j // j ∈ X.dualChild.qFibreSelected}) :
    let A := Y.readiness.qFreshCover.base.cover
      (qFreshBufferedProxyScale W tau (Y.readiness.qBuffer tau))
      (qFreshChildRadius_le_bufferedProxyScale W hdeltaTau
        (Y.readiness.qBuffer tau))
      (Y.readiness.q_bufferedScale_le_one tau hTauRho)
    (X.dualChild.qFibreChildDatum.family.tubes i).carrier ⊆
      (A.coarse.tubes (A.parent i)).carrier := by
  dsimp only
  rw [qFibreChildDatum_family_tubes]
  rw [Y.readiness.qFresh_parent_realizes_buffered_source
    tau hdeltaTau hTauRho i]
  exact (Y.qFresh_buffered_steps tau hdeltaTau hTauRho i).actual_proxy_subset_buffered_parent

/-- Literal all-scale nesting in the supplied real q-fresh cover. -/
theorem qFresh_cover_carrier_subset
    (Y : SelectedFiberFaithfulBufferedCoherentSuccessor W X)
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

/-- Literal all-scale nesting in the supplied real active-parent cover. -/
theorem activeParent_cover_carrier_subset
    (Y : SelectedFiberFaithfulBufferedCoherentSuccessor W X)
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

end SelectedFiberFaithfulBufferedCoherentSuccessor

#print axioms qFreshBufferedProxyScale
#print axioms qFreshChildRadius_le_bufferedProxyScale
#print axioms qFresh_selectedAncestorBufferedStep_of_source
#print axioms FaithfulBufferedCoherentSuccessorReadiness
#print axioms SelectedFiberFaithfulBufferedCoherentSuccessor
#print axioms exists_selectedFiberFaithfulBufferedCoherentSuccessor
#print axioms SelectedFiberFaithfulBufferedCoherentSuccessor.qFresh_fine_subset_realized_buffered_parent
#print axioms SelectedFiberFaithfulBufferedCoherentSuccessor.qFresh_cover_carrier_subset
#print axioms SelectedFiberFaithfulBufferedCoherentSuccessor.activeParent_cover_carrier_subset

end
end Family8SelectedFiberFaithfulBufferedCoherentSuccessorV1
