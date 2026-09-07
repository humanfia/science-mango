import Family8Grounding.Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
import Family8Grounding.Family8BadParentFreshBufferedActualHierarchyReadinessV1
import Family8Grounding.Family8ParentwiseBadParentBufferedFreshReadyPaperFactorConnectorV1
import Family8Grounding.Family8NormalizedFrostmanRerootedCoherentCoverV1
import Mathlib.Tactic

/-!
# Same-selected doubly buffered paper-factor connector

A source coherent cover is first genuinely rerooted at one literal lower
endpoint.  On that rerooted object, the crossing successor and the generic
bad-parent interval construction are definitionally the same cover, parent,
`q`, selected subtype, shading, and fresh datum.

The connector consumes the doubly buffered faithful hierarchy.  Its
ratio-power and small-scale fields derive the q-route axis buffer, while the
active route remains retained in the same hierarchy certificate.  The q
fields are then packaged as `BadParentFreshBufferedActualHierarchyReadiness`
and fed directly to the same-selected paper-factor transition.  There is no
identity cover, index reselection, or bare carrier-inclusion callback.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedFiberDoublyBufferedPaperFactorConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BadParentFreshReadinessV1
open Family8BadParentFreshBufferedActualHierarchyReadinessV1
open Family8ContractedJohnEighthProxyAxisGapBufferPowerV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFrostmanRerootedCoherentCoverV1.CoherentStickyMultiscaleCover
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8SelectedFiberFaithfulCoherentSuccessorV1
open Family8ParentwiseBadParentBufferedFreshReadyPaperFactorConnectorV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2.SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}

/-- The literal coherent cover rerooted at the lower paper endpoint. -/
abbrev rerootedPaperSourceCover
    (Csource : CoherentStickyMultiscaleCover source)
    (tau : NNReal) (hdeltaTau : delta <= tau) (hTauOne : tau <= 1) :=
  Family8NormalizedFrostmanRerootedCoherentCoverV1.CoherentStickyMultiscaleCover.reroot
    Csource tau hdeltaTau hTauOne

/-- The actual lower-endpoint datum.  The endpoint `1` is used only to name
the already fixed lower family; proof irrelevance makes this definitionally
the same datum used at every later crossing radius. -/
abbrev rerootedPaperSourceDatum
    (Csource : CoherentStickyMultiscaleCover source)
    (tau : NNReal) (hdeltaTau : delta <= tau) (hTauOne : tau <= 1)
    (Y : Shading
      (Csource.base.cover tau hdeltaTau hTauOne).coarse.bodyFamily) :=
  badParentBufferedIntervalSourceDatum
    (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
    tau 1 le_rfl hTauOne le_rfl Y

variable {depth : Nat}
  {Csource : CoherentStickyMultiscaleCover source}
  {hdeltaTau : delta <= tau} {hTauOne : tau <= 1}
  {Y : Shading
    (Csource.base.cover tau hdeltaTau hTauOne).coarse.bodyFamily}
  {hDtau : (rerootedPaperSourceDatum Csource tau hdeltaTau
    hTauOne Y).IsAdmissible}
  {S : FiniteScaleSequence tau depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}

/-- The q half of the doubly buffered hierarchy is exactly the generic
buffered bad-parent readiness on the rerooted literal interval. -/
def badParentFreshBufferedReadiness_of_doublyBuffered
    (W : FirstParentwiseNormalizedCrossingWitness
      (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Y)
      hDtau
      (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
      S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor W X) :
    BadParentFreshBufferedActualHierarchyReadiness
      (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
      tau W.rho le_rfl (crossingDeltaLeRho W) (crossingRhoLeOne W)
      Y (crossingRhoPos W) (crossingBaseQ W)
      X.dualChild.qFibreSelected epsilon hDtau.delta_pos
      H.readiness.q_epsilon_pos := by
  exact
    { source_def212Constant := H.readiness.sourceK
      source_exactDef212 := H.readiness.sourceExact
      fresh_admissible := X.dualChild.qFibreChild_admissible
      fresh_coherentCover := H.readiness.qFreshCover
      fresh_def212Constant := H.readiness.qFreshK
      fresh_exactDef212 := H.readiness.qFreshExact
      ratioPower_le := fun sigma hTauSigma hSigmaRho =>
        H.readiness.q_ratio_power sigma hTauSigma hSigmaRho
      small_delta := H.readiness.q_small_delta
      bufferedScale_le_one := fun sigma _hTauSigma hSigmaRho =>
        H.readiness.q_bufferedScale_le_one sigma hSigmaRho
      parent_realizes_buffered_source :=
        fun sigma hTauSigma hSigmaRho i =>
          H.readiness.qFresh_parent_realizes_buffered_source
            sigma hTauSigma hSigmaRho i }

/-- The paper-factor step and the complete two-child hierarchy are retained
together, so the active child is not discarded when the q child is consumed
by the factor transition. -/
structure DoublyBufferedSameSelectedPaperFactorOutput
    (W : FirstParentwiseNormalizedCrossingWitness
      (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Y)
      hDtau
      (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
      S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W) where
  hierarchy :
    SelectedFiberFaithfulDoublyBufferedCoherentSuccessor W X
  paperStep : SameSelectedBufferedFreshReadyPaperFactorStep
    (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
    tau W.rho le_rfl (crossingDeltaLeRho W) (crossingRhoLeOne W)
    Y (crossingRhoPos W) (crossingBaseQ W)
    X.readiness.left X.readiness.right (crossingStopLower W)
    X.readiness.factorC X.dualChild.qFibreState epsilon
    hDtau.delta_pos hierarchy.readiness.q_epsilon_pos

namespace DoublyBufferedSameSelectedPaperFactorOutput

variable
  {W : FirstParentwiseNormalizedCrossingWitness
    (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Y)
    hDtau
    (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
    S epsilon hepsilon eta N}
  {X : ParentwiseCrossingIntegratedSuccessor W}

/-- The supplied transition is pinned to the literal crossing q and the
single selected set already stored by `X`. -/
def transition
    (O : DoublyBufferedSameSelectedPaperFactorOutput W X) :=
  O.paperStep.transition

end DoublyBufferedSameSelectedPaperFactorOutput

/-- Direct end-to-end producer.  The q hierarchy is selected only once in
`X`; `exists_selectedFiberFaithfulDoublyBufferedCoherentSuccessor` supplies
its real cover and buffered parent ledger, which are immediately consumed by
the existing buffered fresh readiness and paper-factor connector. -/
theorem exists_doublyBufferedSameSelectedPaperFactorOutput
    (W : FirstParentwiseNormalizedCrossingWitness
      (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Y)
      hDtau
      (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
      S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (R : FaithfulDoublyBufferedCoherentSuccessorReadiness W X)
    (leftReadiness : PaperFactorReadinessList X.readiness.left)
    (sourceAtomReadiness : PaperFactorAtomReadiness
      (badParentActiveFineSourceAtom
        (badParentBufferedIntervalSourceDatum
          (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
          tau W.rho le_rfl (crossingDeltaLeRho W)
          (crossingRhoLeOne W) Y)
        (badParentSourceIntervalCover
          (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
          tau W.rho le_rfl (crossingDeltaLeRho W)
          (crossingRhoLeOne W))))
    (rightReadiness : PaperFactorReadinessList X.readiness.right)
    (coarseAtomReadiness : PaperFactorAtomReadiness
      (badParentCoarseAtom
        (badParentBufferedIntervalSourceDatum
          (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
          tau W.rho le_rfl (crossingDeltaLeRho W)
          (crossingRhoLeOne W) Y)
        (badParentSourceIntervalCover
          (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
          tau W.rho le_rfl (crossingDeltaLeRho W)
          (crossingRhoLeOne W)))) :
    Nonempty (DoublyBufferedSameSelectedPaperFactorOutput W X) := by
  obtain ⟨H⟩ :=
    exists_selectedFiberFaithfulDoublyBufferedCoherentSuccessor W X R
  let freshReadiness :=
    badParentFreshBufferedReadiness_of_doublyBuffered W X H
  let paperStep : SameSelectedBufferedFreshReadyPaperFactorStep
      (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
      tau W.rho le_rfl (crossingDeltaLeRho W) (crossingRhoLeOne W)
      Y (crossingRhoPos W) (crossingBaseQ W)
      X.readiness.left X.readiness.right (crossingStopLower W)
      X.readiness.factorC X.dualChild.qFibreState epsilon
      hDtau.delta_pos H.readiness.q_epsilon_pos :=
    { leftReadiness := leftReadiness
      sourceAtomReadiness := sourceAtomReadiness
      rightReadiness := rightReadiness
      coarseAtomReadiness := coarseAtomReadiness
      freshReadiness := freshReadiness }
  exact ⟨{ hierarchy := H, paperStep := paperStep }⟩

#print axioms rerootedPaperSourceDatum
#print axioms badParentFreshBufferedReadiness_of_doublyBuffered
#print axioms DoublyBufferedSameSelectedPaperFactorOutput
#print axioms DoublyBufferedSameSelectedPaperFactorOutput.transition
#print axioms exists_doublyBufferedSameSelectedPaperFactorOutput

end
end Family8SelectedFiberDoublyBufferedPaperFactorConnectorV1
