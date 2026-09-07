import Family8Grounding.Family8SelectedFiberDoublyBufferedPaperFactorConnectorV1
import Family8Grounding.Family8SourceDef212BoundCrossingTransitionV2
import Family8Grounding.Family8GroundedQFreshWeightedBarrierConnectorV1
import Mathlib.Tactic

/-!
# One literal Def212-bound doubly-buffered grounded paper step

This connector merges the two positive one-step constructions on one exact
crossing object.  The integrated successor is selected once by the
Definition 2.12-bound constructor.  The same successor, parent, selected
q-fibre, fresh cover, and readiness objects are then used by the doubly
buffered paper transition.

The resulting finite run has exactly one edge and a selector-grounded nil
tail.  It accepts neither an arbitrary `factorC`, a stage inequality, nor an
already assembled tail run.

The grounded edge consumes only the relative-scale ratio equality and the two
genuinely analytic weighted scalar fields needed by its consumers:

* the ratio equality is consumed only to rewrite the destination threshold on
  the common source relative scale;
* `earlier_commonRatio_scaled` is consumed only by
  `GroundedPaperFactorTransitionCertificate.earlierBarrierTransport`;
* `current_commonRatio_scaled` is consumed only by
  `GroundedPaperFactorTransitionCertificate.current_stage_barrier`.

The weighted crossing-value estimate and finiteness/nonvanishing of its loss
are produced from the literal source and destination q-fibres.  No endpoint
scale match, exact affine reindexing, all-step uniformity, or state equality is
assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8DoublyBufferedDef212GroundedOneStepRunV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8BadParentFreshBufferedActualHierarchyReadinessV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8GroundedQFreshWeightedBarrierConnectorV1
open Family8GroundedWeightedEarlierBarrierTransportV1
open Family8GroundedPaperFactorFiniteLossV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentBufferedFreshReadyPaperFactorConnectorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SameSelectedQFibreCrossingValueTransportV1
open Family8SameSelectedQFibreWeightedCrossingValueTransportV1
open Family8SameSelectedQFibreGenericWeightedCrossingValueTransportV1
open Family8SelectedFiberDoublyBufferedPaperFactorConnectorV1
open Family8SelectedFiberFaithfulBufferedCoherentSuccessorV2
open Family8SourceDef212BoundCrossingTransitionV2
open Family8SourceDef212BoundCrossingTransitionV2.SourceDef212CrossingIntegratedSuccessor
open Family8SourceDef212BoundCrossingTransitionV2.SourceDef212PaperStepReadiness
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta tau : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {source : UniformTubeFamily delta sourceIndex}
  {depth : Nat}
  {Csource : CoherentStickyMultiscaleCover source}
  {hdeltaTau : delta <= tau} {hTauOne : tau <= 1}
  {Ysource : Shading
    (Csource.base.cover tau hdeltaTau hTauOne).coarse.bodyFamily}
  {hDtau : (rerootedPaperSourceDatum Csource tau hdeltaTau
    hTauOne Ysource).IsAdmissible}
  {S : FiniteScaleSequence tau depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}
  {W : FirstParentwiseNormalizedCrossingWitness
    (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
    hDtau (rerootedPaperSourceCover Csource tau hdeltaTau hTauOne)
    S epsilon hepsilon eta N}
  {R : SourceDef212CrossingSuccessorReadiness W}
  {X : SourceDef212CrossingIntegratedSuccessor W R}

/-! ## One transition, viewed through both positive connectors -/

/-- Package the same doubly-buffered hierarchy and readiness fields as the
literal same-selected paper-factor output.  No successor is rebuilt here. -/
def sameSelectedOutput
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (leftReadiness : PaperFactorReadinessList R.left)
    (rightReadiness : PaperFactorReadinessList R.right)
    (coarseAtomReadiness : PaperFactorAtomReadiness
      (badParentCoarseAtom
        (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
        (crossingBaseCover W))) :
    DoublyBufferedSameSelectedPaperFactorOutput
      W X.toParentwiseCrossingIntegratedSuccessor :=
  { hierarchy := H
    paperStep :=
      { leftReadiness := leftReadiness
        sourceAtomReadiness := R.sourceAtomReadiness
        rightReadiness := rightReadiness
        coarseAtomReadiness := coarseAtomReadiness
        freshReadiness :=
          badParentFreshBufferedReadiness_of_doublyBuffered
            W X.toParentwiseCrossingIntegratedSuccessor H } }

/-- Re-index the same five readiness objects by the Def212-bound successor.
The fresh atom is still the literal selected q-fibre child of `X`. -/
def boundPaperStepReadiness
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (leftReadiness : PaperFactorReadinessList R.left)
    (rightReadiness : PaperFactorReadinessList R.right)
    (coarseAtomReadiness : PaperFactorAtomReadiness
      (badParentCoarseAtom
        (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
        (crossingBaseCover W))) :
    SourceDef212PaperStepReadiness X :=
  let O := sameSelectedOutput H leftReadiness rightReadiness
    coarseAtomReadiness
  { leftReadiness := O.paperStep.leftReadiness
    rightReadiness := O.paperStep.rightReadiness
    coarseAtomReadiness := O.paperStep.coarseAtomReadiness
    freshAtomReadiness :=
      O.paperStep.freshReadiness.toPaperFactorAtomReadiness }

/-- The same-selected and Def212-indexed views reduce to the same literal
paper transition.  This is an interface audit theorem, not a state-equality
premise of the run producer. -/
theorem boundPaperTransition_eq_sameSelectedTransition
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor)
    (leftReadiness : PaperFactorReadinessList R.left)
    (rightReadiness : PaperFactorReadinessList R.right)
    (coarseAtomReadiness : PaperFactorAtomReadiness
      (badParentCoarseAtom
        (rerootedPaperSourceDatum Csource tau hdeltaTau hTauOne Ysource)
        (crossingBaseCover W))) :
    (boundPaperStepReadiness H leftReadiness rightReadiness
        coarseAtomReadiness).toSameObjectCrossingPaperStep.paperTransition =
      (sameSelectedOutput H leftReadiness rightReadiness
        coarseAtomReadiness).transition := by
  rfl

/-! ## Destination selector on the very same doubly-buffered q-fresh cover -/

/-- The next first crossing is run on the q-fresh cover already stored by
the doubly-buffered hierarchy.  This avoids selecting a second legacy
faithful cover merely to fit an older destination wrapper. -/
structure DoublyBufferedQFreshCrossingDestination
    (H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor) where
  destinationDepth : Nat
  destinationScales : FiniteScaleSequence
    (badParentFreshChildRadius tau W.rho) destinationDepth
  destinationEpsilon : Real
  destinationEpsilon_nonneg : 0 <= destinationEpsilon
  destinationEta : Nat -> Real
  destination : FirstParentwiseNormalizedCrossingWitness
    X.dualChild.qFibreChildDatum X.dualChild.qFibreChild_admissible
    H.readiness.qFreshCover destinationScales destinationEpsilon
      destinationEpsilon_nonneg destinationEta N

/-! ## Ratio-only literal edge and one-step run -/

/-- Assemble the grounded edge from the weakest retained data.

* `Hrelative` is consumed only by
  `destinationThreshold_eq_sourceRelativeScale`; it asserts no endpoint or
  state equality.
* `B.earlier_commonRatio_scaled` is consumed only by
  `GroundedPaperFactorTransitionCertificate.earlierBarrierTransport`.
* `B.current_commonRatio_scaled` is consumed only by
  `GroundedPaperFactorTransitionCertificate.current_stage_barrier`.

Successor membership, finite/nonzero weighted loss, and the weighted
source-to-destination value inequality are all produced internally. -/
theorem groundedEdge
    {H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor}
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (Hrelative :
      Y.destination.rho /
          Y.destinationScales.tau Y.destination.m =
        W.rho / S.tau W.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := W) (destinationEta := Y.destinationEta)) :
    GroundedPaperFactorTransitionCertificate
      W P.toSameObjectCrossingPaperStep Y.destination :=
  Family8GroundedQFreshWeightedBarrierConnectorV1.doublyBufferedGroundedCertificate
    (Wsource := W) (step := P.toSameObjectCrossingPaperStep)
    H Y.destination Hrelative B

/-- The literal one-edge grounded run.  Its tail is the destination selector
already contained in the edge; no final run is an argument. -/
def groundedOneStepRun
    {H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor}
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (Hrelative :
      Y.destination.rho /
          Y.destinationScales.tau Y.destination.m =
        W.rho / S.tau W.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := W) (destinationEta := Y.destinationEta)) :
    GroundedPaperFactorFiniteRun N W.stage Y.destination.stage
      P.toSameObjectCrossingPaperStep.paperTransition.source
      P.toSameObjectCrossingPaperStep.paperTransition.successor :=
  let edge := groundedEdge P Y Hrelative B
  .cons W P.toSameObjectCrossingPaperStep Y.destination edge
    (.nil edge.successor_stage)

/-- Every edge of the one-step run is definitionally Def212-bound. -/
def groundedOneStepBound
    {H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor}
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (Hrelative :
      Y.destination.rho /
          Y.destinationScales.tau Y.destination.m =
        W.rho / S.tau W.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := W) (destinationEta := Y.destinationEta)) :
    SourceDef212BoundGroundedPaperFactorFiniteRun
      (groundedOneStepRun P Y Hrelative B) :=
  let edge := groundedEdge P Y Hrelative B
  .cons W P Y.destination edge (.nil edge.successor_stage)
    (.nil edge.successor_stage)

/-- Automatic finite literal losses for the produced one-step ledger. -/
theorem groundedOneStep_finiteLossData
    {H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor}
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (Hrelative :
      Y.destination.rho /
          Y.destinationScales.tau Y.destination.m =
        W.rho / S.tau W.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := W) (destinationEta := Y.destinationEta)) :
    RepeatedBadParentFiniteLossData
      (groundedOneStepRun P Y Hrelative B).productLedger :=
  (groundedOneStepBound P Y Hrelative B).finiteLossData

/-- Datum-local power absorption for the exact produced run.  This exposes
only the standard smallness premise of the existing power-envelope theorem;
it introduces no all-step uniformity hypothesis. -/
theorem groundedOneStep_datumLocal_power_envelopes
    {H : SelectedFiberFaithfulDoublyBufferedCoherentSuccessor
      W X.toParentwiseCrossingIntegratedSuccessor}
    (P : SourceDef212PaperStepReadiness X)
    (Y : DoublyBufferedQFreshCrossingDestination H)
    (Hrelative :
      Y.destination.rho /
          Y.destinationScales.tau Y.destination.m =
        W.rho / S.tau W.m)
    (B : QFreshWeightedScalarAbsorption
      (Wsource := W) (destinationEta := Y.destinationEta))
    {countExponent outerExponent : Real}
    (hCountExponent : 0 < countExponent)
    (hOuterExponent : 0 < outerExponent)
    (hsmall : reconstructedSourceRadius
        (groundedOneStepRun P Y Hrelative B).productLedger <=
      groundedPaperFactorFiniteRunPowerEnvelopeThreshold
        (groundedOneStepRun P Y Hrelative B)
          countExponent outerExponent) :
    cumulativeForwardLoss
        (groundedOneStepRun P Y Hrelative B).productLedger <=
        ((reconstructedSourceRadius
          (groundedOneStepRun P Y Hrelative B).productLedger : NNReal) :
            ENNReal) ^ (-countExponent) /\
      cumulativeReverseLoss
          (groundedOneStepRun P Y Hrelative B).productLedger <=
        ((reconstructedSourceRadius
          (groundedOneStepRun P Y Hrelative B).productLedger : NNReal) :
            ENNReal) ^ (-outerExponent) :=
  (groundedOneStepBound P Y Hrelative B).datumLocal_power_envelopes
    hCountExponent hOuterExponent hsmall

#print axioms boundPaperTransition_eq_sameSelectedTransition
#print axioms groundedEdge
#print axioms groundedOneStepRun
#print axioms groundedOneStepBound
#print axioms groundedOneStep_finiteLossData
#print axioms groundedOneStep_datumLocal_power_envelopes

end
end Family8DoublyBufferedDef212GroundedOneStepRunV1
