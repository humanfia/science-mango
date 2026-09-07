import Family8Grounding.Family8PaperFactorFiniteRunPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Finite scalar losses on selector-grounded paper-factor runs

This module closes the first scalar-finiteness seam left by the repeated
bad-parent ledger.

* The literal reverse loss `L` is proved finite by expanding the actual
  selected-card envelope.  Its inputs are exactly the crossing stop lower
  barrier, `X.base.fresh_loss_ne_top`, and the finite selected cardinality.
* The arbitrary transition constant `factorC` is not merely postulated
  finite.  `SourceDef212UniformityBinding` identifies it with the `NNReal`
  Definition 2.12 constant carried by readiness for the exact source atom.
* A structurally aligned binding for every edge of the selector-grounded V2
  run produces `RepeatedBadParentFiniteLossData` for its literal ledger.

The resulting finite-product absorption theorem remains datum-local because
its smallness threshold depends on the already selected run.  Uniform
top-level powers must instead use the local-exponent API of
`Family8PaperFactorFiniteRunPowerEnvelopeV1`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal NNReal

namespace Family8GroundedPaperFactorFiniteLossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV1
open Family8PaperFactorFiniteRunV1.PaperFactorFiniteRun
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PaperFactorFiniteRunPowerEnvelopeV1.RepeatedBadParentFiniteLossData
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open Family8StickySelectedFiberLowCFScalarEnvelopeV4
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## The literal outer fresh-retention loss is finite -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Expand the actual bad-parent loss all the way to its finite scalar
ingredients.  No upper power estimate is assumed here. -/
theorem badParentFreshRetentionLoss_ne_top_of_lower
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    {lower : ENNReal} (hlower : lower ≠ ∞)
    (hfresh : selectedParentLowCFFreshLoss
      S hrho hrhoOne q lower ≠ ∞) :
    badParentFreshRetentionLoss
      S hrho hrhoOne q selected lower ≠ ∞ := by
  have hcard : (selected.card : ENNReal) ≠ ∞ := by norm_num
  have hcardEnvelope :
      selectedFiberLowCFCardEnvelope S q selected lower
          (selectedParentLowCFFreshLoss S hrho hrhoOne q lower) ≠ ∞ := by
    unfold selectedFiberLowCFCardEnvelope
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hlower
        (ENNReal.mul_ne_top (by norm_num) hfresh)) hcard
  unfold badParentFreshRetentionLoss
  unfold stickyFiberContractedJohnSourceClosedLoss
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) hcardEnvelope)), by norm_num⟩

/-! ## A Definition 2.12 binding on one actual V2 crossing edge -/

/-- Bind the scalar uniformity constant of a same-object crossing step to
the `NNReal` Definition 2.12 constant carried by readiness for its exact
active-fine source atom.  This is stronger and more faithful than adding an
unrelated `factorC_ne_top` field. -/
structure SourceDef212UniformityBinding
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {depth : Nat}
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}
    (step : SameObjectCrossingPaperStep W) where
  sourceAtomReadiness : PaperFactorAtomReadiness
    (badParentActiveFineSourceAtom D (crossingBaseCover W))
  factorC_eq_sourceDef212 :
    step.integrated.readiness.factorC =
      (sourceAtomReadiness.def212Constant : ENNReal)

namespace SourceDef212UniformityBinding

variable
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {depth : Nat}
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}
    {step : SameObjectCrossingPaperStep W}

/-- The bound transition constant is finite because it is literally the
coercion of a readiness `NNReal`. -/
theorem factorC_ne_top
    (B : SourceDef212UniformityBinding step) :
    step.integrated.readiness.factorC ≠ ∞ := by
  rw [B.factorC_eq_sourceDef212]
  exact ENNReal.coe_ne_top

/-- The forward scalar loss in the exact projected paper step is finite. -/
theorem productStep_uniformityLoss_ne_top
    (B : SourceDef212UniformityBinding step) :
    (paperFactorProductStep step.paperTransition).uniformityLoss ≠ ∞ := by
  change step.integrated.readiness.factorC ≠ ∞
  exact B.factorC_ne_top

end SourceDef212UniformityBinding

/-- The reverse fresh-retention scalar of every actual V2 same-object edge
is finite without another binding field.  The stop lower and inner fresh
loss are fields of the very same integrated successor. -/
theorem sameObjectCrossingPaperStep_freshRetentionLoss_ne_top
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {depth : Nat}
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}
    (step : SameObjectCrossingPaperStep W) :
    (paperFactorProductStep step.paperTransition).freshRetentionLoss ≠ ∞ := by
  change badParentFreshRetentionLoss
    (crossingBaseCover W) (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W)
      step.integrated.dualChild.qFibreState.base.selected
      (crossingStopLower W) ≠ ∞
  exact badParentFreshRetentionLoss_ne_top_of_lower
    (crossingBaseCover W) (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W)
      step.integrated.dualChild.qFibreState.base.selected
      step.integrated.readiness.stopLower_ne_top
      step.integrated.dualChild.qFibreState.base.fresh_loss_ne_top

/-! ## Structurally aligned bindings on a grounded V2 run -/

/-- One Definition 2.12 binding for every actual crossing edge, aligned by
recursion with the V2 run rather than supplied as a callback on erased scalar
steps. -/
inductive GroundedPaperFactorFiniteRunDef212Bindings :
    forall {N sourceStage finalStage : Nat}
      {sourceState finalState : PaperFactorState},
      GroundedPaperFactorFiniteRun N sourceStage finalStage
        sourceState finalState -> Type 7
  | nil
      {N stage : Nat} {state : PaperFactorState}
      (selector : SelectorStageWitness N state stage) :
      GroundedPaperFactorFiniteRunDef212Bindings (.nil selector)
  | cons
      {N finalStage : Nat} {finalState : PaperFactorState}
      {sourceDelta : NNReal} {sourceIndex : Type}
      [Fintype sourceIndex] [DecidableEq sourceIndex]
      {sourceDepth : Nat}
      {Dsource : ActualTubeDatum sourceDelta sourceIndex}
      {hDsource : Dsource.IsAdmissible}
      {Csource : CoherentStickyMultiscaleCover Dsource.family}
      {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
      {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
      {sourceEta : Nat -> Real}
      (Wsource : Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness
        Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
          sourceEta N)
      (step : SameObjectCrossingPaperStep Wsource)
      {successorDelta : NNReal} {successorIndex : Type}
      [Fintype successorIndex] [DecidableEq successorIndex]
      {successorDepth : Nat}
      {Dsuccessor : ActualTubeDatum successorDelta successorIndex}
      {hDsuccessor : Dsuccessor.IsAdmissible}
      {Csuccessor : CoherentStickyMultiscaleCover Dsuccessor.family}
      {Ssuccessor : FiniteScaleSequence successorDelta successorDepth}
      {successorEpsilon : Real}
      {hSuccessorEpsilon : 0 <= successorEpsilon}
      {successorEta : Nat -> Real}
      (Wsuccessor : Family8FirstParentwiseNormalizedCrossingWitnessV1.FirstParentwiseNormalizedCrossingWitness
        Dsuccessor hDsuccessor Csuccessor Ssuccessor
          successorEpsilon hSuccessorEpsilon successorEta N)
      (edge : GroundedPaperFactorTransitionCertificate
        Wsource step Wsuccessor)
      (tail : GroundedPaperFactorFiniteRun N
        Wsuccessor.stage finalStage
        step.paperTransition.successor finalState)
      (headBinding : SourceDef212UniformityBinding step)
      (tailBindings : GroundedPaperFactorFiniteRunDef212Bindings tail) :
      GroundedPaperFactorFiniteRunDef212Bindings
        (.cons Wsource step Wsuccessor edge tail)

/-- The aligned bindings produce pointwise finiteness of both literal losses
in the grounded repeated ledger. -/
theorem groundedPaperFactorFiniteRun_finiteLossData
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    (bindings : GroundedPaperFactorFiniteRunDef212Bindings run) :
    RepeatedBadParentFiniteLossData run.productLedger := by
  induction bindings with
  | nil selector =>
      constructor
      · intro productStep hmem
        change productStep ∈ ([] : List BadParentProductStep) at hmem
        simp at hmem
      · intro productStep hmem
        change productStep ∈ ([] : List BadParentProductStep) at hmem
        simp at hmem
  | cons Wsource step Wsuccessor edge tail headBinding tailBindings tailFinite =>
      constructor
      · intro productStep hmem
        change productStep ∈
          paperFactorProductStep step.paperTransition ::
            tail.productLedger.steps at hmem
        exact (List.mem_cons.mp hmem).elim
          (fun hhead => by
            simpa [hhead] using
              headBinding.productStep_uniformityLoss_ne_top)
          (fun htail =>
            tailFinite.uniformityLoss_ne_top productStep htail)
      · intro productStep hmem
        change productStep ∈
          paperFactorProductStep step.paperTransition ::
            tail.productLedger.steps at hmem
        exact (List.mem_cons.mp hmem).elim
          (fun hhead => by
            simpa [hhead] using
              sameObjectCrossingPaperStep_freshRetentionLoss_ne_top step)
          (fun htail =>
            tailFinite.freshRetentionLoss_ne_top productStep htail)

/-! ## Datum-local cumulative power absorption -/

/-- The finite-product threshold of the exported V1 run.  It depends on this
already chosen grounded run and is not a uniform `rawDelta0`. -/
def groundedPaperFactorFiniteRunPowerEnvelopeThreshold
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    (countExponent outerExponent : Real) : NNReal :=
  paperFactorFiniteRunPowerEnvelopeThreshold
    run.toPaperFactorFiniteRun countExponent outerExponent

/-- Grounded edges with Definition 2.12 bindings feed the finite cumulative
envelope producer.  The conclusion is useful datum-locally; the threshold
premise is deliberately visible. -/
theorem datumLocal_power_envelopes_of_groundedPaperFactorFiniteRun
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    (bindings : GroundedPaperFactorFiniteRunDef212Bindings run)
    {countExponent outerExponent : Real}
    (hCountExponent : 0 < countExponent)
    (hOuterExponent : 0 < outerExponent)
    (hsmall : reconstructedSourceRadius run.productLedger <=
      groundedPaperFactorFiniteRunPowerEnvelopeThreshold run
        countExponent outerExponent) :
    cumulativeForwardLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-countExponent) /\
      cumulativeReverseLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-outerExponent) := by
  let v1 := run.toPaperFactorFiniteRun
  have finiteData : RepeatedBadParentFiniteLossData v1.productLedger := by
    simpa only [v1, GroundedPaperFactorFiniteRun.productLedger] using
      groundedPaperFactorFiniteRun_finiteLossData run bindings
  have hsmallV1 : reconstructedSourceRadius v1.productLedger <=
      paperFactorFiniteRunPowerEnvelopeThreshold v1
        countExponent outerExponent := by
    simpa only [v1, GroundedPaperFactorFiniteRun.productLedger,
      groundedPaperFactorFiniteRunPowerEnvelopeThreshold] using hsmall
  have H := power_envelopes_of_paperFactorFiniteRun_finiteLoss
    v1 finiteData hCountExponent hOuterExponent hsmallV1
  simpa only [v1, GroundedPaperFactorFiniteRun.productLedger] using H

#print axioms badParentFreshRetentionLoss_ne_top_of_lower
#print axioms SourceDef212UniformityBinding.factorC_ne_top
#print axioms SourceDef212UniformityBinding.productStep_uniformityLoss_ne_top
#print axioms sameObjectCrossingPaperStep_freshRetentionLoss_ne_top
#print axioms groundedPaperFactorFiniteRun_finiteLossData
#print axioms datumLocal_power_envelopes_of_groundedPaperFactorFiniteRun

end
end Family8GroundedPaperFactorFiniteLossV1
