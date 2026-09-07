import Family8Grounding.Family8PaperFactorFiniteRunV1
import Family8Grounding.Family8ParentwiseCrossingIntegratedSuccessorV1
import Family8Grounding.Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
import Mathlib.Tactic

/-!
# Selector-grounded finite paper-factor runs

V1 records the arithmetic consequences of strictly increasing natural
stages.  This V2 supplies the missing mathematical grounding.  Every edge
is tied to two actual first-parentwise crossing witnesses, and its paper
transition is tied to the same integrated successor and the same dependent
parent `q` as the source crossing.

Crucially, a V2 edge does not store `sourceStage < successorStage`.  It stores
the transported all-parent barrier for the destination crossing through the
source crossing's stage.  If the destination stage were no larger, that
barrier at the destination's own stage would contradict its literal strict
crossing.  Strict stage progress is therefore a theorem about selector
witnesses, not a freely assigned fuel label.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped BigOperators ENNReal NNReal

namespace Family8PaperFactorFiniteRunV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8PaperFactorFiniteRunV1
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentPaperFactorTransitionV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## Literal scalar predicates of an actual first crossing -/

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}

/-- The literal normalized parent concentration selected by `W`. -/
def actualCrossingValue
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) : ENNReal :=
  parentNormalizedFiberCFAt
    (paperBufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q

/-- The literal threshold on the same scale and parent, at an arbitrary
selector stage. -/
def actualCrossingThresholdAt
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (stage : Nat) : ENNReal :=
  (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta stage)

/-- The stored first-crossing inequality, exposed through the stable scalar
names used by the progress proof. -/
theorem actualCrossingValue_lt_thresholdAt_stage
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    actualCrossingValue W < actualCrossingThresholdAt W W.stage := by
  exact W.strict_crossing

/-- The literal universal all-parent barrier at one stage in the source
selector context. -/
def ActualEarlierParentwiseBarrierAt
    (_W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (stage : Nat) : Prop :=
  forall m : Fin depth, ¬ S.IsLarge epsilon m ->
    forall rho : NNReal,
      (hbuffered : S.IsBuffered epsilon m rho) ->
      forall q : {q // q ∈
          (paperBufferedIntervalCover
            D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
        (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
          parentNormalizedFiberCFAt
            (paperBufferedIntervalCover
              D hD C S epsilon hepsilon m rho hbuffered) q

/-- Every earlier stage of a first-crossing witness supplies the literal
universal barrier, without repicking a scale or parent. -/
theorem actualEarlierParentwiseBarrierAt
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    {stage : Nat} (hstage : stage < W.stage) :
    ActualEarlierParentwiseBarrierAt W stage := by
  exact W.earlier_parentwise_barrier stage hstage

/-- Explicit cross-object transport seam for earlier universal barriers.

The transport is forced to accept the complete barrier from the actual
source selector.  A consumer cannot replace it by a bare natural-number
inequality. -/
structure EarlierBarrierTransport
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    (Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N)
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
    (Wsuccessor : FirstParentwiseNormalizedCrossingWitness
      Dsuccessor hDsuccessor Csuccessor Ssuccessor
        successorEpsilon hSuccessorEpsilon successorEta N) where
  transport : forall stage : Nat, stage < Wsource.stage ->
    ActualEarlierParentwiseBarrierAt Wsource stage ->
      actualCrossingThresholdAt Wsuccessor stage <=
        actualCrossingValue Wsuccessor

namespace EarlierBarrierTransport

/-- Apply the seam only to the actual earlier barrier stored by `Wsource`. -/
theorem transported_earlier
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    {Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N}
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
    {Wsuccessor : FirstParentwiseNormalizedCrossingWitness
      Dsuccessor hDsuccessor Csuccessor Ssuccessor
        successorEpsilon hSuccessorEpsilon successorEta N}
    (H : EarlierBarrierTransport Wsource Wsuccessor)
    {stage : Nat} (hstage : stage < Wsource.stage) :
    actualCrossingThresholdAt Wsuccessor stage <=
      actualCrossingValue Wsuccessor := by
  exact H.transport stage hstage
    (actualEarlierParentwiseBarrierAt Wsource hstage)

end EarlierBarrierTransport

/-! ## One exact same-object paper step -/

/-- A paper transition built on the exact StateV2/q-fibre state of an
integrated first-crossing successor.

The types force the base cover, `crossingBaseQ W`, selected q-fibre state,
left/right lists, and scalar constants to be the ones stored by
`integrated`.  The two explicit equalities keep the same-object and same-q
facts inspectable by downstream consumers. -/
structure SameObjectCrossingPaperStep
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {depth : Nat}
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) where
  integrated : ParentwiseCrossingIntegratedSuccessor W
  paperTransition : ParentwiseBadParentPaperFactorTransition
    D (crossingBaseCover W)
      integrated.readiness.left integrated.readiness.right
      (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W) (crossingStopLower W)
      integrated.readiness.factorC
      integrated.dualChild.qFibreState
  same_qFibre_base :
    integrated.integrated.factorState =
      integrated.dualChild.qFibreState.base
  base_q_val_eq_raw_q : (crossingBaseQ W).1 = W.q.1

namespace SameObjectCrossingPaperStep

/-- Construct the same-object step from explicit readiness for every atom.
This is a value-level producer on one already selected crossing, not a
successor callback. -/
def ofReadiness
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {depth : Nat}
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (leftReadiness : PaperFactorReadinessList X.readiness.left)
    (sourceAtomReadiness : PaperFactorAtomReadiness
      (badParentActiveFineSourceAtom D (crossingBaseCover W)))
    (rightReadiness : PaperFactorReadinessList X.readiness.right)
    (coarseAtomReadiness : PaperFactorAtomReadiness
      (badParentCoarseAtom D (crossingBaseCover W)))
    (freshAtomReadiness : PaperFactorAtomReadiness
      (badParentFreshChildAtom D (crossingBaseCover W)
        (crossingRhoPos W) (crossingRhoLeOne W)
        (crossingBaseQ W) X.dualChild.qFibreState.base.selected)) :
    SameObjectCrossingPaperStep W where
  integrated := X
  paperTransition :=
    parentwiseBadParentPaperFactorTransition
      D (crossingBaseCover W)
      X.readiness.left X.readiness.right
      (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W) (crossingStopLower W)
      X.readiness.factorC X.dualChild.qFibreState
      leftReadiness sourceAtomReadiness rightReadiness
      coarseAtomReadiness freshAtomReadiness
  same_qFibre_base := X.same_qFibre_base
  base_q_val_eq_raw_q := crossingBaseQ_val W

end SameObjectCrossingPaperStep

/-! ## Selector witnesses anchored to paper states -/

/-- A real selector stage attached to one exact paper state.

The crossing constructors are anchored by a same-object paper step.  The
terminal constructor is anchored by a genuine all-parent LongCore selector
and membership of its literal datum atom in the paper state's actual factor
list. -/
inductive SelectorStageWitness (N : Nat) :
    PaperFactorState -> Nat -> Type 5
  | crossingSource
      {delta : NNReal} {iota : Type}
      [Fintype iota] [DecidableEq iota]
      {depth : Nat}
      {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
      {C : CoherentStickyMultiscaleCover D.family}
      {S : FiniteScaleSequence delta depth}
      {epsilon : Real} {hepsilon : 0 <= epsilon}
      {eta : Nat -> Real}
      (W : FirstParentwiseNormalizedCrossingWitness
        D hD C S epsilon hepsilon eta N)
      (step : SameObjectCrossingPaperStep W) :
      SelectorStageWitness N step.paperTransition.source W.stage
  | crossingSuccessor
      {sourceDelta : NNReal} {sourceIndex : Type}
      [Fintype sourceIndex] [DecidableEq sourceIndex]
      {sourceDepth : Nat}
      {Dsource : ActualTubeDatum sourceDelta sourceIndex}
      {hDsource : Dsource.IsAdmissible}
      {Csource : CoherentStickyMultiscaleCover Dsource.family}
      {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
      {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
      {sourceEta : Nat -> Real}
      (Wsource : FirstParentwiseNormalizedCrossingWitness
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
      (Wsuccessor : FirstParentwiseNormalizedCrossingWitness
        Dsuccessor hDsuccessor Csuccessor Ssuccessor
          successorEpsilon hSuccessorEpsilon successorEta N)
      (successorDatum_mem :
        ActualFactorDatum.ofDatum Dsuccessor ∈
          step.paperTransition.successor.factors) :
      SelectorStageWitness N
        step.paperTransition.successor Wsuccessor.stage
  | terminal
      {delta : NNReal} {iota : Type}
      [Fintype iota] [DecidableEq iota]
      {depth : Nat}
      {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
      {C : CoherentStickyMultiscaleCover D.family}
      {S : FiniteScaleSequence delta depth}
      {epsilon : Real} {hepsilon : 0 <= epsilon}
      {eta : Nat -> Real}
      (state : PaperFactorState)
      (W : ParentwiseNormalizedLongIntervalCoreWitness
        D hD C N epsilon hepsilon eta S)
      (datum_mem : ActualFactorDatum.ofDatum D ∈ state.factors) :
      SelectorStageWitness N state W.stage

namespace SelectorStageWitness

/-- Every state stage is bounded because it is literally the stage stored by
its crossing or terminal selector witness. -/
theorem stage_le
    {N stage : Nat} {state : PaperFactorState}
    (W : SelectorStageWitness N state stage) : stage <= N := by
  cases W with
  | crossingSource crossing step => exact crossing.stage_le
  | crossingSuccessor source step successor successorDatum_mem =>
      exact successor.stage_le
  | terminal state terminal datum_mem => exact terminal.stage_le

end SelectorStageWitness

/-! ## A grounded edge: strict progress is derived, never stored -/

/-- One paper edge with a destination selector whose actual all-parent
barrier has been transported through the source crossing stage.

No natural-number progress inequality is a field. -/
structure GroundedPaperFactorTransitionCertificate
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    (Wsource : FirstParentwiseNormalizedCrossingWitness
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
    (Wsuccessor : FirstParentwiseNormalizedCrossingWitness
      Dsuccessor hDsuccessor Csuccessor Ssuccessor
        successorEpsilon hSuccessorEpsilon successorEta N) where
  successorDatum_mem :
    ActualFactorDatum.ofDatum Dsuccessor ∈
      step.paperTransition.successor.factors
  earlierBarrierTransport : EarlierBarrierTransport Wsource Wsuccessor
  current_stage_barrier :
    actualCrossingThresholdAt Wsuccessor Wsource.stage <=
      actualCrossingValue Wsuccessor

namespace GroundedPaperFactorTransitionCertificate

/-- The source paper state is anchored to the literal source crossing. -/
def source_stage
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    {Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N}
    {step : SameObjectCrossingPaperStep Wsource}
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
    {Wsuccessor : FirstParentwiseNormalizedCrossingWitness
      Dsuccessor hDsuccessor Csuccessor Ssuccessor
        successorEpsilon hSuccessorEpsilon successorEta N}
    (_H : GroundedPaperFactorTransitionCertificate
      Wsource step Wsuccessor) :
    SelectorStageWitness N
      step.paperTransition.source Wsource.stage :=
  .crossingSource Wsource step

/-- The successor paper state is anchored to the literal destination datum
and destination first crossing. -/
def successor_stage
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    {Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N}
    {step : SameObjectCrossingPaperStep Wsource}
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
    {Wsuccessor : FirstParentwiseNormalizedCrossingWitness
      Dsuccessor hDsuccessor Csuccessor Ssuccessor
        successorEpsilon hSuccessorEpsilon successorEta N}
    (H : GroundedPaperFactorTransitionCertificate
      Wsource step Wsuccessor) :
    SelectorStageWitness N
      step.paperTransition.successor Wsuccessor.stage :=
  .crossingSuccessor Wsource step Wsuccessor H.successorDatum_mem

/-- Actual first-crossing minimality forces genuine stage progress.

If `Wsuccessor.stage <= Wsource.stage`, the transported destination barrier
applies at `Wsuccessor.stage`; it is incompatible with the destination's
stored strict crossing at that same literal scale and parent. -/
theorem stage_strict
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    {Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N}
    {step : SameObjectCrossingPaperStep Wsource}
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
    {Wsuccessor : FirstParentwiseNormalizedCrossingWitness
      Dsuccessor hDsuccessor Csuccessor Ssuccessor
        successorEpsilon hSuccessorEpsilon successorEta N}
    (H : GroundedPaperFactorTransitionCertificate
      Wsource step Wsuccessor) :
    Wsource.stage < Wsuccessor.stage := by
  by_contra hnot
  have hstage : Wsuccessor.stage <= Wsource.stage := Nat.le_of_not_gt hnot
  have hbarrier :
      actualCrossingThresholdAt Wsuccessor Wsuccessor.stage <=
        actualCrossingValue Wsuccessor := by
    rcases hstage.lt_or_eq with hlt | heq
    · exact H.earlierBarrierTransport.transported_earlier hlt
    · simpa only [heq] using H.current_stage_barrier
  exact (not_lt_of_ge hbarrier)
    (actualCrossingValue_lt_thresholdAt_stage Wsuccessor)

/-- Only after grounding both states and deriving progress do we export the
arithmetic V1 certificate. -/
theorem toV1StageCertificate
    {sourceDelta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {sourceDepth : Nat}
    {Dsource : ActualTubeDatum sourceDelta sourceIndex}
    {hDsource : Dsource.IsAdmissible}
    {Csource : CoherentStickyMultiscaleCover Dsource.family}
    {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
    {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
    {sourceEta : Nat -> Real} {N : Nat}
    {Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N}
    {step : SameObjectCrossingPaperStep Wsource}
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
    {Wsuccessor : FirstParentwiseNormalizedCrossingWitness
      Dsuccessor hDsuccessor Csuccessor Ssuccessor
        successorEpsilon hSuccessorEpsilon successorEta N}
    (H : GroundedPaperFactorTransitionCertificate
      Wsource step Wsuccessor) :
    PaperFactorStageTransitionCertificate
      N Wsource.stage Wsuccessor.stage step.paperTransition where
  sourceStage_le := Wsource.stage_le
  successorStage_le := Wsuccessor.stage_le
  stage_strict := H.stage_strict

end GroundedPaperFactorTransitionCertificate

/-! ## Selector-grounded finite chains -/

/-- A chain in which every edge is grounded by actual source/destination
first crossings.  The zero-edge constructor also requires a real crossing
or terminal selector witness for its paper state. -/
inductive GroundedPaperFactorFiniteRun (N : Nat) :
    Nat -> Nat -> PaperFactorState -> PaperFactorState -> Type 6
  | nil {stage : Nat} {state : PaperFactorState}
      (selector : SelectorStageWitness N state stage) :
      GroundedPaperFactorFiniteRun N stage stage state state
  | cons
      {finalStage : Nat} {finalState : PaperFactorState}
      {sourceDelta : NNReal} {sourceIndex : Type}
      [Fintype sourceIndex] [DecidableEq sourceIndex]
      {sourceDepth : Nat}
      {Dsource : ActualTubeDatum sourceDelta sourceIndex}
      {hDsource : Dsource.IsAdmissible}
      {Csource : CoherentStickyMultiscaleCover Dsource.family}
      {Ssource : FiniteScaleSequence sourceDelta sourceDepth}
      {sourceEpsilon : Real} {hSourceEpsilon : 0 <= sourceEpsilon}
      {sourceEta : Nat -> Real}
      (Wsource : FirstParentwiseNormalizedCrossingWitness
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
      (Wsuccessor : FirstParentwiseNormalizedCrossingWitness
        Dsuccessor hDsuccessor Csuccessor Ssuccessor
          successorEpsilon hSuccessorEpsilon successorEta N)
      (edge : GroundedPaperFactorTransitionCertificate
        Wsource step Wsuccessor)
      (tail : GroundedPaperFactorFiniteRun N
        Wsuccessor.stage finalStage
        step.paperTransition.successor finalState) :
      GroundedPaperFactorFiniteRun N
        Wsource.stage finalStage step.paperTransition.source finalState

namespace GroundedPaperFactorFiniteRun

/-- Forget selector objects only after every V1 stage certificate has been
derived from literal crossing inequalities. -/
def toPaperFactorFiniteRun
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState := by
  induction run with
  | nil selector =>
      exact .nil _ _ selector.stage_le
  | cons Wsource step Wsuccessor edge tail ih =>
      exact .cons step.paperTransition edge.toV1StageCertificate ih

/-- Exact repeated product ledger of the grounded chain. -/
def productLedger
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    RepeatedBadParentLedger sourceState.factors finalState.factors :=
  run.toPaperFactorFiniteRun.productLedger

/-- The finite bound now follows from actual selector stages. -/
theorem productLedger_steps_length_le_N
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    run.productLedger.steps.length <= N := by
  exact run.toPaperFactorFiniteRun.productLedger_steps_length_le_N

/-- Selector-grounded termination with the exact accumulated loss ledger. -/
theorem bounded_cumulative_exactProductCertificate
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    run.productLedger.steps.length <= N + 1 ∧
      factorRadiusProduct sourceState.factors =
        (64 / 3 : NNReal) ^ run.productLedger.steps.length *
          factorRadiusProduct finalState.factors ∧
      factorCardProduct finalState.factors <=
        (run.productLedger.steps.map
          (fun productStep => productStep.uniformityLoss)).prod *
            factorCardProduct sourceState.factors ∧
      factorCardProduct sourceState.factors <=
        (run.productLedger.steps.map (fun productStep =>
          productStep.uniformityLoss *
            productStep.freshRetentionLoss)).prod *
              factorCardProduct finalState.factors := by
  exact
    run.toPaperFactorFiniteRun.bounded_cumulative_exactProductCertificate

end GroundedPaperFactorFiniteRun

#print axioms actualCrossingValue_lt_thresholdAt_stage
#print axioms SameObjectCrossingPaperStep.ofReadiness
#print axioms SelectorStageWitness.stage_le
#print axioms GroundedPaperFactorTransitionCertificate.source_stage
#print axioms GroundedPaperFactorTransitionCertificate.successor_stage
#print axioms GroundedPaperFactorTransitionCertificate.stage_strict
#print axioms GroundedPaperFactorTransitionCertificate.toV1StageCertificate
#print axioms GroundedPaperFactorFiniteRun.toPaperFactorFiniteRun
#print axioms GroundedPaperFactorFiniteRun.productLedger_steps_length_le_N
#print axioms
  GroundedPaperFactorFiniteRun.bounded_cumulative_exactProductCertificate

end
end Family8PaperFactorFiniteRunV2
