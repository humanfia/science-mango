import Family8Grounding.Family8GroundedPaperFactorFiniteLossV1
import Mathlib.Tactic

/-!
# Definition 2.12-bound crossing transitions

This module strengthens the V2 crossing readiness at the earliest honest
scalar seam.  The transition constant is not an arbitrary `ENNReal` later
assumed finite: it is chosen definitionally to be the coercion of the exact
source atom's `NNReal` Definition 2.12 constant.

The remaining analytic input is displayed as
`factor_uniform`: that very constant must uniformize the crossing base cover.
Once this is supplied, the existing positive successor producer can be run
with the chosen constant, and both scalar losses of the resulting literal
paper step are automatically finite.

At run level, `GroundedPaperFactorFiniteRunDef212Bindings.consOfBoundStep`
assembles the already established aligned binding without another scalar
equality premise.  The resulting cumulative power absorption is still
datum-local; uniform top-level powers continue to require the uniform local
exponent budget API.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SourceDef212BoundCrossingTransitionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GroundedPaperFactorFiniteLossV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1
open Family8PaperFactorFiniteRunV1
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentIntegratedFactorStateV1
open Family8ParentwiseBadParentMassAwareActiveCoarseConnectorV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseBadParentPointwiseMassAwareSuccessorV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8StickyActiveCoarseAdmissibleChildV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-! ## Readiness whose transition constant is definitionally Def212-bound -/

/-- The V2 crossing inputs with the scalar `factorC` removed as a free
parameter.  It is replaced everywhere by the exact source atom's stored
Definition 2.12 constant.

The field `factor_uniform` is the earliest remaining analytic seam: exact
Definition 2.12 readiness for the source atom does not by itself identify
its internal coherent cover with the ambient crossing base cover. -/
structure SourceDef212CrossingSuccessorReadiness
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) where
  sourceAtomReadiness : PaperFactorAtomReadiness
    (badParentActiveFineSourceAtom D (crossingBaseCover W))
  left : List ActualFactorDatum
  right : List ActualFactorDatum
  baseError : ENNReal
  massLower : ENNReal
  massUpper : ENNReal
  massLower_ne_zero : massLower ≠ 0
  massLower_ne_top : massLower ≠ ∞
  parentMassComparison : IntervalParentMassComparison
    C (S.tau W.m) (S.delta_le_tau W.m)
      ((crossingTauLeRho W).trans (crossingRhoLeOne W)) massLower massUpper
  base_bound : parentNormalizedFiberCFAt
    (crossingBaseCover W) (crossingBaseQ W) <= baseError
  base_strict : baseError < crossingStopLower W
  stopLower_ne_top : crossingStopLower W ≠ ∞
  factor_uniform : IsCUniform (crossingBaseCover W)
    (sourceAtomReadiness.def212Constant : ENNReal)
  rho_le_half : W.rho <= (2 : NNReal)⁻¹
  rho_le_sixteenth : W.rho <= (1 / 16 : NNReal)
  conflictThreshold : Nat
  conflict_cap : forall a : {q // q ∈ (crossingBaseCover W).activeCoarse},
    (normalizedConflictIndices
      (activeCoarseAggregatedDatum D (crossingBaseCover W)) a).card <=
        conflictThreshold
  activeC : ENNReal
  katzTao_at_scale : (crossingBaseCover W).IsKatzTaoAtScale activeC

namespace SourceDef212CrossingSuccessorReadiness

variable
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}

/-- Forget the strengthening.  The legacy readiness receives the Def212
constant by construction, rather than through a later equality field. -/
def toParentwiseCrossingSuccessorReadiness
    (R : SourceDef212CrossingSuccessorReadiness W) :
    ParentwiseCrossingSuccessorReadiness W where
  left := R.left
  right := R.right
  baseError := R.baseError
  massLower := R.massLower
  massUpper := R.massUpper
  massLower_ne_zero := R.massLower_ne_zero
  massLower_ne_top := R.massLower_ne_top
  parentMassComparison := R.parentMassComparison
  base_bound := R.base_bound
  base_strict := R.base_strict
  stopLower_ne_top := R.stopLower_ne_top
  factorC := (R.sourceAtomReadiness.def212Constant : ENNReal)
  factor_uniform := R.factor_uniform
  rho_le_half := R.rho_le_half
  rho_le_sixteenth := R.rho_le_sixteenth
  conflictThreshold := R.conflictThreshold
  conflict_cap := R.conflict_cap
  activeC := R.activeC
  katzTao_at_scale := R.katzTao_at_scale

@[simp] theorem toParentwise_factorC
    (R : SourceDef212CrossingSuccessorReadiness W) :
    R.toParentwiseCrossingSuccessorReadiness.factorC =
      (R.sourceAtomReadiness.def212Constant : ENNReal) :=
  rfl

theorem factorC_ne_top
    (R : SourceDef212CrossingSuccessorReadiness W) :
    R.toParentwiseCrossingSuccessorReadiness.factorC ≠ ∞ := by
  exact ENNReal.coe_ne_top

end SourceDef212CrossingSuccessorReadiness

/-! ## Positive integrated successor with the chosen constant retained -/

/-- An indexed version of the integrated successor.  Indexing by the
strengthened readiness makes the Def212 choice of `factorC` definitionally
visible to the later paper transition. -/
structure SourceDef212CrossingIntegratedSuccessor
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (R : SourceDef212CrossingSuccessorReadiness W) where
  dualChild : ParentwiseBadParentDualChildCertificate
    D (crossingBaseCover W) R.left R.right
      (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W) (crossingStopLower W)
      (R.sourceAtomReadiness.def212Constant : ENNReal)
      R.conflictThreshold R.activeC
  integrated : IntegratedBadParentFactorState
    D (crossingBaseCover W) R.left R.right
      (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W) (crossingStopLower W)
      (R.sourceAtomReadiness.def212Constant : ENNReal)
  same_qFibre_base :
    integrated.factorState = dualChild.qFibreState.base
  base_bad : parentNormalizedFiberCFAt
    (crossingBaseCover W) (crossingBaseQ W) < crossingStopLower W
  interval_upper : parentNormalizedFiberCFAt
    (crossingIntervalCover W) (crossingBaseQ W) <=
      R.baseError * R.massUpper * R.massLower⁻¹
  raw_interval_strict : parentNormalizedFiberCFAt
      (paperBufferedIntervalCover
        D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q <
    crossingStopLower W

namespace SourceDef212CrossingIntegratedSuccessor

variable
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}
    {R : SourceDef212CrossingSuccessorReadiness W}

/-- Forget the index while preserving the chosen readiness literally. -/
def toParentwiseCrossingIntegratedSuccessor
    (X : SourceDef212CrossingIntegratedSuccessor W R) :
    ParentwiseCrossingIntegratedSuccessor W where
  readiness := R.toParentwiseCrossingSuccessorReadiness
  dualChild := X.dualChild
  integrated := X.integrated
  same_qFibre_base := X.same_qFibre_base
  base_bad := X.base_bad
  interval_upper := X.interval_upper
  raw_interval_strict := X.raw_interval_strict

@[simp] theorem toParentwise_factorC
    (X : SourceDef212CrossingIntegratedSuccessor W R) :
    X.toParentwiseCrossingIntegratedSuccessor.readiness.factorC =
      (R.sourceAtomReadiness.def212Constant : ENNReal) :=
  rfl

end SourceDef212CrossingIntegratedSuccessor

/-- Run the existing positive q-fibre and active-parent producers with the
Def212-bound constant.  No scalar equality is assumed in this construction. -/
theorem exists_sourceDef212CrossingIntegratedSuccessor
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (R : SourceDef212CrossingSuccessorReadiness W) :
    Nonempty (SourceDef212CrossingIntegratedSuccessor W R) := by
  obtain ⟨hstate, hbaseBad, hIntervalUpper⟩ :=
    exists_parentwiseBadParentPointwiseMassAwareSuccessor
      D C R.left R.right hD.delta_pos hD.delta_le_half
        (S.delta_le_tau W.m) (crossingTauLeRho W)
        (crossingRhoLeOne W) (crossingRhoPos W)
        R.massLower_ne_zero R.massLower_ne_top
        R.parentMassComparison (crossingBaseQ W) R.base_bound
        R.base_strict R.stopLower_ne_top R.factor_uniform
  obtain ⟨qState⟩ := hstate
  obtain ⟨activeParentState⟩ :=
    exists_activeCoarseAdmissibleFactorState
      D hD (crossingBaseCover W) (crossingRhoPos W) R.rho_le_half
        R.rho_le_sixteenth ⟨(crossingBaseQ W).1, (crossingBaseQ W).2⟩
        R.conflictThreshold R.conflict_cap R.activeC R.katzTao_at_scale
  let dualChild : ParentwiseBadParentDualChildCertificate
      D (crossingBaseCover W) R.left R.right
        (crossingRhoPos W) (crossingRhoLeOne W)
        (crossingBaseQ W) (crossingStopLower W)
        (R.sourceAtomReadiness.def212Constant : ENNReal)
        R.conflictThreshold R.activeC :=
    { qFibreState := qState
      activeParentState := activeParentState }
  let integrated := integratedStateOfMassAware qState
  exact ⟨
    { dualChild := dualChild
      integrated := integrated
      same_qFibre_base := rfl
      base_bad := hbaseBad
      interval_upper := hIntervalUpper
      raw_interval_strict := crossingRawIntervalStrict W }⟩

/-! ## Literal paper transition and automatic finite losses -/

/-- Readiness for all five atoms of the literal replacement, indexed by the
already selected Def212-bound integrated successor. -/
structure SourceDef212PaperStepReadiness
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}
    {R : SourceDef212CrossingSuccessorReadiness W}
    (X : SourceDef212CrossingIntegratedSuccessor W R) where
  leftReadiness : PaperFactorReadinessList R.left
  rightReadiness : PaperFactorReadinessList R.right
  coarseAtomReadiness : PaperFactorAtomReadiness
    (badParentCoarseAtom D (crossingBaseCover W))
  freshAtomReadiness : PaperFactorAtomReadiness
    (badParentFreshChildAtom D (crossingBaseCover W)
      (crossingRhoPos W) (crossingRhoLeOne W) (crossingBaseQ W)
      X.dualChild.qFibreState.base.selected)

namespace SourceDef212PaperStepReadiness

variable
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    {W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N}
    {R : SourceDef212CrossingSuccessorReadiness W}
    {X : SourceDef212CrossingIntegratedSuccessor W R}

/-- Construct the actual same-object V2 paper step. -/
def toSameObjectCrossingPaperStep
    (P : SourceDef212PaperStepReadiness X) :
    SameObjectCrossingPaperStep W :=
  SameObjectCrossingPaperStep.ofReadiness
    X.toParentwiseCrossingIntegratedSuccessor
    P.leftReadiness R.sourceAtomReadiness P.rightReadiness
    P.coarseAtomReadiness P.freshAtomReadiness

/-- The Def212 scalar binding is automatic for a step produced by the
strengthened connector. -/
def sourceDef212UniformityBinding
    (P : SourceDef212PaperStepReadiness X) :
    SourceDef212UniformityBinding P.toSameObjectCrossingPaperStep where
  sourceAtomReadiness := R.sourceAtomReadiness
  factorC_eq_sourceDef212 := rfl

theorem literal_losses_ne_top
    (P : SourceDef212PaperStepReadiness X) :
    (paperFactorProductStep
        P.toSameObjectCrossingPaperStep.paperTransition).uniformityLoss ≠
        ∞ ∧
      (paperFactorProductStep
        P.toSameObjectCrossingPaperStep.paperTransition).freshRetentionLoss ≠
        ∞ := by
  exact ⟨P.sourceDef212UniformityBinding.productStep_uniformityLoss_ne_top,
    sameObjectCrossingPaperStep_freshRetentionLoss_ne_top
      P.toSameObjectCrossingPaperStep⟩

end SourceDef212PaperStepReadiness

/-! ## Assembly into a selector-grounded run -/

namespace GroundedPaperFactorFiniteRunDef212Bindings

/-- Add a connector-produced head step to aligned bindings for the tail.
There is no new `factorC` equality argument: it is discharged by the
definitionally chosen Def212 constant. -/
def consOfBoundStep
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
    (Wsource : FirstParentwiseNormalizedCrossingWitness
      Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
        sourceEta N)
    {R : SourceDef212CrossingSuccessorReadiness Wsource}
    {X : SourceDef212CrossingIntegratedSuccessor Wsource R}
    (P : SourceDef212PaperStepReadiness X)
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
      Wsource P.toSameObjectCrossingPaperStep Wsuccessor)
    (tail : GroundedPaperFactorFiniteRun N Wsuccessor.stage finalStage
      P.toSameObjectCrossingPaperStep.paperTransition.successor finalState)
    (tailBindings : GroundedPaperFactorFiniteRunDef212Bindings tail) :
    GroundedPaperFactorFiniteRunDef212Bindings
      (.cons Wsource P.toSameObjectCrossingPaperStep Wsuccessor edge tail) :=
  .cons Wsource P.toSameObjectCrossingPaperStep Wsuccessor edge tail
    P.sourceDef212UniformityBinding tailBindings

end GroundedPaperFactorFiniteRunDef212Bindings

/-! ## Full runs with no arbitrary scalar-C edge -/

/-- Provenance that every edge of a selector-grounded run was produced by
the Def212-bound connector above.  Unlike
`GroundedPaperFactorFiniteRunDef212Bindings`, its recursive constructor has
no equality field and cannot certify an arbitrary `factorC` step. -/
inductive SourceDef212BoundGroundedPaperFactorFiniteRun :
    forall {N sourceStage finalStage : Nat}
      {sourceState finalState : PaperFactorState},
      GroundedPaperFactorFiniteRun N sourceStage finalStage
        sourceState finalState -> Type 10
  | nil
      {N stage : Nat} {state : PaperFactorState}
      (selector : SelectorStageWitness N state stage) :
      SourceDef212BoundGroundedPaperFactorFiniteRun (.nil selector)
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
      (Wsource : FirstParentwiseNormalizedCrossingWitness
        Dsource hDsource Csource Ssource sourceEpsilon hSourceEpsilon
          sourceEta N)
      {R : SourceDef212CrossingSuccessorReadiness Wsource}
      {X : SourceDef212CrossingIntegratedSuccessor Wsource R}
      (P : SourceDef212PaperStepReadiness X)
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
        Wsource P.toSameObjectCrossingPaperStep Wsuccessor)
      (tail : GroundedPaperFactorFiniteRun N
        Wsuccessor.stage finalStage
        P.toSameObjectCrossingPaperStep.paperTransition.successor finalState)
      (tailBound : SourceDef212BoundGroundedPaperFactorFiniteRun tail) :
      SourceDef212BoundGroundedPaperFactorFiniteRun
        (.cons Wsource P.toSameObjectCrossingPaperStep
          Wsuccessor edge tail)

namespace SourceDef212BoundGroundedPaperFactorFiniteRun

/-- Forget bound-step provenance to the aligned finite-loss bindings.  Each
head binding is generated definitionally by `consOfBoundStep`. -/
def toDef212Bindings
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    {run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState}
    (B : SourceDef212BoundGroundedPaperFactorFiniteRun run) :
    GroundedPaperFactorFiniteRunDef212Bindings run := by
  induction B with
  | nil selector =>
      exact .nil selector
  | cons Wsource P Wsuccessor edge tail tailBound tailBindings =>
      exact GroundedPaperFactorFiniteRunDef212Bindings.consOfBoundStep
        Wsource P Wsuccessor edge tail tailBindings

/-- Both literal loss products are finite on a fully Def212-bound grounded
run.  No arbitrary `factorC` finiteness or scalar equality is accepted by
this API. -/
theorem finiteLossData
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    {run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState}
    (B : SourceDef212BoundGroundedPaperFactorFiniteRun run) :
    RepeatedBadParentFiniteLossData run.productLedger :=
  groundedPaperFactorFiniteRun_finiteLossData run B.toDef212Bindings

/-- Datum-local absorption for a fully Def212-bound run.  The smallness
threshold still depends on the already chosen run, so this is not a uniform
top-level `rawDelta0` producer. -/
theorem datumLocal_power_envelopes
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    {run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState}
    (B : SourceDef212BoundGroundedPaperFactorFiniteRun run)
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
          (-outerExponent) :=
  datumLocal_power_envelopes_of_groundedPaperFactorFiniteRun
    run B.toDef212Bindings hCountExponent hOuterExponent hsmall

/-- Uniform top-level envelope on the same bound run.  Def212 binding removes
the scalar-finiteness seam, while the displayed per-step power estimates
remain the honest analytic inputs needed for a uniform `rawDelta0`. -/
theorem uniformLocalBudget_power_envelopes
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    {run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState}
    (_B : SourceDef212BoundGroundedPaperFactorFiniteRun run)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 <= uniformityExp)
    (hFreshExp : 0 <= freshExp)
    (hUniformity : forall step, step ∈ run.productLedger.steps ->
      step.uniformityLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : forall step, step ∈ run.productLedger.steps ->
      step.freshRetentionLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp)) :
    cumulativeForwardLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-((N : Real) * uniformityExp)) /\
      cumulativeReverseLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-((N : Real) * (uniformityExp + freshExp))) :=
  power_envelopes_of_groundedPaperFactorFiniteRun_uniformLocalBudget
    run hUniformityExp hFreshExp hUniformity hFresh

end SourceDef212BoundGroundedPaperFactorFiniteRun

#print axioms SourceDef212CrossingSuccessorReadiness.factorC_ne_top
#print axioms exists_sourceDef212CrossingIntegratedSuccessor
#print axioms SourceDef212PaperStepReadiness.sourceDef212UniformityBinding
#print axioms SourceDef212PaperStepReadiness.literal_losses_ne_top
#print axioms GroundedPaperFactorFiniteRunDef212Bindings.consOfBoundStep
#print axioms SourceDef212BoundGroundedPaperFactorFiniteRun.toDef212Bindings
#print axioms SourceDef212BoundGroundedPaperFactorFiniteRun.finiteLossData
#print axioms SourceDef212BoundGroundedPaperFactorFiniteRun.datumLocal_power_envelopes
#print axioms SourceDef212BoundGroundedPaperFactorFiniteRun.uniformLocalBudget_power_envelopes

end
end Family8SourceDef212BoundCrossingTransitionV2
