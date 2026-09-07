import Family8Grounding.Family8PaperFactorFiniteRunV2
import Family8Grounding.Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
import Mathlib.Tactic

/-!
# Lower bound for the grounded reverse paper-factor loss

For an arbitrary erased `BadParentProductStep` neither scalar loss is known
to be at least one.  On a selector-grounded run, however, both facts follow
from the literal provenance of the step:

* the source parent is active, hence its assigned fibre is nonempty, and
  applying the step's actual `IsCUniform` field to that fibre twice gives
  `1 <= C` by cancellation;
* the fresh-retention loss is a nonnegative expression plus `2`.

Their finite product is therefore at least one.  In particular, this lower
bound needs no Definition-2.12 binding beyond the data already stored in a
grounded edge.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal NNReal

namespace Family8GroundedPaperFactorReverseLossLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8PaperFactorFiniteRunV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

/-! ## One-step lower bounds -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem one_le_badParentFreshRetentionLoss
    (S : StickyScaleCover fine rho)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower : ENNReal) :
    1 <= badParentFreshRetentionLoss
      S hrho hrhoOne q selected lower := by
  unfold badParentFreshRetentionLoss
  unfold stickyFiberContractedJohnSourceClosedLoss
  exact (show (1 : ENNReal) <= 2 by norm_num).trans le_add_self

/-- A nonempty occupied fibre prevents an `IsCUniform` constant from being
smaller than one.  This is the precise nondegeneracy needed below; no global
Definition-2.12 package is involved. -/
theorem one_le_isCUniform_of_fiber_nonempty
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {S : StickyScaleCover fine rho} {C : ENNReal}
    (huniform :
      Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover.IsCUniform S C)
    (q : Fin S.coarseCard) (hq : q ∈ S.activeCoarse)
    (hfiber : (S.fiber q).Nonempty) :
    1 <= C := by
  have hn_ne_zero : ((S.fiber q).card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hfiber)
  have hn_ne_top : ((S.fiber q).card : ENNReal) ≠ ∞ := by
    norm_num
  have hself : ((S.fiber q).card : ENNReal) <=
      C * ((S.fiber q).card : ENNReal) := huniform q hq q hq
  exact (ENNReal.mul_le_mul_iff_left hn_ne_zero hn_ne_top).mp (by
    simpa only [one_mul] using hself)

/-- The actual uniformity scalar stored in any same-object crossing step is
at least one.  The distinguished crossing parent is active, and parent
surjectivity supplies the required nonempty fibre. -/
theorem one_le_sameObjectCrossingPaperStep_uniformityLoss
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
    1 <= (paperFactorProductStep step.paperTransition).uniformityLoss := by
  let T := crossingBaseCover W
  let q := crossingBaseQ W
  have hfiber : (T.fiber q.1).Nonempty := by
    obtain ⟨i, hi, hip⟩ := T.parent_surjective q.1 q.2
    exact ⟨i, (T.mem_fiber i q.1).2 ⟨hi, hip⟩⟩
  change 1 <= step.integrated.readiness.factorC
  exact one_le_isCUniform_of_fiber_nonempty
    step.integrated.readiness.factor_uniform q.1 q.2 hfiber

theorem one_le_sameObjectCrossingPaperStep_freshRetentionLoss
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
    1 <= (paperFactorProductStep step.paperTransition).freshRetentionLoss := by
  change 1 <= badParentFreshRetentionLoss
    (crossingBaseCover W) (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W)
      step.integrated.dualChild.qFibreState.base.selected
      (crossingStopLower W)
  exact one_le_badParentFreshRetentionLoss
    (crossingBaseCover W) (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W)
      step.integrated.dualChild.qFibreState.base.selected
      (crossingStopLower W)

/-! ## The aligned cumulative product -/

theorem groundedPaperFactorFiniteRun_one_le_cumulativeReverseLoss
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    1 <= cumulativeReverseLoss run.productLedger := by
  induction run with
  | nil selector =>
      rfl
  | cons Wsource step Wsuccessor edge tail ih =>
      change 1 <=
        ((paperFactorProductStep step.paperTransition).uniformityLoss *
            (paperFactorProductStep step.paperTransition).freshRetentionLoss) *
          cumulativeReverseLoss tail.productLedger
      exact one_le_mul
        (one_le_mul (one_le_sameObjectCrossingPaperStep_uniformityLoss step)
          (one_le_sameObjectCrossingPaperStep_freshRetentionLoss step)) ih

#print axioms one_le_badParentFreshRetentionLoss
#print axioms one_le_isCUniform_of_fiber_nonempty
#print axioms one_le_sameObjectCrossingPaperStep_uniformityLoss
#print axioms one_le_sameObjectCrossingPaperStep_freshRetentionLoss
#print axioms groundedPaperFactorFiniteRun_one_le_cumulativeReverseLoss

end
end Family8GroundedPaperFactorReverseLossLowerV1
