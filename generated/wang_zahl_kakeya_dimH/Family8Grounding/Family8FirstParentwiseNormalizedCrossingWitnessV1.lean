import Family8Grounding.Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1
import Mathlib.Tactic

/-!
# Positive data for a literal first parentwise normalized crossing

The parentwise finite selector has a right branch consisting of one literal
active parent with a strict normalized-CF crossing, together with the full
universal parent barrier at every earlier stage.  This module stores exactly
that output as positive data and packages the raw existential branch without
changing its scale, parent, cover, or inequalities.

The witness is intentionally independent of any endpoint-identity
specialization or contradiction argument, so constructive successor modules
can import it directly.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FirstParentwiseNormalizedCrossingWitnessV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Submission.Kakeya.Uniformity

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

/-- The exact literal-parent first crossing emitted by the parentwise finite
selector.  The strict field concerns the stored parent `q`, and every earlier
barrier retains its universal parent quantifier. -/
structure FirstParentwiseNormalizedCrossingWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) where
  stage : Nat
  stage_le : stage <= N
  m : Fin depth
  rho : NNReal
  notLarge : ¬ S.IsLarge epsilon m
  buffered : S.IsBuffered epsilon m rho
  q : {q // q ∈
    (paperBufferedIntervalCover
      D hD C S epsilon hepsilon m rho buffered).activeCoarse}
  strict_crossing :
    parentNormalizedFiberCFAt
        (paperBufferedIntervalCover
          D hD C S epsilon hepsilon m rho buffered) q <
      (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)
  earlier_parentwise_barrier :
    forall earlier : Nat, earlier < stage ->
      forall m' : Fin depth, ¬ S.IsLarge epsilon m' ->
        forall rho' : NNReal,
          (hbuffered : S.IsBuffered epsilon m' rho') ->
          forall q' : {q // q ∈
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m' rho' hbuffered).activeCoarse},
            (((rho' / S.tau m' : NNReal) : ENNReal) ^ eta earlier) <=
              parentNormalizedFiberCFAt
                (paperBufferedIntervalCover
                  D hD C S epsilon hepsilon m' rho' hbuffered) q'

namespace FirstParentwiseNormalizedCrossingWitness

/-- Package the raw parentwise-selector branch without repicking its stage,
scale, parent, strict inequality, or earlier universal barriers. -/
theorem nonempty_of_selector_output
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 <= epsilon}
    {eta : Nat -> Real} {N : Nat}
    (hfirst :
      exists stage : Nat, stage <= N /\
        (exists m : Fin depth, exists rho : NNReal,
          exists _hnotLarge : ¬ S.IsLarge epsilon m,
          exists hbuffered : S.IsBuffered epsilon m rho,
          exists q : {q // q ∈
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
            parentNormalizedFiberCFAt
                (paperBufferedIntervalCover
                  D hD C S epsilon hepsilon m rho hbuffered) q <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) /\
        forall earlier : Nat, earlier < stage ->
          forall m : Fin depth, ¬ S.IsLarge epsilon m ->
            forall rho : NNReal,
              (hbuffered : S.IsBuffered epsilon m rho) ->
              forall q : {q // q ∈
                  (paperBufferedIntervalCover
                    D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
                (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                  parentNormalizedFiberCFAt
                    (paperBufferedIntervalCover
                      D hD C S epsilon hepsilon m rho hbuffered) q) :
    Nonempty (FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) := by
  rcases hfirst with
    ⟨stage, hstage, ⟨m, rho, hnotLarge, hbuffered, q, hstrict⟩,
      hearlier⟩
  exact ⟨{
    stage := stage
    stage_le := hstage
    m := m
    rho := rho
    notLarge := hnotLarge
    buffered := hbuffered
    q := q
    strict_crossing := hstrict
    earlier_parentwise_barrier := hearlier }⟩

end FirstParentwiseNormalizedCrossingWitness

#print axioms FirstParentwiseNormalizedCrossingWitness
#print axioms FirstParentwiseNormalizedCrossingWitness.nonempty_of_selector_output

end
end Family8FirstParentwiseNormalizedCrossingWitnessV1
