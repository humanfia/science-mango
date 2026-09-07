import Family8Grounding.Family8NormalizedCFDividingWitnessFiniteSelectionV6

open scoped ENNReal NNReal

namespace Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1

open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Submission.Kakeya.Uniformity

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Parentwise normalized finite stopping

Lemma 7.7(A)(ii) of the paper does not merely lower-bound the maximum
normalized fibre concentration.  At every buffered radius it lower-bounds
the normalized concentration over **every** active parent.  Consequently a
strict split is witnessed by one active parent whose fibre lies below the
threshold, and the absence of a strict split gives the desired universal
parentwise barrier.

This module records that quantifier before any mass-popular selection is
performed.  It deliberately leaves the older `CFMax` selector intact for
compatibility, but does not derive the parentwise conclusion from it.
-/

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The literal coherent `tau_m`-to-`rho` cover at a buffered radius.  The
stable name keeps every parentwise statement on definitionally the same
cover. -/
def paperBufferedIntervalCover
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :=
  C.intervalScaleCover (S.tau m) rho
    (S.delta_le_tau m)
    (actualDatum_tau_le_of_isBuffered
      D hD S hepsilon m rho hbuffered)
    (buffered_le_one S hepsilon m rho hbuffered)

/-- Either every stage through `N` has the paper's universal parentwise
barrier, or there is a first stage and a literal bad parent witnessing the
strict split.  Every earlier stage retains the universal barrier. -/
theorem allStagesParentwiseBarrier_or_firstParentwiseNormalizedCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) :
    (forall stage : Nat, stage <= N ->
      forall m : Fin depth, ¬ S.IsLarge epsilon m ->
        forall rho : NNReal, (hbuffered : S.IsBuffered epsilon m rho) ->
          forall k : {k // k ∈
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
            (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
              parentNormalizedFiberCFAt
                (paperBufferedIntervalCover
                  D hD C S epsilon hepsilon m rho hbuffered) k) ∨
      exists stage : Nat, stage <= N ∧
        (exists m : Fin depth, exists rho : NNReal,
          exists _hnotLarge : ¬ S.IsLarge epsilon m,
          exists hbuffered : S.IsBuffered epsilon m rho,
          exists k : {k // k ∈
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
            parentNormalizedFiberCFAt
                (paperBufferedIntervalCover
                  D hD C S epsilon hepsilon m rho hbuffered) k <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) ∧
        forall earlier : Nat, earlier < stage ->
          forall m : Fin depth, ¬ S.IsLarge epsilon m ->
            forall rho : NNReal,
              (hbuffered : S.IsBuffered epsilon m rho) ->
              forall k : {k // k ∈
                  (paperBufferedIntervalCover
                    D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
                (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                  parentNormalizedFiberCFAt
                    (paperBufferedIntervalCover
                      D hD C S epsilon hepsilon m rho hbuffered) k := by
  classical
  let crossing : Nat -> Prop := fun stage =>
    stage <= N ∧
      exists m : Fin depth, exists rho : NNReal,
        exists _hnotLarge : ¬ S.IsLarge epsilon m,
        exists hbuffered : S.IsBuffered epsilon m rho,
        exists k : {k // k ∈
            (paperBufferedIntervalCover
              D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
          parentNormalizedFiberCFAt
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m rho hbuffered) k <
            (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)
  by_cases hex : exists stage, crossing stage
  · right
    let first := Nat.find hex
    have hfirst : crossing first := Nat.find_spec hex
    refine ⟨first, hfirst.1, hfirst.2, ?_⟩
    intro earlier hearlier m hnotLarge rho hbuffered k
    exact le_of_not_gt fun hlt =>
      Nat.find_min hex hearlier
        ⟨hfirst.1.trans' (Nat.le_of_lt hearlier),
          m, rho, hnotLarge, hbuffered, k, hlt⟩
  · left
    intro stage hstage m hnotLarge rho hbuffered k
    exact le_of_not_gt fun hlt =>
      hex ⟨stage, hstage, m, rho, hnotLarge, hbuffered, k, hlt⟩

/-- Terminal form of the parentwise first-crossing theorem.  In the
no-crossing branch the pure finite interval selector supplies a long interval
whose every active parent satisfies the normalized lower barrier. -/
theorem allLarge_or_parentwiseLongTerminalBarrier_or_firstParentwiseCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) :
    (S.AllStepsLarge epsilon ∨
      exists m : Fin depth, S.IsLong epsilon m ∧
        forall rho : NNReal,
          (hbuffered : S.IsBuffered epsilon m rho) ->
          forall k : {k // k ∈
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
            (((rho / S.tau m : NNReal) : ENNReal) ^ eta N) <=
              parentNormalizedFiberCFAt
                (paperBufferedIntervalCover
                  D hD C S epsilon hepsilon m rho hbuffered) k) ∨
      exists stage : Nat, stage <= N ∧
        (exists m : Fin depth, exists rho : NNReal,
          exists _hnotLarge : ¬ S.IsLarge epsilon m,
          exists hbuffered : S.IsBuffered epsilon m rho,
          exists k : {k // k ∈
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
            parentNormalizedFiberCFAt
                (paperBufferedIntervalCover
                  D hD C S epsilon hepsilon m rho hbuffered) k <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) ∧
        forall earlier : Nat, earlier < stage ->
          forall m : Fin depth, ¬ S.IsLarge epsilon m ->
            forall rho : NNReal,
              (hbuffered : S.IsBuffered epsilon m rho) ->
              forall k : {k // k ∈
                  (paperBufferedIntervalCover
                    D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
                (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                  parentNormalizedFiberCFAt
                    (paperBufferedIntervalCover
                      D hD C S epsilon hepsilon m rho hbuffered) k := by
  rcases
      allStagesParentwiseBarrier_or_firstParentwiseNormalizedCrossing
        D hD C S epsilon hepsilon eta N with hallBarrier | hfirst
  · left
    let barrier : Fin depth -> Prop := fun m =>
      forall rho : NNReal,
        (hbuffered : S.IsBuffered epsilon m rho) ->
        forall k : {k // k ∈
            (paperBufferedIntervalCover
              D hD C S epsilon hepsilon m rho hbuffered).activeCoarse},
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta N) <=
            parentNormalizedFiberCFAt
              (paperBufferedIntervalCover
                D hD C S epsilon hepsilon m rho hbuffered) k
    have hterminal : forall m, S.IsLarge epsilon m ∨ barrier m := by
      intro m
      by_cases hlarge : S.IsLarge epsilon m
      · exact Or.inl hlarge
      · exact Or.inr (hallBarrier N le_rfl m hlarge)
    exact S.allStepsLarge_or_exists_long epsilon barrier hterminal
  · exact Or.inr hfirst

#print axioms paperBufferedIntervalCover
#print axioms
  allStagesParentwiseBarrier_or_firstParentwiseNormalizedCrossing
#print axioms
  allLarge_or_parentwiseLongTerminalBarrier_or_firstParentwiseCrossing

end CoherentStickyMultiscaleCover

end
end Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1
