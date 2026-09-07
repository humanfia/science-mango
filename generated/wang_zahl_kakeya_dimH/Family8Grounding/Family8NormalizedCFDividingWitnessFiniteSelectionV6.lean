import Family8Grounding.Family8NormalizedCFDividingWitnessFiniteSelectionV4

open scoped ENNReal NNReal

namespace Family8NormalizedCFDividingWitnessFiniteSelectionV6

open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV2.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Submission.Kakeya.Uniformity

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Literal-cover form of the first normalized crossing

The finite selector in V2 is deliberately totalized outside the legal scale
range.  V4 proves that every buffered witness produced from an admissible
datum is legal and identifies the totalized value with the normalized
concentration of the literal coherent interval cover.

This file performs that rewrite throughout the terminal trichotomy.  Its
output therefore contains actual `StickyScaleCover` values both at the first
crossing and at every earlier barrier.  No crossing value, cover, scale
bound, or concentration comparison is supplied by the caller.
-/

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The callback-free first-crossing trichotomy, rewritten on the literal
coherent interval covers. -/
theorem allLarge_or_longTerminalActualBarrier_or_firstActualNormalizedCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) :
    (S.AllStepsLarge epsilon ∨
      ∃ m : Fin depth, S.IsLong epsilon m ∧
        ∀ rho : NNReal, (hbuffered : S.IsBuffered epsilon m rho) ->
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta N) <=
            parentNormalizedFiberCFMax
              (C.intervalScaleCover (S.tau m) rho
                (S.delta_le_tau m)
                (actualDatum_tau_le_of_isBuffered
                  D hD S hepsilon m rho hbuffered)
                (buffered_le_one S hepsilon m rho hbuffered))) ∨
      ∃ stage : Nat, stage <= N ∧
        (∃ m : Fin depth, ∃ rho : NNReal,
          ∃ _hnotLarge : ¬ S.IsLarge epsilon m,
          ∃ hbuffered : S.IsBuffered epsilon m rho,
            parentNormalizedFiberCFMax
                (C.intervalScaleCover (S.tau m) rho
                  (S.delta_le_tau m)
                  (actualDatum_tau_le_of_isBuffered
                    D hD S hepsilon m rho hbuffered)
                  (buffered_le_one S hepsilon m rho hbuffered)) <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) ∧
        ∀ earlier : Nat, earlier < stage ->
          ∀ m : Fin depth, ¬ S.IsLarge epsilon m ->
            ∀ rho : NNReal, (hbuffered : S.IsBuffered epsilon m rho) ->
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                parentNormalizedFiberCFMax
                  (C.intervalScaleCover (S.tau m) rho
                    (S.delta_le_tau m)
                    (actualDatum_tau_le_of_isBuffered
                      D hD S hepsilon m rho hbuffered)
                    (buffered_le_one S hepsilon m rho hbuffered)) := by
  rcases
      allLarge_or_longTerminalBarrier_or_firstNormalizedCrossing
        C S epsilon eta N with
    hterminal | hfirst
  · left
    rcases hterminal with hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · right
      refine ⟨m, hlong, ?_⟩
      intro rho hbuffered
      rw [← actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
        D hD C S hepsilon m rho hbuffered]
      exact hbarrier rho hbuffered
  · right
    rcases hfirst with ⟨stage, hstage, hcrossing, hearlier⟩
    refine ⟨stage, hstage, ?_, ?_⟩
    · rcases hcrossing with
        ⟨m, rho, hnotLarge, hbuffered, hstrict⟩
      refine ⟨m, rho, hnotLarge, hbuffered, ?_⟩
      rw [← actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
        D hD C S hepsilon m rho hbuffered]
      exact hstrict
    · intro earlier hearlierStage m hnotLarge rho hbuffered
      rw [← actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
        D hD C S hepsilon m rho hbuffered]
      exact hearlier earlier hearlierStage m hnotLarge rho hbuffered

#print axioms
  allLarge_or_longTerminalActualBarrier_or_firstActualNormalizedCrossing

end CoherentStickyMultiscaleCover

end

end Family8NormalizedCFDividingWitnessFiniteSelectionV6
