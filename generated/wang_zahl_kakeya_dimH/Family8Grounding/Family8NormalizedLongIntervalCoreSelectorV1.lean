import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1

/-!
# Direct finite selector for the normalized long-interval consumer core

The canonical middle-scale consumers read only the selected interval, the
terminal stage, longness, and the middle lower barrier.  Those fields are
already supplied by the finite stopping selector before any source or
adjacent Definition 2.12 estimate is invoked.  This file records that direct
projection, avoiding an unnecessary fine-parent commuting obligation on the
path to those consumers.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8NormalizedLongIntervalCoreSelectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

namespace NormalizedLongIntervalCoreWitness

/-- A terminal actual barrier already contains every field used by the
canonical middle-scale consumer core. -/
noncomputable def of_longTerminalActualBarrier
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (m : Fin depth) (hlong : S.IsLong P.epsilon m)
    (hbarrier : ∀ rho : NNReal,
      (hbuffered : S.IsBuffered P.epsilon m rho) →
        (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta P.N) ≤
          parentNormalizedFiberCFMax
            (C.intervalScaleCover (S.tau m) rho
              (S.delta_le_tau m)
              (actualDatum_tau_le_of_isBuffered
                D hD S P.epsilon_pos.le m rho hbuffered)
              (buffered_le_one S P.epsilon_pos.le m rho hbuffered))) :
    NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta S where
  m := m
  stage := P.N
  stage_pos := P.N_pos
  stage_le := le_rfl
  long := hlong
  middle_lower := by
    intro rho hbuffered
    rw [actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
      D hD C S P.epsilon_pos.le m rho hbuffered]
    exact hbarrier rho hbuffered

end NormalizedLongIntervalCoreWitness

/-- Direct trichotomy for all downstream users of the common core.  No
partitioning, rescaled CWA, source-upper, or adjacent-upper datum is needed. -/
theorem allLarge_or_normalizedLongIntervalCore_or_firstCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma) :
    ((S.AllStepsLarge P.epsilon ∨
        Nonempty (NormalizedLongIntervalCoreWitness
          D.family C P.N P.epsilon P.eta S)) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        D hD C S P.epsilon P.epsilon_pos.le P.eta P.N)) := by
  rcases
      Family8NormalizedCFDividingWitnessFiniteSelectionV6.CoherentStickyMultiscaleCover.allLarge_or_longTerminalActualBarrier_or_firstActualNormalizedCrossing
        D hD C S P.epsilon P.epsilon_pos.le P.eta P.N with
    hterminal | hfirst
  · left
    rcases hterminal with hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · exact Or.inr ⟨
        NormalizedLongIntervalCoreWitness.of_longTerminalActualBarrier
          D hD C S P m hlong hbarrier⟩
  · right
    exact FirstActualNormalizedCrossingWitness.nonempty_of_selector_output
      hfirst

#print axioms
  NormalizedLongIntervalCoreWitness.of_longTerminalActualBarrier
#print axioms allLarge_or_normalizedLongIntervalCore_or_firstCrossing

end
end Family8NormalizedLongIntervalCoreSelectorV1
