import Family8Grounding.Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1
import Family8Grounding.Family8NormalizedLongIntervalCoreSelectorV1
import Mathlib.Tactic

/-!
# Parentwise normalized long-interval stopping

Lemma 7.7(A)(ii) is parentwise: at every buffered scale, every surviving
parent fibre reaches the displayed normalized-CF lower barrier.  The older
finite selector first replaced the parent family by its cover-wide CF
maximum.  This file keeps the literal parent quantifier through finite
stopping, then provides an explicit compatibility projection to the older
max-based consumer core.

The strict branch returns the actual low-CF parent.  The long branch stores
the universal lower bound on the same interval cover.  No callback or
externally supplied selector is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8ParentwiseNormalizedLongIntervalCoreSelectorV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {epsilon0 beta gamma : Real}

/-- The literal coherent interval cover at a buffered radius, with legality
proved from the actual admissible datum. -/
def bufferedIntervalCover
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    StickyScaleCover
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m))).coarse rho :=
  C.intervalScaleCover (S.tau m) rho
    (S.delta_le_tau m)
    (actualDatum_tau_le_of_isBuffered
      D hD S hepsilon m rho hbuffered)
    (buffered_le_one S hepsilon m rho hbuffered)

/-- Faithful long-terminal core: the middle lower barrier holds for every
literal active parent, not merely for the maximum over parents. -/
structure ParentwiseNormalizedLongIntervalCoreWitness
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (N : Nat) (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (S : FiniteScaleSequence delta depth) where
  m : Fin depth
  stage : Nat
  stage_pos : 1 ≤ stage
  stage_le : stage ≤ N
  long : S.IsLong epsilon m
  middle_parentwise_lower :
    ∀ rho : NNReal, (hbuffered : S.IsBuffered epsilon m rho) →
      ∀ q : {q // q ∈
        (bufferedIntervalCover D hD C S hepsilon m rho hbuffered).activeCoarse},
        (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) ≤
          parentNormalizedFiberCFAt
            (bufferedIntervalCover D hD C S hepsilon m rho hbuffered) q

namespace ParentwiseNormalizedLongIntervalCoreWitness

/-- A terminal parentwise barrier gives the faithful core at the terminal
stage. -/
noncomputable def of_longTerminalParentwiseBarrier
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (m : Fin depth) (hlong : S.IsLong P.epsilon m)
    (hbarrier :
      ∀ rho : NNReal, (hbuffered : S.IsBuffered P.epsilon m rho) →
        ∀ q : {q // q ∈
          (bufferedIntervalCover
            D hD C S P.epsilon_pos.le m rho hbuffered).activeCoarse},
          (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta P.N) ≤
            parentNormalizedFiberCFAt
              (bufferedIntervalCover
                D hD C S P.epsilon_pos.le m rho hbuffered) q) :
    ParentwiseNormalizedLongIntervalCoreWitness
      D hD C P.N P.epsilon P.epsilon_pos.le P.eta S where
  m := m
  stage := P.N
  stage_pos := P.N_pos
  stage_le := le_rfl
  long := hlong
  middle_parentwise_lower := hbarrier

/-- Compatibility with the established max-based consumer core.  Nonempty
active parent sets are the only extra fact needed to pass from an all-parent
barrier to a lower bound for the maximum. -/
noncomputable def toNormalizedLongIntervalCoreWitness
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    {eta : Nat → Real} {N : Nat}
    (W : ParentwiseNormalizedLongIntervalCoreWitness
      D hD C N epsilon hepsilon eta S)
    (hFine : D.family.refinement.refined.Nonempty) :
    NormalizedLongIntervalCoreWitness
      D.family C N epsilon eta S where
  m := W.m
  stage := W.stage
  stage_pos := W.stage_pos
  stage_le := W.stage_le
  long := W.long
  middle_lower := by
    intro rho hbuffered
    let I := bufferedIntervalCover
      D hD C S hepsilon W.m rho hbuffered
    have hvalue :
        Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover.normalizedFiberCFValueAt
            C S W.m rho =
          parentNormalizedFiberCFMax I := by
      simpa only [I, bufferedIntervalCover] using
        (actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
          D hD C S hepsilon W.m rho hbuffered)
    rw [hvalue]
    have hactive : I.activeCoarse.Nonempty := by
      dsimp only [I, bufferedIntervalCover,
        CoherentStickyMultiscaleCover.intervalScaleCover]
      exact
        FamilyStickyHierarchyEndpointNonemptyProducerV1.StickyScaleCover.activeCoarse_nonempty_of_refined_nonempty
          _ hFine
    obtain ⟨q, hq⟩ := hactive
    calc
      (((rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage) ≤
          parentNormalizedFiberCFAt I ⟨q, hq⟩ := by
        simpa only [I] using
          W.middle_parentwise_lower rho hbuffered ⟨q, hq⟩
      _ ≤ parentNormalizedFiberCFMax I :=
        parentNormalizedFiberCFAt_le I ⟨q, hq⟩

end ParentwiseNormalizedLongIntervalCoreWitness

/-- Pure finite stopping with the paper's literal all-parent predicate.
Failure returns an actual active parent below the barrier; absence of such a
parent produces the universal terminal barrier. -/
theorem allLarge_or_longTerminalParentwiseBarrier_or_parentwiseStrictSplit
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (stage : Nat) :
    (S.AllStepsLarge epsilon ∨
      ∃ m : Fin depth, S.IsLong epsilon m ∧
        ∀ rho : NNReal, (hbuffered : S.IsBuffered epsilon m rho) →
          ∀ q : {q // q ∈
            (bufferedIntervalCover
              D hD C S hepsilon m rho hbuffered).activeCoarse},
            (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) ≤
              parentNormalizedFiberCFAt
                (bufferedIntervalCover
                  D hD C S hepsilon m rho hbuffered) q) ∨
      ∃ m : Fin depth, ∃ rho : NNReal,
        ∃ _hnotLarge : ¬ S.IsLarge epsilon m,
          ∃ hbuffered : S.IsBuffered epsilon m rho,
            ∃ q : {q // q ∈
              (bufferedIntervalCover
                D hD C S hepsilon m rho hbuffered).activeCoarse},
              parentNormalizedFiberCFAt
                  (bufferedIntervalCover
                    D hD C S hepsilon m rho hbuffered) q <
                (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) := by
  classical
  by_cases hsplit :
      ∃ m : Fin depth, ∃ rho : NNReal,
        ∃ _hnotLarge : ¬ S.IsLarge epsilon m,
          ∃ hbuffered : S.IsBuffered epsilon m rho,
            ∃ q : {q // q ∈
              (bufferedIntervalCover
                D hD C S hepsilon m rho hbuffered).activeCoarse},
              parentNormalizedFiberCFAt
                  (bufferedIntervalCover
                    D hD C S hepsilon m rho hbuffered) q <
                (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)
  · exact Or.inr hsplit
  · left
    let barrier : Fin depth → Prop := fun m =>
      ∀ rho : NNReal, (hbuffered : S.IsBuffered epsilon m rho) →
        ∀ q : {q // q ∈
          (bufferedIntervalCover
            D hD C S hepsilon m rho hbuffered).activeCoarse},
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) ≤
            parentNormalizedFiberCFAt
              (bufferedIntervalCover
                D hD C S hepsilon m rho hbuffered) q
    have hterminal : ∀ m, S.IsLarge epsilon m ∨ barrier m := by
      intro m
      by_cases hlarge : S.IsLarge epsilon m
      · exact Or.inl hlarge
      · right
        dsimp only [barrier]
        intro rho hbuffered q
        by_contra hnotLower
        apply hsplit
        exact ⟨m, rho, hlarge, hbuffered, q, lt_of_not_ge hnotLower⟩
    rcases S.allStepsLarge_or_exists_long epsilon barrier hterminal with
      hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · exact Or.inr ⟨m, hlong, hbarrier⟩

/-- Callback-free construction chain from finite parentwise stopping to the
faithful LongCore witness. -/
theorem allLarge_or_parentwiseLongIntervalCore_or_parentwiseStrictSplit
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma) :
    ((S.AllStepsLarge P.epsilon ∨
        Nonempty (ParentwiseNormalizedLongIntervalCoreWitness
          D hD C P.N P.epsilon P.epsilon_pos.le P.eta S)) ∨
      ∃ m : Fin depth, ∃ rho : NNReal,
        ∃ _hnotLarge : ¬ S.IsLarge P.epsilon m,
          ∃ hbuffered : S.IsBuffered P.epsilon m rho,
            ∃ q : {q // q ∈
              (bufferedIntervalCover
                D hD C S P.epsilon_pos.le m rho hbuffered).activeCoarse},
              parentNormalizedFiberCFAt
                  (bufferedIntervalCover
                    D hD C S P.epsilon_pos.le m rho hbuffered) q <
                (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta P.N)) := by
  rcases
      allLarge_or_longTerminalParentwiseBarrier_or_parentwiseStrictSplit
        D hD C S P.epsilon P.epsilon_pos.le P.eta P.N with
    hterminal | hsplit
  · left
    rcases hterminal with hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · exact Or.inr ⟨
        ParentwiseNormalizedLongIntervalCoreWitness.of_longTerminalParentwiseBarrier
          D hD C S P m hlong hbarrier⟩
  · exact Or.inr hsplit
/-- The live paper-faithful chain.  The upstream first-crossing selector keeps
one literal bad parent and universal barriers at every earlier stage.  Only
the terminal universal branch is packaged as the parentwise LongCore; the
crossing branch is returned verbatim for the factoring recursion. -/
theorem allLarge_or_parentwiseLongIntervalCore_or_firstParentwiseCrossing
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma) :
    ((S.AllStepsLarge P.epsilon ∨
        Nonempty (ParentwiseNormalizedLongIntervalCoreWitness
          D hD C P.N P.epsilon P.epsilon_pos.le P.eta S)) ∨
      ∃ stage : Nat, stage ≤ P.N ∧
        (∃ m : Fin depth, ∃ rho : NNReal,
          ∃ _hnotLarge : ¬ S.IsLarge P.epsilon m,
          ∃ hbuffered : S.IsBuffered P.epsilon m rho,
          ∃ q : {q // q ∈
              (paperBufferedIntervalCover
                D hD C S P.epsilon P.epsilon_pos.le
                  m rho hbuffered).activeCoarse},
            parentNormalizedFiberCFAt
                (paperBufferedIntervalCover
                  D hD C S P.epsilon P.epsilon_pos.le
                    m rho hbuffered) q <
              (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta stage)) ∧
        ∀ earlier : Nat, earlier < stage →
          ∀ m : Fin depth, ¬ S.IsLarge P.epsilon m →
            ∀ rho : NNReal,
              (hbuffered : S.IsBuffered P.epsilon m rho) →
              ∀ q : {q // q ∈
                  (paperBufferedIntervalCover
                    D hD C S P.epsilon P.epsilon_pos.le
                      m rho hbuffered).activeCoarse},
                (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta earlier) ≤
                  parentNormalizedFiberCFAt
                    (paperBufferedIntervalCover
                      D hD C S P.epsilon P.epsilon_pos.le
                        m rho hbuffered) q) := by
  rcases
      allLarge_or_parentwiseLongTerminalBarrier_or_firstParentwiseCrossing
        D hD C S P.epsilon P.epsilon_pos.le P.eta P.N with
    hterminal | hfirst
  · left
    rcases hterminal with hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · right
      have hbarrier' :
          ∀ rho : NNReal,
            (hbuffered : S.IsBuffered P.epsilon m rho) →
              ∀ q : {q // q ∈
                (bufferedIntervalCover
                  D hD C S P.epsilon_pos.le m rho hbuffered).activeCoarse},
                (((rho / S.tau m : NNReal) : ENNReal) ^ P.eta P.N) ≤
                  parentNormalizedFiberCFAt
                    (bufferedIntervalCover
                      D hD C S P.epsilon_pos.le m rho hbuffered) q := by
        intro rho hbuffered q
        exact hbarrier rho hbuffered q
      exact ⟨
        ParentwiseNormalizedLongIntervalCoreWitness.of_longTerminalParentwiseBarrier
          D hD C S P m hlong hbarrier'⟩
  · exact Or.inr hfirst

#print axioms
  allLarge_or_parentwiseLongIntervalCore_or_firstParentwiseCrossing
#print axioms bufferedIntervalCover
#print axioms
  ParentwiseNormalizedLongIntervalCoreWitness.of_longTerminalParentwiseBarrier
#print axioms
  ParentwiseNormalizedLongIntervalCoreWitness.toNormalizedLongIntervalCoreWitness
#print axioms
  allLarge_or_longTerminalParentwiseBarrier_or_parentwiseStrictSplit
#print axioms
  allLarge_or_parentwiseLongIntervalCore_or_parentwiseStrictSplit

end

end Family8ParentwiseNormalizedLongIntervalCoreSelectorV1
