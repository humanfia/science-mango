import Family8Grounding.Family8NormalizedCFDividingWitnessActualCoverBridgeV4
import FamilyStickyGrounding.FamilyStickyDividingScalesNoSplitV2

open scoped ENNReal NNReal

namespace Family8NormalizedCFDividingWitnessFiniteSelectionV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesNoSplitV2
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Callback-free finite selection for normalized fibre concentration

The legacy actual-value module totalizes absolute `fiberDeltaMax`.  This file
does the same for the paper-normalized parent-fibre constant and runs the
pure finite terminal selection on that computed value.

The output is an honest trichotomy: all intervals are large; an explicit
strict normalized split exists; or a long interval satisfies the normalized
lower barrier at every buffered radius.  The strict-split branch is retained
rather than hidden in a no-split premise.  Iterating/factoring that branch is
the remaining geometric part of Lemma 7.7(A).
-/

namespace StickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The computed worst parent-normalized fibre constant at scale `rho`,
totalized by zero outside the legal range. -/
def actualParentNormalizedFiberCFMaxAt
    (M : StickyMultiscaleCover fine) (rho : NNReal) : ENNReal :=
  if hdelta : delta <= rho then
    if hrho : rho <= 1 then
      parentNormalizedFiberCFMax (M.cover rho hdelta hrho)
    else 0
  else 0

@[simp] theorem actualParentNormalizedFiberCFMaxAt_eq
    (M : StickyMultiscaleCover fine) (rho : NNReal)
    (hdelta : delta <= rho) (hrho : rho <= 1) :
    actualParentNormalizedFiberCFMaxAt M rho =
      parentNormalizedFiberCFMax (M.cover rho hdelta hrho) := by
  simp [actualParentNormalizedFiberCFMaxAt, hdelta, hrho]

end StickyMultiscaleCover

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat}

/-- The actual parent-normalized fibre value on terminal interval `m`. -/
def normalizedFiberCFValueAt
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (m : Fin depth) (rho : NNReal) : ENNReal :=
  StickyMultiscaleCover.actualParentNormalizedFiberCFMaxAt
    ((C.toActualIntervalCovers S).multiscale m) rho

/-- In range, the totalized value is definitionally the normalized constant
of the literal coherent `tau_m`-to-`rho` cover. -/
theorem normalizedFiberCFValueAt_eq
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (m : Fin depth) (rho : NNReal)
    (htau : S.tau m <= rho) (hrho : rho <= 1) :
    normalizedFiberCFValueAt C S m rho =
      parentNormalizedFiberCFMax
        (C.intervalScaleCover (S.tau m) rho
          (S.delta_le_tau m) htau hrho) := by
  unfold normalizedFiberCFValueAt
  rw [StickyMultiscaleCover.actualParentNormalizedFiberCFMaxAt_eq
    _ rho htau hrho]
  rfl

/-- A callback-free finite selector for the actual normalized values.

If a strict split exists it is returned explicitly.  Otherwise the finite
scale lemma selects a long interval and the negated strict split produces
the pointwise normalized lower barrier. -/
theorem allLarge_or_normalizedStrictSplit_or_longBarrier
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (eta : Nat -> Real) (stage : Nat) :
    S.AllStepsLarge epsilon ∨
      (∃ m : Fin depth, ∃ rho : NNReal,
        ¬ S.IsLarge epsilon m ∧ S.IsBuffered epsilon m rho ∧
          normalizedFiberCFValueAt C S m rho <
            (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) ∨
      (∃ m : Fin depth, S.IsLong epsilon m ∧
        ∀ rho : NNReal, S.IsBuffered epsilon m rho ->
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
            normalizedFiberCFValueAt C S m rho) := by
  classical
  by_cases hsplit : ∃ m : Fin depth, ∃ rho : NNReal,
      ¬ S.IsLarge epsilon m ∧ S.IsBuffered epsilon m rho ∧
        normalizedFiberCFValueAt C S m rho <
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)
  · exact Or.inr (Or.inl hsplit)
  · let barrier : Fin depth -> Prop := fun m =>
      ∀ rho : NNReal, S.IsBuffered epsilon m rho ->
        (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
          normalizedFiberCFValueAt C S m rho
    have hterminal : ∀ m, S.IsLarge epsilon m ∨ barrier m := by
      intro m
      by_cases hlarge : S.IsLarge epsilon m
      · exact Or.inl hlarge
      · right
        apply lowerBound_of_no_strict_split
        intro hlocal
        obtain ⟨rho, hbuffered, hlt⟩ := hlocal
        exact hsplit ⟨m, rho, hlarge, hbuffered, hlt⟩
    rcases S.allStepsLarge_or_exists_long epsilon barrier hterminal with
      hall | ⟨m, hlong, hbarrier⟩
    · exact Or.inl hall
    · exact Or.inr (Or.inr ⟨m, hlong, hbarrier⟩)

#print axioms StickyMultiscaleCover.actualParentNormalizedFiberCFMaxAt_eq
#print axioms normalizedFiberCFValueAt_eq
#print axioms allLarge_or_normalizedStrictSplit_or_longBarrier

end CoherentStickyMultiscaleCover

end
end Family8NormalizedCFDividingWitnessFiniteSelectionV1
