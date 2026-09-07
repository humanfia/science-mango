import Family8Grounding.Family8NormalizedCFDividingWitnessFiniteSelectionV1

open scoped ENNReal NNReal

namespace Family8NormalizedCFDividingWitnessFiniteSelectionV2

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover
open Submission.Kakeya.Uniformity

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# First normalized threshold crossing

For the literal, totalized parent-normalized fibre values, finite
well-ordering gives an honest alternative.  Either no strict split occurs at
any stage through `N`, in which case every such stage has the lower barrier,
or there is a first crossing stage.  At that stage an explicit interval and
radius give the strict normalized upper bound, while every earlier stage has
the lower barrier at every non-large interval and buffered radius.

No crossing, upper, or lower statement is an input to these theorems.
-/

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat}

/-- Callback-free first crossing for the actual normalized values. -/
theorem allStagesBarrier_or_firstNormalizedCrossing
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (eta : Nat -> Real) (N : Nat) :
    (∀ stage : Nat, stage <= N ->
      ∀ m : Fin depth, ¬ S.IsLarge epsilon m ->
        ∀ rho : NNReal, S.IsBuffered epsilon m rho ->
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage) <=
            normalizedFiberCFValueAt C S m rho) ∨
      ∃ stage : Nat, stage <= N ∧
        (∃ m : Fin depth, ∃ rho : NNReal,
          ¬ S.IsLarge epsilon m ∧ S.IsBuffered epsilon m rho ∧
            normalizedFiberCFValueAt C S m rho <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) ∧
        ∀ earlier : Nat, earlier < stage ->
          ∀ m : Fin depth, ¬ S.IsLarge epsilon m ->
            ∀ rho : NNReal, S.IsBuffered epsilon m rho ->
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                normalizedFiberCFValueAt C S m rho := by
  classical
  let crossing : Nat -> Prop := fun stage =>
    stage <= N ∧
      ∃ m : Fin depth, ∃ rho : NNReal,
        ¬ S.IsLarge epsilon m ∧ S.IsBuffered epsilon m rho ∧
          normalizedFiberCFValueAt C S m rho <
            (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)
  by_cases hex : ∃ stage, crossing stage
  · right
    let first := Nat.find hex
    have hfirst : crossing first := Nat.find_spec hex
    refine ⟨first, hfirst.1, hfirst.2, ?_⟩
    intro earlier hearlier m hnotLarge rho hbuffered
    exact le_of_not_gt fun hlt =>
      Nat.find_min hex hearlier
        ⟨hfirst.1.trans' (Nat.le_of_lt hearlier),
          m, rho, hnotLarge, hbuffered, hlt⟩
  · left
    intro stage hstage m hnotLarge rho hbuffered
    exact le_of_not_gt fun hlt =>
      hex ⟨stage, hstage, m, rho, hnotLarge, hbuffered, hlt⟩

/-- Terminal form of the first-crossing theorem.  In the no-crossing branch,
the pure finite scale selector returns either all-large or an actual long
interval carrying the normalized lower barrier at the last allowed stage.
The other branch retains the first strict crossing and every prior lower
barrier verbatim. -/
theorem allLarge_or_longTerminalBarrier_or_firstNormalizedCrossing
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (eta : Nat -> Real) (N : Nat) :
    (S.AllStepsLarge epsilon ∨
      ∃ m : Fin depth, S.IsLong epsilon m ∧
        ∀ rho : NNReal, S.IsBuffered epsilon m rho ->
          (((rho / S.tau m : NNReal) : ENNReal) ^ eta N) <=
            normalizedFiberCFValueAt C S m rho) ∨
      ∃ stage : Nat, stage <= N ∧
        (∃ m : Fin depth, ∃ rho : NNReal,
          ¬ S.IsLarge epsilon m ∧ S.IsBuffered epsilon m rho ∧
            normalizedFiberCFValueAt C S m rho <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) ∧
        ∀ earlier : Nat, earlier < stage ->
          ∀ m : Fin depth, ¬ S.IsLarge epsilon m ->
            ∀ rho : NNReal, S.IsBuffered epsilon m rho ->
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                normalizedFiberCFValueAt C S m rho := by
  rcases allStagesBarrier_or_firstNormalizedCrossing C S epsilon eta N with
    hallBarrier | hfirst
  · left
    let barrier : Fin depth -> Prop := fun m =>
      ∀ rho : NNReal, S.IsBuffered epsilon m rho ->
        (((rho / S.tau m : NNReal) : ENNReal) ^ eta N) <=
          normalizedFiberCFValueAt C S m rho
    have hterminal : ∀ m, S.IsLarge epsilon m ∨ barrier m := by
      intro m
      by_cases hlarge : S.IsLarge epsilon m
      · exact Or.inl hlarge
      · exact Or.inr (hallBarrier N le_rfl m hlarge)
    exact S.allStepsLarge_or_exists_long epsilon barrier hterminal
  · exact Or.inr hfirst

#print axioms allStagesBarrier_or_firstNormalizedCrossing
#print axioms allLarge_or_longTerminalBarrier_or_firstNormalizedCrossing

end CoherentStickyMultiscaleCover

end
end Family8NormalizedCFDividingWitnessFiniteSelectionV2
