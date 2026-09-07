import Family8Grounding.Family8DoubledParentConflictWeightedDef212WitnessV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictExactDegreeBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedDef212WitnessV1.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# The exact finite doubled-parent conflict degree

A bare `StickyScaleCover` contains no separation axiom for its coarse family:
coarse tubes may even repeat.  Consequently it cannot honestly supply a
scale-independent conflict-degree constant.  It does, however, determine a
literal finite conflict graph.  The maximum closed-neighbourhood cardinality
of that graph is the least possible `ENNReal` budget satisfying
`ClosedDoubledParentConflictDegreeBound`.

This exact budget removes the callback from the weighted selection and from
the resulting Definition 2.12 scale witness.  A later geometric theorem may
bound the same explicit quantity by a paper-level constant without changing
the downstream construction.
-/

namespace ScaleCover

variable {delta rho : NNReal}
variable {index : Type} [Fintype index] [DecidableEq index]
variable {fine : UniformTubeFamily delta index}

/-- The literal closed doubled-parent conflict neighbourhood inside the
active coarse family. -/
noncomputable def closedDoubledParentConflictNeighbours
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    Finset (Fin S.coarseCard) := by
  classical
  exact S.activeCoarse.filter fun l ↦
    l = k ∨ DoubledParentConflict S k l

@[simp]
theorem mem_closedDoubledParentConflictNeighbours
    (S : StickyScaleCover fine rho) (k l : Fin S.coarseCard) :
    l ∈ closedDoubledParentConflictNeighbours S k ↔
      l ∈ S.activeCoarse ∧
        (l = k ∨ DoubledParentConflict S k l) := by
  classical
  simp [closedDoubledParentConflictNeighbours]

/-- Exact maximum closed-neighbourhood cardinality of the finite literal
`2A` conflict graph. -/
noncomputable def doubledParentConflictExactDegreeBudget
    (S : StickyScaleCover fine rho) : ENNReal :=
  S.activeCoarse.sup fun k ↦
    ((closedDoubledParentConflictNeighbours S k).card : ENNReal)

theorem closedDoubledParentConflictNeighbours_card_le_exactDegreeBudget
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard)
    (hk : k ∈ S.activeCoarse) :
    ((closedDoubledParentConflictNeighbours S k).card : ENNReal) ≤
      doubledParentConflictExactDegreeBudget S := by
  exact Finset.le_sup
    (f := fun l ↦
      ((closedDoubledParentConflictNeighbours S l).card : ENNReal)) hk

/-- The exact graph maximum is an automatic, callback-free source of the
degree premise used by weighted selection. -/
theorem closedDoubledParentConflictDegreeBound_exact
    (S : StickyScaleCover fine rho) :
    ClosedDoubledParentConflictDegreeBound S
      (doubledParentConflictExactDegreeBudget S) := by
  intro k hk neighbours hneighbours
  have hneighboursEq :
      neighbours = closedDoubledParentConflictNeighbours S k := by
    ext l
    rw [mem_closedDoubledParentConflictNeighbours]
    exact hneighbours l
  rw [hneighboursEq]
  exact closedDoubledParentConflictNeighbours_card_le_exactDegreeBudget
    S k hk

/-- Minimality: every budget satisfying the public degree predicate is at
least the exact finite graph maximum. -/
theorem exactDegreeBudget_le_of_closedDoubledParentConflictDegreeBound
    (S : StickyScaleCover fine rho) {B : ENNReal}
    (hB : ClosedDoubledParentConflictDegreeBound S B) :
    doubledParentConflictExactDegreeBudget S ≤ B := by
  unfold doubledParentConflictExactDegreeBudget
  apply Finset.sup_le
  intro k hk
  apply hB k hk (closedDoubledParentConflictNeighbours S k)
  intro l
  exact mem_closedDoubledParentConflictNeighbours S k l

/-- The exact budget improves the previous unconditional replacement by the
whole active-coarse cardinality. -/
theorem exactDegreeBudget_le_activeCoarse_card
    (S : StickyScaleCover fine rho) :
    doubledParentConflictExactDegreeBudget S ≤
      (S.activeCoarse.card : ENNReal) := by
  classical
  unfold doubledParentConflictExactDegreeBudget
  apply Finset.sup_le
  intro k _hk
  have hsubset : closedDoubledParentConflictNeighbours S k ⊆
      S.activeCoarse := by
    intro l hl
    exact (mem_closedDoubledParentConflictNeighbours S k l).mp hl |>.1
  exact_mod_cast Finset.card_le_card hsubset

/-- Weighted doubled-parent extraction with no degree callback: its loss is
the exact maximum degree of the source conflict graph. -/
theorem exists_doubledParentConflictWeightedSelection_exactDegree
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) :
    Nonempty (DoubledParentConflictWeightedSelection S weight
      (doubledParentConflictExactDegreeBudget S)) :=
  exists_doubledParentConflictWeightedSelection S weight
    (doubledParentConflictExactDegreeBudget S)
    (closedDoubledParentConflictDegreeBound_exact S)

variable {rho0 Cnn : NNReal}

/-- Callback-free selected Definition 2.12 scale witness.  The retained
cardinality and arbitrary parent mass lose exactly the finite graph maximum,
and all four geometric/CWA fields belong to the same restricted cover. -/
theorem exists_weightedDef212ScaleEndpoint_exactDegree
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal)
    (hrho0 : rho0 ≤ rho) (hrhoOne : rho ≤ 1)
    (hrhoWindow : rho < Cnn * rho0)
    (R : UnitRescalingGeometry S)
    (hCWA : R.FibresSatisfyCWA (Cnn : ENNReal))
    (huniform : IsCUniform S (Cnn : ENNReal))
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Nonempty
      (WeightedDef212ScaleEndpoint S weight
        (doubledParentConflictExactDegreeBudget S) rho0 Cnn) :=
  exists_weightedDef212ScaleEndpoint S weight
    (doubledParentConflictExactDegreeBudget S)
    hrho0 hrhoOne hrhoWindow R hCWA
    (closedDoubledParentConflictDegreeBound_exact S) huniform hpaper

#print axioms mem_closedDoubledParentConflictNeighbours
#print axioms closedDoubledParentConflictNeighbours_card_le_exactDegreeBudget
#print axioms closedDoubledParentConflictDegreeBound_exact
#print axioms exactDegreeBudget_le_of_closedDoubledParentConflictDegreeBound
#print axioms exactDegreeBudget_le_activeCoarse_card
#print axioms exists_doubledParentConflictWeightedSelection_exactDegree
#print axioms exists_weightedDef212ScaleEndpoint_exactDegree

end ScaleCover
end
end Family8DoubledParentConflictExactDegreeBudgetV1
