import Family8Grounding.Family8DoubledParentConflictClusteringV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedRetentionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictClusteringV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1

noncomputable section

/-!
# Quantitative doubled-parent conflict extraction

The loss parameter below is not inferred from the mere existence of an
owner partition.  It is the literal cardinality bound for a closed
`2A`-conflict neighbourhood.  Under precisely that geometric input, the
largest-mass greedy theorem produces one parent selection which
simultaneously retains parent cardinality and arbitrary `ENNReal` mass.
-/

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}

/-- A conflict-free parent selection with simultaneous cardinality and
arbitrary-mass retention. -/
structure DoubledParentConflictWeightedSelection
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B : ENNReal) where
  selected : Finset (Fin S.coarseCard)
  selected_subset : selected ⊆ S.activeCoarse
  selected_nonempty : S.activeCoarse.Nonempty → selected.Nonempty
  selected_pairwise : Set.Pairwise
    (↑selected : Set (Fin S.coarseCard))
    (fun k l ↦ ¬ DoubledParentConflict S k l)
  card_le : (S.activeCoarse.card : ENNReal) ≤
    B * (selected.card : ENNReal)
  mass_le : (∑ k ∈ S.activeCoarse, weight k) ≤
    B * ∑ k ∈ selected, weight k

/-- The exact geometric seam needed for quantitative `2A` selection.  The
extensional-neighbourhood formulation keeps an implementation-only
`DecidableRel` instance out of this public proposition. -/
def ClosedDoubledParentConflictDegreeBound
    (S : StickyScaleCover fine rho) (B : ENNReal) : Prop :=
  ∀ k, k ∈ S.activeCoarse →
    ∀ neighbours : Finset (Fin S.coarseCard),
      (∀ l, l ∈ neighbours ↔
        l ∈ S.activeCoarse ∧
          (l = k ∨ DoubledParentConflict S k l)) →
      (neighbours.card : ENNReal) ≤ B

/-- Largest-mass greedy extraction specialized to the literal doubled-parent
conflict graph.  The same selection gives both advertised inequalities. -/
theorem exists_doubledParentConflictWeightedSelection
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B : ENNReal)
    (hneighbour : ClosedDoubledParentConflictDegreeBound S B) :
    Nonempty (DoubledParentConflictWeightedSelection S weight B) := by
  classical
  have hfiltered : ∀ k, k ∈ S.activeCoarse →
      ((S.activeCoarse.filter fun l ↦
        l = k ∨ DoubledParentConflict S k l).card : ENNReal) ≤ B := by
    intro k hk
    apply hneighbour k hk
    intro l
    simp
  obtain ⟨selected, hsubset, hnonempty, hpairwise, hcard, hmass⟩ :=
    exists_greedy_pairwise_not_relation S.activeCoarse
      (DoubledParentConflict S) (doubledParentConflict_symm S)
      weight B hfiltered
  exact ⟨
    { selected := selected
      selected_subset := hsubset
      selected_nonempty := hnonempty
      selected_pairwise := hpairwise
      card_le := hcard
      mass_le := hmass }⟩

/-- A completely unconditional but generally non-useful degree bound.  It
records that the remaining mathematical task is to replace
`activeCoarse.card` by a scale-uniform geometric constant (or another
acceptable paper loss), not to manufacture retention from a partition. -/
theorem closedDoubledParentConflictDegreeBound_activeCard
    (S : StickyScaleCover fine rho) :
    ClosedDoubledParentConflictDegreeBound S
      (S.activeCoarse.card : ENNReal) := by
  intro k hk neighbours hneighbours
  have hsubset : neighbours ⊆ S.activeCoarse := by
    intro l hl
    exact (hneighbours l).mp hl |>.1
  exact_mod_cast Finset.card_le_card hsubset

#print axioms exists_doubledParentConflictWeightedSelection
#print axioms closedDoubledParentConflictDegreeBound_activeCard

end ScaleCover
end
end Family8DoubledParentConflictWeightedRetentionV3
