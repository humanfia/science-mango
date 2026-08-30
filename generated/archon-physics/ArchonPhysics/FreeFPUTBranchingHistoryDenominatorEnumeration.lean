import ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
import ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle

/-!
# Exact small-denominator enumeration for complete branching FPUT histories

Every branching Duhamel tree is a finite sum over its linear extensions.
This module concatenates the exact ordered integration-by-parts denominator
list over those extensions.  It proves both the exact nonresonance
characterization and the occurrence budget

`linearExtensionCount * (2 ^ order - 1)`.

Thus a later one-denominator small-ball bound has a completely explicit
finite-union budget.  No positive-time RPA, probabilistic independence,
diagram cancellation, or kinetic-time summability is asserted here.
-/

namespace ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration

open ArchonPhysics
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

noncomputable section

/-- Concatenate the complete ordered-IBP denominator lists over every linear
extension of a branching interaction tree. -/
def branchingHistoryDenominators
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) : List Real :=
  (branchingPhaseLinearExtensions tree assignment).flatMap
    orderedHistoryDenominators

/-- Full branching nonresonance is exactly pointwise separation of every
denominator occurrence in every linear extension. -/
theorem fullyNonresonantBranchingHistory_iff_forall_mem_denominators
    (gamma : Real) (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    FullyNonresonantBranchingHistory gamma tree assignment ↔
      ∀ delta ∈ branchingHistoryDenominators tree assignment,
        gamma ≤ |delta| := by
  constructor
  · intro hregular delta hdelta
    simp only [branchingHistoryDenominators, List.mem_flatMap] at hdelta
    rcases hdelta with ⟨phases, hphases, hdelta⟩
    exact
      (fullyNonresonantOrderedHistory_iff_forall_mem_denominators
        gamma phases).mp (hregular phases hphases) delta hdelta
  · intro hall phases hphases
    apply
      (fullyNonresonantOrderedHistory_iff_forall_mem_denominators
        gamma phases).mpr
    intro delta hdelta
    exact hall delta (by
      simp only [branchingHistoryDenominators, List.mem_flatMap]
      exact ⟨phases, hphases, hdelta⟩)

/-- An irregular branching history exposes a concrete small cumulative phase
gap in one of its linear extensions. -/
theorem not_fullyNonresonantBranchingHistory_iff_exists_small_denominator
    (gamma : Real) (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    ¬ FullyNonresonantBranchingHistory gamma tree assignment ↔
      ∃ delta ∈ branchingHistoryDenominators tree assignment,
        |delta| < gamma := by
  rw [fullyNonresonantBranchingHistory_iff_forall_mem_denominators]
  push Not
  rfl

/-- A finite family of order-`r` phase histories contributes exactly
`2 ^ r - 1` denominator occurrences per history. -/
theorem length_flatMap_orderedHistoryDenominators_of_fixed_length
    (histories : List (List Real)) (order : Nat)
    (hlength : ∀ phases ∈ histories, phases.length = order) :
    (histories.flatMap orderedHistoryDenominators).length =
      histories.length * (2 ^ order - 1) := by
  induction histories with
  | nil => simp
  | cons phases histories ih =>
      have hhead : phases.length = order := hlength phases (by simp)
      have htail : ∀ candidate ∈ histories, candidate.length = order := by
        intro candidate hcandidate
        exact hlength candidate (by simp [hcandidate])
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [length_orderedHistoryDenominators, hhead, ih htail]
      simp [Nat.add_mul, Nat.add_comm]

/-- Exact high-order occurrence budget for one branching tree.  The
linear-extension multiplicity remains visible. -/
theorem length_branchingHistoryDenominators
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    (branchingHistoryDenominators tree assignment).length =
      (branchingPhaseLinearExtensions tree assignment).length *
        (2 ^ tree.order - 1) := by
  apply length_flatMap_orderedHistoryDenominators_of_fixed_length
  intro phases hphases
  exact length_eq_order_of_mem_branchingPhaseLinearExtensions
    tree assignment hphases

end

end ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
