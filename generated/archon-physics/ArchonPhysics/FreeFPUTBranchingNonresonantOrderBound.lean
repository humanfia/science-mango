import ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle

/-!
# Order-only bounds for fully nonresonant branching FPUT histories

The exact branching estimate retains the number of linear extensions of the
chosen binary interaction tree.  This module proves that this multiplicity is
bounded by the factorial of the interaction order.  Consequently the
fully-nonresonant Duhamel coefficient has a bound depending only on the order,
not on the tree shape, phase assignment, or time.

The factorial loss is intentionally explicit.  It is a deterministic
combinatorial estimate and does not assert the probabilistic gap estimates
needed to prove RPA from the Hamiltonian dynamics.
-/

namespace ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.FreeFPUTBranchingOscillatoryShuffle

noncomputable section

/-! ## Exact shuffle cardinalities -/

/-- The recursive list of order-preserving shuffles has the binomial
cardinality.  List multiplicity is essential when phase values coincide. -/
theorem length_orderedPhaseShuffles (left right : List Real) :
    (orderedPhaseShuffles left right).length =
      Nat.choose (left.length + right.length) left.length := by
  cases left with
  | nil =>
      simp
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simp
      | cons rightHead rightTail =>
          simp only [orderedPhaseShuffles, List.length_append,
            List.length_map, List.length_cons]
          rw [length_orderedPhaseShuffles leftTail (rightHead :: rightTail),
            length_orderedPhaseShuffles (leftHead :: leftTail) rightTail]
          simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            (Nat.choose_succ_succ'
              (leftTail.length + rightTail.length + 1)
              leftTail.length).symm
termination_by left.length + right.length
decreasing_by all_goals simp_all

/-- Shuffling one fixed-length history through a constant-length family has
the expected product cardinality. -/
private theorem length_flatMap_orderedPhaseShuffles_of_constant_length
    (leftHistory : List Real) (rightFamily : List (List Real))
    (leftOrder rightOrder : Nat)
    (hleft : leftHistory.length = leftOrder)
    (hright : forall history,
      history ∈ rightFamily -> history.length = rightOrder) :
    (rightFamily.flatMap fun rightHistory =>
        orderedPhaseShuffles leftHistory rightHistory).length =
      rightFamily.length * Nat.choose (leftOrder + rightOrder) leftOrder := by
  induction rightFamily with
  | nil => simp
  | cons rightHistory rightFamily ih =>
      have hrightHead : rightHistory.length = rightOrder :=
        hright rightHistory (by simp)
      have hrightTail : forall history,
          history ∈ rightFamily -> history.length = rightOrder := by
        intro history hhistory
        exact hright history (by simp [hhistory])
      simp only [List.flatMap_cons, List.length_append]
      rw [length_orderedPhaseShuffles, ih hrightTail,
        hleft, hrightHead]
      simp only [List.length_cons, Nat.succ_mul]
      ac_rfl

/-- Pairwise shuffling two constant-order families multiplies both family
cardinalities and the binomial shuffle cardinality. -/
theorem length_shufflePhaseFamilies_of_constant_length
    (leftFamily rightFamily : List (List Real))
    (leftOrder rightOrder : Nat)
    (hleft : forall history,
      history ∈ leftFamily -> history.length = leftOrder)
    (hright : forall history,
      history ∈ rightFamily -> history.length = rightOrder) :
    (shufflePhaseFamilies leftFamily rightFamily).length =
      leftFamily.length * rightFamily.length *
        Nat.choose (leftOrder + rightOrder) leftOrder := by
  induction leftFamily with
  | nil => simp [shufflePhaseFamilies]
  | cons leftHistory leftFamily ih =>
      have hleftHead : leftHistory.length = leftOrder :=
        hleft leftHistory (by simp)
      have hleftTail : forall history,
          history ∈ leftFamily -> history.length = leftOrder := by
        intro history hhistory
        exact hleft history (by simp [hhistory])
      unfold shufflePhaseFamilies
      simp only [List.flatMap_cons, List.length_append]
      rw [length_flatMap_orderedPhaseShuffles_of_constant_length
          leftHistory rightFamily leftOrder rightOrder hleftHead hright,
        ← shufflePhaseFamilies, ih hleftTail]
      simp only [List.length_cons, Nat.succ_mul]
      ring

/-- Exact recursive cardinality of the internal-node linear extensions of a
binary interaction tree. -/
theorem length_branchingPhaseLinearExtensions_node
    (left right : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment (.node left right)) :
    (branchingPhaseLinearExtensions (.node left right) assignment).length =
      (branchingPhaseLinearExtensions left assignment.2.1).length *
        (branchingPhaseLinearExtensions right assignment.2.2).length *
          Nat.choose (left.order + right.order) left.order := by
  rw [branchingPhaseLinearExtensions, List.length_map]
  apply length_shufflePhaseFamilies_of_constant_length
  · intro history hhistory
    exact length_eq_order_of_mem_branchingPhaseLinearExtensions
      left assignment.2.1 hhistory
  · intro history hhistory
    exact length_eq_order_of_mem_branchingPhaseLinearExtensions
      right assignment.2.2 hhistory

/-! ## Shape-uniform factorial bound -/

/-- The number of tree-order linear extensions is at most `order!`. -/
theorem length_branchingPhaseLinearExtensions_le_factorial
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree) :
    (branchingPhaseLinearExtensions tree assignment).length <=
      tree.order.factorial := by
  induction tree with
  | leaf => simp [branchingPhaseLinearExtensions,
      BinaryInteractionTree.order]
  | node left right hleft hright =>
      rw [length_branchingPhaseLinearExtensions_node]
      have hproduct :
          (branchingPhaseLinearExtensions left assignment.2.1).length *
              (branchingPhaseLinearExtensions right assignment.2.2).length <=
            left.order.factorial * right.order.factorial :=
        Nat.mul_le_mul (hleft assignment.2.1) (hright assignment.2.2)
      have hpreRoot :
          (branchingPhaseLinearExtensions left assignment.2.1).length *
                (branchingPhaseLinearExtensions right assignment.2.2).length *
              Nat.choose (left.order + right.order) left.order <=
            (left.order + right.order).factorial := by
        calc
          (branchingPhaseLinearExtensions left assignment.2.1).length *
                  (branchingPhaseLinearExtensions right assignment.2.2).length *
                Nat.choose (left.order + right.order) left.order <=
              (left.order.factorial * right.order.factorial) *
                Nat.choose (left.order + right.order) left.order :=
            Nat.mul_le_mul_right _ hproduct
          _ = Nat.choose (left.order + right.order) left.order *
                right.order.factorial * left.order.factorial := by
            ac_rfl
          _ = (left.order + right.order).factorial := by
            simpa [Nat.add_comm] using
              Nat.add_choose_mul_factorial_mul_factorial
                right.order left.order
      calc
        (branchingPhaseLinearExtensions left assignment.2.1).length *
              (branchingPhaseLinearExtensions right assignment.2.2).length *
            Nat.choose (left.order + right.order) left.order <=
          (left.order + right.order).factorial := hpreRoot
        _ <= (left.order + right.order + 1).factorial := by
          rw [Nat.factorial_succ]
          exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- Fully nonresonant branching histories obey a time- and shape-uniform
bound depending only on the interaction order. -/
theorem norm_branchingOscillatoryDuhamelIntegral_le_factorial_order
    {gamma : Real} (hgamma : 0 < gamma)
    (tree : BinaryInteractionTree)
    (assignment : BinaryInteractionTreePhaseAssignment tree)
    (hregular : FullyNonresonantBranchingHistory gamma tree assignment)
    (time : Real) :
    ‖branchingOscillatoryDuhamelIntegral tree assignment time‖ <=
      (tree.order.factorial : Real) * (2 / gamma) ^ tree.order := by
  calc
    ‖branchingOscillatoryDuhamelIntegral tree assignment time‖ <=
        ((branchingPhaseLinearExtensions tree assignment).length : Real) *
          (2 / gamma) ^ tree.order :=
      norm_branchingOscillatoryDuhamelIntegral_le_linearExtensionCard
        hgamma tree assignment hregular time
    _ <= (tree.order.factorial : Real) * (2 / gamma) ^ tree.order := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast
          length_branchingPhaseLinearExtensions_le_factorial tree assignment)
        (pow_nonneg (by positivity) tree.order)

end

end ArchonPhysics.FreeFPUTBranchingNonresonantOrderBound
