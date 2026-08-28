import ArchonPhysics.FreeFPUTBinaryTreeTimeSimplexWeight

/-!
# Summing exact binary-tree time weights

This module proves that the tree-factorial weights remove the Catalan growth
when all ordered quadratic Picard shapes of one order are summed.  It first
constructs the exact root-splitting equivalence

`shape(r + 1) ≃ Σ i ≤ r, shape(i) × shape(r - i)`

and then proves that the sum of `T^r / treeFactorial` over all order-`r`
shapes is exactly `T^r`.

Consequently the raw fixed-root sum over shapes, branch signs, and momenta is
exactly `4^r N^r T^r`, rather than the cruder Catalan multiple.  This remains
an absolute short-time estimate; kinetic-time control still needs oscillatory
diagram cancellation and probabilistic structure.
-/

namespace ArchonPhysics.FreeFPUTBinaryTreeTimeWeightSummation

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTBinaryTreeTimeSimplexWeight

noncomputable section

/-- Choice of the left subtree order and the two exact-order subtrees of a
successor-order binary shape. -/
abbrev BinaryInteractionTreeSuccessorSplit (r : Nat) :=
  Σ leftOrder : Fin (r + 1),
    BinaryInteractionTreeOfOrder leftOrder.1 ×
      BinaryInteractionTreeOfOrder (r - leftOrder.1)

/-- Split a non-leaf tree at its root. -/
def splitBinaryInteractionTreeSuccessor (r : Nat)
    (tree : BinaryInteractionTreeOfOrder (r + 1)) :
    BinaryInteractionTreeSuccessorSplit r := by
  rcases tree with ⟨tree, horder⟩
  cases tree with
  | leaf =>
      simp [BinaryInteractionTree.order] at horder
  | node left right =>
      have hsum : left.order + right.order = r := by
        simp only [BinaryInteractionTree.order] at horder
        omega
      have hleftLe : left.order ≤ r := by omega
      have hrightOrder : right.order = r - left.order := by omega
      exact
        ⟨⟨left.order, by omega⟩,
          ⟨⟨left, rfl⟩, ⟨right, by simpa using hrightOrder⟩⟩⟩

/-- Join a root split into a successor-order binary shape. -/
def joinBinaryInteractionTreeSuccessor (r : Nat)
    (split : BinaryInteractionTreeSuccessorSplit r) :
    BinaryInteractionTreeOfOrder (r + 1) := by
  rcases split with ⟨leftOrder, left, right⟩
  refine ⟨.node left.1 right.1, ?_⟩
  simp only [BinaryInteractionTree.order, left.2, right.2]
  have hleftOrder := leftOrder.2
  omega

theorem join_splitBinaryInteractionTreeSuccessor (r : Nat)
    (tree : BinaryInteractionTreeOfOrder (r + 1)) :
    joinBinaryInteractionTreeSuccessor r
        (splitBinaryInteractionTreeSuccessor r tree) = tree := by
  apply Subtype.ext
  rcases tree with ⟨tree, horder⟩
  cases tree with
  | leaf =>
      simp [BinaryInteractionTree.order] at horder
  | node left right =>
      simp [splitBinaryInteractionTreeSuccessor,
        joinBinaryInteractionTreeSuccessor]

theorem split_joinBinaryInteractionTreeSuccessor (r : Nat)
    (split : BinaryInteractionTreeSuccessorSplit r) :
    splitBinaryInteractionTreeSuccessor r
        (joinBinaryInteractionTreeSuccessor r split) = split := by
  rcases split with ⟨⟨leftOrder, hleftOrder⟩,
    ⟨left, hleft⟩, ⟨right, hright⟩⟩
  change left.order = leftOrder at hleft
  change right.order = r - leftOrder at hright
  change left.order = leftOrder at hleft
  subst leftOrder
  simp [splitBinaryInteractionTreeSuccessor,
    joinBinaryInteractionTreeSuccessor]

/-- Exact root-splitting equivalence for ordered binary interaction shapes. -/
def binaryInteractionTreeSuccessorEquiv (r : Nat) :
    BinaryInteractionTreeOfOrder (r + 1) ≃
      BinaryInteractionTreeSuccessorSplit r where
  toFun := splitBinaryInteractionTreeSuccessor r
  invFun := joinBinaryInteractionTreeSuccessor r
  left_inv := join_splitBinaryInteractionTreeSuccessor r
  right_inv := split_joinBinaryInteractionTreeSuccessor r

/-! ## Exact summation of tree-simplex weights -/

theorem binaryTreeTimeSimplexWeight_node
    (left right : BinaryInteractionTree) (T : Real) :
    binaryTreeTimeSimplexWeight (.node left right) T =
      (T / (left.order + right.order + 1 : Nat)) *
        binaryTreeTimeSimplexWeight left T *
        binaryTreeTimeSimplexWeight right T := by
  have hleft : ((binaryTreeFactorial left : Nat) : Real) ≠ 0 := by
    exact_mod_cast binaryTreeFactorial_ne_zero left
  have hright : ((binaryTreeFactorial right : Nat) : Real) ≠ 0 := by
    exact_mod_cast binaryTreeFactorial_ne_zero right
  have horder : ((left.order + right.order + 1 : Nat) : Real) ≠ 0 := by
    positivity
  unfold binaryTreeTimeSimplexWeight
  simp only [BinaryInteractionTree.order, binaryTreeFactorial_node,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem binaryTreeTimeSimplexWeight_join
    (r : Nat) (split : BinaryInteractionTreeSuccessorSplit r) (T : Real) :
    binaryTreeTimeSimplexWeight
        (joinBinaryInteractionTreeSuccessor r split).1 T =
      (T / (r + 1 : Nat)) *
        binaryTreeTimeSimplexWeight split.2.1.1 T *
        binaryTreeTimeSimplexWeight split.2.2.1 T := by
  rcases split with ⟨⟨leftOrder, hleftOrder⟩,
    ⟨left, hleft⟩, ⟨right, hright⟩⟩
  rw [show (joinBinaryInteractionTreeSuccessor r
      ⟨⟨leftOrder, hleftOrder⟩,
        (⟨left, hleft⟩, ⟨right, hright⟩)⟩).1 =
      .node left right by rfl]
  rw [binaryTreeTimeSimplexWeight_node]
  have hleftLe : leftOrder ≤ r := Nat.le_of_lt_succ hleftOrder
  rw [hleft, hright, Nat.add_sub_of_le hleftLe]

/-- Total exact time-simplex weight over all ordered shapes at order `r`. -/
def totalBinaryInteractionTreeTimeWeight (r : Nat) (T : Real) : Real :=
  ∑ tree : BinaryInteractionTreeOfOrder r,
    binaryTreeTimeSimplexWeight tree.1 T

private theorem totalBinaryInteractionTreeTimeWeight_zero (T : Real) :
    totalBinaryInteractionTreeTimeWeight 0 T = 1 := by
  have hweight : ∀ tree : BinaryInteractionTreeOfOrder 0,
      binaryTreeTimeSimplexWeight tree.1 T = 1 := by
    intro tree
    rcases tree with ⟨tree, horder⟩
    cases tree with
    | leaf => simp
    | node left right =>
        simp [BinaryInteractionTree.order] at horder
  unfold totalBinaryInteractionTreeTimeWeight
  simp_rw [hweight]
  rw [Finset.sum_const, Finset.card_univ,
    card_binaryInteractionTreeOfOrder]
  norm_num

private theorem sum_joinBinaryInteractionTreeSuccessor
    (r : Nat) (T : Real) :
    totalBinaryInteractionTreeTimeWeight (r + 1) T =
      ∑ split : BinaryInteractionTreeSuccessorSplit r,
        binaryTreeTimeSimplexWeight
          (joinBinaryInteractionTreeSuccessor r split).1 T := by
  unfold totalBinaryInteractionTreeTimeWeight
  apply Fintype.sum_equiv (binaryInteractionTreeSuccessorEquiv r)
  intro tree
  change binaryTreeTimeSimplexWeight tree.1 T =
    binaryTreeTimeSimplexWeight
      (joinBinaryInteractionTreeSuccessor r
        (splitBinaryInteractionTreeSuccessor r tree)).1 T
  rw [join_splitBinaryInteractionTreeSuccessor]

/-- The nested time simplices exactly cancel the Catalan shape count:
the sum of all order-`r` tree weights is `T ^ r`. -/
theorem totalBinaryInteractionTreeTimeWeight_eq_pow
    (r : Nat) (T : Real) :
    totalBinaryInteractionTreeTimeWeight r T = T ^ r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          simpa using totalBinaryInteractionTreeTimeWeight_zero T
      | succ n =>
          rw [sum_joinBinaryInteractionTreeSuccessor]
          rw [Fintype.sum_sigma]
          change
            (∑ leftOrder : Fin (n + 1),
              ∑ pair : BinaryInteractionTreeOfOrder leftOrder.1 ×
                  BinaryInteractionTreeOfOrder (n - leftOrder.1),
                binaryTreeTimeSimplexWeight
                  (joinBinaryInteractionTreeSuccessor n
                    ⟨leftOrder, pair⟩).1 T) = T ^ (n + 1)
          calc
            _ = ∑ _leftOrder : Fin (n + 1),
                T ^ (n + 1) / (n + 1 : Nat) := by
              apply Finset.sum_congr rfl
              intro leftOrder _leftOrderMem
              rw [Fintype.sum_prod_type]
              simp_rw [binaryTreeTimeSimplexWeight_join]
              calc
                (∑ left : BinaryInteractionTreeOfOrder leftOrder.1,
                    ∑ right : BinaryInteractionTreeOfOrder
                        (n - leftOrder.1),
                      T / (n + 1 : Nat) *
                          binaryTreeTimeSimplexWeight left.1 T *
                        binaryTreeTimeSimplexWeight right.1 T) =
                    (T / (n + 1 : Nat)) *
                      totalBinaryInteractionTreeTimeWeight leftOrder.1 T *
                      totalBinaryInteractionTreeTimeWeight
                        (n - leftOrder.1) T := by
                  unfold totalBinaryInteractionTreeTimeWeight
                  rw [show
                    (T / (n + 1 : Nat) *
                        ∑ left : BinaryInteractionTreeOfOrder leftOrder.1,
                          binaryTreeTimeSimplexWeight left.1 T) *
                        ∑ right : BinaryInteractionTreeOfOrder
                            (n - leftOrder.1),
                          binaryTreeTimeSimplexWeight right.1 T =
                      T / (n + 1 : Nat) *
                        ((∑ left : BinaryInteractionTreeOfOrder leftOrder.1,
                            binaryTreeTimeSimplexWeight left.1 T) *
                          ∑ right : BinaryInteractionTreeOfOrder
                              (n - leftOrder.1),
                            binaryTreeTimeSimplexWeight right.1 T) by ring]
                  rw [Fintype.sum_mul_sum]
                  simp_rw [Finset.mul_sum]
                  ring_nf
                _ = (T / (n + 1 : Nat)) * T ^ leftOrder.1 *
                      T ^ (n - leftOrder.1) := by
                  rw [ih leftOrder.1 (by omega),
                    ih (n - leftOrder.1) (by omega)]
                _ = T ^ (n + 1) / (n + 1 : Nat) := by
                  have hpow :
                      T ^ leftOrder.1 * T ^ (n - leftOrder.1) =
                        T ^ n := by
                    rw [← pow_add,
                      Nat.add_sub_of_le
                        (Nat.le_of_lt_succ leftOrder.2)]
                  calc
                    T / (n + 1 : Nat) * T ^ leftOrder.1 *
                        T ^ (n - leftOrder.1) =
                        T / (n + 1 : Nat) *
                          (T ^ leftOrder.1 * T ^ (n - leftOrder.1)) := by ring
                    _ = T / (n + 1 : Nat) * T ^ n := by rw [hpow]
                    _ = T ^ (n + 1) / (n + 1 : Nat) := by
                      rw [pow_succ]
                      ring
            _ = T ^ (n + 1) := by
              have hden : ((n + 1 : Nat) : Real) ≠ 0 := by
                positivity
              rw [Finset.sum_const, Finset.card_univ,
                Fintype.card_fin]
              simp only [nsmul_eq_mul]
              field_simp

/-! ## Exact raw fixed-root sum -/

/-- After summing exact tree-simplex weights, the Catalan factor disappears.
Only the `4 ^ r` branch signs and `N ^ r` fixed-root momentum assignments
remain. -/
theorem fixedRootRawHistoryTimeWeight_eq
    {N : Nat} [NeZero N] (r : Nat) (rootMomentum : Site N)
    (T : Real) :
    fixedRootRawHistoryTimeWeight r rootMomentum T =
      (4 ^ r * N ^ r : Nat) * T ^ r := by
  classical
  unfold fixedRootRawHistoryTimeWeight
  simp_rw [Finset.sum_const, Finset.card_univ,
    card_fixedRootLeafMomentumFiber rootMomentum,
    nsmul_eq_mul]
  simp_rw [Finset.sum_const, Finset.card_univ,
    card_binarySignDecoration_of_order, nsmul_eq_mul]
  rw [show
    (∑ tree : BinaryInteractionTreeOfOrder r,
        (4 ^ r : Nat) *
          ((N ^ r : Nat) * binaryTreeTimeSimplexWeight tree.1 T)) =
      ((4 ^ r : Nat) * (N ^ r : Nat)) *
        totalBinaryInteractionTreeTimeWeight r T by
      unfold totalBinaryInteractionTreeTimeWeight
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tree _treeMem
      push_cast
      ring]
  rw [totalBinaryInteractionTreeTimeWeight_eq_pow]
  push_cast
  ring

end

end ArchonPhysics.FreeFPUTBinaryTreeTimeWeightSummation
