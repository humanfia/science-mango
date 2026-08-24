import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCanonicalSplitQSumV1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalSplitQSumV1

/-!
# Actual order-sign product on the canonical split occurrence type

`Sum (Fin u) (Fin v)` labels the symbols in `u ++ v`.  `firstRank` is their
rank in `u ++ v`; `splitReverseRank` is their rank in
`u.reverse ++ v.reverse`.  Thus `taggedSplitQ` is the literal finite sum of
the paper's two order signs, before relabeling the tags by actual symbols.
-/

def rankSign {ι : Type*} [DecidableEq ι]
    (rank : ι → Nat) (a b : ι) : Real :=
  if a = b then 0 else if rank a < rank b then 1 else -1

def firstRank {u v : Nat} : Sum (Fin u) (Fin v) → Nat
  | Sum.inl i => i.1
  | Sum.inr j => u + j.1

def splitReverseRank {u v : Nat} : Sum (Fin u) (Fin v) → Nat
  | Sum.inl i => u - 1 - i.1
  | Sum.inr j => u + (v - 1 - j.1)

def canonicalPairTerm {u v : Nat}
    (a b : Sum (Fin u) (Fin v)) : Real :=
  match a, b with
  | Sum.inl i, Sum.inl j => if i = j then 0 else -1
  | Sum.inr i, Sum.inr j => if i = j then 0 else -1
  | Sum.inl _, Sum.inr _ => 1
  | Sum.inr _, Sum.inl _ => 1

theorem reverseRank_lt_iff {n : Nat} (i j : Fin n) :
    n - 1 - i.1 < n - 1 - j.1 ↔ j.1 < i.1 := by
  omega

theorem rankSign_product_eq_canonicalPairTerm
    {u v : Nat} (a b : Sum (Fin u) (Fin v)) :
    rankSign firstRank a b * rankSign splitReverseRank a b =
      canonicalPairTerm a b := by
  rcases a with i | i <;> rcases b with j | j
  · by_cases hij : i = j
    · subst j
      simp [rankSign, canonicalPairTerm]
    · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      have hrev := reverseRank_lt_iff i j
      rcases lt_or_gt_of_ne hval with hji | hijv
      · simp [rankSign, firstRank, splitReverseRank,
          canonicalPairTerm, hij, hji, hrev]
        omega
      · simp [rankSign, firstRank, splitReverseRank,
          canonicalPairTerm, hij, hijv, hrev]
        omega
  · have hfirst : i.1 < u + j.1 := by omega
    have hsecond : u - 1 - i.1 < u + (v - 1 - j.1) := by omega
    simp [rankSign, firstRank, splitReverseRank, canonicalPairTerm,
      hfirst, hsecond]
  · have hfirst : ¬ u + i.1 < j.1 := by omega
    have hsecond : ¬ u + (v - 1 - i.1) < u - 1 - j.1 := by omega
    simp [rankSign, firstRank, splitReverseRank, canonicalPairTerm,
      hfirst, hsecond]
  · by_cases hij : i = j
    · subst j
      simp [rankSign, canonicalPairTerm]
    · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      have hrev := reverseRank_lt_iff i j
      rcases lt_or_gt_of_ne hval with hji | hijv
      · simp [rankSign, firstRank, splitReverseRank,
          canonicalPairTerm, hij, hji, hrev]
        omega
      · simp [rankSign, firstRank, splitReverseRank,
          canonicalPairTerm, hij, hijv, hrev]
        omega

theorem sum_sum_if_eq_zero_else_neg_one
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (∑ a : ι, ∑ b : ι, if a = b then (0 : Real) else -1) =
      -(((Finset.univ : Finset ι).offDiag.card : Nat) : Real) := by
  classical
  rw [← Finset.sum_product']
  rw [← Finset.diag_union_offDiag]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  have hdiag :
      (∑ x ∈ (Finset.univ : Finset ι).diag,
        if x.1 = x.2 then (0 : Real) else -1) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [(Finset.mem_diag.mp hx).2]
  have hoff :
      (∑ x ∈ (Finset.univ : Finset ι).offDiag,
        if x.1 = x.2 then (0 : Real) else -1) =
        ∑ _x ∈ (Finset.univ : Finset ι).offDiag, (-1 : Real) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [(Finset.mem_offDiag.mp hx).2.2]
  rw [hdiag, zero_add, hoff]
  simp

def taggedSplitQ (u v : Nat) : Real :=
  ∑ a : Sum (Fin u) (Fin v), ∑ b : Sum (Fin u) (Fin v),
    rankSign firstRank a b * rankSign splitReverseRank a b

theorem taggedSplitQ_eq_canonicalSplitQ (u v : Nat) :
    taggedSplitQ u v = canonicalSplitQ u v := by
  simp_rw [taggedSplitQ, rankSign_product_eq_canonicalPairTerm]
  simp only [canonicalPairTerm, Fintype.sum_sum_type]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [sum_sum_if_eq_zero_else_neg_one,
    sum_sum_if_eq_zero_else_neg_one]
  simp [canonicalSplitQ]
  ring

theorem taggedSplitQ_le_length (u v : Nat) :
    taggedSplitQ u v ≤ (u + v : Nat) := by
  rw [taggedSplitQ_eq_canonicalSplitQ]
  exact canonicalSplitQ_le_length u v

theorem taggedReverseQ_eq (r : Nat) :
    taggedSplitQ r 0 = (r : Real) - (r : Real) ^ 2 := by
  rw [taggedSplitQ_eq_canonicalSplitQ, canonicalReverseQ_eq]

#print axioms rankSign
#print axioms firstRank
#print axioms splitReverseRank
#print axioms rankSign_product_eq_canonicalPairTerm
#print axioms taggedSplitQ
#print axioms taggedSplitQ_eq_canonicalSplitQ
#print axioms taggedSplitQ_le_length
#print axioms taggedReverseQ_eq

end FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1
