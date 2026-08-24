import Mathlib.Data.List.Cycle

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1

open List

/-!
# Marcus--Tardos cyclic-sequence core

This is the finite sequence language used in Marcus--Tardos, *Intersection
reverse sequences and geometric applications*, Theorem 1 and Corollary 6.
A cyclic sequence is represented by a chosen linear listing with no repeated
symbol.  Statements are invariant under changing that listing by rotation.

The hard Marcus--Tardos length estimate is deliberately absent.  In
particular, this module does not expose an `O(n^(3/2) log n)` hypothesis.
-/

/-- A cyclically ordered sequence of distinct symbols, represented by one
linear cut of the cyclic order. -/
structure DistinctCyclicSequence (symbol : Type*) where
  order : List symbol
  nodup_order : order.Nodup

namespace DistinctCyclicSequence

variable {symbol : Type*} [DecidableEq symbol]

/-- The finite set of symbols occurring in a cyclic sequence. -/
def support (A : DistinctCyclicSequence symbol) : Finset symbol :=
  A.order.toFinset

@[simp]
theorem mem_support_iff (A : DistinctCyclicSequence symbol) (a : symbol) :
    a ∈ A.support ↔ a ∈ A.order := by
  simp [support]

@[simp]
theorem card_support (A : DistinctCyclicSequence symbol) :
    A.support.card = A.order.length := by
  simpa [support] using List.toFinset_card_of_nodup A.nodup_order

/-- The order induced by `A` on the symbols also occurring in `B`. -/
def commonOrder (A B : DistinctCyclicSequence symbol) : List symbol :=
  A.order.filter fun a => a ∈ B.support

theorem commonOrder_nodup (A B : DistinctCyclicSequence symbol) :
    (A.commonOrder B).Nodup :=
  A.nodup_order.filter _

@[simp]
theorem mem_commonOrder_iff (A B : DistinctCyclicSequence symbol)
    (a : symbol) :
    a ∈ A.commonOrder B ↔ a ∈ A.support ∧ a ∈ B.support := by
  simp [commonOrder]

theorem commonOrder_toFinset (A B : DistinctCyclicSequence symbol) :
    (A.commonOrder B).toFinset = A.support ∩ B.support := by
  ext a
  simp

theorem commonOrder_length (A B : DistinctCyclicSequence symbol) :
    (A.commonOrder B).length = (A.support ∩ B.support).card := by
  rw [← commonOrder_toFinset A B]
  exact (List.toFinset_card_of_nodup (commonOrder_nodup A B)).symm

/-- Exact Marcus--Tardos definition: the common symbols occur in opposite
cyclic orders.  Reversal is taken before comparison modulo rotation. -/
def IntersectionReverse (A B : DistinctCyclicSequence symbol) : Prop :=
  (A.commonOrder B).reverse ~r B.commonOrder A

theorem intersectionReverse_comm (A B : DistinctCyclicSequence symbol) :
    IntersectionReverse A B ↔ IntersectionReverse B A := by
  constructor
  · intro h
    have hr := h.symm.reverse
    simpa [IntersectionReverse] using hr
  · intro h
    have hr := h.symm.reverse
    simpa [IntersectionReverse] using hr

theorem IntersectionReverse.symm {A B : DistinctCyclicSequence symbol}
    (h : IntersectionReverse A B) : IntersectionReverse B A :=
  (intersectionReverse_comm A B).mp h

/-- A finite indexed family is pairwise intersection reverse. -/
def PairwiseIntersectionReverse {index : Type*}
    (family : index → DistinctCyclicSequence symbol) : Prop :=
  Pairwise fun i j => IntersectionReverse (family i) (family j)

theorem PairwiseIntersectionReverse.comp_injective
    {index index' : Type*}
    {family : index → DistinctCyclicSequence symbol}
    (h : PairwiseIntersectionReverse family)
    (f : index' → index) (hf : Function.Injective f) :
    PairwiseIntersectionReverse (family ∘ f) := by
  intro i j hij
  exact h (hf.ne hij)

/-- Filtering respects cyclic rotation.  This is the elementary invariance
needed to show that `IntersectionReverse` does not depend on the chosen cut
of either cyclic list. -/
theorem IsRotated.filterByFinset {l l' : List symbol} (s : Finset symbol)
    (h : l ~r l') :
    (l.filter fun a => a ∈ s) ~r (l'.filter fun a => a ∈ s) := by
  rcases h with ⟨n, rfl⟩
  let k := n % l.length
  have hrot : l.rotate n = l.drop k ++ l.take k := by
    simpa [k] using (rotate_eq_drop_append_take_mod (l := l) (n := n))
  rw [hrot, filter_append]
  have hsplit : l.filter (fun a => a ∈ s) =
      (l.take k).filter (fun a => a ∈ s) ++
        (l.drop k).filter (fun a => a ∈ s) := by
    rw [← filter_append, take_append_drop]
  rw [hsplit]
  exact isRotated_append

/-- Rotation of the representative of the left cyclic sequence preserves
the intersection-reverse relation. -/
theorem intersectionReverse_of_left_rotated
    {A A' B : DistinctCyclicSequence symbol}
    (hrot : A.order ~r A'.order)
    (h : IntersectionReverse A B) :
    IntersectionReverse A' B := by
  have hsupport : A.support = A'.support := by
    ext a
    simpa [mem_support_iff] using hrot.mem_iff (a := a)
  have hcommon : A.commonOrder B ~r A'.commonOrder B := by
    exact IsRotated.filterByFinset B.support hrot
  have hrev : (A'.commonOrder B).reverse ~r
      (A.commonOrder B).reverse := hcommon.symm.reverse
  exact hrev.trans
    (by simpa [IntersectionReverse, commonOrder, hsupport] using h)

/-- Rotation of the representative of the right cyclic sequence preserves
the intersection-reverse relation. -/
theorem intersectionReverse_of_right_rotated
    {A B B' : DistinctCyclicSequence symbol}
    (hrot : B.order ~r B'.order)
    (h : IntersectionReverse A B) :
    IntersectionReverse A B' := by
  apply IntersectionReverse.symm
  exact intersectionReverse_of_left_rotated hrot h.symm

#print axioms mem_support_iff
#print axioms card_support
#print axioms commonOrder_toFinset
#print axioms commonOrder_length
#print axioms intersectionReverse_comm
#print axioms PairwiseIntersectionReverse.comp_injective
#print axioms IsRotated.filterByFinset
#print axioms intersectionReverse_of_left_rotated
#print axioms intersectionReverse_of_right_rotated

end DistinctCyclicSequence

end FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
