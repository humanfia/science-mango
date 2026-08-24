import Mathlib.Data.List.Cycle

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1

/-!
# Linear block order and hereditary intersection reversal

Dyadic blocks in Marcus--Tardos are linearly ordered sublists of the original
cyclic list.  This module records the exact linear intersection-reverse notion
and proves it survives independently restricting both blocks.
-/

structure DistinctLinearSequence (symbol : Type*) where
  order : List symbol
  nodup_order : order.Nodup

namespace DistinctLinearSequence

variable {symbol : Type*} [DecidableEq symbol]

def support (A : DistinctLinearSequence symbol) : Finset symbol :=
  A.order.toFinset

@[simp]
theorem mem_support_iff (A : DistinctLinearSequence symbol) (a : symbol) :
    a ∈ A.support ↔ a ∈ A.order := by
  simp [support]

def commonOrder (A B : DistinctLinearSequence symbol) : List symbol :=
  A.order.filter fun a => a ∈ B.support

/-- Linear, not cyclic, intersection reversal. -/
def IntersectionReverse (A B : DistinctLinearSequence symbol) : Prop :=
  (A.commonOrder B).reverse = B.commonOrder A

def restrict (A : DistinctLinearSequence symbol) (s : Finset symbol) :
    DistinctLinearSequence symbol where
  order := A.order.filter fun a => a ∈ s
  nodup_order := A.nodup_order.filter _

@[simp]
theorem restrict_order (A : DistinctLinearSequence symbol) (s : Finset symbol) :
    (A.restrict s).order = A.order.filter fun a => a ∈ s := rfl

/-- The common order of two independently restricted lists is the old common
order filtered to the intersection of the two restriction sets. -/
theorem commonOrder_restrict
    (A B : DistinctLinearSequence symbol) (s t : Finset symbol) :
    (A.restrict s).commonOrder (B.restrict t) =
      (A.commonOrder B).filter fun a => a ∈ s ∩ t := by
  simp only [commonOrder, restrict, support, List.filter_filter,
    List.mem_toFinset, Finset.mem_inter]
  apply List.filter_congr
  intro a ha
  simp [Bool.and_assoc, Bool.and_comm]

/-- Intersection reversal is hereditary under taking subblocks/restrictions. -/
theorem IntersectionReverse.restrict
    {A B : DistinctLinearSequence symbol}
    (h : IntersectionReverse A B) (s t : Finset symbol) :
    IntersectionReverse (A.restrict s) (B.restrict t) := by
  rw [IntersectionReverse, commonOrder_restrict, commonOrder_restrict]
  rw [← List.filter_reverse, h]
  simp [Finset.inter_comm]

#print axioms commonOrder_restrict
#print axioms IntersectionReverse.restrict

end DistinctLinearSequence

end FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
