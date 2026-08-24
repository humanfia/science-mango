import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosCyclicPrefixRestrictionV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence

variable {symbol : Type*} [DecidableEq symbol]

/-! Arbitrary support restriction and prefix truncation preserve IR. -/

def restrictSequence (A : DistinctCyclicSequence symbol) (s : Finset symbol) :
    DistinctCyclicSequence symbol where
  order := A.order.filter fun a ↦ a ∈ s
  nodup_order := A.nodup_order.filter _

@[simp]
theorem support_restrictSequence (A : DistinctCyclicSequence symbol)
    (s : Finset symbol) :
    (restrictSequence A s).support = A.support ∩ s := by
  ext a
  simp [restrictSequence]

theorem commonOrder_restrictSequence
    (A B : DistinctCyclicSequence symbol) (s t : Finset symbol) :
    (restrictSequence A s).commonOrder (restrictSequence B t) =
      (A.commonOrder B).filter fun a ↦ a ∈ s ∩ t := by
  unfold commonOrder
  change
    (A.order.filter (fun a ↦ a ∈ s)).filter
        (fun a ↦ a ∈ (restrictSequence B t).support) =
      (A.order.filter (fun a ↦ a ∈ B.support)).filter
        (fun a ↦ a ∈ s ∩ t)
  rw [support_restrictSequence]
  simp only [List.filter_filter]
  congr 1
  funext a
  by_cases hs : a ∈ s <;>
    by_cases ht : a ∈ t <;>
      by_cases hB : a ∈ B.support <;> simp_all

theorem intersectionReverse_restrictSequence
    {A B : DistinctCyclicSequence symbol} (s t : Finset symbol)
    (h : IntersectionReverse A B) :
    IntersectionReverse (restrictSequence A s) (restrictSequence B t) := by
  unfold IntersectionReverse at h ⊢
  rw [commonOrder_restrictSequence, commonOrder_restrictSequence]
  have hf := IsRotated.filterByFinset (s ∩ t) h
  simpa [List.filter_reverse, Finset.inter_comm] using hf

def prefixRestrict (A : DistinctCyclicSequence symbol) (d : Nat) :
    DistinctCyclicSequence symbol :=
  restrictSequence A (A.order.take d).toFinset

theorem prefixRestrict_length
    (A : DistinctCyclicSequence symbol) {d : Nat}
    (hd : d ≤ A.order.length) :
    (prefixRestrict A d).order.length = d := by
  rw [← card_support]
  simp only [prefixRestrict, support_restrictSequence]
  have hsubset : (A.order.take d).toFinset ⊆ A.support := by
    intro a ha
    simp only [List.mem_toFinset] at ha
    simpa [support] using List.mem_of_mem_take ha
  rw [Finset.inter_eq_right.mpr hsubset]
  rw [List.toFinset_card_of_nodup A.nodup_order.take]
  rw [List.length_take, Nat.min_eq_left hd]

theorem intersectionReverse_prefixRestrict
    {A B : DistinctCyclicSequence symbol} (d e : Nat)
    (h : IntersectionReverse A B) :
    IntersectionReverse (prefixRestrict A d) (prefixRestrict B e) := by
  exact intersectionReverse_restrictSequence _ _ h

theorem pairwiseIntersectionReverse_prefixRestrict
    {index : Type*} {family : index → DistinctCyclicSequence symbol}
    (h : PairwiseIntersectionReverse family) (d : index → Nat) :
    PairwiseIntersectionReverse
      (fun i ↦ prefixRestrict (family i) (d i)) := by
  intro i j hij
  exact intersectionReverse_prefixRestrict _ _ (h hij)

#print axioms support_restrictSequence
#print axioms commonOrder_restrictSequence
#print axioms intersectionReverse_restrictSequence
#print axioms prefixRestrict_length
#print axioms pairwiseIntersectionReverse_prefixRestrict

end FamilyStickyCinematicL32Prop41MarcusTardosCyclicPrefixRestrictionV1
