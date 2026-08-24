import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
import Mathlib.Data.List.Permutation

set_option autoImplicit false

open List

namespace FamilyStickyCinematicL32Prop41MarcusTardosCyclicSmallIntersectionV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence

/-!
# Small common supports are automatically intersection reverse

Marcus--Tardos explicitly observes that two cyclic sequences with at most
two common symbols are trivially intersection reverse.  This module proves
that finite fact from the exact `List.IsRotated` definition.
-/

/-- Two duplicate-free lists with the same at-most-two-element support have
opposite orders modulo cyclic rotation. -/
theorem isRotated_reverse_of_nodup_toFinset_eq_card_le_two
    {symbol : Type*} [DecidableEq symbol]
    {l r : List symbol} (hl : l.Nodup) (hr : r.Nodup)
    (hs : l.toFinset = r.toFinset) (hc : l.toFinset.card ≤ 2) :
    l.reverse ~r r := by
  have hp : l ~ r := (List.perm_ext_iff_of_nodup hl hr).2 (by
    intro a
    simpa only [List.mem_toFinset] using Finset.ext_iff.mp hs a)
  have hlen : l.length ≤ 2 := by
    rw [← List.toFinset_card_of_nodup hl]
    exact hc
  have hlenr : r.length ≤ 2 := hp.length_eq ▸ hlen
  rcases l with _ | ⟨a, l⟩
  · have : r = [] := hp.symm.eq_nil
    simp [this]
  rcases l with _ | ⟨b, l⟩
  · have : r = [a] := by simpa using hp.symm
    simp [this]
  rcases l with _ | ⟨c, l⟩
  · rcases r with _ | ⟨x, r⟩
    · simp at hp
    rcases r with _ | ⟨y, r⟩
    · simp at hp
    rcases r with _ | ⟨z, r⟩
    · rw [List.pair_perm] at hp
      rcases hp with hp | hp
      · exact ⟨1, by simp [hp]⟩
      · exact ⟨0, by simp [hp]⟩
    simp at hlenr
  simp at hlen

/-- Source-level trivial case: common support cardinality at most two
implies the exact Marcus--Tardos intersection-reverse predicate. -/
theorem intersectionReverse_of_common_card_le_two
    {symbol : Type*} [DecidableEq symbol]
    (A B : DistinctCyclicSequence symbol)
    (hcard : (A.support ∩ B.support).card ≤ 2) :
    IntersectionReverse A B := by
  apply isRotated_reverse_of_nodup_toFinset_eq_card_le_two
      (commonOrder_nodup A B) (commonOrder_nodup B A)
  · rw [commonOrder_toFinset A B, commonOrder_toFinset B A,
      Finset.inter_comm]
  · simpa only [commonOrder_toFinset] using hcard

#print axioms isRotated_reverse_of_nodup_toFinset_eq_card_le_two
#print axioms intersectionReverse_of_common_card_le_two

end FamilyStickyCinematicL32Prop41MarcusTardosCyclicSmallIntersectionV1
