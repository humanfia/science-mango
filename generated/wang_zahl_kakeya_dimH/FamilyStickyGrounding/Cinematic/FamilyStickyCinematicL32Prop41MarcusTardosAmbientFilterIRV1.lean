import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosAmbientFilterIRV1

open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1

/-!
# Ambient support filters do not change the common induced orders

If `C` already lies in `s` and `D` already lies in `t`, filtering `C` by
`t` and `D` by `s` deletes only symbols that were not common to the pair.
-/

theorem filter_ambient_filter_common
    {α : Type*} [DecidableEq α]
    (C D : List α) (s t : Finset α)
    (hC : ∀ a ∈ C, a ∈ s) (hD : ∀ a ∈ D, a ∈ t) :
    (C.filter fun a => a ∈ t).filter
        (fun a => a ∈ (D.filter fun b => b ∈ s).toFinset) =
      C.filter fun a => a ∈ D.toFinset := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro a haC
  by_cases haD : a ∈ D
  · simp [haD, hC a haC, hD a haD]
  · simp [haD]

theorem commonOrder_ambientFilters
    {α : Type*} [DecidableEq α]
    (C D : List α) (hCnodup : C.Nodup) (hDnodup : D.Nodup)
    (s t : Finset α)
    (hC : ∀ a ∈ C, a ∈ s) (hD : ∀ a ∈ D, a ∈ t) :
    (linearOfList (C.filter fun a => a ∈ t) (hCnodup.filter _)).commonOrder
        (linearOfList (D.filter fun a => a ∈ s) (hDnodup.filter _)) =
      (linearOfList C hCnodup).commonOrder
        (linearOfList D hDnodup) := by
  exact filter_ambient_filter_common C D s t hC hD

theorem intersectionReverse_ambientFilters_iff
    {α : Type*} [DecidableEq α]
    (C D : List α) (hCnodup : C.Nodup) (hDnodup : D.Nodup)
    (s t : Finset α)
    (hC : ∀ a ∈ C, a ∈ s) (hD : ∀ a ∈ D, a ∈ t) :
    (linearOfList (C.filter fun a => a ∈ t) (hCnodup.filter _)).IntersectionReverse
        (linearOfList (D.filter fun a => a ∈ s) (hDnodup.filter _)) ↔
      (linearOfList C hCnodup).IntersectionReverse
        (linearOfList D hDnodup) := by
  unfold IntersectionReverse
  rw [commonOrder_ambientFilters C D hCnodup hDnodup s t hC hD,
    commonOrder_ambientFilters D C hDnodup hCnodup t s hD hC]

#print axioms filter_ambient_filter_common
#print axioms commonOrder_ambientFilters
#print axioms intersectionReverse_ambientFilters_iff

end FamilyStickyCinematicL32Prop41MarcusTardosAmbientFilterIRV1
