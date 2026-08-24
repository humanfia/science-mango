import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosBlockPairSplitCoreV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1

/-! # Literal left/right common-symbol split for a block pair -/

def leftCommon
    {α : Type*} [DecidableEq α]
    (u C D : List α) : List α :=
  u.filter fun a => a ∈ C.toFinset ∩ D.toFinset

def rightCommon
    {α : Type*} [DecidableEq α]
    (v C D : List α) : List α :=
  v.filter fun a => a ∈ C.toFinset ∩ D.toFinset

theorem first_commonOrder_eq_split
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup) (hC : C <+ u ++ v)
    (hCnodup : C.Nodup) (hDnodup : D.Nodup) :
    (linearOfList C hCnodup).commonOrder (linearOfList D hDnodup) =
      leftCommon u C D ++ rightCommon v C D := by
  have hrecover :
      (u ++ v).filter (fun a => a ∈ C.toFinset) = C :=
    filter_toFinset_eq_of_sublist_of_nodup hC huv
  change C.filter (fun a => a ∈ D.toFinset) =
    leftCommon u C D ++ rightCommon v C D
  calc
    _ = ((u ++ v).filter (fun a => a ∈ C.toFinset)).filter
        (fun a => a ∈ D.toFinset) := by rw [hrecover]
    _ = leftCommon u C D ++ rightCommon v C D := by
      rw [List.filter_filter, List.filter_append]
      simp [leftCommon, rightCommon, Bool.and_comm]

theorem second_commonOrder_eq_split_reverse
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup) (hD : D <+ u.reverse ++ v.reverse)
    (hCnodup : C.Nodup) (hDnodup : D.Nodup) :
    (linearOfList D hDnodup).commonOrder (linearOfList C hCnodup) =
      (leftCommon u C D).reverse ++ (rightCommon v C D).reverse := by
  have hvurev : (v.reverse ++ u.reverse).Nodup := by
    simpa using (List.nodup_reverse.mpr huv)
  have hreverseNodup : (u.reverse ++ v.reverse).Nodup :=
    List.nodup_append_comm.mpr hvurev
  have hrecover :
      (u.reverse ++ v.reverse).filter (fun a => a ∈ D.toFinset) = D :=
    filter_toFinset_eq_of_sublist_of_nodup hD hreverseNodup
  change D.filter (fun a => a ∈ C.toFinset) =
    (leftCommon u C D).reverse ++ (rightCommon v C D).reverse
  calc
    _ = ((u.reverse ++ v.reverse).filter
          (fun a => a ∈ D.toFinset)).filter
        (fun a => a ∈ C.toFinset) := by rw [hrecover]
    _ = (leftCommon u C D).reverse ++
        (rightCommon v C D).reverse := by
      rw [List.filter_filter, List.filter_append,
        List.filter_reverse, List.filter_reverse]
      simp [leftCommon, rightCommon]

theorem blockPair_commonOrder_split
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup)
    (hC : C <+ u ++ v) (hD : D <+ u.reverse ++ v.reverse)
    (hCnodup : C.Nodup) (hDnodup : D.Nodup) :
    (linearOfList C hCnodup).commonOrder (linearOfList D hDnodup) =
        leftCommon u C D ++ rightCommon v C D ∧
      (linearOfList D hDnodup).commonOrder (linearOfList C hCnodup) =
        (leftCommon u C D).reverse ++ (rightCommon v C D).reverse :=
  ⟨first_commonOrder_eq_split huv hC hCnodup hDnodup,
    second_commonOrder_eq_split_reverse huv hD hCnodup hDnodup⟩

#print axioms leftCommon
#print axioms rightCommon
#print axioms first_commonOrder_eq_split
#print axioms second_commonOrder_eq_split_reverse
#print axioms blockPair_commonOrder_split

end FamilyStickyCinematicL32Prop41MarcusTardosBlockPairSplitCoreV1
