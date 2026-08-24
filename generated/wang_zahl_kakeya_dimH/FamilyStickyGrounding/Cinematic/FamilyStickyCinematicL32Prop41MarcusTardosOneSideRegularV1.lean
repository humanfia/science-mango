import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosOneSideRegularV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1

/-!
# A block confined to one cut side is regular

Even if the other block crosses the cyclic cut, its common symbols with a
block contained in `u` form a sublist of `u.reverse`.  Hence the block pair
is linearly intersection reverse.  This is the key contrapositive used to
show that every singular pair crosses the cut on both sides.
-/

theorem filter_sublist_filter
    {α : Type*} {C D : List α} (p : α → Bool)
    (hsub : C <+ D) : C.filter p <+ D.filter p := by
  induction hsub with
  | slnil => simp
  | cons a hsub ih =>
      by_cases ha : p a = true <;> simp [ha, ih]
  | cons_cons a hsub ih =>
      by_cases ha : p a = true <;> simp [ha, ih]

theorem reverse_eq_of_sublist_reverse_toFinset_eq
    {α : Type*} [DecidableEq α] {u F E : List α}
    (hu : u.Nodup) (hF : F <+ u) (hE : E <+ u.reverse)
    (hsupport : F.toFinset = E.toFinset) :
    F.reverse = E := by
  have hir := intersectionReverse_of_sublist_reverse hu hF hE
  rw [IntersectionReverse] at hir
  have hleft :
      (linearOfList F (hu.sublist hF)).commonOrder
        (linearOfList E ((List.nodup_reverse.mpr hu).sublist hE)) = F := by
    apply List.filter_eq_self.mpr
    intro a ha
    rw [decide_eq_true_eq]
    change a ∈ E.toFinset
    change a ∈ F at ha
    have haf : a ∈ F.toFinset := by simpa using ha
    rwa [hsupport] at haf
  have hright :
      (linearOfList E ((List.nodup_reverse.mpr hu).sublist hE)).commonOrder
        (linearOfList F (hu.sublist hF)) = E := by
    apply List.filter_eq_self.mpr
    intro a ha
    rw [decide_eq_true_eq]
    change a ∈ F.toFinset
    change a ∈ E at ha
    have hae : a ∈ E.toFinset := by simpa using ha
    rwa [hsupport]
  rw [hleft, hright] at hir
  exact hir

theorem intersectionReverse_of_left_sublist_of_commonRight_sublist_reverse
    {α : Type*} [DecidableEq α] {u C D : List α}
    (hu : u.Nodup) (hCnodup : C.Nodup) (hDnodup : D.Nodup)
    (hC : C <+ u)
    (hcommonRight : D.filter (fun a => a ∈ C.toFinset) <+ u.reverse) :
    (linearOfList C hCnodup).IntersectionReverse
      (linearOfList D hDnodup) := by
  let F := C.filter fun a => a ∈ D.toFinset
  let E := D.filter fun a => a ∈ C.toFinset
  have hF : F <+ u :=
    (List.filter_sublist : C.filter (fun a => a ∈ D.toFinset) <+ C).trans hC
  have hE : E <+ u.reverse := hcommonRight
  have hsupport : F.toFinset = E.toFinset := by
    ext a
    simp [F, E, and_comm]
  have hreverse : F.reverse = E :=
    reverse_eq_of_sublist_reverse_toFinset_eq hu hF hE hsupport
  rw [IntersectionReverse]
  change F.reverse = E
  exact hreverse

theorem intersectionReverse_of_left_sublist_left_split
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup) (hCnodup : C.Nodup) (hDnodup : D.Nodup)
    (hC : C <+ u) (hD : D <+ u.reverse ++ v.reverse) :
    (linearOfList C hCnodup).IntersectionReverse
      (linearOfList D hDnodup) := by
  have hu := huv.of_append_left
  have hdisjoint := huv.disjoint
  have hvfilter : v.reverse.filter (fun a => a ∈ C.toFinset) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hav : a ∈ v := by simpa using ha
    have hau : a ∉ u := fun hau =>
      (List.disjoint_left.mp hdisjoint) hau hav
    have hac : a ∉ C := fun hac => hau (hC.subset hac)
    simp [hac]
  have hfiltered := filter_sublist_filter
    (fun a => a ∈ C.toFinset) hD
  rw [List.filter_append, hvfilter, List.append_nil] at hfiltered
  exact intersectionReverse_of_left_sublist_of_commonRight_sublist_reverse
    hu hCnodup hDnodup hC
      (hfiltered.trans List.filter_sublist)

theorem intersectionReverse_of_left_sublist_right_split
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup) (hCnodup : C.Nodup) (hDnodup : D.Nodup)
    (hC : C <+ v) (hD : D <+ u.reverse ++ v.reverse) :
    (linearOfList C hCnodup).IntersectionReverse
      (linearOfList D hDnodup) := by
  have hv := huv.of_append_right
  have hdisjoint := huv.disjoint
  have hufilter : u.reverse.filter (fun a => a ∈ C.toFinset) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    have hau : a ∈ u := by simpa using ha
    have hav : a ∉ v := fun hav =>
      (List.disjoint_left.mp hdisjoint) hau hav
    have hac : a ∉ C := fun hac => hav (hC.subset hac)
    simp [hac]
  have hfiltered := filter_sublist_filter
    (fun a => a ∈ C.toFinset) hD
  rw [List.filter_append, hufilter, List.nil_append] at hfiltered
  exact intersectionReverse_of_left_sublist_of_commonRight_sublist_reverse
    hv hCnodup hDnodup hC
      (hfiltered.trans List.filter_sublist)

#print axioms filter_sublist_filter
#print axioms reverse_eq_of_sublist_reverse_toFinset_eq
#print axioms intersectionReverse_of_left_sublist_of_commonRight_sublist_reverse
#print axioms intersectionReverse_of_left_sublist_left_split
#print axioms intersectionReverse_of_left_sublist_right_split

end FamilyStickyCinematicL32Prop41MarcusTardosOneSideRegularV1
