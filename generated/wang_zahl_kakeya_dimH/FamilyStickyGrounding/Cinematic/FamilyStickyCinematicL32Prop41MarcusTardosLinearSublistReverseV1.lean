import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTerminalRegularV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1

/-! # Subblocks of a list and its reverse are intersection reverse -/

def linearOfList {α : Type*} (l : List α) (hl : l.Nodup) :
    DistinctLinearSequence α where
  order := l
  nodup_order := hl

theorem linearOfList_reverse_intersectionReverse
    {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) :
    (linearOfList l hl).IntersectionReverse
      (linearOfList l.reverse (List.nodup_reverse.mpr hl)) := by
  simp [linearOfList, IntersectionReverse, commonOrder, support]

theorem linearOfList_eq_restrict_of_sublist
    {α : Type*} [DecidableEq α] {child parent : List α}
    (hparent : parent.Nodup) (hsub : child <+ parent) :
    linearOfList child (hparent.sublist hsub) =
      (linearOfList parent hparent).restrict child.toFinset := by
  apply distinctLinearSequence_ext_order
  exact (filter_toFinset_eq_of_sublist_of_nodup hsub hparent).symm

theorem intersectionReverse_of_sublist_reverse
    {α : Type*} [DecidableEq α] {u C D : List α}
    (hu : u.Nodup) (hC : C <+ u) (hD : D <+ u.reverse) :
    (linearOfList C (hu.sublist hC)).IntersectionReverse
      (linearOfList D ((List.nodup_reverse.mpr hu).sublist hD)) := by
  rw [linearOfList_eq_restrict_of_sublist hu hC,
    linearOfList_eq_restrict_of_sublist (List.nodup_reverse.mpr hu) hD]
  exact (linearOfList_reverse_intersectionReverse u hu).restrict _ _

theorem linearOfList_disjoint_intersectionReverse
    {α : Type*} [DecidableEq α] {u v : List α}
    (hu : u.Nodup) (hv : v.Nodup) (hdisjoint : List.Disjoint u v) :
    (linearOfList u hu).IntersectionReverse (linearOfList v hv) := by
  have huv : ∀ a, a ∈ u → a ∉ v := by
    exact fun a ha hv => (List.disjoint_left.mp hdisjoint) ha hv
  have hvu : ∀ a, a ∈ v → a ∉ u := by
    exact fun a ha hu => (List.disjoint_left.mp hdisjoint.symm) ha hu
  have hfilterUV : u.filter (fun a => a ∈ v.toFinset) = [] := by
    exact List.filter_eq_nil_iff.mpr fun a ha => by simp [huv a ha]
  have hfilterVU : v.filter (fun a => a ∈ u.toFinset) = [] := by
    exact List.filter_eq_nil_iff.mpr fun a ha => by simp [hvu a ha]
  simp only [List.mem_toFinset] at hfilterUV hfilterVU
  rw [IntersectionReverse]
  simp only [commonOrder, support, linearOfList, List.mem_toFinset]
  rw [hfilterUV, hfilterVU]
  rfl

theorem intersectionReverse_of_sublist_disjoint
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (hu : u.Nodup) (hv : v.Nodup) (hdisjoint : List.Disjoint u v)
    (hC : C <+ u) (hD : D <+ v) :
    (linearOfList C (hu.sublist hC)).IntersectionReverse
      (linearOfList D (hv.sublist hD)) := by
  rw [linearOfList_eq_restrict_of_sublist hu hC,
    linearOfList_eq_restrict_of_sublist hv hD]
  exact (linearOfList_disjoint_intersectionReverse hu hv hdisjoint).restrict _ _

#print axioms linearOfList
#print axioms linearOfList_reverse_intersectionReverse
#print axioms linearOfList_eq_restrict_of_sublist
#print axioms intersectionReverse_of_sublist_reverse
#print axioms linearOfList_disjoint_intersectionReverse
#print axioms intersectionReverse_of_sublist_disjoint

end FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
