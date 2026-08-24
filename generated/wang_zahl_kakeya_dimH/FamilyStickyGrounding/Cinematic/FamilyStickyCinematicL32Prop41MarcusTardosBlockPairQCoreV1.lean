import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosBlockPairSplitCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
open FamilyStickyCinematicL32Prop41MarcusTardosBlockPairSplitCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalSplitQSumV1

/-! # Actual block-pair `Q_st` and the Lemma 2 pointwise bounds -/

def blockPairQ
    {α : Type*} [DecidableEq α]
    (u v C D : List α) : Real :=
  taggedSplitQ (leftCommon u C D).length (rightCommon v C D).length

theorem taggedSplitQ_zero_left (r : Nat) :
    taggedSplitQ 0 r = (r : Real) - (r : Real) ^ 2 := by
  rw [taggedSplitQ_eq_canonicalSplitQ,
    canonicalSplitQ_eq_length_sub_square]
  norm_num

theorem leftCommon_disjoint_rightCommon
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup) :
    List.Disjoint (leftCommon u C D) (rightCommon v C D) := by
  rw [List.disjoint_left]
  intro a haL haR
  exact (List.disjoint_left.mp huv.disjoint)
    (List.filter_sublist.subset haL)
    (List.filter_sublist.subset haR)

theorem eq_nil_or_eq_nil_of_append_comm_of_disjoint
    {α : Type*} {L R : List α}
    (hdisjoint : List.Disjoint L R)
    (hcomm : L ++ R = R ++ L) :
    L = [] ∨ R = [] := by
  cases L with
  | nil => exact Or.inl rfl
  | cons a L =>
      cases R with
      | nil => exact Or.inr rfl
      | cons b R =>
          have hab : a = b := (List.cons.inj hcomm).1
          exfalso
          have hnot := (List.disjoint_left.mp hdisjoint) (a := a)
          exact hnot (by simp) (by simp [hab])

theorem blockPairQ_le_common_length
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup) (hC : C <+ u ++ v)
    (hCnodup : C.Nodup) (hDnodup : D.Nodup) :
    blockPairQ u v C D ≤
      ((linearOfList C hCnodup).commonOrder
        (linearOfList D hDnodup)).length := by
  rw [blockPairQ,
    first_commonOrder_eq_split huv hC hCnodup hDnodup,
    List.length_append]
  exact taggedSplitQ_le_length _ _

theorem regular_implies_one_split_side_empty
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup)
    (hC : C <+ u ++ v) (hD : D <+ u.reverse ++ v.reverse)
    (hCnodup : C.Nodup) (hDnodup : D.Nodup)
    (hregular : (linearOfList C hCnodup).IntersectionReverse
      (linearOfList D hDnodup)) :
    leftCommon u C D = [] ∨ rightCommon v C D = [] := by
  obtain ⟨hfirst, hsecond⟩ :=
    blockPair_commonOrder_split huv hC hD hCnodup hDnodup
  have hcommReverse :
      (rightCommon v C D).reverse ++ (leftCommon u C D).reverse =
        (leftCommon u C D).reverse ++ (rightCommon v C D).reverse := by
    rw [IntersectionReverse, hfirst, hsecond] at hregular
    simpa using hregular
  have hcomm := congrArg List.reverse hcommReverse
  have hcomm' :
      leftCommon u C D ++ rightCommon v C D =
        rightCommon v C D ++ leftCommon u C D := by
    simpa using hcomm
  exact eq_nil_or_eq_nil_of_append_comm_of_disjoint
    (leftCommon_disjoint_rightCommon huv) hcomm'

theorem blockPairQ_eq_regular_score
    {α : Type*} [DecidableEq α] {u v C D : List α}
    (huv : (u ++ v).Nodup)
    (hC : C <+ u ++ v) (hD : D <+ u.reverse ++ v.reverse)
    (hCnodup : C.Nodup) (hDnodup : D.Nodup)
    (hregular : (linearOfList C hCnodup).IntersectionReverse
      (linearOfList D hDnodup)) :
    blockPairQ u v C D =
      (((linearOfList C hCnodup).commonOrder
        (linearOfList D hDnodup)).length : Real) -
      (((linearOfList C hCnodup).commonOrder
        (linearOfList D hDnodup)).length : Real) ^ 2 := by
  have hfirst := first_commonOrder_eq_split huv hC hCnodup hDnodup
  rcases regular_implies_one_split_side_empty
      huv hC hD hCnodup hDnodup hregular with hleft | hright
  · rw [blockPairQ, hleft, List.length_nil, taggedSplitQ_zero_left]
    rw [hfirst, hleft, List.nil_append]
  · rw [blockPairQ, hright, List.length_nil, taggedReverseQ_eq]
    rw [hfirst, hright, List.append_nil]

#print axioms blockPairQ
#print axioms taggedSplitQ_zero_left
#print axioms leftCommon_disjoint_rightCommon
#print axioms eq_nil_or_eq_nil_of_append_comm_of_disjoint
#print axioms blockPairQ_le_common_length
#print axioms regular_implies_one_split_side_empty
#print axioms blockPairQ_eq_regular_score

end FamilyStickyCinematicL32Prop41MarcusTardosBlockPairQCoreV1
