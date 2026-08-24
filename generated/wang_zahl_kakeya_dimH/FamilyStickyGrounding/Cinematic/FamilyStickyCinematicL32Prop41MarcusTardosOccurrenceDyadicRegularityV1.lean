import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderPathV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosAmbientFilterIRV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceDyadicRegularityV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderPathV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicLemmaTwoCertificateV1
open FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceCommonPairCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosAmbientFilterIRV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearSublistReverseV1
open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1

/-! # The occurrence-path regularity is the actual dyadic pair regularity -/

theorem mem_support_of_mem_occurrenceBlock
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol)
    (x a : symbol) (hx : x ∈ A.support)
    (ha : a ∈ occurrenceBlock depth A.order A.nodup_order x
      ((A.mem_support_iff x).mp hx)) :
    a ∈ A.support := by
  apply (A.mem_support_iff a).mpr
  have haFlat : a ∈ (dyadicBlocks depth A.order).flatten := by
    apply List.mem_flatten.mpr
    exact ⟨occurrenceBlock depth A.order A.nodup_order x
      ((A.mem_support_iff x).mp hx), blockAt_mem _ _ _, ha⟩
  simpa using haFlat

theorem occurrenceFilteredPair_regular_iff
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hx : x ∈ A.support ∩ B.support) :
    (linearOfList
        (partitionBlock (commonBlocks depth A B)
          (occurrenceCommonPairIndex depth A B x hx).1)
        ((flatten_commonBlocks_nodup depth A B).sublist
          (partitionBlock_sublist_flatten _ _))).IntersectionReverse
      (linearOfList
        (partitionBlock (commonBlocks depth B A)
          (occurrenceCommonPairIndex depth A B x hx).2)
        ((flatten_commonBlocks_nodup depth B A).sublist
          (partitionBlock_sublist_flatten _ _))) ↔
      occurrenceRegular A.order B.order A.nodup_order B.nodup_order x
        ((A.mem_support_iff x).mp (Finset.mem_inter.mp hx).1)
        ((B.mem_support_iff x).mp (Finset.mem_inter.mp hx).2) depth := by
  let hxA := (Finset.mem_inter.mp hx).1
  let hxB := (Finset.mem_inter.mp hx).2
  let hxAo := (A.mem_support_iff x).mp hxA
  let hxBo := (B.mem_support_iff x).mp hxB
  let C := occurrenceBlock depth A.order A.nodup_order x hxAo
  let D := occurrenceBlock depth B.order B.nodup_order x hxBo
  let hCn := occurrenceBlock_nodup depth A.order A.nodup_order x hxAo
  let hDn := occurrenceBlock_nodup depth B.order B.nodup_order x hxBo
  have hC : ∀ a ∈ C, a ∈ A.support := by
    intro a ha
    exact mem_support_of_mem_occurrenceBlock depth A x a hxA ha
  have hD : ∀ a ∈ D, a ∈ B.support := by
    intro a ha
    exact mem_support_of_mem_occurrenceBlock depth B x a hxB ha
  have hir := intersectionReverse_ambientFilters_iff
    C D hCn hDn A.support B.support hC hD
  have hLA : linearOfList C hCn =
      occurrenceLinearBlock depth A.order A.nodup_order x hxAo := by
    apply distinctLinearSequence_ext_order
    rfl
  have hLB : linearOfList D hDn =
      occurrenceLinearBlock depth B.order B.nodup_order x hxBo := by
    apply distinctLinearSequence_ext_order
    rfl
  rw [hLA, hLB] at hir
  simpa [hxA, hxB, hxAo, hxBo, C, D, hCn, hDn, occurrenceRegular,
    occurrenceCommonPairIndex] using hir

theorem not_dyadicPairSingular_occurrence_iff
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol)
    (x : symbol) (hx : x ∈ A.support ∩ B.support) :
    ¬dyadicPairSingular depth A B
        (occurrenceCommonPairIndex depth A B x hx) ↔
      occurrenceRegular A.order B.order A.nodup_order B.nodup_order x
        ((A.mem_support_iff x).mp (Finset.mem_inter.mp hx).1)
        ((B.mem_support_iff x).mp (Finset.mem_inter.mp hx).2) depth := by
  classical
  unfold dyadicPairSingular SingularPair
  rw [not_not]
  exact occurrenceFilteredPair_regular_iff depth A B x hx

#print axioms mem_support_of_mem_occurrenceBlock
#print axioms occurrenceFilteredPair_regular_iff
#print axioms not_dyadicPairSingular_occurrence_iff

end FamilyStickyCinematicL32Prop41MarcusTardosOccurrenceDyadicRegularityV1
