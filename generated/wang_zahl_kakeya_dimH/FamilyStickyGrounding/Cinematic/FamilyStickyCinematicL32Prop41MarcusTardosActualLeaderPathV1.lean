import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicTerminalV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTerminalRegularV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosUniqueLeaderV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderPathV1

open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceNestedV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicTerminalV1
open FamilyStickyCinematicL32Prop41MarcusTardosTerminalRegularV1.DistinctLinearSequence
open FamilyStickyCinematicL32Prop41MarcusTardosUniqueLeaderV1

/-!
# The actual unique leader of a common symbol

For a common symbol of two source lists, `occurrenceRegular level` says that
the two literal dyadic blocks containing that symbol are intersection reverse.
Nested-block restriction makes this predicate monotone.  At paper depth the
left terminal block is a singleton, so regularity is automatic and the first
regular level is a unique leader.
-/

noncomputable def occurrenceRegular
    {α : Type*} [DecidableEq α]
    (lA lB : List α) (hA : lA.Nodup) (hB : lB.Nodup)
    (x : α) (hxA : x ∈ lA) (hxB : x ∈ lB)
    (level : Nat) : Prop :=
  (occurrenceLinearBlock level lA hA x hxA).IntersectionReverse
    (occurrenceLinearBlock level lB hB x hxB)

theorem occurrenceRegular_succ
    {α : Type*} [DecidableEq α]
    (lA lB : List α) (hA : lA.Nodup) (hB : lB.Nodup)
    (x : α) (hxA : x ∈ lA) (hxB : x ∈ lB)
    (level : Nat)
    (hregular : occurrenceRegular lA lB hA hB x hxA hxB level) :
    occurrenceRegular lA lB hA hB x hxA hxB (level + 1) := by
  unfold occurrenceRegular at hregular ⊢
  rw [occurrenceLinearBlock_succ_eq_restrict hA x hxA,
    occurrenceLinearBlock_succ_eq_restrict hB x hxB]
  exact hregular.restrict _ _

theorem occurrenceRegular_terminal
    {α : Type*} [DecidableEq α]
    (lA lB : List α) (hA : lA.Nodup) (hB : lB.Nodup)
    (x : α) (hxA : x ∈ lA) (hxB : x ∈ lB)
    (depth : Nat) (hlength : lA.length ≤ 2 ^ depth) :
    occurrenceRegular lA lB hA hB x hxA hxB depth := by
  unfold occurrenceRegular
  apply intersectionReverse_of_left_length_le_one
  change (occurrenceBlock depth lA hA x hxA).length ≤ 1
  apply length_le_one_of_length_le_pow hlength
  exact blockAt_mem _ _ _

theorem exists_unique_occurrenceLeader
    {α : Type*} [DecidableEq α]
    (lA lB : List α) (hA : lA.Nodup) (hB : lB.Nodup)
    (x : α) (hxA : x ∈ lA) (hxB : x ∈ lB)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hlength : lA.length ≤ 2 ^ depth) :
    ∃! level, level ≤ depth ∧
      IsLeaderLevel
        (occurrenceRegular lA lB hA hB x hxA hxB) level := by
  classical
  apply exists_unique_leaderLevel
    (occurrenceRegular lA lB hA hB x hxA hxB) depth hdepth
  · intro level hlevel
    exact occurrenceRegular_succ lA lB hA hB x hxA hxB level
  · exact occurrenceRegular_terminal
      lA lB hA hB x hxA hxB depth hlength

#print axioms occurrenceRegular
#print axioms occurrenceRegular_succ
#print axioms occurrenceRegular_terminal
#print axioms exists_unique_occurrenceLeader

end FamilyStickyCinematicL32Prop41MarcusTardosActualLeaderPathV1
