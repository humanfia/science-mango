import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosUniqueLeaderV1

/-!
# Unique first regular level on a dyadic occurrence path

Linear intersection reversal is hereditary under restriction, so regularity
along a fixed symbol's nested block-pair path is monotone.  Terminal singleton
blocks are regular.  Therefore every occurrence has a unique leader level:
the first regular level after level one.
-/

def IsLeaderLevel (regular : Nat → Prop) (level : Nat) : Prop :=
  1 ≤ level ∧ regular level ∧
    (level = 1 ∨ ¬regular (level - 1))

theorem exists_unique_leaderLevel
    (regular : Nat → Prop) [DecidablePred regular]
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hmono : ∀ level < depth,
      regular level → regular (level + 1))
    (hterminal : regular depth) :
    ∃! level, level ≤ depth ∧ IsLeaderLevel regular level := by
  let candidate : Nat → Prop := fun level =>
    1 ≤ level ∧ level ≤ depth ∧ regular level
  have hex : ∃ level, candidate level :=
    ⟨depth, hdepth, le_rfl, hterminal⟩
  let first := Nat.find hex
  have hfirstSpec : candidate first := Nat.find_spec hex
  have hfirstPrev : first = 1 ∨ ¬regular (first - 1) := by
    by_cases hone : first = 1
    · exact Or.inl hone
    · right
      intro hprev
      have hprevOne : 1 ≤ first - 1 := by omega
      have hprevDepth : first - 1 ≤ depth := by omega
      exact Nat.find_min hex (by omega)
        ⟨hprevOne, hprevDepth, hprev⟩
  refine ⟨first, ⟨hfirstSpec.2.1,
    hfirstSpec.1, hfirstSpec.2.2, hfirstPrev⟩, ?_⟩
  intro level hlevel
  have hfirstLe : first ≤ level :=
    Nat.find_min' hex
      ⟨hlevel.2.1, hlevel.1, hlevel.2.2.1⟩
  apply Nat.le_antisymm ?_ hfirstLe
  by_contra hnot
  have hlt : first < level := lt_of_not_ge hnot
  have hpredBounds : first ≤ level - 1 ∧ level - 1 ≤ depth := by omega
  let boundedRegular : Nat → Prop := fun n => n ≤ depth → regular n
  have hboundedSucc : ∀ n,
      boundedRegular n → boundedRegular (n + 1) := by
    intro n hn hnDepth
    exact hmono n (by omega) (hn (by omega))
  have hboundedMono : Monotone boundedRegular :=
    monotone_nat_of_le_succ hboundedSucc
  have hpredRegular : regular (level - 1) :=
    hboundedMono hpredBounds.1 (fun _ => hfirstSpec.2.2)
      hpredBounds.2
  rcases hlevel.2.2.2 with hlevelOne | hnotPred
  · omega
  · exact hnotPred hpredRegular

#print axioms IsLeaderLevel
#print axioms exists_unique_leaderLevel

end FamilyStickyCinematicL32Prop41MarcusTardosUniqueLeaderV1
