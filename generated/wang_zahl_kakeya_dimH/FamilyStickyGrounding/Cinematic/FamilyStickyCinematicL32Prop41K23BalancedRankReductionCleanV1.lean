import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1

/-!
# Balanced-word reduction for six ordered `K_{2,3}` incidences

The six incidences are transported along an injective rank map to a balanced
binary word.  A kernel-checked `64`-word computation says that the word either
contains four alternating host labels or one host occupies three consecutive
ranks.  No crossing, no-same-triple, intersection-reverse, or geometric
conclusion occurs among the premises.
-/

def AlternatingFour {alpha : Type*} [DecidableEq alpha]
    (rank : K23Edge -> Fin 6) (label : K23Edge -> alpha) : Prop :=
  exists e0 e1 e2 e3 : K23Edge,
    rank e0 < rank e1 /\ rank e1 < rank e2 /\ rank e2 < rank e3 /\
    label e0 = label e2 /\ label e1 = label e3 /\ label e0 ≠ label e1

def HostConsecutiveBlock (rank : K23Edge -> Fin 6) : Prop :=
  exists h : Fin 2, exists s : Fin 4, forall j : Fin 3,
    (rank (h, j) : Nat) = (s : Nat) \/
      (rank (h, j) : Nat) = (s : Nat) + 1 \/
      (rank (h, j) : Nat) = (s : Nat) + 2

def BalancedHostWord (word : Fin 6 -> Fin 2) : Prop :=
  ((Finset.univ.filter fun i => word i = 0).card = 3)

def WordAlternatingFour (word : Fin 6 -> Fin 2) : Prop :=
  exists i0 i1 i2 i3 : Fin 6,
    i0 < i1 /\ i1 < i2 /\ i2 < i3 /\
      word i0 = word i2 /\ word i1 = word i3 /\ word i0 ≠ word i1

def WordExactConsecutiveTriple (word : Fin 6 -> Fin 2) : Prop :=
  exists s : Fin 4, exists h : Fin 2, forall i : Fin 6,
    word i = h <->
      i = ⟨s, by omega⟩ \/ i = ⟨s + 1, by omega⟩ \/
        i = ⟨s + 2, by omega⟩

/- Kernel-checked `64`-word combinatorial core. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem wordAlternating_or_exactConsecutive_of_balanced :
    forall word : Fin 6 -> Fin 2,
      BalancedHostWord word ->
      WordAlternatingFour word \/ WordExactConsecutiveTriple word := by
  unfold BalancedHostWord WordAlternatingFour WordExactConsecutiveTriple
  decide

theorem hostAlternating_or_consecutiveBlock
    (rank : K23Edge -> Fin 6) (hinj : Function.Injective rank) :
    AlternatingFour rank (fun e => e.1) \/ HostConsecutiveBlock rank := by
  have hcard : Fintype.card K23Edge = Fintype.card (Fin 6) := by decide
  have hbij : Function.Bijective rank :=
    (Fintype.bijective_iff_injective_and_card rank).mpr ⟨hinj, hcard⟩
  let E : K23Edge ≃ Fin 6 := Equiv.ofBijective rank hbij
  let word : Fin 6 -> Fin 2 := fun i => (E.symm i).1
  let fiberEquiv : {i : Fin 6 // word i = 0} ≃ Fin 3 :=
    { toFun := fun i => (E.symm i).2
      invFun := fun j => ⟨E (0, j), by simp [word]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        change E (0, (E.symm i).2) = i
        have hp : (0, (E.symm i).2) = E.symm i := by
          apply Prod.ext
          · exact i.property.symm
          · rfl
        rw [hp, E.apply_symm_apply]
      right_inv := by
        intro j
        simp }
  have hbalanced : BalancedHostWord word := by
    unfold BalancedHostWord
    rw [← Fintype.card_subtype]
    calc
      Fintype.card {i : Fin 6 // word i = 0} = Fintype.card (Fin 3) :=
        Fintype.card_congr fiberEquiv
      _ = 3 := Fintype.card_fin 3
  rcases wordAlternating_or_exactConsecutive_of_balanced word hbalanced with
      halt | hblock
  · left
    rcases halt with ⟨i0, i1, i2, i3, h01, h12, h23, h02, h13, hne⟩
    have hr0 := E.apply_symm_apply i0
    have hr1 := E.apply_symm_apply i1
    have hr2 := E.apply_symm_apply i2
    have hr3 := E.apply_symm_apply i3
    change rank (E.symm i0) = i0 at hr0
    change rank (E.symm i1) = i1 at hr1
    change rank (E.symm i2) = i2 at hr2
    change rank (E.symm i3) = i3 at hr3
    refine ⟨E.symm i0, E.symm i1, E.symm i2, E.symm i3, ?_⟩
    rw [hr0, hr1, hr2, hr3]
    exact ⟨h01, h12, h23, h02, h13, hne⟩
  · right
    rcases hblock with ⟨s, h, hblock⟩
    refine ⟨h, s, ?_⟩
    intro j
    have hword : word (E (h, j)) = h := by simp [word]
    rcases (hblock (E (h, j))).mp hword with heq | heq | heq
    · left
      have hval := congrArg Fin.val heq
      simpa [E] using hval
    · right; left
      have hval := congrArg Fin.val heq
      simpa [E] using hval
    · right; right
      have hval := congrArg Fin.val heq
      simpa [E] using hval

#print axioms wordAlternating_or_exactConsecutive_of_balanced
#print axioms hostAlternating_or_consecutiveBlock

end FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1
