import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41FiniteMonotoneOpenIntervalPortSelectionCleanV1

/-!
# Strictly ordered ports in a finite monotone family of open intervals

If the left endpoints of finitely many nonempty real intervals are
nondecreasing in a prescribed finite linear order, ports can be chosen inside
the intervals in strictly increasing order.  Equal left endpoints are split
without any arbitrary geometric assumption.  This is the finite selector
needed after the actual entry-parameter/local-angle lexicographic order has
been established.
-/

private theorem exists_strictMono_interval_choice_fin
    (n : Nat) (left right : Fin n -> Real)
    (hleft : Monotone left)
    (hinterval : forall i, left i < right i) :
    exists port : Fin n -> Real,
      (forall i, port i ∈ Ioo (left i) (right i)) ∧
      StrictMono port := by
  induction n with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        let port : Fin 1 -> Real := fun _ => (left 0 + right 0) / 2
        refine ⟨port, ?_, ?_⟩
        · intro i
          have hi : i = 0 := by
            apply Fin.ext
            omega
          subst i
          dsimp [port]
          constructor <;> linarith [hinterval 0]
        · intro i j hij
          omega
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let leftTail : Fin n -> Real := fun i => left i.succ
        let rightTail : Fin n -> Real := fun i => right i.succ
        have hleftTail : Monotone leftTail := by
          intro i j hij
          apply hleft
          exact Nat.succ_le_succ hij
        have hintervalTail : forall i, leftTail i < rightTail i := by
          intro i
          exact hinterval i.succ
        rcases ih leftTail rightTail hleftTail hintervalTail with
          ⟨tailPort, htailMem, htailStrict⟩
        let firstTail : Fin n := ⟨0, hnpos⟩
        let cap : Real := min (right 0) (tailPort firstTail)
        have hleft0_le_tailLeft : left 0 <= leftTail firstTail := by
          exact hleft (Fin.zero_le _)
        have hleft0_lt_tailPort : left 0 < tailPort firstTail :=
          lt_of_le_of_lt hleft0_le_tailLeft (htailMem firstTail).1
        have hleft0_lt_cap : left 0 < cap := by
          exact lt_min (hinterval 0) hleft0_lt_tailPort
        let firstPort : Real := (left 0 + cap) / 2
        have hfirstMem : firstPort ∈ Ioo (left 0) (right 0) := by
          constructor
          · dsimp [firstPort]
            linarith
          · have hcap : cap <= right 0 := min_le_left _ _
            dsimp [firstPort]
            linarith
        have hfirst_lt_tail0 : firstPort < tailPort firstTail := by
          have hcap : cap <= tailPort firstTail := min_le_right _ _
          dsimp [firstPort]
          linarith
        let port : Fin (n + 1) -> Real := Fin.cons firstPort tailPort
        refine ⟨port, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa [port] using hfirstMem
          · simpa [port, leftTail, rightTail] using htailMem j
        · rw [show port = Fin.cons firstPort tailPort by rfl,
            Fin.strictMono_cons]
          refine ⟨?_, htailStrict⟩
          intro j
          have hfirstTailLe : firstTail <= j := by
            exact Nat.zero_le _
          exact hfirst_lt_tail0.trans_le
            (htailStrict.monotone hfirstTailLe)

/-- Ordered finite interval choice.  The output order is exactly the input
linear order; no tertiary enumeration affects the geometric port order. -/
theorem exists_strictMono_interval_choice
    {alpha : Type*} [Fintype alpha] [LinearOrder alpha]
    (left right : alpha -> Real)
    (hleft : Monotone left)
    (hinterval : forall i, left i < right i) :
    exists port : alpha -> Real,
      (forall i, port i ∈ Ioo (left i) (right i)) ∧
      StrictMono port := by
  let e : Fin (Fintype.card alpha) ≃o alpha :=
    Fintype.orderIsoFinOfCardEq alpha rfl
  have hleftFin : Monotone (fun i => left (e i)) :=
    hleft.comp e.monotone
  have hintervalFin : forall i,
      left (e i) < right (e i) := fun i => hinterval (e i)
  rcases exists_strictMono_interval_choice_fin (Fintype.card alpha)
      (fun i => left (e i)) (fun i => right (e i))
      hleftFin hintervalFin with ⟨portFin, hportFin, hstrictFin⟩
  let port : alpha -> Real := fun i => portFin (e.symm i)
  refine ⟨port, ?_, ?_⟩
  · intro i
    simpa [port] using hportFin (e.symm i)
  · intro i j hij
    exact hstrictFin (e.symm.lt_iff_lt.mpr hij)

#print axioms exists_strictMono_interval_choice

end FamilyStickyCinematicL32Prop41FiniteMonotoneOpenIntervalPortSelectionCleanV1
