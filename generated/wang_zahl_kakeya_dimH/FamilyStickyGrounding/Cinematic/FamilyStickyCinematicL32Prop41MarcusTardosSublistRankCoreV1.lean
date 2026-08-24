import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosSublistRankCoreV1

open List

/-! # Index-order invariance under a nodup sublist -/

theorem idxOf_lt_iff_of_nodup_sublist
    {symbol : Type*} [DecidableEq symbol]
    {small large : List symbol} (hsub : small <+ large)
    (hlarge : large.Nodup) {a b : symbol}
    (ha : a ∈ small) (hb : b ∈ small) :
    small.idxOf a < small.idxOf b ↔
      large.idxOf a < large.idxOf b := by
  induction hsub generalizing a b with
  | slnil => simp at ha
  | cons pivot hsub ih =>
      have hparts := List.nodup_cons.mp hlarge
      have hneA : pivot ≠ a := by
        intro h
        subst a
        exact hparts.1 (hsub.subset ha)
      have hneB : pivot ≠ b := by
        intro h
        subst b
        exact hparts.1 (hsub.subset hb)
      rw [List.idxOf_cons_ne _ hneA, List.idxOf_cons_ne _ hneB]
      simpa using ih hparts.2 ha hb
  | cons_cons pivot hsub ih =>
      have hparts := List.nodup_cons.mp hlarge
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · simp
      · have hne : a ≠ b := by
          intro heq
          subst b
          exact hparts.1 (hsub.subset hb)
        simp [hne]
      · simp
      · have hneA : pivot ≠ a := by
          intro heq
          subst a
          exact hparts.1 (hsub.subset ha)
        have hneB : pivot ≠ b := by
          intro heq
          subst b
          exact hparts.1 (hsub.subset hb)
        rw [List.idxOf_cons_ne _ hneA, List.idxOf_cons_ne _ hneB,
          List.idxOf_cons_ne _ hneA, List.idxOf_cons_ne _ hneB]
        simpa using ih hparts.2 ha hb

#print axioms idxOf_lt_iff_of_nodup_sublist

end FamilyStickyCinematicL32Prop41MarcusTardosSublistRankCoreV1
