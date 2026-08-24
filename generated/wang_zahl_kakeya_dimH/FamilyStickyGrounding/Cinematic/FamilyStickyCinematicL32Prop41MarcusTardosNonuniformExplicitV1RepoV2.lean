import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosNonuniformBaselineStepV1RepoV2
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosNonuniformExplicitV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1
open FamilyStickyCinematicL32Prop41MarcusTardosNonuniformBaselineStepV1

theorem nonuniform_total_length_le_explicit
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (hsymbolPow : Fintype.card symbol ≤ 2 ^ depth) :
    (∑ i : index, ((family i).order.length : Real)) ≤
      16 * (depth : Real) * (Fintype.card index : Real) *
          Real.sqrt (Fintype.card symbol : Real) +
        105 * (Fintype.card symbol : Real) *
          Real.sqrt (Fintype.card index : Real) := by
  have h := nonuniform_total_length_le_baseline_step
    family hreverse depth hdepth hsymbolPow
  let m : Real := Fintype.card index
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card index)
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hquot : m / Real.sqrt m = Real.sqrt m := by
    apply (div_eq_iff hsm.ne').2
    exact (Real.mul_self_sqrt hm.le).symm
  have hstep :
      (21 * (Fintype.card symbol : Real) / Real.sqrt m) * m =
        21 * (Fintype.card symbol : Real) * Real.sqrt m := by
    calc
      (21 * (Fintype.card symbol : Real) / Real.sqrt m) * m =
          21 * (Fintype.card symbol : Real) *
            (m / Real.sqrt m) := by ring
      _ = 21 * (Fintype.card symbol : Real) * Real.sqrt m := by rw [hquot]
  calc
    (∑ i : index, ((family i).order.length : Real)) ≤
        2 * paperBaseline depth symbol * (Fintype.card index : Real) +
          5 * paperStep index symbol * (Fintype.card index : Real) := h
    _ = 16 * (depth : Real) * (Fintype.card index : Real) *
          Real.sqrt (Fintype.card symbol : Real) +
        105 * (Fintype.card symbol : Real) *
          Real.sqrt (Fintype.card index : Real) := by
      dsimp [paperBaseline, paperStep, m] at hstep ⊢
      calc
        2 * (8 * (depth : Real) *
              Real.sqrt (Fintype.card symbol : Real)) *
              (Fintype.card index : Real) +
            5 * (21 * (Fintype.card symbol : Real) /
              Real.sqrt (Fintype.card index : Real)) *
              (Fintype.card index : Real) =
          16 * (depth : Real) * (Fintype.card index : Real) *
              Real.sqrt (Fintype.card symbol : Real) +
            5 * ((21 * (Fintype.card symbol : Real) /
              Real.sqrt (Fintype.card index : Real)) *
              (Fintype.card index : Real)) := by ring
        _ = 16 * (depth : Real) * (Fintype.card index : Real) *
              Real.sqrt (Fintype.card symbol : Real) +
            5 * (21 * (Fintype.card symbol : Real) *
              Real.sqrt (Fintype.card index : Real)) := by rw [hstep]
        _ = 16 * (depth : Real) * (Fintype.card index : Real) *
              Real.sqrt (Fintype.card symbol : Real) +
            105 * (Fintype.card symbol : Real) *
              Real.sqrt (Fintype.card index : Real) := by ring

#print axioms nonuniform_total_length_le_explicit

end FamilyStickyCinematicL32Prop41MarcusTardosNonuniformExplicitV1
