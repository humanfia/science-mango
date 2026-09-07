import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal
open FamilyStickyAtEveryScaleCoreV1

/-!
# Dyadic fibre cardinalities give Definition 2.12 uniformity

The owner-cardinality pigeonhole step places all retained nonempty fibres in
one dyadic interval.  This file performs the exact final conversion to the
`IsCUniform` field of `Def212ScaleWitness`; it introduces no new selection or
uniformity callback.
-/

namespace Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity

noncomputable section

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The uniformity constant may be enlarged. -/
theorem IsCUniform.mono
    {S : StickyScaleCover fine rho} {C C' : ENNReal}
    (h : IsCUniform S C) (hCC' : C <= C') :
    IsCUniform S C' := by
  intro k hk l hl
  exact (h k hk l hl).trans (by gcongr)

/-- Fibres in one occupied dyadic cardinality class are `2`-uniform. -/
theorem isCUniform_two_of_dyadic_fiber_card
    (S : StickyScaleCover fine rho) (level : Nat)
    (hlower : forall k, k ∈ S.activeCoarse ->
      2 ^ level <= (S.fiber k).card)
    (hupper : forall k, k ∈ S.activeCoarse ->
      (S.fiber k).card < 2 * 2 ^ level) :
    IsCUniform S 2 := by
  intro k hk l hl
  have hkNat : (S.fiber k).card <= 2 * (S.fiber l).card := by
    calc
      (S.fiber k).card <= 2 * 2 ^ level := Nat.le_of_lt (hupper k hk)
      _ <= 2 * (S.fiber l).card := Nat.mul_le_mul_left 2 (hlower l hl)
  exact_mod_cast hkNat

/-- The same dyadic class supplies any requested constant at least `2`. -/
theorem isCUniform_of_two_le_of_dyadic_fiber_card
    (S : StickyScaleCover fine rho) (level : Nat) (C : ENNReal)
    (hC : 2 <= C)
    (hlower : forall k, k ∈ S.activeCoarse ->
      2 ^ level <= (S.fiber k).card)
    (hupper : forall k, k ∈ S.activeCoarse ->
      (S.fiber k).card < 2 * 2 ^ level) :
    IsCUniform S C :=
  (isCUniform_two_of_dyadic_fiber_card S level hlower hupper).mono hC

#print axioms IsCUniform.mono
#print axioms isCUniform_two_of_dyadic_fiber_card
#print axioms isCUniform_of_two_le_of_dyadic_fiber_card

end
end Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
