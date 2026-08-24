import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TwoZeroGeometryV1
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualRootEncCardV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TwoZeroGeometryV1

/-!
# Genuine finite at-most-two root carrier

This module uses `Set.encard`, not bare `Set.ncard`: the resulting bound
therefore proves finiteness even before any cardinal arithmetic.  The
analytic producer is the actual twice-Rolle `traceFunction_no_three...`
theorem.
-/

/-- If two chosen distinct points cover every further point, a set has
extended cardinality at most two. -/
theorem encard_le_two_of_pair_cover
    {alpha : Type*} (s : Set alpha)
    (hcover : forall a, a ∈ s -> forall b, b ∈ s -> a ≠ b ->
      forall c, c ∈ s -> c = a ∨ c = b) :
    s.encard <= 2 := by
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha⟩ := hs
    by_cases hb : exists b, b ∈ s ∧ b ≠ a
    · obtain ⟨b, hb, hba⟩ := hb
      have hsub : s ⊆ ({a, b} : Set alpha) := by
        intro c hc
        rcases hcover a ha b hb hba.symm c hc with hca | hcb
        · exact Or.inl hca
        · exact Or.inr hcb
      exact (encard_mono hsub).trans (encard_pair hba.symm).le
    · have hsub : s ⊆ ({a} : Set alpha) := by
        intro b hbmem
        have hba : ¬ b ≠ a := by
          intro hne
          exact hb ⟨b, hbmem, hne⟩
        simpa only [mem_singleton_iff] using not_not.mp hba
      exact (encard_mono hsub).trans (by simp)
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp

/-- The actual PYZ twice-Rolle theorem gives a genuine `encard <= 2`
bound for the global trace root set. -/
theorem traceFunction_rootSet_encard_le_two
    (f f1 f2 : Real -> Real) (da db dd : Real) {A B : Real}
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f1 (f2 theta) theta)
    (hosc0 : forall x, x ∈ Icc A B -> forall y, y ∈ Icc A B ->
      |traceJet0 da db dd (f x) x - traceJet0 da db dd (f y) y| <
        coefficientDistance da db dd / 1200)
    (hosc1 : forall x, x ∈ Icc A B -> forall y, y ∈ Icc A B ->
      |traceJet1 db dd (f x) (f1 x) x -
        traceJet1 db dd (f y) (f1 y) y| <
          coefficientDistance da db dd / 1200) :
    {theta | theta ∈ Icc A B ∧
      traceFunction f da db dd theta = 0}.encard <= 2 := by
  let roots : Set Real := {theta | theta ∈ Icc A B ∧
    traceFunction f da db dd theta = 0}
  have hnoOrdered : forall {a b c : Real}, a < b -> b < c ->
      a ∈ roots -> b ∈ roots -> c ∈ roots -> False := by
    intro a b c hab hbc ha hb hc
    have hsub : Icc a c ⊆ Icc A B := by
      intro theta htheta
      exact ⟨ha.1.1.trans htheta.1, htheta.2.trans hc.1.2⟩
    exact traceFunction_no_three_ordered_zeros f f1 f2 da db dd
      hab hbc hcoefficient
      (fun theta htheta => hparameter theta (hsub htheta))
      (fun theta htheta => hft theta (hsub htheta))
      (fun theta htheta => hf1Lower theta (hsub htheta))
      (fun theta htheta => hf1Upper theta (hsub htheta))
      (fun theta htheta => hf2 theta (hsub htheta))
      (fun theta htheta => hfDeriv theta (hsub htheta))
      (fun theta htheta => hf1Deriv theta (hsub htheta))
      (fun x hx y hy => hosc0 x (hsub hx) y (hsub hy))
      (fun x hx y hy => hosc1 x (hsub hx) y (hsub hy))
      ha.2 hb.2 hc.2
  change roots.encard <= 2
  apply encard_le_two_of_pair_cover roots
  intro a ha b hb hab c hc
  by_contra hcover
  push Not at hcover
  rcases hcover with ⟨hca, hcb⟩
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_or_gt_of_ne hca with hcalt | haclt
    · exact hnoOrdered hcalt hablt hc ha hb
    · rcases lt_or_gt_of_ne hcb with hcblt | hbclt
      · exact hnoOrdered haclt hcblt ha hc hb
      · exact hnoOrdered hablt hbclt ha hb hc
  · rcases lt_or_gt_of_ne hcb with hcblt | hbclt
    · exact hnoOrdered hcblt hbalt hc hb ha
    · rcases lt_or_gt_of_ne hca with hcalt | haclt
      · exact hnoOrdered hbclt hcalt hb hc ha
      · exact hnoOrdered hbalt haclt hb ha hc

/-- In particular, the actual root carrier is finite. -/
theorem traceFunction_rootSet_finite
    (f f1 f2 : Real -> Real) (da db dd : Real) {A B : Real}
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc A B ->
      HasDerivAt f1 (f2 theta) theta)
    (hosc0 : forall x, x ∈ Icc A B -> forall y, y ∈ Icc A B ->
      |traceJet0 da db dd (f x) x - traceJet0 da db dd (f y) y| <
        coefficientDistance da db dd / 1200)
    (hosc1 : forall x, x ∈ Icc A B -> forall y, y ∈ Icc A B ->
      |traceJet1 db dd (f x) (f1 x) x -
        traceJet1 db dd (f y) (f1 y) y| <
          coefficientDistance da db dd / 1200) :
    {theta | theta ∈ Icc A B ∧
      traceFunction f da db dd theta = 0}.Finite := by
  exact finite_of_encard_le_coe
    (traceFunction_rootSet_encard_le_two f f1 f2 da db dd
      hcoefficient hparameter hft hf1Lower hf1Upper hf2 hfDeriv
      hf1Deriv hosc0 hosc1)

#print axioms encard_le_two_of_pair_cover
#print axioms traceFunction_rootSet_encard_le_two
#print axioms traceFunction_rootSet_finite

end FamilyStickyCinematicL32Prop41ActualRootEncCardV1
