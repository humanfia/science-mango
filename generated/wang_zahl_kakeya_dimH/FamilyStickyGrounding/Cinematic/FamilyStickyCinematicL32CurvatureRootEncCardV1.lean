import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualRootEncCardV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CurvatureRootEncCardV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32Prop41ActualRootEncCardV1

/-!
# At most two roots from nonvanishing second derivative

This is the cardinality half of PYZ Lemma 3.8(1b).  Three ordered zeros
would give a second-derivative zero by two applications of Rolle's theorem,
contradicting the supplied positive absolute curvature lower bound.  The
conclusion is an `encard` bound, so finiteness is genuine rather than hidden
behind `Set.ncard`'s infinite-set convention.
-/

/-- A twice differentiable function whose second derivative is bounded away
from zero on an interval has at most two zeros there. -/
theorem rootSet_encard_le_two_of_abs_secondDerivative_lower
    (h h1 h2 : Real -> Real) {A B kappa : Real}
    (hkappa : 0 < kappa)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|) :
    ({z : Real | z ∈ Icc A B /\ h z = 0} : Set Real).encard <= 2 := by
  let roots : Set Real := {z : Real | z ∈ Icc A B /\ h z = 0}
  have hnoOrdered : forall {a b c : Real}, a < b -> b < c ->
      a ∈ roots -> b ∈ roots -> c ∈ roots -> False := by
    intro a b c hab hbc ha hb hc
    have hsub : Icc a c ⊆ Icc A B := by
      intro z hz
      exact ⟨ha.1.1.trans hz.1, hz.2.trans hc.1.2⟩
    obtain ⟨x, hx, y, hy, z, hz, _hx0, _hy0, hz0⟩ :=
      second_derivative_zero_between_three_zeros h h1 h2 hab hbc
        (fun u hu => hderiv u (hsub hu))
        (fun u hu => hderiv1 u (hsub hu)) ha.2 hb.2 hc.2
    have hzOuter : z ∈ Icc A B := hsub ⟨
      (le_of_lt hx.1).trans (le_of_lt hz.1),
      (le_of_lt hz.2).trans (le_of_lt hy.2)⟩
    have hpositive := hcurvatureLower z hzOuter
    rw [hz0, abs_zero] at hpositive
    linarith
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

#print axioms rootSet_encard_le_two_of_abs_secondDerivative_lower

end FamilyStickyCinematicL32CurvatureRootEncCardV1
