import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TangencyMinimizerV1

/-!
# A genuine minimizer for the cinematic tangency parameter

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Definition 3.7
and the first line of the proof of Lemma 3.8.  Their parameter is the
minimum on the compact middle interval of the value--slope cost
`|h(theta)| + |h'(theta)|`.

This module produces the minimizing point from compactness and continuity;
neither the minimum nor its universal lower-bound property is a callback.
-/

/-- The pointwise value--slope cost minimized by the PYZ tangency
parameter. -/
def jetCost (h h1 : Real -> Real) (theta : Real) : Real :=
  |h theta| + |h1 theta|

/-- A continuous value--slope cost attains its minimum on a nonempty closed
interval. -/
theorem exists_jetCost_minimizer
    (h h1 : Real -> Real) {A B : Real} (hAB : A <= B)
    (hContinuous : ContinuousOn h (Icc A B))
    (h1Continuous : ContinuousOn h1 (Icc A B)) :
    exists thetaDelta, thetaDelta ∈ Icc A B ∧
      forall theta, theta ∈ Icc A B ->
        jetCost h h1 thetaDelta <= jetCost h h1 theta := by
  have hcostContinuous :
      ContinuousOn (jetCost h h1) (Icc A B) := by
    exact hContinuous.abs.add h1Continuous.abs
  obtain ⟨thetaDelta, hthetaDelta, hminimum⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hAB) hcostContinuous
  exact ⟨thetaDelta, hthetaDelta, fun _theta htheta => hminimum htheta⟩

/-- The attained minimum can be packaged as an explicit nonnegative
tangency parameter together with both its defining equality and universal
minimality inequality. -/
theorem exists_tangencyParameter_with_minimizer
    (h h1 : Real -> Real) {A B : Real} (hAB : A <= B)
    (hContinuous : ContinuousOn h (Icc A B))
    (h1Continuous : ContinuousOn h1 (Icc A B)) :
    exists Delta thetaDelta,
      0 <= Delta ∧ thetaDelta ∈ Icc A B ∧
      Delta = jetCost h h1 thetaDelta ∧
      forall theta, theta ∈ Icc A B ->
        Delta <= jetCost h h1 theta := by
  obtain ⟨thetaDelta, hthetaDelta, hminimum⟩ :=
    exists_jetCost_minimizer h h1 hAB hContinuous h1Continuous
  refine ⟨jetCost h h1 thetaDelta, thetaDelta, ?_, hthetaDelta, rfl, hminimum⟩
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

#print axioms exists_jetCost_minimizer
#print axioms exists_tangencyParameter_with_minimizer

end FamilyStickyCinematicL32TangencyMinimizerV1
