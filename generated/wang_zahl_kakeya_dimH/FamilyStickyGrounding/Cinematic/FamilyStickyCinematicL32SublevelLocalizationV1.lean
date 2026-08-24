import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalValueLowerV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32SublevelLocalizationV1

open FamilyStickyCinematicL32CriticalValueLowerV1

/-!
# Localization of a sublevel point near the critical point

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(2a).

The analytic input is the already proved quadratic value separation from
Lemma 3.8(1b).  The first theorem below records only the reusable square-root
algebra; the second theorem supplies that input from actual derivative and
curvature hypotheses.
-/

/-- A quadratic lower bound and a sublevel upper bound give the explicit
square-root radius. -/
theorem distance_le_two_sqrt_of_quadratic_value_lower
    {x kappa Delta delta value : Real}
    (hkappa : 0 < kappa)
    (hvalueLower : (kappa / 4) * |x| ^ 2 - Delta <= value)
    (hsublevel : value <= delta) :
    |x| <= 2 * Real.sqrt ((Delta + delta) / kappa) := by
  have hquad : (kappa / 4) * |x| ^ 2 <= Delta + delta := by
    linarith
  have hsum : 0 <= Delta + delta := by
    have hleft : 0 <= (kappa / 4) * |x| ^ 2 :=
      mul_nonneg (div_nonneg (le_of_lt hkappa) (by norm_num)) (sq_nonneg _)
    exact hleft.trans hquad
  have hscale : 0 <= 4 / kappa :=
    div_nonneg (by norm_num) (le_of_lt hkappa)
  have hxSq : |x| ^ 2 <= 4 * ((Delta + delta) / kappa) := by
    calc
      |x| ^ 2 = (4 / kappa) * ((kappa / 4) * |x| ^ 2) := by
        field_simp
      _ <= (4 / kappa) * (Delta + delta) :=
        mul_le_mul_of_nonneg_left hquad hscale
      _ = 4 * ((Delta + delta) / kappa) := by ring
  have hratio : 0 <= (Delta + delta) / kappa :=
    div_nonneg hsum (le_of_lt hkappa)
  have hsqrt := Real.sq_sqrt hratio
  nlinarith [abs_nonneg x, Real.sqrt_nonneg ((Delta + delta) / kappa)]

/-- Every point of the `delta`-sublevel set lies in the explicit
`2 * sqrt ((Delta + delta) / kappa)` neighborhood of the critical point. -/
theorem sublevel_point_localized_near_criticalPoint
    (h h1 h2 : Real -> Real)
    {theta0 theta kappa Delta delta : Real}
    (hkappa : 0 < kappa) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 [[theta0, theta]])
    (hcurvatureLower : forall z, z ∈ [[theta0, theta]] ->
      kappa <= |h2 z|)
    (hcriticalValue : |h theta0| <= Delta)
    (hsublevel : |h theta| <= delta) :
    |theta - theta0| <=
      2 * Real.sqrt ((Delta + delta) / kappa) := by
  exact distance_le_two_sqrt_of_quadratic_value_lower hkappa
    (value_lower_away_from_criticalPoint h h1 h2 hkappa hcritical
      hderiv hderiv1 h2Continuous hcurvatureLower hcriticalValue)
    hsublevel

#print axioms distance_le_two_sqrt_of_quadratic_value_lower
#print axioms sublevel_point_localized_near_criticalPoint

end FamilyStickyCinematicL32SublevelLocalizationV1
