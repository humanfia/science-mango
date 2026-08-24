import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelIntervalV1
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32CriticalPointGrowthV1

open FamilyStickyCinematicL32SublevelIntervalV1

/-!
# Quantitative growth away from a cinematic critical point

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8, equations (3.4)--(3.6).

The results below isolate the two genuine calculus producers used there.
An upper curvature bound gives quadratic value growth away from a critical
point.  A nonvanishing lower curvature bound gives linear first-derivative
growth.  Combining them turns a value gap `Delta - delta` into the explicit
first-derivative scale

`kappa * sqrt ((Delta - delta) / M)`.

Every constant is displayed, and neither a sublevel-length estimate nor any
incidence/maximal estimate is assumed.
-/

/-- Mean-value norm bound on an unordered real interval. -/
theorem abs_sub_le_of_hasDerivAt_bound_on_uIcc
    (h h1 : Real -> Real) {a b C x y : Real}
    (hx : x ∈ [[a, b]]) (hy : y ∈ [[a, b]])
    (hderiv : forall z, z ∈ [[a, b]] -> HasDerivAt h (h1 z) z)
    (hbound : forall z, z ∈ [[a, b]] -> |h1 z| <= C) :
    |h x - h y| <= C * |x - y| := by
  have hmean : ‖h x - h y‖ <= C * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := h) (f' := h1) (s := [[a, b]])
      (fun z hz => (hderiv z hz).hasDerivWithinAt)
      (fun z hz => by
        simpa [Real.norm_eq_abs] using hbound z hz)
      (convex_uIcc a b) hy hx
  simpa [Real.norm_eq_abs] using hmean

/-- If `h'` vanishes at `theta0` and `|h''| <= M`, then value growth from
that critical point is at most `M * |theta - theta0|^2`. -/
theorem abs_value_sub_critical_le_curvature_mul_sq
    (h h1 h2 : Real -> Real) {theta0 theta M : Real}
    (hM : 0 <= M) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (hcurvatureUpper : forall z, z ∈ [[theta0, theta]] ->
      |h2 z| <= M) :
    |h theta - h theta0| <= M * |theta - theta0| ^ 2 := by
  have hfirstBound : forall z, z ∈ [[theta0, theta]] ->
      |h1 z| <= M * |theta - theta0| := by
    intro z hz
    have hosc := abs_sub_le_of_hasDerivAt_bound_on_uIcc
      h1 h2 hz left_mem_uIcc hderiv1 hcurvatureUpper
    have hdistance := abs_sub_left_of_mem_uIcc hz
    calc
      |h1 z| = |h1 z - h1 theta0| := by rw [hcritical, sub_zero]
      _ <= M * |z - theta0| := hosc
      _ <= M * |theta - theta0| :=
        mul_le_mul_of_nonneg_left hdistance hM
  have hvalue := abs_sub_le_of_hasDerivAt_bound_on_uIcc
    h h1 right_mem_uIcc left_mem_uIcc hderiv hfirstBound
  calc
    |h theta - h theta0| <=
        (M * |theta - theta0|) * |theta - theta0| := hvalue
    _ = M * |theta - theta0| ^ 2 := by ring

/-- The value gap between a critical point and a sublevel point forces a
quadratic lower bound for their parameter distance. -/
theorem critical_value_gap_forces_distance_sq
    (h h1 h2 : Real -> Real)
    {theta0 theta M Delta delta : Real}
    (hM : 0 < M) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (hcurvatureUpper : forall z, z ∈ [[theta0, theta]] ->
      |h2 z| <= M)
    (hcenter : Delta <= |h theta0|)
    (hsublevel : |h theta| <= delta) :
    (Delta - delta) / M <= |theta - theta0| ^ 2 := by
  have hquadratic := abs_value_sub_critical_le_curvature_mul_sq
    h h1 h2 (le_of_lt hM) hcritical hderiv hderiv1 hcurvatureUpper
  have htriangle : Delta <=
      M * |theta - theta0| ^ 2 + delta := by
    calc
      Delta <= |h theta0| := hcenter
      _ = |(h theta0 - h theta) + h theta| := by ring_nf
      _ <= |h theta0 - h theta| + |h theta| := abs_add_le _ _
      _ = |h theta - h theta0| + |h theta| := by
        rw [abs_sub_comm]
      _ <= M * |theta - theta0| ^ 2 + delta :=
        add_le_add hquadratic hsublevel
  apply (div_le_iff₀ hM).2
  nlinarith

/-- Square-root form of the preceding distance bound. -/
theorem critical_value_gap_forces_sqrt_distance
    (h h1 h2 : Real -> Real)
    {theta0 theta M Delta delta : Real}
    (hM : 0 < M) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (hcurvatureUpper : forall z, z ∈ [[theta0, theta]] ->
      |h2 z| <= M)
    (hcenter : Delta <= |h theta0|)
    (hsublevel : |h theta| <= delta) :
    Real.sqrt ((Delta - delta) / M) <= |theta - theta0| := by
  apply Real.sqrt_le_iff.2
  exact ⟨abs_nonneg _, critical_value_gap_forces_distance_sq
    h h1 h2 hM hcritical hderiv hderiv1 hcurvatureUpper
    hcenter hsublevel⟩

/-- A derivative lower bound integrates to a quantitative endpoint growth
bound, with no hidden constant. -/
theorem mul_interval_length_le_function_sub_of_deriv_lower
    (q q1 : Real -> Real) {a b kappa : Real}
    (hab : a <= b)
    (hderiv : forall z, z ∈ Icc a b -> HasDerivAt q (q1 z) z)
    (hlower : forall z, z ∈ Icc a b -> kappa <= q1 z) :
    kappa * (b - a) <= q b - q a := by
  rcases eq_or_lt_of_le hab with habEq | habLt
  · subst b
    simp
  obtain ⟨z, hz, hslope⟩ := exists_hasDerivAt_eq_slope
    q q1 habLt (HasDerivAt.continuousOn hderiv)
    (fun u hu => hderiv u (Ioo_subset_Icc_self hu))
  have hslopeLower := hlower z (Ioo_subset_Icc_self hz)
  rw [hslope] at hslopeLower
  exact (le_div_iff₀ (sub_pos.2 habLt)).1 hslopeLower

/-- A fixed positive curvature lower bound produces linear growth of the
first derivative away from its zero. -/
theorem curvature_lower_forces_first_derivative_growth
    (h1 h2 : Real -> Real) {theta0 theta kappa : Real}
    (hkappa : 0 <= kappa) (hcritical : h1 theta0 = 0)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (hcurvatureLower : forall z, z ∈ [[theta0, theta]] ->
      kappa <= h2 z) :
    kappa * |theta - theta0| <= |h1 theta| := by
  rcases le_total theta0 theta with horder | horder
  · have hgrowth := mul_interval_length_le_function_sub_of_deriv_lower
      h1 h2 horder
      (fun z hz => hderiv1 z (by
        simpa [uIcc_of_le horder] using hz))
      (fun z hz => hcurvatureLower z (by
        simpa [uIcc_of_le horder] using hz))
    have hfirstNonneg : 0 <= h1 theta := by
      rw [hcritical, sub_zero] at hgrowth
      exact (mul_nonneg hkappa (sub_nonneg.2 horder)).trans hgrowth
    rw [abs_of_nonneg (sub_nonneg.2 horder), abs_of_nonneg hfirstNonneg]
    simpa [hcritical] using hgrowth
  · have hgrowth := mul_interval_length_le_function_sub_of_deriv_lower
      h1 h2 horder
      (fun z hz => hderiv1 z (by
        simpa [uIcc_of_ge horder] using hz))
      (fun z hz => hcurvatureLower z (by
        simpa [uIcc_of_ge horder] using hz))
    have hfirstNonpos : h1 theta <= 0 := by
      rw [hcritical, zero_sub] at hgrowth
      nlinarith [mul_nonneg hkappa (sub_nonneg.2 horder)]
    rw [abs_of_nonpos (sub_nonpos.2 horder), abs_of_nonpos hfirstNonpos]
    rw [hcritical, zero_sub] at hgrowth
    nlinarith

/-- The interval version of the fixed-sign producer from the preceding
sublevel module, now stated on an unordered interval. -/
theorem continuous_fixed_sign_of_abs_lower_on_uIcc
    (q : Real -> Real) {a b kappa : Real}
    (hkappa : 0 < kappa)
    (hqContinuous : ContinuousOn q [[a, b]])
    (habs : forall z, z ∈ [[a, b]] -> kappa <= |q z|) :
    (forall z, z ∈ [[a, b]] -> kappa <= q z) ∨
      (forall z, z ∈ [[a, b]] -> q z <= -kappa) := by
  rcases le_total a b with hab | hba
  · simpa [uIcc_of_le hab] using
      continuous_fixed_sign_of_abs_lower_on_Icc
        q hab hkappa
        (by simpa [uIcc_of_le hab] using hqContinuous)
        (by simpa [uIcc_of_le hab] using habs)
  · simpa [uIcc_of_ge hba] using
      continuous_fixed_sign_of_abs_lower_on_Icc
        q hba hkappa
        (by simpa [uIcc_of_ge hba] using hqContinuous)
        (by simpa [uIcc_of_ge hba] using habs)

/-- A continuous curvature bounded away from zero produces first-derivative
growth without assuming its sign. -/
theorem abs_curvature_lower_forces_first_derivative_growth
    (h1 h2 : Real -> Real) {theta0 theta kappa : Real}
    (hkappa : 0 < kappa) (hcritical : h1 theta0 = 0)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 [[theta0, theta]])
    (hcurvatureLower : forall z, z ∈ [[theta0, theta]] ->
      kappa <= |h2 z|) :
    kappa * |theta - theta0| <= |h1 theta| := by
  rcases continuous_fixed_sign_of_abs_lower_on_uIcc
      h2 hkappa h2Continuous hcurvatureLower with hpositive | hnegative
  · exact curvature_lower_forces_first_derivative_growth
      h1 h2 (le_of_lt hkappa) hcritical hderiv1 hpositive
  · have hgrowth := curvature_lower_forces_first_derivative_growth
      (-h1) (-h2) (le_of_lt hkappa)
      (show (-h1) theta0 = 0 by
        change -h1 theta0 = 0
        rw [hcritical, neg_zero])
      (fun z hz => (hderiv1 z hz).neg)
      (fun z hz => by
        change kappa <= -h2 z
        linarith [hnegative z hz])
    change kappa * |theta - theta0| <= |h1 theta|
    change kappa * |theta - theta0| <= |(-h1) theta| at hgrowth
    simpa only [Pi.neg_apply, abs_neg] using hgrowth

/-- PYZ (3.5)--(3.6), with constants explicit: a critical value gap and
two-sided curvature bounds force the square-root first-derivative scale at a
sublevel point. -/
theorem critical_sublevel_first_derivative_sqrt_lower
    (h h1 h2 : Real -> Real)
    {theta0 theta M kappa Delta delta : Real}
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 [[theta0, theta]])
    (hcurvatureUpper : forall z, z ∈ [[theta0, theta]] ->
      |h2 z| <= M)
    (hcurvatureLower : forall z, z ∈ [[theta0, theta]] ->
      kappa <= |h2 z|)
    (hcenter : Delta <= |h theta0|)
    (hsublevel : |h theta| <= delta) :
    kappa * Real.sqrt ((Delta - delta) / M) <= |h1 theta| := by
  have hdistance := critical_value_gap_forces_sqrt_distance
    h h1 h2 hM hcritical hderiv hderiv1 hcurvatureUpper
    hcenter hsublevel
  have hfirst := abs_curvature_lower_forces_first_derivative_growth
    h1 h2 hkappa hcritical hderiv1 h2Continuous hcurvatureLower
  exact (mul_le_mul_of_nonneg_left hdistance (le_of_lt hkappa)).trans hfirst

/-- The square-root first-derivative scale is strictly positive under the
same explicit positivity regime. -/
theorem sqrt_first_derivative_scale_pos
    {M kappa Delta delta : Real}
    (hM : 0 < M) (hkappa : 0 < kappa) (hgap : delta < Delta) :
    0 < kappa * Real.sqrt ((Delta - delta) / M) := by
  exact mul_pos hkappa (Real.sqrt_pos.2 (div_pos (sub_pos.2 hgap) hM))

#print axioms abs_sub_le_of_hasDerivAt_bound_on_uIcc
#print axioms abs_value_sub_critical_le_curvature_mul_sq
#print axioms critical_value_gap_forces_distance_sq
#print axioms critical_value_gap_forces_sqrt_distance
#print axioms mul_interval_length_le_function_sub_of_deriv_lower
#print axioms curvature_lower_forces_first_derivative_growth
#print axioms continuous_fixed_sign_of_abs_lower_on_uIcc
#print axioms abs_curvature_lower_forces_first_derivative_growth
#print axioms critical_sublevel_first_derivative_sqrt_lower
#print axioms sqrt_first_derivative_scale_pos

end FamilyStickyCinematicL32CriticalPointGrowthV1
