import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointGrowthV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32CriticalValueLowerV1

open FamilyStickyCinematicL32CriticalPointGrowthV1

/-!
# Quadratic value separation away from a critical point

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1b), equation (3.4).

The proof below avoids an integral callback.  It splits the segment from the
critical point to the target at its midpoint and applies the mean value
theorem twice.  This gives the fully explicit constant `1/4` in

`(kappa / 4) * |theta - theta0|^2 <= |h(theta) - h(theta0)|`.
-/

/-- Positive curvature produces one-sided quadratic value growth away from
a critical point. -/
theorem curvature_lower_critical_forces_value_sub_lower
    (h h1 h2 : Real -> Real) {theta0 theta kappa : Real}
    (hkappa : 0 <= kappa) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (hcurvatureLower : forall z, z ∈ [[theta0, theta]] ->
      kappa <= h2 z) :
    (kappa / 4) * |theta - theta0| ^ 2 <= h theta - h theta0 := by
  rcases le_total theta0 theta with horder | horder
  · let mid : Real := (theta0 + theta) / 2
    have htheta0mid : theta0 <= mid := by
      dsimp [mid]
      linarith
    have hmidtheta : mid <= theta := by
      dsimp [mid]
      linarith
    have hderivI : forall z, z ∈ Icc theta0 theta ->
        HasDerivAt h (h1 z) z := by
      intro z hz
      exact hderiv z (by simpa [uIcc_of_le horder] using hz)
    have hderiv1I : forall z, z ∈ Icc theta0 theta ->
        HasDerivAt h1 (h2 z) z := by
      intro z hz
      exact hderiv1 z (by simpa [uIcc_of_le horder] using hz)
    have hcurvatureI : forall z, z ∈ Icc theta0 theta ->
        kappa <= h2 z := by
      intro z hz
      exact hcurvatureLower z (by simpa [uIcc_of_le horder] using hz)
    have hfirstGrowth : forall z, z ∈ Icc theta0 theta ->
        kappa * (z - theta0) <= h1 z := by
      intro z hz
      have hpathSubset : Icc theta0 z ⊆ Icc theta0 theta :=
        Icc_subset_Icc le_rfl hz.2
      have hgrowth := mul_interval_length_le_function_sub_of_deriv_lower
        h1 h2 hz.1
        (fun w hw => hderiv1I w (hpathSubset hw))
        (fun w hw => hcurvatureI w (hpathSubset hw))
      simpa [hcritical] using hgrowth
    have hfirstNonneg : forall z, z ∈ Icc theta0 mid ->
        0 <= h1 z := by
      intro z hz
      have hzFull : z ∈ Icc theta0 theta :=
        ⟨hz.1, hz.2.trans hmidtheta⟩
      exact (mul_nonneg hkappa (sub_nonneg.2 hz.1)).trans
        (hfirstGrowth z hzFull)
    have hbase := mul_interval_length_le_function_sub_of_deriv_lower
      h h1 htheta0mid
      (fun z hz => hderivI z ⟨hz.1, hz.2.trans hmidtheta⟩)
      (fun z hz => hfirstNonneg z hz)
    have hfarDerivative : forall z, z ∈ Icc mid theta ->
        kappa * (mid - theta0) <= h1 z := by
      intro z hz
      have hzFull : z ∈ Icc theta0 theta :=
        ⟨htheta0mid.trans hz.1, hz.2⟩
      have hdistance : mid - theta0 <= z - theta0 :=
        sub_le_sub_right hz.1 theta0
      exact (mul_le_mul_of_nonneg_left hdistance hkappa).trans
        (hfirstGrowth z hzFull)
    have hfar := mul_interval_length_le_function_sub_of_deriv_lower
      h h1 hmidtheta
      (fun z hz => hderivI z ⟨htheta0mid.trans hz.1, hz.2⟩)
      (fun z hz => hfarDerivative z hz)
    have hidentity :
        (kappa / 4) * |theta - theta0| ^ 2 =
          (kappa * (mid - theta0)) * (theta - mid) := by
      rw [abs_of_nonneg (sub_nonneg.2 horder)]
      dsimp [mid]
      ring
    rw [hidentity]
    nlinarith
  · let mid : Real := (theta + theta0) / 2
    have hthetamid : theta <= mid := by
      dsimp [mid]
      linarith
    have hmidtheta0 : mid <= theta0 := by
      dsimp [mid]
      linarith
    have hderivI : forall z, z ∈ Icc theta theta0 ->
        HasDerivAt h (h1 z) z := by
      intro z hz
      exact hderiv z (by simpa [uIcc_of_ge horder] using hz)
    have hderiv1I : forall z, z ∈ Icc theta theta0 ->
        HasDerivAt h1 (h2 z) z := by
      intro z hz
      exact hderiv1 z (by simpa [uIcc_of_ge horder] using hz)
    have hcurvatureI : forall z, z ∈ Icc theta theta0 ->
        kappa <= h2 z := by
      intro z hz
      exact hcurvatureLower z (by simpa [uIcc_of_ge horder] using hz)
    have hfirstGrowth : forall z, z ∈ Icc theta theta0 ->
        kappa * (theta0 - z) <= -h1 z := by
      intro z hz
      have hpathSubset : Icc z theta0 ⊆ Icc theta theta0 :=
        Icc_subset_Icc hz.1 le_rfl
      have hgrowth := mul_interval_length_le_function_sub_of_deriv_lower
        h1 h2 hz.2
        (fun w hw => hderiv1I w (hpathSubset hw))
        (fun w hw => hcurvatureI w (hpathSubset hw))
      rw [hcritical, zero_sub] at hgrowth
      exact hgrowth
    have hfirstNonnegNeg : forall z, z ∈ Icc mid theta0 ->
        0 <= -h1 z := by
      intro z hz
      have hzFull : z ∈ Icc theta theta0 :=
        ⟨hthetamid.trans hz.1, hz.2⟩
      exact (mul_nonneg hkappa (sub_nonneg.2 hz.2)).trans
        (hfirstGrowth z hzFull)
    have hbase := mul_interval_length_le_function_sub_of_deriv_lower
      (-h) (-h1) hmidtheta0
      (fun z hz => (hderivI z ⟨hthetamid.trans hz.1, hz.2⟩).neg)
      (fun z hz => hfirstNonnegNeg z hz)
    have hfarDerivative : forall z, z ∈ Icc theta mid ->
        kappa * (theta0 - mid) <= -h1 z := by
      intro z hz
      have hzFull : z ∈ Icc theta theta0 :=
        ⟨hz.1, hz.2.trans hmidtheta0⟩
      have hdistance : theta0 - mid <= theta0 - z :=
        sub_le_sub_left hz.2 theta0
      exact (mul_le_mul_of_nonneg_left hdistance hkappa).trans
        (hfirstGrowth z hzFull)
    have hfar := mul_interval_length_le_function_sub_of_deriv_lower
      (-h) (-h1) hthetamid
      (fun z hz => (hderivI z ⟨hz.1, hz.2.trans hmidtheta0⟩).neg)
      (fun z hz => hfarDerivative z hz)
    have hidentity :
        (kappa / 4) * |theta - theta0| ^ 2 =
          (kappa * (theta0 - mid)) * (mid - theta) := by
      rw [abs_of_nonpos (sub_nonpos.2 horder)]
      dsimp [mid]
      ring
    rw [hidentity]
    change 0 * (theta0 - mid) <= (-h) theta0 - (-h) mid at hbase
    change (kappa * (theta0 - mid)) * (mid - theta) <=
      (-h) mid - (-h) theta at hfar
    simp only [Pi.neg_apply, zero_mul] at hbase hfar
    nlinarith

/-- Orientation-independent quadratic separation.  Curvature continuity
produces its sign internally. -/
theorem abs_curvature_lower_critical_forces_abs_value_sub_lower
    (h h1 h2 : Real -> Real) {theta0 theta kappa : Real}
    (hkappa : 0 < kappa) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 [[theta0, theta]])
    (hcurvatureLower : forall z, z ∈ [[theta0, theta]] ->
      kappa <= |h2 z|) :
    (kappa / 4) * |theta - theta0| ^ 2 <=
      |h theta - h theta0| := by
  rcases continuous_fixed_sign_of_abs_lower_on_uIcc
      h2 hkappa h2Continuous hcurvatureLower with hpositive | hnegative
  · exact (curvature_lower_critical_forces_value_sub_lower
      h h1 h2 (le_of_lt hkappa) hcritical hderiv hderiv1 hpositive).trans
        (le_abs_self _)
  · have hgrowth := curvature_lower_critical_forces_value_sub_lower
      (-h) (-h1) (-h2) (le_of_lt hkappa)
      (show (-h1) theta0 = 0 by
        change -h1 theta0 = 0
        rw [hcritical, neg_zero])
      (fun z hz => (hderiv z hz).neg)
      (fun z hz => (hderiv1 z hz).neg)
      (fun z hz => by
        change kappa <= -h2 z
        linarith [hnegative z hz])
    have hgrowth' : (kappa / 4) * |theta - theta0| ^ 2 <=
        -(h theta - h theta0) := by
      change (kappa / 4) * |theta - theta0| ^ 2 <=
        -h theta - (-h theta0) at hgrowth
      linarith
    exact hgrowth'.trans (neg_le_abs _)

/-- Reverse triangle inequality converts quadratic separation into an
explicit pointwise lower bound away from the critical point. -/
theorem value_lower_away_from_criticalPoint
    (h h1 h2 : Real -> Real)
    {theta0 theta kappa Delta : Real}
    (hkappa : 0 < kappa) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 [[theta0, theta]])
    (hcurvatureLower : forall z, z ∈ [[theta0, theta]] ->
      kappa <= |h2 z|)
    (hcriticalValue : |h theta0| <= Delta) :
    (kappa / 4) * |theta - theta0| ^ 2 - Delta <= |h theta| := by
  have hgrowth := abs_curvature_lower_critical_forces_abs_value_sub_lower
    h h1 h2 hkappa hcritical hderiv hderiv1
    h2Continuous hcurvatureLower
  have htriangle : |h theta - h theta0| <=
      |h theta| + |h theta0| := by
    calc
      |h theta - h theta0| = |h theta + (-h theta0)| := by ring_nf
      _ <= |h theta| + |-h theta0| := abs_add_le _ _
      _ = |h theta| + |h theta0| := by rw [abs_neg]
  linarith

#print axioms curvature_lower_critical_forces_value_sub_lower
#print axioms abs_curvature_lower_critical_forces_abs_value_sub_lower
#print axioms value_lower_away_from_criticalPoint

end FamilyStickyCinematicL32CriticalValueLowerV1
