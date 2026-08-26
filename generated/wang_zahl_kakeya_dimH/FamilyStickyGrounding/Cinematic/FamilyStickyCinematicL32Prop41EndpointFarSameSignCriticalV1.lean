import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalValueLowerV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Interval

namespace FamilyStickyCinematicL32Prop41EndpointFarSameSignCriticalV1

open FamilyStickyCinematicL32SublevelIntervalV1
open FamilyStickyCinematicL32CriticalValueLowerV1

/-!
# Far same-sign endpoints from a sharp critical point

A continuous second derivative bounded away from zero has one fixed sign.
Consequently a critical point is a quantitative minimum or maximum.  If it
has room `m` to both endpoints and its value plus the shift scale lies below
the quadratic growth `(kappa / 4) * m^2`, then both endpoint values lie
beyond the shift scale and have the same strict sign.

The endpoint sign is derived from curvature; it is not an input.
-/

/-- A sharp critical point with two-sided parameter room produces endpoint
values farther than `s` from zero and with the same strict sign. -/
theorem endpoint_far_same_sign_of_critical_sharp_curvature
    (h h1 h2 : Real -> Real) {A B theta0 kappa m s : Real}
    (hAB : A < B) (htheta0 : theta0 ∈ Icc A B)
    (hkappa : 0 < kappa) (hm : 0 < m) (hs : 0 < s)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|)
    (hmLeft : m <= theta0 - A) (hmRight : m <= B - theta0)
    (hcriticalGap :
      |h theta0| + s < (kappa / 4) * m ^ 2) :
    s < |h A| ∧ s < |h B| ∧ 0 < h A * h B := by
  have hATheta : A <= theta0 := htheta0.1
  have hThetaB : theta0 <= B := htheta0.2
  have hpathA : [[theta0, A]] ⊆ Icc A B := by
    intro z hz
    have hz' : z ∈ Icc A theta0 := by
      simpa [uIcc_of_ge hATheta] using hz
    exact ⟨hz'.1, hz'.2.trans hThetaB⟩
  have hpathB : [[theta0, B]] ⊆ Icc A B := by
    intro z hz
    have hz' : z ∈ Icc theta0 B := by
      simpa [uIcc_of_le hThetaB] using hz
    exact ⟨hATheta.trans hz'.1, hz'.2⟩
  have hmAbsA : m <= |A - theta0| := by
    rw [abs_of_nonpos (sub_nonpos.mpr hATheta)]
    linarith
  have hmAbsB : m <= |B - theta0| := by
    rw [abs_of_nonneg (sub_nonneg.mpr hThetaB)]
    exact hmRight
  have hmSqA : m ^ 2 <= |A - theta0| ^ 2 :=
    (sq_le_sq₀ hm.le (abs_nonneg _)).mpr hmAbsA
  have hmSqB : m ^ 2 <= |B - theta0| ^ 2 :=
    (sq_le_sq₀ hm.le (abs_nonneg _)).mpr hmAbsB
  have hkappaQuarter : 0 <= kappa / 4 := by positivity
  have hquadA : (kappa / 4) * m ^ 2 <=
      (kappa / 4) * |A - theta0| ^ 2 :=
    mul_le_mul_of_nonneg_left hmSqA hkappaQuarter
  have hquadB : (kappa / 4) * m ^ 2 <=
      (kappa / 4) * |B - theta0| ^ 2 :=
    mul_le_mul_of_nonneg_left hmSqB hkappaQuarter
  have hvalueA := value_lower_away_from_criticalPoint
    h h1 h2 (theta0 := theta0) (theta := A) (kappa := kappa)
      (Delta := |h theta0|) hkappa hcritical
      (fun z hz => hderiv z (hpathA hz))
      (fun z hz => hderiv1 z (hpathA hz))
      (h2Continuous.mono hpathA)
      (fun z hz => hcurvatureLower z (hpathA hz)) le_rfl
  have hvalueB := value_lower_away_from_criticalPoint
    h h1 h2 (theta0 := theta0) (theta := B) (kappa := kappa)
      (Delta := |h theta0|) hkappa hcritical
      (fun z hz => hderiv z (hpathB hz))
      (fun z hz => hderiv1 z (hpathB hz))
      (h2Continuous.mono hpathB)
      (fun z hz => hcurvatureLower z (hpathB hz)) le_rfl
  have hfarA : s < |h A| := by
    linarith
  have hfarB : s < |h B| := by
    linarith
  have hcurvatureSign := continuous_fixed_sign_of_abs_lower_on_Icc
    h2 hAB.le hkappa h2Continuous hcurvatureLower
  rcases hcurvatureSign with hpositive | hnegative
  · have hgrowthA := curvature_lower_critical_forces_value_sub_lower
      h h1 h2 (theta0 := theta0) (theta := A) (kappa := kappa)
        hkappa.le hcritical
        (fun z hz => hderiv z (hpathA hz))
        (fun z hz => hderiv1 z (hpathA hz))
        (fun z hz => hpositive z (hpathA hz))
    have hgrowthB := curvature_lower_critical_forces_value_sub_lower
      h h1 h2 (theta0 := theta0) (theta := B) (kappa := kappa)
        hkappa.le hcritical
        (fun z hz => hderiv z (hpathB hz))
        (fun z hz => hderiv1 z (hpathB hz))
        (fun z hz => hpositive z (hpathB hz))
    have hApos : 0 < h A := by
      nlinarith [neg_abs_le (h theta0)]
    have hBpos : 0 < h B := by
      nlinarith [neg_abs_le (h theta0)]
    exact ⟨hfarA, hfarB, mul_pos hApos hBpos⟩
  · have hgrowthA := curvature_lower_critical_forces_value_sub_lower
      (-h) (-h1) (-h2) (theta0 := theta0) (theta := A)
        (kappa := kappa) hkappa.le
        (show (-h1) theta0 = 0 by simp [hcritical])
        (fun z hz => (hderiv z (hpathA hz)).neg)
        (fun z hz => (hderiv1 z (hpathA hz)).neg)
        (fun z hz => by
          change kappa <= -h2 z
          linarith [hnegative z (hpathA hz)])
    have hgrowthB := curvature_lower_critical_forces_value_sub_lower
      (-h) (-h1) (-h2) (theta0 := theta0) (theta := B)
        (kappa := kappa) hkappa.le
        (show (-h1) theta0 = 0 by simp [hcritical])
        (fun z hz => (hderiv z (hpathB hz)).neg)
        (fun z hz => (hderiv1 z (hpathB hz)).neg)
        (fun z hz => by
          change kappa <= -h2 z
          linarith [hnegative z (hpathB hz)])
    have hAneg : h A < 0 := by
      change (kappa / 4) * |A - theta0| ^ 2 <=
        -h A - -h theta0 at hgrowthA
      nlinarith [le_abs_self (h theta0)]
    have hBneg : h B < 0 := by
      change (kappa / 4) * |B - theta0| ^ 2 <=
        -h B - -h theta0 at hgrowthB
      nlinarith [le_abs_self (h theta0)]
    exact ⟨hfarA, hfarB, mul_pos_of_neg_of_neg hAneg hBneg⟩

#print axioms endpoint_far_same_sign_of_critical_sharp_curvature

end FamilyStickyCinematicL32Prop41EndpointFarSameSignCriticalV1
