import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelLocalizationV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32MediumRectangleTangencyV1

open FamilyStickyCinematicL32SublevelLocalizationV1

/-!
# Medium-regime rectangle tangency

Provenance: the subcase `delta` comparable to `Delta` in
Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemmas 3.8(2a)--(2b) and 3.9.

Localization of both endpoints gives a component span bound.  Comparing it
with the rectangle width and using `Delta <= K*delta` gives the desired
tangency product, with every constant explicit.
-/

/-- Two sublevel endpoints localized near the same critical point span at
most four times the square-root localization radius. -/
theorem sublevel_interval_length_le_four_sqrt
    (h h1 h2 : Real -> Real)
    {A B theta0 x y kappa Delta delta : Real}
    (_hxy : x <= y)
    (htheta0 : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hkappa : 0 < kappa) (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|)
    (hcriticalValue : |h theta0| <= Delta)
    (hxSublevel : |h x| <= delta) (hySublevel : |h y| <= delta) :
    y - x <= 4 * Real.sqrt ((Delta + delta) / kappa) := by
  have hxLocalized := sublevel_point_localized_near_criticalPoint
    h h1 h2 hkappa hcritical
    (fun z hz => hderiv z
      (uIcc_subset_Icc htheta0 hxDomain hz))
    (fun z hz => hderiv1 z
      (uIcc_subset_Icc htheta0 hxDomain hz))
    (h2Continuous.mono (uIcc_subset_Icc htheta0 hxDomain))
    (fun z hz => hcurvatureLower z
      (uIcc_subset_Icc htheta0 hxDomain hz))
    hcriticalValue hxSublevel
  have hyLocalized := sublevel_point_localized_near_criticalPoint
    h h1 h2 hkappa hcritical
    (fun z hz => hderiv z
      (uIcc_subset_Icc htheta0 hyDomain hz))
    (fun z hz => hderiv1 z
      (uIcc_subset_Icc htheta0 hyDomain hz))
    (h2Continuous.mono (uIcc_subset_Icc htheta0 hyDomain))
    (fun z hz => hcurvatureLower z
      (uIcc_subset_Icc htheta0 hyDomain hz))
    hcriticalValue hySublevel
  have hspan : y - x <= |y - theta0| + |x - theta0| := by
    nlinarith [le_abs_self (y - theta0), neg_le_abs (x - theta0)]
  calc
    y - x <= |y - theta0| + |x - theta0| := hspan
    _ <= 2 * Real.sqrt ((Delta + delta) / kappa) +
        2 * Real.sqrt ((Delta + delta) / kappa) :=
      add_le_add hyLocalized hxLocalized
    _ = 4 * Real.sqrt ((Delta + delta) / kappa) := by ring

/-- Pure medium-regime square-root comparison. -/
theorem medium_rectangle_product_of_length_bounds
    {delta rho Delta kappa c K T ell : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hDelta : 0 <= Delta) (hkappa : 0 < kappa)
    (_hc : 0 < c) (_hT : 0 < T) (hK : 0 <= K)
    (hDeltaComparable : Delta <= K * delta)
    (hcurvatureScale : c * T <= kappa)
    (hrectangle : Real.sqrt (delta / rho) <= ell)
    (hlength : ell <= 4 * Real.sqrt ((Delta + delta) / kappa)) :
    c * (Delta + delta) * T <=
      16 * (K + 1) ^ 2 * delta * rho := by
  have hwidthRatio : 0 <= delta / rho :=
    div_nonneg (le_of_lt hdelta) (le_of_lt hrho)
  have hsum : 0 <= Delta + delta :=
    add_nonneg hDelta (le_of_lt hdelta)
  have hsumRatio : 0 <= (Delta + delta) / kappa :=
    div_nonneg hsum (le_of_lt hkappa)
  have hcompare : Real.sqrt (delta / rho) <=
      4 * Real.sqrt ((Delta + delta) / kappa) :=
    hrectangle.trans hlength
  have hleftNonneg := Real.sqrt_nonneg (delta / rho)
  have hrightNonneg :
      0 <= 4 * Real.sqrt ((Delta + delta) / kappa) := by positivity
  have hsquare : delta / rho <=
      16 * ((Delta + delta) / kappa) := by
    have hsquareRaw := (sq_le_sq₀ hleftNonneg hrightNonneg).2 hcompare
    rw [Real.sq_sqrt hwidthRatio, mul_pow,
      Real.sq_sqrt hsumRatio] at hsquareRaw
    nlinarith
  have hdeltaKappa : delta * kappa <=
      16 * (Delta + delta) * rho := by
    apply (div_le_div_iff₀ hrho hkappa).1
    calc
      delta / rho <= 16 * ((Delta + delta) / kappa) := hsquare
      _ = (16 * (Delta + delta)) / kappa := by ring
  have hsumComparable : Delta + delta <= (K + 1) * delta := by
    nlinarith
  have hKoneNonneg : 0 <= K + 1 := by linarith
  have hkappaNonneg : 0 <= kappa := le_of_lt hkappa
  have hsumKappa : (Delta + delta) * kappa <=
      16 * (K + 1) ^ 2 * delta * rho := by
    calc
      (Delta + delta) * kappa <=
          ((K + 1) * delta) * kappa :=
        mul_le_mul_of_nonneg_right hsumComparable hkappaNonneg
      _ = (K + 1) * (delta * kappa) := by ring
      _ <= (K + 1) * (16 * (Delta + delta) * rho) :=
        mul_le_mul_of_nonneg_left hdeltaKappa hKoneNonneg
      _ <= (K + 1) *
          (16 * ((K + 1) * delta) * rho) := by
        gcongr
      _ = 16 * (K + 1) ^ 2 * delta * rho := by ring
  calc
    c * (Delta + delta) * T =
        (Delta + delta) * (c * T) := by ring
    _ <= (Delta + delta) * kappa :=
      mul_le_mul_of_nonneg_left hcurvatureScale hsum
    _ <= 16 * (K + 1) ^ 2 * delta * rho := hsumKappa

/-- Callback-free medium regime: actual critical localization supplies the
length estimate before the rectangle comparison. -/
theorem medium_rectangle_width_forces_tangency_product
    (h h1 h2 : Real -> Real)
    {A B theta0 x y delta rho Delta kappa c K T : Real}
    (hxy : x <= y)
    (htheta0 : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hkappa : 0 < kappa) (hc : 0 < c) (hT : 0 < T) (hK : 0 <= K)
    (hDeltaComparable : Delta <= K * delta)
    (hcurvatureScale : c * T <= kappa)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|)
    (hcriticalValue : |h theta0| <= Delta)
    (hxSublevel : |h x| <= delta) (hySublevel : |h y| <= delta)
    (hrectangleWidth : Real.sqrt (delta / rho) <= y - x) :
    c * (Delta + delta) * T <=
      16 * (K + 1) ^ 2 * delta * rho := by
  have hDelta : 0 <= Delta :=
    (abs_nonneg (h theta0)).trans hcriticalValue
  have hlength := sublevel_interval_length_le_four_sqrt
    h h1 h2 hxy htheta0 hxDomain hyDomain hkappa hcritical
    hderiv hderiv1 h2Continuous hcurvatureLower
    hcriticalValue hxSublevel hySublevel
  exact medium_rectangle_product_of_length_bounds
    hdelta hrho hDelta hkappa hc hT hK hDeltaComparable
    hcurvatureScale hrectangleWidth hlength

#print axioms sublevel_interval_length_le_four_sqrt
#print axioms medium_rectangle_product_of_length_bounds
#print axioms medium_rectangle_width_forces_tangency_product

end FamilyStickyCinematicL32MediumRectangleTangencyV1
