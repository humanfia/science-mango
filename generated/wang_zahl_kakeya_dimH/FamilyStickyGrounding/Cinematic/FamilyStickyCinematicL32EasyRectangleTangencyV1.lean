import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32EasySublevelV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32EasyRectangleTangencyV1

open FamilyStickyCinematicL32EasySublevelV1

/-!
# Easy-regime rectangle tangency

Provenance: the derivative-separated case of Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemmas 3.8(2b) and 3.9.

The genuine first-derivative lower bound gives the component length estimate.
Comparing this with the square-root rectangle width and eliminating the first
derivative scale yields the tangency product, with all constants explicit.
-/

/-- Pure positive square-root algebra for the derivative-separated regime. -/
theorem easy_rectangle_product_of_length_bounds
    {delta rho Delta m c K T ell : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hm : 0 < m) (_hc : 0 < c) (hT : 0 < T) (hK : 0 <= K)
    (hparameterScale : Delta + delta <= K * T)
    (hfirstJetScale : c * T <= m)
    (hrectangle : Real.sqrt (delta / rho) <= ell)
    (hlength : ell <= 2 * delta / m) :
    c ^ 2 * (Delta + delta) * T <= 4 * K * delta * rho := by
  have hwidthRatio : 0 <= delta / rho :=
    div_nonneg (le_of_lt hdelta) (le_of_lt hrho)
  have hcompare : Real.sqrt (delta / rho) <= 2 * delta / m :=
    hrectangle.trans hlength
  have hproduct : Real.sqrt (delta / rho) * m <= 2 * delta :=
    (le_div_iff₀ hm).1 hcompare
  have hleftNonneg : 0 <= Real.sqrt (delta / rho) * m :=
    mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hm)
  have hrightNonneg : 0 <= 2 * delta := by positivity
  have hproductSq :
      (Real.sqrt (delta / rho) * m) ^ 2 <= (2 * delta) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hproduct
  rw [mul_pow, Real.sq_sqrt hwidthRatio] at hproductSq
  have hdivRho : (delta * m ^ 2) / rho <= (2 * delta) ^ 2 := by
    convert hproductSq using 1; ring
  have hmulRho : delta * m ^ 2 <= (2 * delta) ^ 2 * rho :=
    (div_le_iff₀ hrho).1 hdivRho
  have hmSq : m ^ 2 <= 4 * delta * rho := by
    apply le_of_mul_le_mul_left _ hdelta
    calc
      delta * m ^ 2 <= (2 * delta) ^ 2 * rho := hmulRho
      _ = delta * (4 * delta * rho) := by ring
  have hfirstJetNonneg : 0 <= c * T := by positivity
  have hfirstJetSq : (c * T) ^ 2 <= m ^ 2 :=
    (sq_le_sq₀ hfirstJetNonneg (le_of_lt hm)).2 hfirstJetScale
  have hcoefficientNonneg : 0 <= c ^ 2 * T := by positivity
  calc
    c ^ 2 * (Delta + delta) * T =
        (c ^ 2 * T) * (Delta + delta) := by ring
    _ <= (c ^ 2 * T) * (K * T) :=
      mul_le_mul_of_nonneg_left hparameterScale hcoefficientNonneg
    _ = K * (c * T) ^ 2 := by ring
    _ <= K * m ^ 2 := mul_le_mul_of_nonneg_left hfirstJetSq hK
    _ <= K * (4 * delta * rho) := mul_le_mul_of_nonneg_left hmSq hK
    _ = 4 * K * delta * rho := by ring

/-- Callback-free easy regime: the proved derivative-separated sublevel
theorem supplies the length estimate before the rectangle comparison. -/
theorem easy_rectangle_width_forces_tangency_product
    (h h1 : Real -> Real)
    {A B x y delta rho Delta m c K T : Real}
    (hxy : x <= y)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hm : 0 < m) (hc : 0 < c) (hT : 0 < T) (hK : 0 <= K)
    (hparameterScale : Delta + delta <= K * T)
    (hfirstJetScale : c * T <= m)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (h1Continuous : ContinuousOn h1 (Icc A B))
    (hfirstLower : forall z, z ∈ Icc A B -> m <= |h1 z|)
    (hcomponentSublevel : forall z, z ∈ Icc x y -> |h z| <= delta)
    (hrectangleWidth : Real.sqrt (delta / rho) <= y - x) :
    c ^ 2 * (Delta + delta) * T <= 4 * K * delta * rho := by
  have hlength := easy_sublevel_interval_length_le
    h h1 hxy hxDomain hyDomain hm hderiv h1Continuous
    hfirstLower hcomponentSublevel
  exact easy_rectangle_product_of_length_bounds
    hdelta hrho hm hc hT hK hparameterScale hfirstJetScale
    hrectangleWidth hlength

#print axioms easy_rectangle_product_of_length_bounds
#print axioms easy_rectangle_width_forces_tangency_product

end FamilyStickyCinematicL32EasyRectangleTangencyV1
