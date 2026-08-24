import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelComponentV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32HardRectangleTangencyV1

open FamilyStickyCinematicL32SublevelComponentV1

/-!
# Hard-regime rectangle width forces tangency

Provenance: the hard case of Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.9, using Lemma 3.8(2b), equations
(3.5)--(3.6).

The square-root rectangle width and the already proved critical-component
length upper bound are eliminated with all constants explicit.
-/

/-- Pure positive square-root algebra for the hard cinematic regime. -/
theorem hard_rectangle_product_of_length_bounds
    {delta rho Delta M kappa ell : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hM : 0 < M) (hkappa : 0 < kappa) (hgap : delta < Delta)
    (hrectangle : Real.sqrt (delta / rho) <= ell)
    (hcomponent : ell <=
      2 * delta /
        (kappa * Real.sqrt ((Delta - delta) / M))) :
    (Delta - delta) * kappa ^ 2 <= 4 * delta * M * rho := by
  have hwidthRatio : 0 <= delta / rho :=
    div_nonneg (le_of_lt hdelta) (le_of_lt hrho)
  have hgapRatio : 0 <= (Delta - delta) / M :=
    div_nonneg (sub_nonneg.2 (le_of_lt hgap)) (le_of_lt hM)
  have hgapSqrt : 0 < Real.sqrt ((Delta - delta) / M) :=
    Real.sqrt_pos.2 (div_pos (sub_pos.2 hgap) hM)
  have hdenominator :
      0 < kappa * Real.sqrt ((Delta - delta) / M) :=
    mul_pos hkappa hgapSqrt
  have hcompare : Real.sqrt (delta / rho) <=
      2 * delta /
        (kappa * Real.sqrt ((Delta - delta) / M)) :=
    hrectangle.trans hcomponent
  have hproduct :
      Real.sqrt (delta / rho) *
          (kappa * Real.sqrt ((Delta - delta) / M)) <=
        2 * delta :=
    (le_div_iff₀ hdenominator).1 hcompare
  have hleftNonneg : 0 <=
      Real.sqrt (delta / rho) *
        (kappa * Real.sqrt ((Delta - delta) / M)) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (le_of_lt hkappa) (Real.sqrt_nonneg _))
  have hrightNonneg : 0 <= 2 * delta := by positivity
  have hproductSq :
      (Real.sqrt (delta / rho) *
          (kappa * Real.sqrt ((Delta - delta) / M))) ^ 2 <=
        (2 * delta) ^ 2 :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hproduct
  rw [mul_pow, Real.sq_sqrt hwidthRatio, mul_pow,
    Real.sq_sqrt hgapRatio] at hproductSq
  have hdivRho :
      (delta * (kappa ^ 2 * ((Delta - delta) / M))) / rho <=
        (2 * delta) ^ 2 := by
    convert hproductSq using 1; ring
  have hmulRho :
      delta * (kappa ^ 2 * ((Delta - delta) / M)) <=
        (2 * delta) ^ 2 * rho :=
    (div_le_iff₀ hrho).1 hdivRho
  have hdivM :
      (delta * (kappa ^ 2 * (Delta - delta))) / M <=
        (2 * delta) ^ 2 * rho := by
    convert hmulRho using 1; ring
  have hmulM :
      delta * (kappa ^ 2 * (Delta - delta)) <=
        (2 * delta) ^ 2 * rho * M :=
    (div_le_iff₀ hM).1 hdivM
  apply le_of_mul_le_mul_left _ hdelta
  calc
    delta * ((Delta - delta) * kappa ^ 2) =
        delta * (kappa ^ 2 * (Delta - delta)) := by ring
    _ <= (2 * delta) ^ 2 * rho * M := hmulM
    _ = delta * (4 * delta * M * rho) := by ring

/-- Callback-free hard-regime form: the genuine sublevel component theorem
supplies the length upper bound before the square-root elimination. -/
theorem hard_rectangle_width_forces_critical_product
    (h h1 h2 : Real -> Real)
    {A B theta0 x y delta rho Delta M kappa : Real}
    (hxy : x <= y)
    (htheta0Domain : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hM : 0 < M) (hkappa : 0 < kappa) (hgap : delta < Delta)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureUpper : forall z, z ∈ Icc A B -> |h2 z| <= M)
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|)
    (hcenter : Delta <= |h theta0|)
    (hcomponentSublevel : forall z, z ∈ Icc x y -> |h z| <= delta)
    (hrectangleWidth : Real.sqrt (delta / rho) <= y - x) :
    (Delta - delta) * kappa ^ 2 <= 4 * delta * M * rho := by
  have hlength := sublevel_component_length_le_of_critical_curvature
    h h1 h2 hxy htheta0Domain hxDomain hyDomain
    hM hkappa hgap hcritical hderiv hderiv1 h2Continuous
    hcurvatureUpper hcurvatureLower hcenter hcomponentSublevel
  exact hard_rectangle_product_of_length_bounds
    hdelta hrho hM hkappa hgap hrectangleWidth hlength

#print axioms hard_rectangle_product_of_length_bounds
#print axioms hard_rectangle_width_forces_critical_product

end FamilyStickyCinematicL32HardRectangleTangencyV1
