import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointGrowthV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32CriticalValueTransferV1

open FamilyStickyCinematicL32CriticalPointGrowthV1

/-!
# Transferring the anchor value to the critical point

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1a), in the estimate `|h(theta0)| \lesssim Delta`.

The paper first locates the critical point near the minimizing parameter.
Here the quantitative calculation is isolated with no hidden constants:
if the anchor slope is at most `eta`, the curvature lies between `kappa`
and `M`, and `h'(theta0)=0`, then

`|theta0 - thetaDelta| <= eta / kappa`

and

`|h(theta0)| <= Delta + M * (eta / kappa)^2`.
-/

/-- Nonvanishing curvature controls the distance from a small-slope anchor
to an actual critical point. -/
theorem criticalPoint_distance_le_anchorSlope_div_curvature
    (h1 h2 : Real -> Real) {theta0 thetaDelta eta kappa : Real}
    (hkappa : 0 < kappa) (hcritical : h1 theta0 = 0)
    (hderiv1 : forall z, z ∈ [[theta0, thetaDelta]] ->
      HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 [[theta0, thetaDelta]])
    (hcurvatureLower : forall z, z ∈ [[theta0, thetaDelta]] ->
      kappa <= |h2 z|)
    (hanchorSlope : |h1 thetaDelta| <= eta) :
    |thetaDelta - theta0| <= eta / kappa := by
  have hgrowth := abs_curvature_lower_forces_first_derivative_growth
    h1 h2 hkappa hcritical hderiv1 h2Continuous hcurvatureLower
  apply (le_div_iff₀ hkappa).2
  nlinarith

/-- Explicit critical-value transfer with quadratic error. -/
theorem criticalPoint_value_le_anchorValue_add_quadratic_error
    (h h1 h2 : Real -> Real)
    {theta0 thetaDelta M kappa Delta eta : Real}
    (hM : 0 <= M) (hkappa : 0 < kappa)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ [[theta0, thetaDelta]] ->
      HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ [[theta0, thetaDelta]] ->
      HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 [[theta0, thetaDelta]])
    (hcurvatureUpper : forall z, z ∈ [[theta0, thetaDelta]] ->
      |h2 z| <= M)
    (hcurvatureLower : forall z, z ∈ [[theta0, thetaDelta]] ->
      kappa <= |h2 z|)
    (hanchorValue : |h thetaDelta| <= Delta)
    (hanchorSlope : |h1 thetaDelta| <= eta) :
    |h theta0| <= Delta + M * (eta / kappa) ^ 2 := by
  have heta : 0 <= eta := (abs_nonneg (h1 thetaDelta)).trans hanchorSlope
  have hratio : 0 <= eta / kappa :=
    div_nonneg heta (le_of_lt hkappa)
  have hdistance := criticalPoint_distance_le_anchorSlope_div_curvature
    h1 h2 hkappa hcritical hderiv1 h2Continuous
    hcurvatureLower hanchorSlope
  have hdistanceSq : |thetaDelta - theta0| ^ 2 <=
      (eta / kappa) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hratio).2 hdistance
  have hquadratic := abs_value_sub_critical_le_curvature_mul_sq
    h h1 h2 hM hcritical hderiv hderiv1 hcurvatureUpper
  have hscaled : M * |thetaDelta - theta0| ^ 2 <=
      M * (eta / kappa) ^ 2 :=
    mul_le_mul_of_nonneg_left hdistanceSq hM
  calc
    |h theta0| = |(h theta0 - h thetaDelta) + h thetaDelta| := by
      ring_nf
    _ <= |h theta0 - h thetaDelta| + |h thetaDelta| :=
      abs_add_le _ _
    _ = |h thetaDelta - h theta0| + |h thetaDelta| := by
      rw [abs_sub_comm]
    _ <= M * |thetaDelta - theta0| ^ 2 + Delta :=
      add_le_add hquadratic hanchorValue
    _ <= M * (eta / kappa) ^ 2 + Delta :=
      add_le_add hscaled le_rfl
    _ = Delta + M * (eta / kappa) ^ 2 := by ring

#print axioms criticalPoint_distance_le_anchorSlope_div_curvature
#print axioms criticalPoint_value_le_anchorValue_add_quadratic_error

end FamilyStickyCinematicL32CriticalValueTransferV1
