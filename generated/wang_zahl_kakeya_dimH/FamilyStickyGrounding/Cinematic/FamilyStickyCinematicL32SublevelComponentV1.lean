import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointGrowthV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32SublevelComponentV1

open FamilyStickyCinematicL32SublevelIntervalV1
open FamilyStickyCinematicL32CriticalPointGrowthV1

/-!
# Explicit length of a cinematic sublevel component

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(2b), equations (3.5)--(3.6).

This module composes the independently verified critical-point square-root
growth producer with the independently verified one-dimensional sublevel
interval bound.  On an ambient interval with

`kappa <= |h''| <= M`, `h'(theta0) = 0`, and
`Delta <= |h(theta0)|`,

each interval contained in `{theta : |h theta| <= delta}` has the completely
explicit length bound

`2 * delta / (kappa * sqrt ((Delta - delta) / M))`

whenever `delta < Delta`.  The length conclusion is produced, never assumed.
-/

/-- Explicit hard-subcase component bound from PYZ Lemma 3.8(2b). -/
theorem sublevel_component_length_le_of_critical_curvature
    (h h1 h2 : Real -> Real)
    {A B theta0 x y M kappa Delta delta : Real}
    (hxy : x <= y)
    (htheta0Domain : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hM : 0 < M) (hkappa : 0 < kappa) (hgap : delta < Delta)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureUpper : forall z, z ∈ Icc A B -> |h2 z| <= M)
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|)
    (hcenter : Delta <= |h theta0|)
    (hcomponentSublevel : forall z, z ∈ Icc x y -> |h z| <= delta) :
    y - x <=
      2 * delta / (kappa * Real.sqrt ((Delta - delta) / M)) := by
  have hcomponentSubset : Icc x y ⊆ Icc A B :=
    Icc_subset_Icc hxDomain.1 hyDomain.2
  have hscalePos :
      0 < kappa * Real.sqrt ((Delta - delta) / M) :=
    sqrt_first_derivative_scale_pos hM hkappa hgap
  have hfirstLower : forall z, z ∈ Icc x y ->
      kappa * Real.sqrt ((Delta - delta) / M) <= |h1 z| := by
    intro z hz
    have hzDomain : z ∈ Icc A B := hcomponentSubset hz
    have hpathSubset : [[theta0, z]] ⊆ Icc A B :=
      uIcc_subset_Icc htheta0Domain hzDomain
    exact critical_sublevel_first_derivative_sqrt_lower
      h h1 h2 hM hkappa hcritical
      (fun w hw => hderiv w (hpathSubset hw))
      (fun w hw => hderiv1 w (hpathSubset hw))
      (h2Continuous.mono hpathSubset)
      (fun w hw => hcurvatureUpper w (hpathSubset hw))
      (fun w hw => hcurvatureLower w (hpathSubset hw))
      hcenter (hcomponentSublevel z hz)
  apply sublevel_interval_length_le_of_abs_deriv_lower
    h h1 hxy hscalePos
  · exact hcomponentSublevel x (left_mem_Icc.2 hxy)
  · exact hcomponentSublevel y (right_mem_Icc.2 hxy)
  · intro z hz
    exact hderiv z (hcomponentSubset hz)
  · exact HasDerivAt.continuousOn
      (fun z hz => hderiv1 z (hcomponentSubset hz))
  · exact hfirstLower

#print axioms sublevel_component_length_le_of_critical_curvature

end FamilyStickyCinematicL32SublevelComponentV1
