import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceHardRectangleTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32HardScaleComparisonV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceHardTangencyProductV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceHardRectangleTangencyV1
open FamilyStickyCinematicL32HardScaleComparisonV1

/-!
# Hard-regime tangency product for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.9,
hard regime, specialized to the trace in Wang--Zahl Lemma 7.3.
-/

/-- The actual trace calculus, rectangle-width bound, and curvature-scale
comparability jointly imply the standard hard-regime tangency product. -/
theorem trace_hard_rectangle_width_forces_tangency_product
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B theta0 x y delta rho Delta M kappa c C T : Real}
    (hxy : x <= y)
    (htheta0Domain : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hT : 0 < T) (hc : 0 < c)
    (hsmall : 3 * delta <= Delta)
    (hcurvatureLowerScale : c * T <= kappa)
    (hcurvatureUpperScale : M <= C * T)
    (hcritical : traceFirstDerivative f f1 db dd theta0 = 0)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcurvatureUpper : forall z, z ∈ Icc A B ->
      |traceSecondDerivative f1 f2 db dd z| <= M)
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z|)
    (hcenter : Delta <= |traceFunction f da db dd theta0|)
    (hcomponentSublevel : forall z, z ∈ Icc x y ->
      |traceFunction f da db dd z| <= delta)
    (hrectangleWidth : Real.sqrt (delta / rho) <= y - x) :
    c ^ 2 * (Delta + delta) * T <= 8 * C * delta * rho := by
  have hgap : delta < Delta := by
    nlinarith
  have hcriticalProduct :=
    trace_hard_rectangle_width_forces_critical_product
      f f1 f2 da db dd hxy htheta0Domain hxDomain hyDomain
      hdelta hrho hM hkappa hgap hcritical
      hfDeriv hf1Deriv hf2Continuous
      hcurvatureUpper hcurvatureLower hcenter
      hcomponentSublevel hrectangleWidth
  exact hard_critical_product_to_tangency_product
    hdelta hrho hT hc hcurvatureLowerScale hcurvatureUpperScale
    hcriticalProduct hsmall

#print axioms trace_hard_rectangle_width_forces_tangency_product

end FamilyStickyCinematicL32TraceHardTangencyProductV1
