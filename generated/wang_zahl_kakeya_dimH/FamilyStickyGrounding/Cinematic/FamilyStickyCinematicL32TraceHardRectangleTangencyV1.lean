import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelComponentV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32HardRectangleTangencyV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceHardRectangleTangencyV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceSublevelComponentV1
open FamilyStickyCinematicL32HardRectangleTangencyV1

/-!
# Hard rectangle tangency for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.9,
hard regime, specialized to the trace in Wang--Zahl Lemma 7.3.
-/

/-- Actual-trace form of the hard rectangle-width tangency product bound. -/
theorem trace_hard_rectangle_width_forces_critical_product
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B theta0 x y delta rho Delta M kappa : Real}
    (hxy : x <= y)
    (htheta0Domain : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hM : 0 < M) (hkappa : 0 < kappa) (hgap : delta < Delta)
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
    (Delta - delta) * kappa ^ 2 <= 4 * delta * M * rho := by
  have hlength :=
    trace_sublevel_component_length_le_of_critical_curvature
      f f1 f2 da db dd hxy htheta0Domain hxDomain hyDomain
      hM hkappa hgap hcritical hfDeriv hf1Deriv hf2Continuous
      hcurvatureUpper hcurvatureLower hcenter hcomponentSublevel
  exact hard_rectangle_product_of_length_bounds
    hdelta hrho hM hkappa hgap hrectangleWidth hlength

#print axioms trace_hard_rectangle_width_forces_critical_product

end FamilyStickyCinematicL32TraceHardRectangleTangencyV1
