import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelComponentV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32MediumRectangleTangencyV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceMediumRectangleTangencyV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceSublevelComponentV1
open FamilyStickyCinematicL32MediumRectangleTangencyV1

/-!
# Medium-regime tangency product for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.9,
medium regime, specialized to the trace in Wang--Zahl Lemma 7.3.
-/

/-- Actual-trace form of the medium rectangle tangency product. -/
theorem trace_medium_rectangle_width_forces_tangency_product
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B theta0 x y delta rho Delta kappa c K T : Real}
    (hxy : x <= y)
    (htheta0 : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hkappa : 0 < kappa) (hc : 0 < c) (hT : 0 < T) (hK : 0 <= K)
    (hDeltaComparable : Delta <= K * delta)
    (hcurvatureScale : c * T <= kappa)
    (hcritical : traceFirstDerivative f f1 db dd theta0 = 0)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z|)
    (hcriticalValue : |traceFunction f da db dd theta0| <= Delta)
    (hxSublevel : |traceFunction f da db dd x| <= delta)
    (hySublevel : |traceFunction f da db dd y| <= delta)
    (hrectangleWidth : Real.sqrt (delta / rho) <= y - x) :
    c * (Delta + delta) * T <=
      16 * (K + 1) ^ 2 * delta * rho := by
  have htraceDeriv : forall z, z ∈ Icc A B ->
      HasDerivAt (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFunction f f1 da db dd z (hfDeriv z hz)
  have htraceFirstDeriv : forall z, z ∈ Icc A B ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z hz) (hf1Deriv z hz)
  exact medium_rectangle_width_forces_tangency_product
    (traceFunction f da db dd)
    (traceFirstDerivative f f1 db dd)
    (traceSecondDerivative f1 f2 db dd)
    hxy htheta0 hxDomain hyDomain hdelta hrho hkappa hc hT hK
    hDeltaComparable hcurvatureScale hcritical
    htraceDeriv htraceFirstDeriv
    (continuousOn_traceSecondDerivative f1 f2 db dd
      hf1Deriv hf2Continuous)
    hcurvatureLower hcriticalValue hxSublevel hySublevel
    hrectangleWidth

#print axioms trace_medium_rectangle_width_forces_tangency_product

end FamilyStickyCinematicL32TraceMediumRectangleTangencyV1
