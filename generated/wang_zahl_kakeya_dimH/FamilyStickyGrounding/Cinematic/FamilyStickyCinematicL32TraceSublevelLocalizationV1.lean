import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceCriticalValueLowerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelLocalizationV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceSublevelLocalizationV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceCriticalValueLowerV1
open FamilyStickyCinematicL32SublevelLocalizationV1

/-!
# Sublevel localization for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(2a), specialized to the trace in Wang--Zahl Lemma 7.3.

This is a thin composition of the actual-trace quadratic value lower bound
and the square-root extraction lemma.
-/

/-- Every actual trace sublevel point lies in the explicit square-root
neighborhood of its critical point. -/
theorem trace_sublevel_point_localized_near_criticalPoint
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B theta0 theta kappa Delta delta : Real}
    (htheta0 : theta0 ∈ Icc A B) (htheta : theta ∈ Icc A B)
    (hkappa : 0 < kappa)
    (hcritical : traceFirstDerivative f f1 db dd theta0 = 0)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z|)
    (hcriticalValue : |traceFunction f da db dd theta0| <= Delta)
    (hsublevel : |traceFunction f da db dd theta| <= delta) :
    |theta - theta0| <=
      2 * Real.sqrt ((Delta + delta) / kappa) := by
  exact distance_le_two_sqrt_of_quadratic_value_lower hkappa
    (trace_value_lower_away_from_criticalPoint
      f f1 f2 da db dd htheta0 htheta hkappa hcritical
      hfDeriv hf1Deriv hf2Continuous hcurvatureLower hcriticalValue)
    hsublevel

#print axioms trace_sublevel_point_localized_near_criticalPoint

end FamilyStickyCinematicL32TraceSublevelLocalizationV1
