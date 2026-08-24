import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelComponentV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalValueTransferV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32TraceCriticalValueV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceSublevelComponentV1
open FamilyStickyCinematicL32CriticalValueTransferV1

/-!
# Critical-value transfer for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1a), specialized to the trace in Wang--Zahl Lemma 7.3.

This module restricts ambient `C^2` trace data to the segment joining the
anchor and critical point, then applies the explicit value-transfer theorem.
-/

/-- An explicit critical point of the trace inherits the anchor value up to
the quadratic error `M * (eta / kappa)^2`. -/
theorem trace_criticalPoint_value_le_anchorValue_add_quadratic_error
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B theta0 thetaDelta M kappa Delta eta : Real}
    (htheta0 : theta0 ∈ Icc A B)
    (hthetaDelta : thetaDelta ∈ Icc A B)
    (hM : 0 <= M) (hkappa : 0 < kappa)
    (hcritical : traceFirstDerivative f f1 db dd theta0 = 0)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcurvatureUpper : forall z, z ∈ Icc A B ->
      |traceSecondDerivative f1 f2 db dd z| <= M)
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z|)
    (hanchorValue : |traceFunction f da db dd thetaDelta| <= Delta)
    (hanchorSlope : |traceFirstDerivative f f1 db dd thetaDelta| <= eta) :
    |traceFunction f da db dd theta0| <=
      Delta + M * (eta / kappa) ^ 2 := by
  have hpathSubset : [[theta0, thetaDelta]] ⊆ Icc A B :=
    uIcc_subset_Icc htheta0 hthetaDelta
  have htraceDeriv : forall z, z ∈ [[theta0, thetaDelta]] ->
      HasDerivAt (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFunction f f1 da db dd z
      (hfDeriv z (hpathSubset hz))
  have htraceFirstDeriv : forall z, z ∈ [[theta0, thetaDelta]] ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z (hpathSubset hz))
      (hf1Deriv z (hpathSubset hz))
  exact criticalPoint_value_le_anchorValue_add_quadratic_error
    (traceFunction f da db dd)
    (traceFirstDerivative f f1 db dd)
    (traceSecondDerivative f1 f2 db dd)
    hM hkappa hcritical htraceDeriv htraceFirstDeriv
    ((continuousOn_traceSecondDerivative f1 f2 db dd
      hf1Deriv hf2Continuous).mono hpathSubset)
    (fun z hz => hcurvatureUpper z (hpathSubset hz))
    (fun z hz => hcurvatureLower z (hpathSubset hz))
    hanchorValue hanchorSlope

#print axioms trace_criticalPoint_value_le_anchorValue_add_quadratic_error

end FamilyStickyCinematicL32TraceCriticalValueV1
