import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelComponentV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalValueLowerV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32TraceCriticalValueLowerV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceSublevelComponentV1
open FamilyStickyCinematicL32CriticalValueLowerV1

/-!
# Quadratic value separation for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1b), specialized to the trace in Wang--Zahl Lemma 7.3.

The derivative identities and continuity of the second trace jet are proved
by the earlier trace bridges.  This file only restricts those facts to the
segment joining the critical point and target.
-/

/-- Away from an actual critical point, the Wang--Zahl trace has the explicit
quadratic lower bound from PYZ Lemma 3.8(1b). -/
theorem trace_value_lower_away_from_criticalPoint
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B theta0 theta kappa Delta : Real}
    (htheta0 : theta0 ∈ Icc A B) (htheta : theta ∈ Icc A B)
    (hkappa : 0 < kappa)
    (hcritical : traceFirstDerivative f f1 db dd theta0 = 0)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z|)
    (hcriticalValue : |traceFunction f da db dd theta0| <= Delta) :
    (kappa / 4) * |theta - theta0| ^ 2 - Delta <=
      |traceFunction f da db dd theta| := by
  have hpathSubset : [[theta0, theta]] ⊆ Icc A B :=
    uIcc_subset_Icc htheta0 htheta
  have htraceDeriv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFunction f f1 da db dd z
      (hfDeriv z (hpathSubset hz))
  have htraceFirstDeriv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z (hpathSubset hz))
      (hf1Deriv z (hpathSubset hz))
  exact value_lower_away_from_criticalPoint
    (traceFunction f da db dd)
    (traceFirstDerivative f f1 db dd)
    (traceSecondDerivative f1 f2 db dd)
    hkappa hcritical htraceDeriv htraceFirstDeriv
    ((continuousOn_traceSecondDerivative f1 f2 db dd
      hf1Deriv hf2Continuous).mono hpathSubset)
    (fun z hz => hcurvatureLower z (hpathSubset hz))
    hcriticalValue

#print axioms trace_value_lower_away_from_criticalPoint

end FamilyStickyCinematicL32TraceCriticalValueLowerV1
