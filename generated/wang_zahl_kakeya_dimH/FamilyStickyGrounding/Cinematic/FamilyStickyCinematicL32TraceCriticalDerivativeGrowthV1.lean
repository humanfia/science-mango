import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelComponentV1

set_option autoImplicit false

open Set
open scoped Interval

namespace FamilyStickyCinematicL32TraceCriticalDerivativeGrowthV1

open FamilyStickyCinematicL32CriticalPointGrowthV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceSublevelComponentV1

/-!
# First-jet growth away from an actual trace critical point

Provenance: the monotonicity step in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.8(1b)--(2b), specialized to the
Wang--Zahl Lemma 7.3 trace.

The trace derivative identities restrict the ambient hypotheses to the
segment from the critical point to the target, where the previously proved
absolute-curvature growth theorem applies.
-/

/-- Uniform absolute second-jet separation makes the actual first trace jet
grow at least linearly with distance from its zero. -/
theorem trace_curvature_lower_forces_firstDerivative_growth
    (f f1 f2 : Real -> Real) (db dd : Real)
    {A B theta0 theta kappa : Real}
    (htheta0 : theta0 ∈ Icc A B) (htheta : theta ∈ Icc A B)
    (hkappa : 0 < kappa)
    (hcritical : traceFirstDerivative f f1 db dd theta0 = 0)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z|) :
    kappa * |theta - theta0| <=
      |traceFirstDerivative f f1 db dd theta| := by
  have hpathSubset : [[theta0, theta]] ⊆ Icc A B :=
    uIcc_subset_Icc htheta0 htheta
  have htraceFirstDeriv : forall z, z ∈ [[theta0, theta]] ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z (hpathSubset hz))
      (hf1Deriv z (hpathSubset hz))
  exact abs_curvature_lower_forces_first_derivative_growth
    (traceFirstDerivative f f1 db dd)
    (traceSecondDerivative f1 f2 db dd)
    hkappa hcritical htraceFirstDeriv
    ((continuousOn_traceSecondDerivative f1 f2 db dd
      hf1Deriv hf2Continuous).mono hpathSubset)
    (fun z hz => hcurvatureLower z (hpathSubset hz))

#print axioms trace_curvature_lower_forces_firstDerivative_growth

end FamilyStickyCinematicL32TraceCriticalDerivativeGrowthV1
