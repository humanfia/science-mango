import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32RolleBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelComponentV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceSublevelComponentV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32SublevelComponentV1

/-!
# Explicit sublevel component bound for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(2b), specialized to the trace in Wang--Zahl Lemma 7.3.

The algebraic first- and second-derivative identities are supplied by the
Rolle bridge.  Continuity of the second trace jet is proved directly from its
formula and the base `C^2` data; it is not assumed as a callback.
-/

/-- The explicit second trace derivative is continuous whenever `f2` is
continuous and `f1' = f2`. -/
theorem continuousOn_traceSecondDerivative
    (f1 f2 : Real -> Real) (db dd : Real) {A B : Real}
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B)) :
    ContinuousOn (traceSecondDerivative f1 f2 db dd) (Icc A B) := by
  have hf1Continuous : ContinuousOn f1 (Icc A B) :=
    HasDerivAt.continuousOn hf1Deriv
  have hcontinuous : ContinuousOn
      (fun z => db * f2 z + dd * (2 * f1 z + z * f2 z))
      (Icc A B) :=
    (continuousOn_const.mul hf2Continuous).add
      (continuousOn_const.mul
        ((continuousOn_const.mul hf1Continuous).add
          (continuousOn_id.mul hf2Continuous)))
  change ContinuousOn
    (fun z => db * f2 z + dd * (2 * f1 z + z * f2 z)) (Icc A B)
  exact hcontinuous

/-- Actual-trace specialization of the explicit hard-subcase component
bound in PYZ Lemma 3.8(2b). -/
theorem trace_sublevel_component_length_le_of_critical_curvature
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B theta0 x y M kappa Delta delta : Real}
    (hxy : x <= y)
    (htheta0Domain : theta0 ∈ Icc A B)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
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
      |traceFunction f da db dd z| <= delta) :
    y - x <=
      2 * delta / (kappa * Real.sqrt ((Delta - delta) / M)) := by
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
  exact sublevel_component_length_le_of_critical_curvature
    (traceFunction f da db dd)
    (traceFirstDerivative f f1 db dd)
    (traceSecondDerivative f1 f2 db dd)
    hxy htheta0Domain hxDomain hyDomain hM hkappa hgap hcritical
    htraceDeriv htraceFirstDeriv
    (continuousOn_traceSecondDerivative f1 f2 db dd
      hf1Deriv hf2Continuous)
    hcurvatureUpper hcurvatureLower hcenter hcomponentSublevel

#print axioms continuousOn_traceSecondDerivative
#print axioms trace_sublevel_component_length_le_of_critical_curvature

end FamilyStickyCinematicL32TraceSublevelComponentV1
