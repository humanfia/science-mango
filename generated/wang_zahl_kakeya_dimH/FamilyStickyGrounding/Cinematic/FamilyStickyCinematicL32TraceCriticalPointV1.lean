import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelComponentV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalPointExistenceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceCriticalPointV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceSublevelComponentV1
open FamilyStickyCinematicL32CriticalPointExistenceV1

/-!
# The unique critical point of the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1a), specialized to the trace in Wang--Zahl Lemma 7.3.

Actual first/second derivative identities and continuity of the second trace
jet discharge every calculus premise of the buffered critical-point producer.
-/

/-- A small first jet at a buffered anchor and nonvanishing second jet produce
the unique critical point of the explicit trace. -/
theorem trace_buffered_anchor_existsUnique_criticalPoint
    (f f1 f2 : Real -> Real) (db dd : Real)
    {A B thetaDelta eta kappa : Real}
    (hthetaDelta : thetaDelta ∈ Icc A B) (hkappa : 0 < kappa)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z|)
    (hanchor : |traceFirstDerivative f f1 db dd thetaDelta| <= eta)
    (hleftBuffer : eta <= kappa * (thetaDelta - A))
    (hrightBuffer : eta <= kappa * (B - thetaDelta)) :
    ∃! theta : Real, theta ∈ Icc A B ∧
      traceFirstDerivative f f1 db dd theta = 0 := by
  have htraceFirstDeriv : forall z, z ∈ Icc A B ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z hz) (hf1Deriv z hz)
  exact buffered_small_value_existsUnique_zero_of_abs_deriv_lower
    (traceFirstDerivative f f1 db dd)
    (traceSecondDerivative f1 f2 db dd)
    hthetaDelta hkappa htraceFirstDeriv
    (continuousOn_traceSecondDerivative f1 f2 db dd
      hf1Deriv hf2Continuous)
    hcurvatureLower hanchor hleftBuffer hrightBuffer

#print axioms trace_buffered_anchor_existsUnique_criticalPoint

end FamilyStickyCinematicL32TraceCriticalPointV1
