import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32RolleBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TangencyMinimizerV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceTangencyMinimizerV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TangencyMinimizerV1

/-!
# Tangency minimizer for the Wang--Zahl trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Definition 3.7
and Lemma 3.8, specialized to the trace in Wang--Zahl Lemma 7.3.

The already proved trace derivative identities supply continuity of both
the value and first jet, so compactness produces the actual minimizing
parameter and its universal comparison property.
-/

/-- The explicit value--slope cost for a Wang--Zahl coefficient-difference
trace. -/
def traceTangencyCost
    (f f1 : Real -> Real) (da db dd theta : Real) : Real :=
  |traceFunction f da db dd theta| +
    |traceFirstDerivative f f1 db dd theta|

/-- The actual Wang--Zahl trace has an attained, nonnegative PYZ tangency
parameter on every nonempty closed interval. -/
theorem exists_trace_tangencyParameter_with_minimizer
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B : Real} (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) :
    exists Delta thetaDelta,
      0 <= Delta ∧ thetaDelta ∈ Icc A B ∧
      Delta = traceTangencyCost f f1 da db dd thetaDelta ∧
      forall theta, theta ∈ Icc A B ->
        Delta <= traceTangencyCost f f1 da db dd theta := by
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
  obtain ⟨Delta, thetaDelta, hDelta, hthetaDelta, hdef, hminimum⟩ :=
    exists_tangencyParameter_with_minimizer
      (traceFunction f da db dd)
      (traceFirstDerivative f f1 db dd)
      hAB (HasDerivAt.continuousOn htraceDeriv)
      (HasDerivAt.continuousOn htraceFirstDeriv)
  refine ⟨Delta, thetaDelta, hDelta, hthetaDelta, ?_, ?_⟩
  · simpa [traceTangencyCost, jetCost] using hdef
  · intro theta htheta
    simpa [traceTangencyCost, jetCost] using hminimum theta htheta

#print axioms exists_trace_tangencyParameter_with_minimizer

end FamilyStickyCinematicL32TraceTangencyMinimizerV1
