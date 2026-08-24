import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32RolleBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32EasySublevelV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceEasySublevelV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32SublevelShapeV1
open FamilyStickyCinematicL32EasySublevelV1

/-!
# Derivative-separated sublevels for the Wang--Zahl trace

Provenance: the easier cases of Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.8(2b), specialized to Wang--Zahl Lemma 7.3.

The actual trace derivatives generate all continuity and monotonicity inputs.
Only the quantitative first-jet lower bound remains as geometric data.
-/

/-- The actual trace sublevel set is order-connected when its first jet is
uniformly separated from zero. -/
theorem trace_easy_sublevelOn_ordConnected
    (f f1 f2 : Real -> Real) (da db dd delta : Real)
    {A B m : Real} (hAB : A <= B) (hm : 0 < m)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hfirstLower : forall z, z ∈ Icc A B ->
      m <= |traceFirstDerivative f f1 db dd z|) :
    (SublevelOn (traceFunction f da db dd) delta (Icc A B)).OrdConnected := by
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
  exact sublevelOn_ordConnected_of_abs_deriv_lower
    (traceFunction f da db dd)
    (traceFirstDerivative f f1 db dd)
    delta hAB hm htraceDeriv
    (HasDerivAt.continuousOn htraceFirstDeriv) hfirstLower

/-- Any actual-trace sublevel interval in the derivative-separated regime
has length at most `2 * delta / m`. -/
theorem trace_easy_sublevel_interval_length_le
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B x y delta m : Real}
    (hxy : x <= y) (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hm : 0 < m)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hfirstLower : forall z, z ∈ Icc A B ->
      m <= |traceFirstDerivative f f1 db dd z|)
    (hcomponentSublevel : forall z, z ∈ Icc x y ->
      |traceFunction f da db dd z| <= delta) :
    y - x <= 2 * delta / m := by
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
  exact easy_sublevel_interval_length_le
    (traceFunction f da db dd)
    (traceFirstDerivative f f1 db dd)
    hxy hxDomain hyDomain hm htraceDeriv
    (HasDerivAt.continuousOn htraceFirstDeriv)
    hfirstLower hcomponentSublevel

#print axioms trace_easy_sublevelOn_ordConnected
#print axioms trace_easy_sublevel_interval_length_le

end FamilyStickyCinematicL32TraceEasySublevelV1
