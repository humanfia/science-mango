import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceEasySublevelV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32EasyRectangleTangencyV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TraceEasyRectangleTangencyV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceEasySublevelV1
open FamilyStickyCinematicL32EasyRectangleTangencyV1

/-!
# Easy rectangle tangency for the Wang--Zahl trace

Provenance: the derivative-separated case of Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemmas 3.8(2b) and 3.9, specialized to the
Wang--Zahl Lemma 7.3 trace.

The actual trace derivative identities produce the easy sublevel length.
The square-root width comparison is then discharged by the frozen generic
algebra theorem; no containment or length callback is assumed.
-/

/-- An actual-trace component in the derivative-separated regime satisfies
the explicit easy tangency product. -/
theorem trace_easy_rectangle_width_forces_tangency_product
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B x y delta rho Delta m c K T : Real}
    (hxy : x <= y)
    (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hm : 0 < m) (hc : 0 < c) (hT : 0 < T) (hK : 0 <= K)
    (hparameterScale : Delta + delta <= K * T)
    (hfirstJetScale : c * T <= m)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hfirstLower : forall z, z ∈ Icc A B ->
      m <= |traceFirstDerivative f f1 db dd z|)
    (hcomponentSublevel : forall z, z ∈ Icc x y ->
      |traceFunction f da db dd z| <= delta)
    (hrectangleWidth : Real.sqrt (delta / rho) <= y - x) :
    c ^ 2 * (Delta + delta) * T <= 4 * K * delta * rho := by
  have hlength := trace_easy_sublevel_interval_length_le
    f f1 f2 da db dd hxy hxDomain hyDomain hm
    hfDeriv hf1Deriv hfirstLower hcomponentSublevel
  exact easy_rectangle_product_of_length_bounds
    hdelta hrho hm hc hT hK hparameterScale hfirstJetScale
    hrectangleWidth hlength

#print axioms trace_easy_rectangle_width_forces_tangency_product

end FamilyStickyCinematicL32TraceEasyRectangleTangencyV1
