import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32LocalTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32RolleBridgeV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TwoZeroGeometryV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1

/-!
# No three local intersections for the explicit cinematic trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.6,
specialized to the Wang--Zahl family from their Lemma 7.3.

The proof composes the independently verified short-interval jet trichotomy
with the independently verified twice-iterated Rolle bridge.  Thus derivative
zeros and curvature zeros are produced by Mathlib calculus; none of the
zero-count conclusion, Proposition 4.1, or the L3/2 estimate is assumed.
-/

/-- Under the local PYZ oscillation regime, a nontrivial Wang--Zahl trace
cannot vanish at three ordered parameters. -/
theorem traceFunction_no_three_ordered_zeros
    (f f1 f2 : Real -> Real) (da db dd : Real) {a b c : Real}
    (hab : a < b) (hbc : b < c)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hparameter : forall theta, theta ∈ Icc a c -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc a c -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc a c -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc a c -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc a c -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt f1 (f2 theta) theta)
    (hosc0 : forall x, x ∈ Icc a c -> forall y, y ∈ Icc a c ->
      |traceJet0 da db dd (f x) x - traceJet0 da db dd (f y) y| <
        coefficientDistance da db dd / 1200)
    (hosc1 : forall x, x ∈ Icc a c -> forall y, y ∈ Icc a c ->
      |traceJet1 db dd (f x) (f1 x) x -
        traceJet1 db dd (f y) (f1 y) y| <
          coefficientDistance da db dd / 1200)
    (ha : traceFunction f da db dd a = 0)
    (hb : traceFunction f da db dd b = 0)
    (hc : traceFunction f da db dd c = 0) : False := by
  have htraceDeriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd theta) theta := by
    intro theta htheta
    exact hasDerivAt_traceFunction f f1 da db dd theta
      (hfDeriv theta htheta)
  have htraceFirstDeriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd theta) theta := by
    intro theta htheta
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd theta
      (hfDeriv theta htheta) (hf1Deriv theta htheta)
  obtain ⟨x, hx, y, hy, z, hz, hx0, hy0, hz0⟩ :=
    second_derivative_zero_between_three_zeros
      (traceFunction f da db dd)
      (traceFirstDerivative f f1 db dd)
      (traceSecondDerivative f1 f2 db dd)
      hab hbc htraceDeriv htraceFirstDeriv ha hb hc
  have htrichotomy := local_value_slope_curvature_trichotomy
    (Icc a c) da db dd f f1 f2 (fun theta => theta)
    hparameter hft hf1Lower hf1Upper hf2 hosc0 hosc1
  rcases htrichotomy with hvalue | hslope | hcurvature
  · have hlarge := hvalue a ⟨le_rfl, le_of_lt (hab.trans hbc)⟩
    have ha' : traceJet0 da db dd (f a) a = 0 := by
      simpa [traceFunction] using ha
    rw [ha', abs_zero] at hlarge
    have hpositive : 0 < coefficientDistance da db dd / 1200 := by
      positivity
    linarith
  · have hxI : x ∈ Icc a c :=
      ⟨le_of_lt hx.1, (le_of_lt hx.2).trans (le_of_lt hbc)⟩
    have hlarge := hslope x hxI
    have hx0' : traceJet1 db dd (f x) (f1 x) x = 0 := by
      simpa [traceFirstDerivative] using hx0
    rw [hx0', abs_zero] at hlarge
    have hpositive : 0 < coefficientDistance da db dd / 1200 := by
      positivity
    linarith
  · have hzI : z ∈ Icc a c :=
      ⟨le_of_lt (hx.1.trans hz.1),
        le_of_lt (hz.2.trans hy.2)⟩
    have hlarge := hcurvature z hzI
    have hz0' : traceJet2 db dd (f1 z) (f2 z) z = 0 := by
      simpa [traceSecondDerivative] using hz0
    rw [hz0', abs_zero] at hlarge
    have hpositive : 0 < coefficientDistance da db dd / 600 := by
      positivity
    linarith

#print axioms traceFunction_no_three_ordered_zeros

end FamilyStickyCinematicL32TwoZeroGeometryV1
