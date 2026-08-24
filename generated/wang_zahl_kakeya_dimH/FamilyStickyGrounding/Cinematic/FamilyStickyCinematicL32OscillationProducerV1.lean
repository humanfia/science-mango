import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TwoZeroGeometryV1
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32OscillationProducerV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TwoZeroGeometryV1

/-!
# Short-interval oscillation producers for cinematic traces

Provenance: the short-interval reduction in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemmas 3.5--3.6, specialized to the explicit
Wang--Zahl trace from their Lemma 7.3.

This module removes the two local oscillation hypotheses from the preceding
zero-count module.  The oscillation bounds are produced by Mathlib's mean
value theorem from the actual first and second derivatives, with every
constant explicit.  No zero-count, incidence, projection, or L3/2 conclusion
is used as a callback.
-/

/-- On the normalized parameter range, the first trace jet is at most four
times the coefficient distance. -/
theorem abs_traceJet1_le_four_coefficientDistance
    (da db dd ft f1 t : Real)
    (ht : |t| <= 1) (hft : |ft| <= 2) (hf1 : |f1| <= 2) :
    |traceJet1 db dd ft f1 t| <=
      4 * coefficientDistance da db dd := by
  have htf1 : |t * f1| <= 2 := by
    rw [abs_mul]
    have ht0 : 0 <= |t| := abs_nonneg t
    nlinarith
  have hinside : |ft + t * f1| <= 4 := by
    calc
      |ft + t * f1| <= |ft| + |t * f1| := abs_add_le _ _
      _ <= 4 := by linarith
  have hlinear : |db * f1| <= 2 * |db| := by
    rw [abs_mul]
    have hdb0 : 0 <= |db| := abs_nonneg db
    nlinarith
  have hquadratic : |dd * (ft + t * f1)| <= 4 * |dd| := by
    rw [abs_mul]
    have hdd0 : 0 <= |dd| := abs_nonneg dd
    nlinarith
  calc
    |traceJet1 db dd ft f1 t| <=
        |db * f1| + |dd * (ft + t * f1)| := by
      rw [traceJet1]
      exact abs_add_le _ _
    _ <= 2 * |db| + 4 * |dd| := add_le_add hlinear hquadratic
    _ <= 4 * coefficientDistance da db dd := by
      rw [coefficientDistance]
      nlinarith [abs_nonneg da, abs_nonneg db, abs_nonneg dd]

/-- On the normalized parameter range, the second trace jet is at most five
times the coefficient distance. -/
theorem abs_traceJet2_le_five_coefficientDistance
    (da db dd f1 f2 t : Real)
    (ht : |t| <= 1) (hf1 : |f1| <= 2)
    (hf2 : |f2| <= 1 / 100) :
    |traceJet2 db dd f1 f2 t| <=
      5 * coefficientDistance da db dd := by
  have htwo : |2 * f1| <= 4 := by
    rw [abs_mul]
    norm_num
    linarith
  have htf2 : |t * f2| <= 1 / 100 := by
    rw [abs_mul]
    have ht0 : 0 <= |t| := abs_nonneg t
    nlinarith [abs_nonneg f2]
  have hinside : |2 * f1 + t * f2| <= 5 := by
    calc
      |2 * f1 + t * f2| <= |2 * f1| + |t * f2| := abs_add_le _ _
      _ <= 5 := by linarith
  have hlinear : |db * f2| <= 5 * |db| := by
    rw [abs_mul]
    have hdb0 : 0 <= |db| := abs_nonneg db
    nlinarith [abs_nonneg f2]
  have hquadratic : |dd * (2 * f1 + t * f2)| <= 5 * |dd| := by
    rw [abs_mul]
    have hdd0 : 0 <= |dd| := abs_nonneg dd
    nlinarith
  calc
    |traceJet2 db dd f1 f2 t| <=
        |db * f2| + |dd * (2 * f1 + t * f2)| := by
      rw [traceJet2]
      exact abs_add_le _ _
    _ <= 5 * |db| + 5 * |dd| := add_le_add hlinear hquadratic
    _ <= 5 * coefficientDistance da db dd := by
      rw [coefficientDistance]
      nlinarith [abs_nonneg da, abs_nonneg db, abs_nonneg dd]

/-- A thin scalar specialization of Mathlib's convex-set mean value bound. -/
theorem abs_sub_le_of_hasDerivAt_bound_on_Icc
    (h h1 : Real -> Real) {a c C x y : Real}
    (hx : x ∈ Icc a c) (hy : y ∈ Icc a c)
    (hderiv : forall t, t ∈ Icc a c -> HasDerivAt h (h1 t) t)
    (hbound : forall t, t ∈ Icc a c -> |h1 t| <= C) :
    |h x - h y| <= C * |x - y| := by
  have hmean : ‖h x - h y‖ <= C * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := h) (f' := h1) (s := Icc a c)
      (fun t ht => (hderiv t ht).hasDerivWithinAt)
      (fun t ht => by
        simpa [Real.norm_eq_abs] using hbound t ht)
      (convex_Icc a c) hy hx
  simpa [Real.norm_eq_abs] using hmean

/-- A parameter interval of length below `1/6000` automatically supplies
both oscillation hypotheses used by the local cinematic trichotomy. -/
theorem traceFunction_oscillations_on_short_Icc
    (f f1 f2 : Real -> Real) (da db dd : Real) {a c : Real}
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hshort : c - a < 1 / 6000)
    (hparameter : forall theta, theta ∈ Icc a c -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc a c -> |f theta| <= 2)
    (hf1Upper : forall theta, theta ∈ Icc a c -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc a c -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt f1 (f2 theta) theta) :
    (forall x, x ∈ Icc a c -> forall y, y ∈ Icc a c ->
      |traceJet0 da db dd (f x) x - traceJet0 da db dd (f y) y| <
        coefficientDistance da db dd / 1200) ∧
    (forall x, x ∈ Icc a c -> forall y, y ∈ Icc a c ->
      |traceJet1 db dd (f x) (f1 x) x -
        traceJet1 db dd (f y) (f1 y) y| <
          coefficientDistance da db dd / 1200) := by
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
  have hfirstBound : forall theta, theta ∈ Icc a c ->
      |traceFirstDerivative f f1 db dd theta| <=
        4 * coefficientDistance da db dd := by
    intro theta htheta
    simpa [traceFirstDerivative] using
      abs_traceJet1_le_four_coefficientDistance
        da db dd (f theta) (f1 theta) theta
        (hparameter theta htheta) (hft theta htheta)
        (hf1Upper theta htheta)
  have hsecondBound : forall theta, theta ∈ Icc a c ->
      |traceSecondDerivative f1 f2 db dd theta| <=
        5 * coefficientDistance da db dd := by
    intro theta htheta
    simpa [traceSecondDerivative] using
      abs_traceJet2_le_five_coefficientDistance
        da db dd (f1 theta) (f2 theta) theta
        (hparameter theta htheta) (hf1Upper theta htheta)
        (hf2 theta htheta)
  constructor
  · intro x hx y hy
    have hxy : |x - y| <= c - a := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hxysmall : |x - y| < 1 / 6000 :=
      lt_of_le_of_lt hxy hshort
    have hlip := abs_sub_le_of_hasDerivAt_bound_on_Icc
      (traceFunction f da db dd)
      (traceFirstDerivative f f1 db dd) hx hy htraceDeriv hfirstBound
    have hmul :
        4 * coefficientDistance da db dd * |x - y| <
          4 * coefficientDistance da db dd * (1 / 6000) :=
      mul_lt_mul_of_pos_left hxysmall (by nlinarith)
    simpa [traceFunction] using
      (show |traceFunction f da db dd x - traceFunction f da db dd y| <
          coefficientDistance da db dd / 1200 by
        nlinarith)
  · intro x hx y hy
    have hxy : |x - y| <= c - a := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hxysmall : |x - y| < 1 / 6000 :=
      lt_of_le_of_lt hxy hshort
    have hlip := abs_sub_le_of_hasDerivAt_bound_on_Icc
      (traceFirstDerivative f f1 db dd)
      (traceSecondDerivative f1 f2 db dd) hx hy
      htraceFirstDeriv hsecondBound
    have hmul :
        5 * coefficientDistance da db dd * |x - y| <
          5 * coefficientDistance da db dd * (1 / 6000) :=
      mul_lt_mul_of_pos_left hxysmall (by nlinarith)
    simpa [traceFirstDerivative] using
      (show |traceFirstDerivative f f1 db dd x -
          traceFirstDerivative f f1 db dd y| <
            coefficientDistance da db dd / 1200 by
        nlinarith)

/-- Callback-free short-interval form of PYZ Lemma 3.6 for the explicit
Wang--Zahl cinematic trace. -/
theorem traceFunction_no_three_ordered_zeros_of_short_interval
    (f f1 f2 : Real -> Real) (da db dd : Real) {a b c : Real}
    (hab : a < b) (hbc : b < c)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hshort : c - a < 1 / 6000)
    (hparameter : forall theta, theta ∈ Icc a c -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc a c -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc a c -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc a c -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc a c -> |f2 theta| <= 1 / 100)
    (hfDeriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, theta ∈ Icc a c ->
      HasDerivAt f1 (f2 theta) theta)
    (ha : traceFunction f da db dd a = 0)
    (hb : traceFunction f da db dd b = 0)
    (hc : traceFunction f da db dd c = 0) : False := by
  obtain ⟨hosc0, hosc1⟩ := traceFunction_oscillations_on_short_Icc
    f f1 f2 da db dd hcoefficient hshort hparameter hft hf1Upper hf2
    hfDeriv hf1Deriv
  exact traceFunction_no_three_ordered_zeros
    f f1 f2 da db dd hab hbc hcoefficient hparameter hft
    hf1Lower hf1Upper hf2 hfDeriv hf1Deriv hosc0 hosc1 ha hb hc

#print axioms abs_traceJet1_le_four_coefficientDistance
#print axioms abs_traceJet2_le_five_coefficientDistance
#print axioms abs_sub_le_of_hasDerivAt_bound_on_Icc
#print axioms traceFunction_oscillations_on_short_Icc
#print axioms traceFunction_no_three_ordered_zeros_of_short_interval

end FamilyStickyCinematicL32OscillationProducerV1
