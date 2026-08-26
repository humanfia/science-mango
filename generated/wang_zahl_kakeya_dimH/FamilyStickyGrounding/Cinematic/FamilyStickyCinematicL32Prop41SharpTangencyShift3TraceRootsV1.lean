import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CriticalValueTransferV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41EndpointFarSameSignCriticalV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41Shift3TwoRootsV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Interval

namespace FamilyStickyCinematicL32Prop41SharpTangencyShift3TraceRootsV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceSublevelComponentV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32CriticalValueTransferV1
open FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionHalfMarginV1
open FamilyStickyCinematicL32Prop41EndpointFarSameSignCriticalV1
open FamilyStickyCinematicL32Prop41Shift3TwoRootsV1

/-!
# From sharp trace tangency to one of three two-root shifts

This module composes the root-free sharp-curvature branch.  A small attained
tangency cost first supplies a genuine critical point.  Its distance from the
minimizing parameter is controlled by curvature, so a minimizer in the
concentric half interval leaves a fixed `1/16` margin on both sides.  The
critical-point growth theorem then derives far same-sign endpoint values, and
the three-shift intermediate-value argument creates one root on each side.

The two explicit scale inequalities are the remaining quantitative input:
the shift must dominate the critical value, while critical value plus shift
must fit below the quadratic endpoint growth.  No root or endpoint-sign
premise is assumed.
-/

/-- Shifting the constant trace coefficient is exactly vertical translation
of the trace. -/
@[simp] theorem traceFunction_add_constantCoefficient
    (f : Real -> Real) (da db dd shift theta : Real) :
    traceFunction f (da + shift) db dd theta =
      traceFunction f da db dd theta + shift := by
  simp only [traceFunction, traceJet0]
  ring

/-- In the globally sharp-curvature branch, sufficiently small tangency and
the two explicit shift-scale inequalities produce an integer shift
`eta in {-1,0,1}` whose shifted trace has one root on either side of the
critical point.  The shifted endpoint values retain the same strict sign. -/
theorem trace_sharp_tangency_exists_int_shift3_two_sided_roots
    (f f1 f2 : Real -> Real) (da db dd Delta thetaDelta s : Real)
    {A B : Real}
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hthetaDelta :
      thetaDelta ∈ centeredFractionIcc A B (1 / 2 : Real))
    (hDeltaDef :
      Delta = traceTangencyCost f f1 da db dd thetaDelta)
    (hDeltaSmall : Delta < coefficientDistance da db dd / 1200)
    (hs : 0 < s)
    (hcriticalBelowShift : 10 * Delta < s)
    (hendpointGrowth :
      10 * Delta + s <
        ((coefficientDistance da db dd / 45) / 4) *
          (1 / 16 : Real) ^ 2)
    (hfDeriv : ∀ z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hparameter : ∀ z, z ∈ Icc A B -> |z| <= 1)
    (hf1Upper : ∀ z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : ∀ z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hcurvatureStrict : ∀ z, z ∈ Icc A B ->
      coefficientDistance da db dd / 45 <
        |traceSecondDerivative f1 f2 db dd z|) :
    ∃ (eta : Int) (theta0 thetaLeft thetaRight : Real),
      (eta = -1 ∨ eta = 0 ∨ eta = 1) ∧
      theta0 ∈ Icc A B ∧
      traceFirstDerivative f f1 db dd theta0 = 0 ∧
      0 <
        traceFunction f (da + (eta : Real) * s) db dd A *
          traceFunction f (da + (eta : Real) * s) db dd B ∧
      thetaLeft ∈ Ioo A theta0 ∧
      traceFunction f (da + (eta : Real) * s) db dd thetaLeft = 0 ∧
      thetaRight ∈ Ioo theta0 B ∧
      traceFunction f (da + (eta : Real) * s) db dd thetaRight = 0 := by
  let coefficient : Real := coefficientDistance da db dd
  let kappa : Real := coefficient / 45
  have hcoefficientPos : 0 < coefficient := by
    simpa [coefficient] using hcoefficient
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hAB : A < B := by linarith
  have hmargins :=
    mem_half_has_eighth_whole_margin hwidth hthetaDelta
  have hthetaDeltaOuter : thetaDelta ∈ Icc A B := by
    constructor <;> linarith [hmargins.1, hmargins.2]
  obtain ⟨theta0, htheta0, hcritical, hcriticalValue⟩ :=
    trace_sharp_curvature_small_tangency_exists_criticalPoint_value_bound
      f f1 f2 da db dd Delta thetaDelta hwidth hcoefficient
      hthetaDelta hDeltaDef hDeltaSmall hfDeriv hf1Deriv hf2Continuous
      hparameter hf1Upper hf2 hcurvatureStrict
  have htraceDeriv : ∀ z, z ∈ Icc A B ->
      HasDerivAt (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFunction f f1 da db dd z (hfDeriv z hz)
  have htraceFirstDeriv : ∀ z, z ∈ Icc A B ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z hz) (hf1Deriv z hz)
  have htraceSecondContinuous :
      ContinuousOn (traceSecondDerivative f1 f2 db dd) (Icc A B) :=
    continuousOn_traceSecondDerivative f1 f2 db dd
      hf1Deriv hf2Continuous
  have hcurvatureLower : ∀ z, z ∈ Icc A B ->
      kappa <= |traceSecondDerivative f1 f2 db dd z| := by
    intro z hz
    exact le_of_lt (by
      simpa [kappa, coefficient] using hcurvatureStrict z hz)
  have hanchorSlope :
      |traceFirstDerivative f f1 db dd thetaDelta| <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    exact le_add_of_nonneg_left (abs_nonneg _)
  have hpath : [[theta0, thetaDelta]] ⊆ Icc A B :=
    uIcc_subset_Icc htheta0 hthetaDeltaOuter
  have hdistance : |thetaDelta - theta0| <= Delta / kappa :=
    criticalPoint_distance_le_anchorSlope_div_curvature
      (traceFirstDerivative f f1 db dd)
      (traceSecondDerivative f1 f2 db dd)
      hkappa hcritical
      (fun z hz => htraceFirstDeriv z (hpath hz))
      (htraceSecondContinuous.mono hpath)
      (fun z hz => hcurvatureLower z (hpath hz)) hanchorSlope
  have hratio : Delta / kappa < (1 / 16 : Real) := by
    apply (div_lt_iff₀ hkappa).2
    dsimp [kappa, coefficient]
    nlinarith [hDeltaSmall, hcoefficient]
  have hmLeft : (1 / 16 : Real) <= theta0 - A := by
    have hleftDistance : thetaDelta - theta0 <= Delta / kappa :=
      (le_abs_self (thetaDelta - theta0)).trans hdistance
    linarith [hmargins.1]
  have hmRight : (1 / 16 : Real) <= B - theta0 := by
    have hrightDistance : theta0 - thetaDelta <= Delta / kappa := by
      have hbound := (neg_le_abs (thetaDelta - theta0)).trans hdistance
      linarith
    linarith [hmargins.2]
  have hATheta : A < theta0 := by linarith
  have hThetaB : theta0 < B := by linarith
  have hcriticalGap :
      |traceFunction f da db dd theta0| + s <
        (kappa / 4) * (1 / 16 : Real) ^ 2 := by
    calc
      |traceFunction f da db dd theta0| + s <= 10 * Delta + s :=
        by simpa [add_comm] using add_le_add_right hcriticalValue s
      _ < (kappa / 4) * (1 / 16 : Real) ^ 2 := by
        simpa [kappa, coefficient] using hendpointGrowth
  obtain ⟨hAfar, hBfar, hsame⟩ :=
    endpoint_far_same_sign_of_critical_sharp_curvature
      (traceFunction f da db dd)
      (traceFirstDerivative f f1 db dd)
      (traceSecondDerivative f1 f2 db dd)
      hAB htheta0 hkappa (by norm_num) hs hcritical htraceDeriv
      htraceFirstDeriv htraceSecondContinuous hcurvatureLower
      hmLeft hmRight hcriticalGap
  have hcenter : |traceFunction f da db dd theta0| < s :=
    hcriticalValue.trans_lt hcriticalBelowShift
  obtain ⟨eta, thetaLeft, thetaRight, heta, hendpoints,
      hthetaLeft, hrootLeft, hthetaRight, hrootRight⟩ :=
    exists_shift3_two_sided_roots
      (traceFunction f da db dd)
      (HasDerivAt.continuousOn htraceDeriv)
      hATheta hThetaB hs hcenter hAfar hBfar hsame
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heta
  rcases heta with heta | heta | heta
  · subst eta
    refine ⟨-1, theta0, thetaLeft, thetaRight, Or.inl rfl, htheta0,
      hcritical, ?_, hthetaLeft, ?_, hthetaRight, ?_⟩
    · simpa using hendpoints
    · simpa using hrootLeft
    · simpa using hrootRight
  · subst eta
    refine ⟨0, theta0, thetaLeft, thetaRight, Or.inr (Or.inl rfl),
      htheta0, hcritical, ?_, hthetaLeft, ?_, hthetaRight, ?_⟩
    · simpa using hendpoints
    · simpa using hrootLeft
    · simpa using hrootRight
  · subst eta
    refine ⟨1, theta0, thetaLeft, thetaRight, Or.inr (Or.inr rfl),
      htheta0, hcritical, ?_, hthetaLeft, ?_, hthetaRight, ?_⟩
    · simpa using hendpoints
    · simpa using hrootLeft
    · simpa using hrootRight

#print axioms traceFunction_add_constantCoefficient
#print axioms trace_sharp_tangency_exists_int_shift3_two_sided_roots

end FamilyStickyCinematicL32Prop41SharpTangencyShift3TraceRootsV1
