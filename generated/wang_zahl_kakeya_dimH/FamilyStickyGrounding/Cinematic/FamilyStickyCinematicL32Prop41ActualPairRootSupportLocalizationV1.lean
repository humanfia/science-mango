import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelLocalizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
open FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
open FamilyStickyCinematicL32TraceSublevelLocalizationV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Actual two-root support localization for PYZ Lemma 4.7

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1) and the proof of Lemma 4.7.

Two genuine intersections exclude the globally value-separated and
first-jet-separated branches.  Rolle's theorem therefore produces the sharp
second-jet regime.  The canonical attained tangency minimum then produces
the unique critical parameter.  Lemma 3.8(1b) localizes both roots, and the
separate numerical module localizes their entire interval hull.

No root-support localization, rectangle comparability, or lens-counting
estimate is accepted as a premise.
-/

/-- The parameter support of the lens cut out by two ordered roots. -/
def prop41PairRootSupport (thetaLeft thetaRight : Real) : Set Real :=
  Icc thetaLeft thetaRight

/-- Two actual ordered roots exclude the first two branches of the sharp
global jet trichotomy, forcing uniform second-jet separation. -/
theorem trace_two_ordered_roots_force_sharp_curvature
    (f f1 f2 : Real -> Real) (da db dd : Real)
    {A B thetaLeft thetaRight : Real}
    (hthetaOrder : thetaLeft < thetaRight)
    (hthetaLeft : thetaLeft ∈ Icc A B)
    (hthetaRight : thetaRight ∈ Icc A B)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hrootLeft : traceFunction f da db dd thetaLeft = 0)
    (hrootRight : traceFunction f da db dd thetaRight = 0)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z) :
    forall z, z ∈ Icc A B ->
      coefficientDistance da db dd / 45 <
        |traceSecondDerivative f1 f2 db dd z| := by
  rcases global_value_or_first_or_second_jet_separation_sharp da db dd with
      hvalue | hfirst | hsecond
  · have hvalueAt : coefficientDistance da db dd / 3 <=
        |traceFunction f da db dd thetaLeft| := by
      simpa [traceFunction] using
        hvalue (f thetaLeft) thetaLeft
          (hparameter thetaLeft hthetaLeft) (hft thetaLeft hthetaLeft)
    rw [hrootLeft, abs_zero] at hvalueAt
    exfalso
    nlinarith
  · have htraceDeriv : forall z, z ∈ Icc thetaLeft thetaRight ->
        HasDerivAt (traceFunction f da db dd)
          (traceFirstDerivative f f1 db dd z) z := by
      intro z hz
      have hzOuter : z ∈ Icc A B :=
        ⟨hthetaLeft.1.trans hz.1, hz.2.trans hthetaRight.2⟩
      exact hasDerivAt_traceFunction f f1 da db dd z
        (hfDeriv z hzOuter)
    obtain ⟨z, hz, hzero⟩ :=
      exists_derivative_zero_between_zeros
        (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd)
        hthetaOrder htraceDeriv hrootLeft hrootRight
    have hzOuter : z ∈ Icc A B :=
      ⟨hthetaLeft.1.trans (le_of_lt hz.1),
        (le_of_lt hz.2).trans hthetaRight.2⟩
    have hfirstAt : coefficientDistance da db dd / 12 <=
        |traceFirstDerivative f f1 db dd z| := by
      simpa [traceFirstDerivative] using
        hfirst (f z) (f1 z) z (hparameter z hzOuter) (hft z hzOuter)
          (hf1Lower z hzOuter) (hf1Upper z hzOuter)
    rw [hzero, abs_zero] at hfirstAt
    exfalso
    nlinarith
  · intro z hz
    simpa [traceSecondDerivative] using
      hsecond (f1 z) (f2 z) z (hparameter z hz)
        (hf1Lower z hz) (hf2 z hz)

/-- Under nonvanishing curvature, a critical point of the actual trace is
unique on the ambient interval. -/
theorem trace_criticalPoint_unique_of_sharp_curvature
    (f f1 f2 : Real -> Real) (db dd coefficient : Real)
    {A B theta0 : Real}
    (htheta0 : theta0 ∈ Icc A B)
    (hcritical : traceFirstDerivative f f1 db dd theta0 = 0)
    (hcoefficient : 0 < coefficient)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hcurvature : forall z, z ∈ Icc A B ->
      coefficient / 45 < |traceSecondDerivative f1 f2 db dd z|) :
    forall theta, theta ∈ Icc A B ->
      traceFirstDerivative f f1 db dd theta = 0 -> theta = theta0 := by
  intro theta htheta hthetaCritical
  rcases lt_trichotomy theta theta0 with hlt | heq | hgt
  · obtain ⟨z, hz, hzero⟩ :=
      exists_derivative_zero_between_zeros
        (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd) hlt
        (fun u hu =>
          hasDerivAt_traceFirstDerivative f f1 f2 db dd u
            (hfDeriv u
              ⟨htheta.1.trans hu.1, hu.2.trans htheta0.2⟩)
            (hf1Deriv u
              ⟨htheta.1.trans hu.1, hu.2.trans htheta0.2⟩))
        hthetaCritical hcritical
    have hzOuter : z ∈ Icc A B :=
      ⟨htheta.1.trans (le_of_lt hz.1),
        (le_of_lt hz.2).trans htheta0.2⟩
    have hpositive := hcurvature z hzOuter
    rw [hzero, abs_zero] at hpositive
    exfalso
    nlinarith
  · exact heq
  · obtain ⟨z, hz, hzero⟩ :=
      exists_derivative_zero_between_zeros
        (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd) hgt
        (fun u hu =>
          hasDerivAt_traceFirstDerivative f f1 f2 db dd u
            (hfDeriv u
              ⟨htheta0.1.trans hu.1, hu.2.trans htheta.2⟩)
            (hf1Deriv u
              ⟨htheta0.1.trans hu.1, hu.2.trans htheta.2⟩))
        hcritical hthetaCritical
    have hzOuter : z ∈ Icc A B :=
      ⟨htheta0.1.trans (le_of_lt hz.1),
        (le_of_lt hz.2).trans htheta.2⟩
    have hpositive := hcurvature z hzOuter
    rw [hzero, abs_zero] at hpositive
    exfalso
    nlinarith

/-- Scalar two-root version of PYZ Lemma 3.8(1), with the root-support
localization already normalized to the external coefficient scale `t`. -/
theorem trace_twoRoots_exists_uniqueCritical_and_rootSupport_localized
    (f f1 f2 : Real -> Real) (da db dd Delta thetaDelta : Real)
    {A B thetaLeft thetaRight delta t K : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hK : 0 <= K)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hthetaOrder : thetaLeft < thetaRight)
    (hthetaLeft : thetaLeft ∈ Icc A B)
    (hthetaRight : thetaRight ∈ Icc A B)
    (hrootLeft : traceFunction f da db dd thetaLeft = 0)
    (hrootRight : traceFunction f da db dd thetaRight = 0)
    (hcoefficientLower : t <= coefficientDistance da db dd)
    (hthetaDelta :
      thetaDelta ∈ centeredFractionIcc A B (1 / 2 : Real))
    (hDeltaDef : Delta = traceTangencyCost f f1 da db dd thetaDelta)
    (hDeltaUpper : Delta <= K * delta)
    (hsmallScale : K * delta < t / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B)) :
    exists theta0, theta0 ∈ Icc A B ∧
      traceFirstDerivative f f1 db dd theta0 = 0 ∧
      |traceFunction f da db dd theta0| <= 10 * Delta ∧
      (forall theta, theta ∈ Icc A B ->
        traceFirstDerivative f f1 db dd theta = 0 -> theta = theta0) ∧
      forall theta, theta ∈ prop41PairRootSupport thetaLeft thetaRight ->
        |theta - theta0| <=
          prop41CriticalLocalizationFactor K 0 * Real.sqrt (delta / t) := by
  have hcoefficient : 0 < coefficientDistance da db dd :=
    lt_of_lt_of_le ht hcoefficientLower
  have hDelta : 0 <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    positivity
  have hDeltaSmall : Delta < coefficientDistance da db dd / 1200 := by
    nlinarith
  have hcurvatureStrict :=
    trace_two_ordered_roots_force_sharp_curvature
      f f1 f2 da db dd hthetaOrder hthetaLeft hthetaRight hcoefficient
      hrootLeft hrootRight hparameter hft hf1Lower hf1Upper hf2 hfDeriv
  have hcurvatureLower : forall z, z ∈ Icc A B ->
      coefficientDistance da db dd / 45 <=
        |traceSecondDerivative f1 f2 db dd z| := by
    intro z hz
    exact le_of_lt (hcurvatureStrict z hz)
  obtain ⟨theta0, htheta0, hcritical, hcriticalValue⟩ :=
    trace_sharp_curvature_small_tangency_exists_criticalPoint_value_bound
      f f1 f2 da db dd Delta thetaDelta hwidth hcoefficient
      hthetaDelta hDeltaDef hDeltaSmall hfDeriv hf1Deriv hf2Continuous
      hparameter hf1Upper hf2 hcurvatureStrict
  have hkappa : 0 < coefficientDistance da db dd / 45 := by positivity
  have hleftLocalized : |thetaLeft - theta0| <=
      2 * Real.sqrt ((10 * Delta) /
        (coefficientDistance da db dd / 45)) := by
    have hraw := trace_sublevel_point_localized_near_criticalPoint
      f f1 f2 da db dd htheta0 hthetaLeft hkappa hcritical
      hfDeriv hf1Deriv hf2Continuous hcurvatureLower hcriticalValue
      (show |traceFunction f da db dd thetaLeft| <= 0 by
        rw [hrootLeft, abs_zero])
    simpa only [add_zero] using hraw
  have hrightLocalized : |thetaRight - theta0| <=
      2 * Real.sqrt ((10 * Delta) /
        (coefficientDistance da db dd / 45)) := by
    have hraw := trace_sublevel_point_localized_near_criticalPoint
      f f1 f2 da db dd htheta0 hthetaRight hkappa hcritical
      hfDeriv hf1Deriv hf2Continuous hcurvatureLower hcriticalValue
      (show |traceFunction f da db dd thetaRight| <= 0 by
        rw [hrootRight, abs_zero])
    simpa only [add_zero] using hraw
  refine ⟨theta0, htheta0, hcritical, hcriticalValue, ?_, ?_⟩
  · exact trace_criticalPoint_unique_of_sharp_curvature
      f f1 f2 db dd (coefficientDistance da db dd)
      htheta0 hcritical hcoefficient hfDeriv hf1Deriv hcurvatureStrict
  · intro theta htheta
    exact rootSupport_localized_at_critical_scale
      hdelta ht hcoefficientLower hDelta hK hDeltaUpper
      (by simpa [prop41PairRootSupport] using htheta)
      hleftLocalized hrightLocalized

/-- The canonical PYZ tangency distance for an actual tube pair, minimized
on the concentric middle half of the ambient interval. -/
noncomputable def prop41TubePairTangencyDistance
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (A B : Real) (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z) : Real :=
  tubePairAttainedTangencyDistance T U f f1 f2
    (centeredFractionLeft A B (1 / 2 : Real))
    (centeredFractionRight A B (1 / 2 : Real))
    (by
      simp only [centeredFractionLeft, centeredFractionRight]
      linarith)
    (fun z hz => hfDeriv z (by
      rcases hz with ⟨hzLeft, hzRight⟩
      constructor <;>
        simp only [centeredFractionLeft, centeredFractionRight] at * <;>
        linarith))
    (fun z hz => hf1Deriv z (by
      rcases hz with ⟨hzLeft, hzRight⟩
      constructor <;>
        simp only [centeredFractionLeft, centeredFractionRight] at * <;>
        linarith))

/-- Actual project tubes with two genuine graph intersections produce the
unique critical parameter and localized lens root support. -/
theorem actualTubePair_twoRoots_exists_uniqueCritical_and_rootSupport_localized
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    {A B thetaLeft thetaRight delta t K : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < t) (hK : 0 <= K)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hthetaOrder : thetaLeft < thetaRight)
    (hthetaLeft : thetaLeft ∈ Icc A B)
    (hthetaRight : thetaRight ∈ Icc A B)
    (hcommonC : tubeGraphC T = tubeGraphC U)
    (hrootLeft :
      cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) thetaLeft =
        cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) thetaLeft)
    (hrootRight :
      cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) thetaRight =
        cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) thetaRight)
    (hcoefficientLower : t <= tubePairCoefficientDistance T U)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hDeltaUpper :
      prop41TubePairTangencyDistance T U f f1 f2 A B hAB
        hfDeriv hf1Deriv <= K * delta)
    (hsmallScale : K * delta < t / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B)) :
    exists theta0, theta0 ∈ Icc A B ∧
      traceFirstDerivative f f1
        (tubePairDeltaB T U) (tubePairDeltaD T U) theta0 = 0 ∧
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) theta0| <=
          10 * prop41TubePairTangencyDistance T U f f1 f2 A B hAB
            hfDeriv hf1Deriv ∧
      (forall theta, theta ∈ Icc A B ->
        traceFirstDerivative f f1
          (tubePairDeltaB T U) (tubePairDeltaD T U) theta = 0 ->
        theta = theta0) ∧
      forall theta, theta ∈ prop41PairRootSupport thetaLeft thetaRight ->
        |theta - theta0| <=
          prop41CriticalLocalizationFactor K 0 * Real.sqrt (delta / t) := by
  let halfA := centeredFractionLeft A B (1 / 2 : Real)
  let halfB := centeredFractionRight A B (1 / 2 : Real)
  have hhalfAB : halfA <= halfB := by
    dsimp [halfA, halfB]
    simp only [centeredFractionLeft, centeredFractionRight]
    linarith
  have hhalfSubset : Icc halfA halfB ⊆ Icc A B := by
    intro z hz
    rcases hz with ⟨hzLeft, hzRight⟩
    constructor <;>
      dsimp [halfA, halfB] at * <;>
      simp only [centeredFractionLeft, centeredFractionRight] at * <;>
      linarith
  have hfDerivHalf : forall z, z ∈ Icc halfA halfB ->
      HasDerivAt f (f1 z) z := fun z hz => hfDeriv z (hhalfSubset hz)
  have hf1DerivHalf : forall z, z ∈ Icc halfA halfB ->
      HasDerivAt f1 (f2 z) z := fun z hz => hf1Deriv z (hhalfSubset hz)
  let Delta := prop41TubePairTangencyDistance T U f f1 f2 A B hAB
    hfDeriv hf1Deriv
  obtain ⟨thetaDelta, hthetaDelta, _hDeltaNonneg,
      hDeltaDef, _hminimum⟩ :=
    tubePairAttainedTangencyDistance_spec T U f f1 f2 halfA halfB
      hhalfAB hfDerivHalf hf1DerivHalf
  have hthetaDeltaCentered :
      thetaDelta ∈ centeredFractionIcc A B (1 / 2 : Real) := by
    simpa [centeredFractionIcc, halfA, halfB] using hthetaDelta
  have hDeltaDef' : Delta = traceTangencyCost f f1
      (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) thetaDelta := by
    simpa [Delta, prop41TubePairTangencyDistance, halfA, halfB] using
      hDeltaDef
  have htraceRootLeft : traceFunction f
      (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) thetaLeft = 0 := by
    rw [← tube_cinematicTraceValue_sub_eq_traceFunction
      T U f hcommonC thetaLeft, hrootLeft, sub_self]
  have htraceRootRight : traceFunction f
      (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) thetaRight = 0 := by
    rw [← tube_cinematicTraceValue_sub_eq_traceFunction
      T U f hcommonC thetaRight, hrootRight, sub_self]
  apply trace_twoRoots_exists_uniqueCritical_and_rootSupport_localized
    f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) Delta thetaDelta
      hdelta ht hK hwidth hthetaOrder hthetaLeft hthetaRight
      htraceRootLeft htraceRootRight
  · simpa [tubePairCoefficientDistance] using hcoefficientLower
  · exact hthetaDeltaCentered
  · exact hDeltaDef'
  · simpa [Delta] using hDeltaUpper
  · exact hsmallScale
  · exact hparameter
  · exact hft
  · exact hf1Lower
  · exact hf1Upper
  · exact hf2
  · exact hfDeriv
  · exact hf1Deriv
  · exact hf2Continuous

#print axioms trace_two_ordered_roots_force_sharp_curvature
#print axioms trace_criticalPoint_unique_of_sharp_curvature
#print axioms trace_twoRoots_exists_uniqueCritical_and_rootSupport_localized
#print axioms prop41TubePairTangencyDistance
#print axioms actualTubePair_twoRoots_exists_uniqueCritical_and_rootSupport_localized

end

end FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
