import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairRootFreeRectangleTangencyV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairAutomaticSharpCurvatureV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRootFreeRectangleTangencyV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Automatically entering the sharp-curvature branch

Coefficient separation and the normalized `f`, `f'`, and `f''` bounds alone
do not force curvature separation: the coefficient difference may be purely
constant.  The honest automatic statement is the global value/first/second
jet trichotomy.  Once a tangency-cost witness is smaller than
`coefficientDistance / 1200`, its value and first-jet components exclude the
first two alternatives at that same parameter, leaving the uniform sharp
curvature branch.
-/

/-- A concrete obstruction to deriving sharp curvature from coefficient
separation and the normalization bounds alone: a purely constant coefficient
difference has positive coefficient distance and identically zero second
jet. -/
theorem coefficientBounds_alone_do_not_force_sharpCurvature :
    Not (forall da db dd ft f1 f2 t : Real,
      0 < coefficientDistance da db dd ->
      |t| <= 1 -> |ft| <= 2 ->
      1 <= |f1| -> |f1| <= 2 -> |f2| <= 1 / 100 ->
      coefficientDistance da db dd / 45 <
        |traceJet2 db dd f1 f2 t|) := by
  intro h
  have hfalse := h 1 0 0 0 1 0 0
    (by norm_num [coefficientDistance])
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [coefficientDistance, traceJet2] at hfalse

/-- Honest automatic specialization of the global coefficient trichotomy to
the reduced trace of an actual tube pair on one interval.  The third branch
is exactly the `hcurvatureStrict` interface used downstream; the first two
branches remain explicit rather than being silently discarded. -/
theorem actualTubePair_value_or_first_or_sharpCurvature
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) {A B : Real}
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    (forall z, z ∈ Icc A B ->
      tubePairCoefficientDistance T U / 3 <=
        |traceFunction f
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) z|) ∨
    (forall z, z ∈ Icc A B ->
      tubePairCoefficientDistance T U / 12 <=
        |traceFirstDerivative f f1
          (tubePairDeltaB T U) (tubePairDeltaD T U) z|) ∨
    (forall z, z ∈ Icc A B ->
      tubePairCoefficientDistance T U / 45 <
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z|) := by
  rcases global_value_or_first_or_second_jet_separation_sharp
      (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U) with
    hvalue | hfirst | hcurvature
  · left
    intro z hz
    simpa [tubePairCoefficientDistance, traceFunction] using
      hvalue (f z) z (hparameter z hz) (hft z hz)
  · right
    left
    intro z hz
    simpa [tubePairCoefficientDistance, traceFirstDerivative] using
      hfirst (f z) (f1 z) z (hparameter z hz) (hft z hz)
        (hf1Lower z hz) (hf1Upper z hz)
  · right
    right
    intro z hz
    simpa [tubePairCoefficientDistance, traceSecondDerivative] using
      hcurvature (f1 z) (f2 z) z (hparameter z hz)
        (hf1Lower z hz) (hf2 z hz)

/-- A sufficiently small attained tangency cost excludes the uniform value
and uniform first-jet alternatives at its attaining parameter.  Hence the
actual tube pair is automatically in the global sharp-curvature branch.
No root, endpoint sign, or curvature hypothesis is assumed. -/
theorem actualTubePair_small_tangency_forces_sharpCurvature
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) (Delta thetaDelta : Real)
    {A B : Real}
    (hthetaDelta : thetaDelta ∈ Icc A B)
    (hDeltaDef :
      Delta = traceTangencyCost f f1
        (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) thetaDelta)
    (hDeltaSmall :
      Delta < tubePairCoefficientDistance T U / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100) :
    forall z, z ∈ Icc A B ->
      tubePairCoefficientDistance T U / 45 <
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| := by
  have hvalueUpper :
      |traceFunction f
        (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) thetaDelta| <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hfirstUpper :
      |traceFirstDerivative f f1
        (tubePairDeltaB T U) (tubePairDeltaD T U) thetaDelta| <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    exact le_add_of_nonneg_left (abs_nonneg _)
  have hDeltaNonneg : 0 <= Delta := by
    rw [hDeltaDef, traceTangencyCost]
    positivity
  rcases actualTubePair_value_or_first_or_sharpCurvature
      T U f f1 f2 hparameter hft hf1Lower hf1Upper hf2 with
    hvalue | hfirst | hcurvature
  · have hvalueLower := hvalue thetaDelta hthetaDelta
    exfalso
    nlinarith
  · have hfirstLower := hfirst thetaDelta hthetaDelta
    exfalso
    nlinarith
  · exact hcurvature

/-- A common canonical-quarter rectangle in the small-scale regime supplies
its tangency minimizer internally and therefore forces the sharp-curvature
branch automatically.  This is the root-free actual-pair producer needed to
remove an externally supplied `hcurvatureStrict` from the high-payload chain.
-/
theorem actualTubePair_commonCanonicalQuarterRectangle_forces_sharpCurvature
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B x y delta t q baseRadius graphRadius : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hxy : x <= y)
    (hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hrectangleWidth : Real.sqrt (delta / t) <= y - x)
    (hcommonC : tubeGraphC T = tubeGraphC U)
    (hcoefficientLower : t <= tubePairCoefficientDistance T U)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hsmallScale :
      prop41TangencyScaleFactor q * delta < t / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hbaseRadius : 0 <= baseRadius)
    (hfirst : cinematicVerticalNeighborhood reference (Icc x y) baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T)) (Icc x y) graphRadius)
    (hsecond : cinematicVerticalNeighborhood reference (Icc x y) baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U)) (Icc x y) graphRadius)
    (htraceRadius : 2 * graphRadius <= q * delta) :
    forall z, z ∈ Icc A B ->
      tubePairCoefficientDistance T U / 45 <
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| := by
  obtain ⟨Delta, thetaDelta, hthetaDelta, _hDeltaNonneg,
      hDeltaDef, _hminimum, _hproduct, hDeltaUpper⟩ :=
    actualTubePair_commonCanonicalQuarterRectangle_forces_tangency_bound
      T U f f1 f2 reference hdelta ht hq hwidth hxy hxBase hyBase
      hrectangleWidth hcommonC hcoefficientLower hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hbaseRadius hfirst hsecond htraceRadius
  have hDeltaSmall :
      Delta < tubePairCoefficientDistance T U / 1200 := by
    calc
      Delta <= prop41TangencyScaleFactor q * delta := hDeltaUpper
      _ < t / 1200 := hsmallScale
      _ <= tubePairCoefficientDistance T U / 1200 := by linarith
  have hthetaDeltaOuter : thetaDelta ∈ Icc A B := by
    rcases hthetaDelta with ⟨hleft, hright⟩
    constructor <;>
      simp only [centeredFractionLeft, centeredFractionRight] at * <;>
      linarith
  exact actualTubePair_small_tangency_forces_sharpCurvature
    T U f f1 f2 Delta thetaDelta hthetaDeltaOuter hDeltaDef hDeltaSmall
      hparameter hft hf1Lower hf1Upper hf2

#print axioms coefficientBounds_alone_do_not_force_sharpCurvature
#print axioms actualTubePair_value_or_first_or_sharpCurvature
#print axioms actualTubePair_small_tangency_forces_sharpCurvature
#print axioms actualTubePair_commonCanonicalQuarterRectangle_forces_sharpCurvature

end

end FamilyStickyCinematicL32Prop41ActualPairAutomaticSharpCurvatureV1
