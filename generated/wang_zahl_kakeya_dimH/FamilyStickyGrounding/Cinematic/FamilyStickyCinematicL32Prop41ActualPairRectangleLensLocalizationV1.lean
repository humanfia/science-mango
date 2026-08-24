import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TraceSublevelLocalizationV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1
open FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Actual rectangle and lens localization for PYZ Lemma 4.7

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemmas 3.8,
3.9, and 4.7.

A common graph strip produces the literal trace sublevel on the rectangle
base.  The canonical-quarter Lemma 3.9 product and the coefficient lower
scale automatically produce `Delta <= K(q) * delta`.  The two-root module
then constructs the unique critical parameter.  Both the rectangle base and
the full interval between the roots are localized at that same parameter.
-/

/-- One radius that simultaneously contains the rectangle base and the
root-support interval. -/
noncomputable def prop41ActualPairLocalizationRadius
    (q delta t : Real) : Real :=
  prop41CriticalLocalizationFactor (prop41TangencyScaleFactor q) q *
    Real.sqrt (delta / t)

/-- General `q`-scale form.  No tangency-distance upper bound is supplied:
it is derived from the actual canonical Lemma 3.9 product. -/
theorem actualTubePair_rectangleBase_and_rootSupport_localized
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B thetaLeft thetaRight x y delta t q baseRadius graphRadius : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hxy : x <= y)
    (hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hrectangleWidth : Real.sqrt (delta / t) <= y - x)
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
    exists theta0, theta0 ∈ Icc A B ∧
      traceFirstDerivative f f1
        (tubePairDeltaB T U) (tubePairDeltaD T U) theta0 = 0 ∧
      (forall theta, theta ∈ Icc A B ->
        traceFirstDerivative f f1
          (tubePairDeltaB T U) (tubePairDeltaD T U) theta = 0 ->
        theta = theta0) ∧
      (forall theta, theta ∈ prop41PairRootSupport thetaLeft thetaRight ->
        |theta - theta0| <= prop41ActualPairLocalizationRadius q delta t) ∧
      forall theta, theta ∈ Icc x y ->
        |theta - theta0| <= prop41ActualPairLocalizationRadius q delta t := by
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
  obtain ⟨thetaDelta, hthetaDelta, hDeltaNonneg,
      hDeltaDef, hminimum⟩ :=
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
  have hminimum' : forall z,
      z ∈ centeredFractionIcc A B (1 / 2 : Real) ->
        Delta <= traceTangencyCost f f1
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) z := by
    intro z hz
    have hzHalf : z ∈ Icc halfA halfB := by
      simpa [centeredFractionIcc, halfA, halfB] using hz
    simpa [Delta, prop41TubePairTangencyDistance, halfA, halfB] using
      hminimum z hzHalf
  have hcoefficient : 0 < tubePairCoefficientDistance T U :=
    lt_of_lt_of_le ht hcoefficientLower
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqdelta : 0 < q * delta := mul_pos hqPos hdelta
  have hqt : 0 < q * t := mul_pos hqPos ht
  have hdeltaSmall : q * delta < tubePairCoefficientDistance T U / 2400 :=
    q_mul_delta_lt_coefficient_div_2400_of_scaleSmall
      hdelta ht hq hcoefficientLower hsmallScale
  have hcomponentSublevel : forall z, z ∈ Icc x y ->
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) z| <= q * delta := by
    intro z hz
    exact (common_strip_tangency_forces_tubePair_trace_sublevel
      T U f reference (Icc x y) hcommonC hbaseRadius hfirst hsecond
      z hz).trans htraceRadius
  have hscaledWidth : Real.sqrt ((q * delta) / (q * t)) <= y - x := by
    have hratio : (q * delta) / (q * t) = delta / t := by
      field_simp [ne_of_gt hqPos, ne_of_gt ht]
    simpa only [hratio] using hrectangleWidth
  have hproduct := canonical_quarter_rectangle_width_forces_tangency_product
    f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) Delta thetaDelta hxy hxBase hyBase hwidth
      hqdelta hqt
      (by simpa [tubePairCoefficientDistance] using hcoefficient)
      (by simpa [tubePairCoefficientDistance] using hdeltaSmall)
      hthetaDeltaCentered hDeltaDef' hminimum' hparameter hft hf1Lower
      hf1Upper hf2 hfDeriv hf1Deriv hf2Continuous hcomponentSublevel
      hscaledWidth
  have hproduct' :
      prop41TangencyProductCoefficient * (Delta + q * delta) *
          tubePairCoefficientDistance T U <=
        20000 * (q * delta) * (q * t) := by
    simpa [prop41TangencyProductCoefficient, tubePairCoefficientDistance]
      using hproduct
  have hDeltaUpper : Delta <= prop41TangencyScaleFactor q * delta :=
    tangency_le_prop41TangencyScaleFactor_mul_delta_of_product
      hdelta ht hqPos hcoefficientLower hproduct'
  have hscaleFactorPos : 0 < prop41TangencyScaleFactor q := by
    rw [prop41TangencyScaleFactor]
    exact div_pos (by positivity) prop41TangencyProductCoefficient_pos
  have hDeltaNonnegCanonical : 0 <=
      prop41TubePairTangencyDistance T U f f1 f2 A B hAB
        hfDeriv hf1Deriv := by
    change 0 <= Delta
    rw [hDeltaDef', traceTangencyCost]
    positivity
  obtain ⟨theta0, htheta0, hcritical, hcriticalValue,
      hcriticalUnique, hrootLocalized⟩ :=
    actualTubePair_twoRoots_exists_uniqueCritical_and_rootSupport_localized
      T U f f1 f2 hAB hdelta ht
      (le_of_lt hscaleFactorPos)
      hwidth hthetaOrder hthetaLeft hthetaRight hcommonC
      hrootLeft hrootRight hcoefficientLower hfDeriv hf1Deriv
      hDeltaUpper hsmallScale
      hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
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
  have hcurvatureStrict :=
    trace_two_ordered_roots_force_sharp_curvature
      f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) hthetaOrder hthetaLeft hthetaRight
      (by simpa [tubePairCoefficientDistance] using hcoefficient)
      htraceRootLeft htraceRootRight hparameter hft hf1Lower hf1Upper hf2
      hfDeriv
  have hcurvatureLower : forall z, z ∈ Icc A B ->
      tubePairCoefficientDistance T U / 45 <=
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| := by
    intro z hz
    simpa [tubePairCoefficientDistance] using le_of_lt (hcurvatureStrict z hz)
  have hkappa : 0 < tubePairCoefficientDistance T U / 45 := by positivity
  have hquarterSubset : centeredFractionIcc A B (1 / 4 : Real) ⊆
      Icc A B := by
    intro z hz
    rcases hz with ⟨hzLeft, hzRight⟩
    constructor <;>
      simp only [centeredFractionLeft, centeredFractionRight] at * <;>
      linarith
  have hxOuter : x ∈ Icc A B := hquarterSubset hxBase
  have hyOuter : y ∈ Icc A B := hquarterSubset hyBase
  have hbaseLocalized : forall z, z ∈ Icc x y ->
      |z - theta0| <= prop41ActualPairLocalizationRadius q delta t := by
    intro z hz
    have hzOuter : z ∈ Icc A B :=
      ⟨hxOuter.1.trans hz.1, hz.2.trans hyOuter.2⟩
    have hraw := trace_sublevel_point_localized_near_criticalPoint
      f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) htheta0 hzOuter hkappa hcritical
      hfDeriv hf1Deriv hf2Continuous hcurvatureLower hcriticalValue
      (hcomponentSublevel z hz)
    exact hraw.trans (by
      simpa [prop41ActualPairLocalizationRadius] using
        two_mul_sqrt_critical_ratio_le_factor_mul_sqrt_delta_div_scale
          hdelta ht hcoefficientLower hDeltaNonnegCanonical
          (le_of_lt hscaleFactorPos) (le_of_lt hqPos) hDeltaUpper)
  have hfactorMono :
      prop41CriticalLocalizationFactor (prop41TangencyScaleFactor q) 0 <=
        prop41CriticalLocalizationFactor (prop41TangencyScaleFactor q) q := by
    dsimp [prop41CriticalLocalizationFactor]
    gcongr
  have hsqrtNonneg : 0 <= Real.sqrt (delta / t) := Real.sqrt_nonneg _
  refine ⟨theta0, htheta0, hcritical, hcriticalUnique, ?_, hbaseLocalized⟩
  intro z hz
  exact (hrootLocalized z hz).trans (by
    dsimp [prop41ActualPairLocalizationRadius]
    exact mul_le_mul_of_nonneg_right hfactorMono hsqrtNonneg)

/-- Literal common `2 * lambda * delta` tangency, the form used in PYZ
Lemma 4.7. -/
theorem actualTubePair_twoLambdaTangent_rectangleBase_and_rootSupport_localized
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B thetaLeft thetaRight x y delta t lambda baseRadius : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < t)
    (hlambda : 1 <= lambda)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hxy : x <= y)
    (hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hrectangleWidth : Real.sqrt (delta / t) <= y - x)
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
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda) * delta <
      t / 1200)
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
          (tubeGraphC T) (tubeGraphD T)) (Icc x y) (2 * lambda * delta))
    (hsecond : cinematicVerticalNeighborhood reference (Icc x y) baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U)) (Icc x y) (2 * lambda * delta)) :
    exists theta0, theta0 ∈ Icc A B ∧
      traceFirstDerivative f f1
        (tubePairDeltaB T U) (tubePairDeltaD T U) theta0 = 0 ∧
      (forall theta, theta ∈ Icc A B ->
        traceFirstDerivative f f1
          (tubePairDeltaB T U) (tubePairDeltaD T U) theta = 0 ->
        theta = theta0) ∧
      (forall theta, theta ∈ prop41PairRootSupport thetaLeft thetaRight ->
        |theta - theta0| <=
          prop41ActualPairLocalizationRadius (4 * lambda) delta t) ∧
      forall theta, theta ∈ Icc x y ->
        |theta - theta0| <=
          prop41ActualPairLocalizationRadius (4 * lambda) delta t := by
  apply actualTubePair_rectangleBase_and_rootSupport_localized
    T U f f1 f2 reference hAB hdelta ht
      (show 1 <= 4 * lambda by nlinarith)
      hwidth hxy hxBase hyBase hrectangleWidth hthetaOrder
      hthetaLeft hthetaRight hcommonC hrootLeft hrootRight
      hcoefficientLower hfDeriv hf1Deriv hsmallScale hparameter hft
      hf1Lower hf1Upper hf2 hf2Continuous hbaseRadius hfirst hsecond
  ring_nf
  exact le_rfl

#print axioms prop41ActualPairLocalizationRadius
#print axioms actualTubePair_rectangleBase_and_rootSupport_localized
#print axioms actualTubePair_twoLambdaTangent_rectangleBase_and_rootSupport_localized

end

end FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
