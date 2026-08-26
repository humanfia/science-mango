import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairAutomaticSharpCurvatureV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairShift3PointwiseAdapterV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairExactCShift3AutomaticV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleShift3TraceRootsV1
open FamilyStickyCinematicL32Prop41ActualPairAutomaticSharpCurvatureV1
open FamilyStickyCinematicL32Prop41ActualPairShift3PointwiseAdapterV1
open FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Exact-slice actual-pair roots with automatic sharp curvature

The common canonical-quarter rectangle first produces a small attained
tangency cost.  The global value/first/curvature trichotomy then forces the
sharp-curvature branch automatically.  Consequently the three-shift root
theorem needs no externally supplied curvature, root, endpoint sign, or
tangency parameter.
-/

/-- In the exact common-`c` slice, all sharp-curvature input is generated
from the common rectangle and the strengthened scale inequality.  The
result is the same integer three-shift/two-root conclusion as the earlier
conditional theorem, but `hcurvatureStrict` is absent from the signature. -/
theorem actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots_automaticSharp
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B x y delta t q lambda baseRadius graphRadius : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hlambda : 0 < lambda)
    (hshiftDominates : 10 * prop41TangencyScaleFactor q < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hxy : x <= y)
    (hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hrectangleWidth : Real.sqrt (delta / t) <= y - x)
    (hcommonC : tubeGraphC T = tubeGraphC U)
    (hcoefficientLower : t <= tubePairCoefficientDistance T U)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
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
    exists (eta : Int) (theta0 thetaLeft thetaRight : Real),
      (eta = -1 ∨ eta = 0 ∨ eta = 1) ∧
      theta0 ∈ Icc A B ∧
      traceFirstDerivative f f1
        (tubePairDeltaB T U) (tubePairDeltaD T U) theta0 = 0 ∧
      0 <
        traceFunction f
            (tubePairDeltaA T U + (eta : Real) * (lambda * delta))
            (tubePairDeltaB T U) (tubePairDeltaD T U) A *
          traceFunction f
            (tubePairDeltaA T U + (eta : Real) * (lambda * delta))
            (tubePairDeltaB T U) (tubePairDeltaD T U) B ∧
      thetaLeft ∈ Ioo A theta0 ∧
      traceFunction f
          (tubePairDeltaA T U + (eta : Real) * (lambda * delta))
          (tubePairDeltaB T U) (tubePairDeltaD T U) thetaLeft = 0 ∧
      thetaRight ∈ Ioo theta0 B ∧
      traceFunction f
          (tubePairDeltaA T U + (eta : Real) * (lambda * delta))
          (tubePairDeltaB T U) (tubePairDeltaD T U) thetaRight = 0 := by
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hfactorPos : 0 < prop41TangencyScaleFactor q := by
    rw [prop41TangencyScaleFactor]
    exact div_pos (mul_pos (by norm_num) (pow_pos hqPos 2))
      prop41TangencyProductCoefficient_pos
  have hfactorBelowCombined :
      prop41TangencyScaleFactor q <
        10 * prop41TangencyScaleFactor q + lambda := by
    nlinarith
  have hsmallScale :
      prop41TangencyScaleFactor q * delta < t / 1200 := by
    calc
      prop41TangencyScaleFactor q * delta <
          (10 * prop41TangencyScaleFactor q + lambda) * delta :=
        mul_lt_mul_of_pos_right hfactorBelowCombined hdelta
      _ < t / 46080 := hstrengthenedScale
      _ < t / 1200 := by nlinarith
  have hcurvatureStrict :=
    actualTubePair_commonCanonicalQuarterRectangle_forces_sharpCurvature
      T U f f1 f2 reference hdelta ht hq hwidth hxy hxBase hyBase
      hrectangleWidth hcommonC hcoefficientLower hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hbaseRadius hfirst hsecond htraceRadius
  exact
    actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots
      T U f f1 f2 reference hdelta ht hq hlambda hshiftDominates
      hstrengthenedScale hwidth hxy hxBase hyBase hrectangleWidth
      hcommonC hcoefficientLower hfDeriv hf1Deriv hparameter hft
      hf1Lower hf1Upper hf2 hf2Continuous hcurvatureStrict hbaseRadius
      hfirst hsecond htraceRadius

/-- Direct pointwise form for the global three-shift pigeonhole interface.
It performs the integer-to-real conversion internally and fixes the shift
scale to `lambda * delta`. -/
theorem actualTubePair_commonCanonicalQuarterRectangle_exists_real_shift3_scalarRoots_automaticSharp
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B x y delta t q lambda baseRadius graphRadius : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hlambda : 0 < lambda)
    (hshiftDominates : 10 * prop41TangencyScaleFactor q < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hxy : x <= y)
    (hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hrectangleWidth : Real.sqrt (delta / t) <= y - x)
    (hcommonC : tubeGraphC T = tubeGraphC U)
    (hcoefficientLower : t <= tubePairCoefficientDistance T U)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
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
    exists eta : Real,
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      HasScalarTwoSidedRootsAtShift
        T U f A B (lambda * delta) eta := by
  obtain ⟨eta, theta0, thetaLeft, thetaRight, heta,
      _htheta0, _hcritical, _hendpoints, hthetaLeft, hrootLeft,
      hthetaRight, hrootRight⟩ :=
    actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots_automaticSharp
      T U f f1 f2 reference hdelta ht hq hlambda hshiftDominates
      hstrengthenedScale hwidth hxy hxBase hyBase hrectangleWidth
      hcommonC hcoefficientLower hfDeriv hf1Deriv hparameter hft
      hf1Lower hf1Upper hf2 hf2Continuous hbaseRadius hfirst hsecond
      htraceRadius
  exact exists_real_threeShift_scalarRoots_of_int_threeShift_scalarRoots
    T U f A B (lambda * delta)
      ⟨eta, theta0, thetaLeft, thetaRight, heta,
        hthetaLeft, hrootLeft, hthetaRight, hrootRight⟩

#print axioms actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots_automaticSharp
#print axioms actualTubePair_commonCanonicalQuarterRectangle_exists_real_shift3_scalarRoots_automaticSharp

end

end FamilyStickyCinematicL32Prop41ActualPairExactCShift3AutomaticV1
