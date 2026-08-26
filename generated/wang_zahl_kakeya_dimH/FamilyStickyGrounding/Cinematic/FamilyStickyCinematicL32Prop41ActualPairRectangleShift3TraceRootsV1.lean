import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairRootFreeRectangleTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SharpTangencyShift3TraceRootsV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairRectangleShift3TraceRootsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRootFreeRectangleTangencyV1
open FamilyStickyCinematicL32Prop41SharpTangencyShift3TraceRootsV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# A common actual-tube rectangle produces a three-shift two-root trace

This module connects the root-free canonical-quarter rectangle estimate to
the sharp-curvature three-shift argument.  The attained tangency parameter is
constructed internally.  A single strengthened small-scale inequality and a
dimensionless choice of shift multiplier discharge all three quantitative
premises of the sharp-curvature consumer.
-/

/-- The numerical splice used by the actual-pair theorem.  Once
`Delta <= K(q) * delta`, choosing `s = lambda * delta` with
`10 * K(q) < lambda` makes the shift dominate the critical value.  The one
strengthened scale inequality also puts both the tangency and the shifted
critical value below the curvature-growth threshold. -/
theorem prop41TangencyBound_shift3_numerics
    {Delta delta t coefficient q lambda : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hcoefficientLower : t <= coefficient)
    (hDeltaUpper : Delta <= prop41TangencyScaleFactor q * delta)
    (hlambda : 0 < lambda)
    (hshiftDominates : 10 * prop41TangencyScaleFactor q < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080) :
    Delta < coefficient / 1200 ∧
      0 < lambda * delta ∧
      10 * Delta < lambda * delta ∧
      10 * Delta + lambda * delta <
        ((coefficient / 45) / 4) * (1 / 16 : Real) ^ 2 := by
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hfactorPos : 0 < prop41TangencyScaleFactor q := by
    rw [prop41TangencyScaleFactor]
    exact div_pos (mul_pos (by norm_num) (pow_pos hqPos 2))
      prop41TangencyProductCoefficient_pos
  have hfactorBelowCombined :
      prop41TangencyScaleFactor q <
        10 * prop41TangencyScaleFactor q + lambda := by
    nlinarith
  have hfactorScale :
      prop41TangencyScaleFactor q * delta < t / 1200 := by
    calc
      prop41TangencyScaleFactor q * delta <
          (10 * prop41TangencyScaleFactor q + lambda) * delta :=
        mul_lt_mul_of_pos_right hfactorBelowCombined hdelta
      _ < t / 46080 := hstrengthenedScale
      _ < t / 1200 := by nlinarith
  have hDeltaSmall : Delta < coefficient / 1200 := by
    calc
      Delta <= prop41TangencyScaleFactor q * delta := hDeltaUpper
      _ < t / 1200 := hfactorScale
      _ <= coefficient / 1200 := by linarith
  have hs : 0 < lambda * delta := mul_pos hlambda hdelta
  have hshiftScaled :
      (10 * prop41TangencyScaleFactor q) * delta < lambda * delta :=
    mul_lt_mul_of_pos_right hshiftDominates hdelta
  have hcriticalBelowShift : 10 * Delta < lambda * delta := by
    calc
      10 * Delta <= 10 * (prop41TangencyScaleFactor q * delta) := by
        gcongr
      _ = (10 * prop41TangencyScaleFactor q) * delta := by ring
      _ < lambda * delta := hshiftScaled
  have hendpointGrowth :
      10 * Delta + lambda * delta <
        ((coefficient / 45) / 4) * (1 / 16 : Real) ^ 2 := by
    calc
      10 * Delta + lambda * delta <=
          10 * (prop41TangencyScaleFactor q * delta) +
            lambda * delta := by
        gcongr
      _ = (10 * prop41TangencyScaleFactor q + lambda) * delta := by ring
      _ < t / 46080 := hstrengthenedScale
      _ <= coefficient / 46080 := by linarith
      _ = ((coefficient / 45) / 4) * (1 / 16 : Real) ^ 2 := by ring
  exact ⟨hDeltaSmall, hs, hcriticalBelowShift, hendpointGrowth⟩

/-- A common canonical-quarter rectangle for an actual tube pair in one
`c`-slice, together with the sharp-curvature branch, produces one of the
three integer vertical shifts whose trace has a root on each side of its
critical point.  Neither a tangency distance nor any root or endpoint sign is
assumed. -/
theorem actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots
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
    (hcurvatureStrict : forall z, z ∈ Icc A B ->
      tubePairCoefficientDistance T U / 45 <
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z|)
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
    ∃ (eta : Int) (theta0 thetaLeft thetaRight : Real),
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
  have hcoefficient : 0 < tubePairCoefficientDistance T U :=
    lt_of_lt_of_le ht hcoefficientLower
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
  obtain ⟨Delta, thetaDelta, hthetaDelta, _hDeltaNonneg,
      hDeltaDef, _hminimum, _hproduct, hDeltaUpper⟩ :=
    actualTubePair_commonCanonicalQuarterRectangle_forces_tangency_bound
      T U f f1 f2 reference hdelta ht hq hwidth hxy hxBase hyBase
      hrectangleWidth hcommonC hcoefficientLower hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hbaseRadius hfirst hsecond htraceRadius
  obtain ⟨hDeltaSmall, hs, hcriticalBelowShift, hendpointGrowth⟩ :=
    prop41TangencyBound_shift3_numerics hdelta ht hq hcoefficientLower
      hDeltaUpper hlambda hshiftDominates hstrengthenedScale
  exact trace_sharp_tangency_exists_int_shift3_two_sided_roots
    f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) Delta thetaDelta (lambda * delta)
      hwidth
      (by simpa [tubePairCoefficientDistance] using hcoefficient)
      hthetaDelta hDeltaDef
      (by simpa [tubePairCoefficientDistance] using hDeltaSmall)
      hs hcriticalBelowShift
      (by simpa [tubePairCoefficientDistance] using hendpointGrowth)
      hfDeriv hf1Deriv hf2Continuous hparameter hf1Upper hf2
      (by
        intro z hz
        simpa [tubePairCoefficientDistance] using hcurvatureStrict z hz)

#print axioms prop41TangencyBound_shift3_numerics
#print axioms actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots

end

end FamilyStickyCinematicL32Prop41ActualPairRectangleShift3TraceRootsV1
