import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairApproxTraceV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SharpTangencyShift3TraceRootsV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairApproxCRectangleShift3TraceRootsV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32TubePairApproxTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41SharpTangencyShift3TraceRootsV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Approximate-c actual-pair rectangle to three-shift roots

Actual tubes selected from one narrow `c` bucket need not have literally
equal `c` coefficients.  The tracked approximate-trace adapter leaves the
linear `c` discrepancy explicit and absorbs it into the trace radius on
`|theta| <= 1`.  This module uses the exact budget
`2 * graphRadius + cError <= q * delta`, constructs the attained tangency
parameter internally, and then enters the root-free sharp-curvature
three-shift argument.

No root, tangency distance, critical point, or endpoint-sign datum is an
input.
-/

/-- A common canonical-quarter rectangle for an actual tube pair in an
approximate `c` bucket constructs its attained middle-half tangency minimum
and bounds it at the Proposition 4.1 scale. -/
theorem actualTubePair_commonCanonicalQuarterRectangle_approxC_forces_tangency_bound
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B x y delta t q cError baseRadius graphRadius : Real}
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hxy : x <= y)
    (hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real))
    (hrectangleWidth : Real.sqrt (delta / t) <= y - x)
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= cError)
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
    (htraceRadius : 2 * graphRadius + cError <= q * delta) :
    exists Delta thetaDelta,
      thetaDelta ∈ centeredFractionIcc A B (1 / 2 : Real) ∧
      0 <= Delta ∧
      Delta = traceTangencyCost f f1
        (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) thetaDelta ∧
      (forall z, z ∈ centeredFractionIcc A B (1 / 2 : Real) ->
        Delta <= traceTangencyCost f f1
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) z) ∧
      prop41TangencyProductCoefficient * (Delta + q * delta) *
          tubePairCoefficientDistance T U <=
        20000 * (q * delta) * (q * t) ∧
      Delta <= prop41TangencyScaleFactor q * delta := by
  let halfA := centeredFractionLeft A B (1 / 2 : Real)
  let halfB := centeredFractionRight A B (1 / 2 : Real)
  have hAB : A <= B := by linarith
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
  have hquarterSubset : centeredFractionIcc A B (1 / 4 : Real) ⊆
      Icc A B := quarter_subset_whole hAB
  have hxOuter : x ∈ Icc A B := hquarterSubset hxBase
  have hyOuter : y ∈ Icc A B := hquarterSubset hyBase
  have hcomponentOuter : Icc x y ⊆ Icc A B :=
    Icc_subset_Icc hxOuter.1 hyOuter.2
  have hfDerivHalf : forall z, z ∈ Icc halfA halfB ->
      HasDerivAt f (f1 z) z := fun z hz => hfDeriv z (hhalfSubset hz)
  have hf1DerivHalf : forall z, z ∈ Icc halfA halfB ->
      HasDerivAt f1 (f2 z) z := fun z hz => hf1Deriv z (hhalfSubset hz)
  obtain ⟨Delta, thetaDelta, hDeltaNonneg, hthetaDelta,
      hDeltaDef, hminimum⟩ :=
    exists_trace_tangencyParameter_with_minimizer
      f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) hhalfAB hfDerivHalf hf1DerivHalf
  have hthetaDeltaCentered :
      thetaDelta ∈ centeredFractionIcc A B (1 / 2 : Real) := by
    simpa [centeredFractionIcc, halfA, halfB] using hthetaDelta
  have hminimum' : forall z,
      z ∈ centeredFractionIcc A B (1 / 2 : Real) ->
        Delta <= traceTangencyCost f f1
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) z := by
    intro z hz
    have hzHalf : z ∈ Icc halfA halfB := by
      simpa [centeredFractionIcc, halfA, halfB] using hz
    exact hminimum z hzHalf
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
    exact (common_strip_tangency_forces_approx_tubePair_trace_sublevel
      T U f reference (Icc x y) cError
      (fun theta htheta => hparameter theta (hcomponentOuter htheta))
      hcBucket hbaseRadius hfirst hsecond z hz).trans htraceRadius
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
      hthetaDeltaCentered hDeltaDef hminimum' hparameter hft hf1Lower
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
  exact ⟨Delta, thetaDelta, hthetaDeltaCentered, hDeltaNonneg,
    hDeltaDef, hminimum', hproduct', hDeltaUpper⟩

/-- Numerical splice from the internally produced tangency bound to the
three-shift sharp-curvature consumer. -/
theorem approxC_prop41TangencyBound_shift3_numerics
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

/-- A common canonical-quarter rectangle for an actual tube pair in an
approximate `c` bucket produces one of the three integer shifts with one
trace root on each side of the constructed critical point. -/
theorem actualTubePair_commonCanonicalQuarterRectangle_approxC_exists_int_shift3_two_sided_roots
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B x y delta t q lambda cError baseRadius graphRadius : Real}
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
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= cError)
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
    (htraceRadius : 2 * graphRadius + cError <= q * delta) :
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
    actualTubePair_commonCanonicalQuarterRectangle_approxC_forces_tangency_bound
      T U f f1 f2 reference hdelta ht hq hwidth hxy hxBase hyBase
      hrectangleWidth hcBucket hcoefficientLower hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hbaseRadius hfirst hsecond htraceRadius
  obtain ⟨hDeltaSmall, hs, hcriticalBelowShift, hendpointGrowth⟩ :=
    approxC_prop41TangencyBound_shift3_numerics
      hdelta ht hq hcoefficientLower hDeltaUpper hlambda
      hshiftDominates hstrengthenedScale
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

#print axioms actualTubePair_commonCanonicalQuarterRectangle_approxC_forces_tangency_bound
#print axioms approxC_prop41TangencyBound_shift3_numerics
#print axioms actualTubePair_commonCanonicalQuarterRectangle_approxC_exists_int_shift3_two_sided_roots

end

end FamilyStickyCinematicL32Prop41ActualPairApproxCRectangleShift3TraceRootsV1
