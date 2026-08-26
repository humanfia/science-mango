import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairRootFreeRectangleTangencyV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CanonicalQuarterTangencyProductV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Root-free rectangle control of actual-pair tangency

The common-strip hypothesis gives a trace sublevel on a canonical-quarter
rectangle.  The attained minimum on the middle half and the canonical
Lemma 3.9 product then bound that minimum at the Proposition 4.1 scale.

This module is deliberately upstream of all root-selection arguments: its
theorem assumes neither intersections nor endpoint signs.
-/

/-- A common canonical-quarter rectangle for an actual tube pair produces
an attained middle-half tangency minimum, the precise Lemma 3.9 product,
and its resulting linear-in-`delta` upper bound.  No root data is used. -/
theorem actualTubePair_commonCanonicalQuarterRectangle_forces_tangency_bound
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

#print axioms actualTubePair_commonCanonicalQuarterRectangle_forces_tangency_bound

end

end FamilyStickyCinematicL32Prop41ActualPairRootFreeRectangleTangencyV1
