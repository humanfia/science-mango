import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped Interval

namespace FamilyStickyCinematicL32Prop41ActualY1SharpPointSlopeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32Prop41ActualPairAutomaticSharpCurvatureV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
open FamilyStickyCinematicL32TraceSublevelLocalizationV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# The Lemma 3.8(2c) point-slope estimate for an actual Y1 pair

The attained tangency cost `Delta₀` is compared to the actual reduced
coefficient distance `d`.

* If `Delta₀ < d / 1200`, the global jet trichotomy forces sharp curvature.
  A genuine critical point then localizes the physical Y1 parameter, and
  second-jet transport gives a square-root point-slope bound.
* Otherwise `d <= 1200 Delta₀ <= 2400 globalDelta`, so the direct normalized
  first-jet estimate gives the same square-root bound.

No component-interior conclusion or point-slope estimate is assumed.
-/

/-- The sharpened two-regime form of PYZ Lemma 3.8(2c), specialized to the
literal active tube and assigned tube at an actual Y1 point. -/
theorem ActualCenteredHalfY1ActiveGeometryFacts.actual_pointSlope_le_sharpScale
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical :
      FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
        (Real × Real) iota)
    (E : Set (Real × Real))
    (activeAtPoint : Real × Real -> Finset iota)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (N : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (q : Real × Real) (hq : q ∈ E)
    (hqTheta : q.2 ∈ centeredFractionIcc outerA outerB (1 / 16 : Real))
    (i : iota) (hi : i ∈ activeAtPoint q) :
    |tubeCinematicTraceFirstValue (fine.tubes i) f f1 q.2 -
        tubeCinematicTraceFirstValue (tubeAt q) f f1 q.2| <=
      prop41Y1SharpSlopeConstant *
        Real.sqrt (tGlobal * globalDelta) := by
  let T := fine.tubes i
  let U := tubeAt q
  let halfA := centeredFractionLeft outerA outerB (1 / 2 : Real)
  let halfB := centeredFractionRight outerA outerB (1 / 2 : Real)
  have hhalf : halfA <= halfB :=
    (centered_half_and_quarter_endpoints_ordered hOuter).1
  let hfHalf : forall z, z ∈ Icc halfA halfB -> HasDerivAt f (f1 z) z :=
    fun z _hz => hf z
  let hf1Half : forall z, z ∈ Icc halfA halfB -> HasDerivAt f1 (f2 z) z :=
    fun z _hz => hf1 z
  let Delta := tubePairAttainedTangencyDistance T U f f1 f2 halfA halfB
    hhalf hfHalf hf1Half
  obtain ⟨thetaDelta, hthetaDeltaHalf, hDeltaNonneg, hDeltaDef,
      _hminimum⟩ :=
    tubePairAttainedTangencyDistance_spec T U f f1 f2 halfA halfB
      hhalf hfHalf hf1Half
  have hDeltaNonneg' : 0 <= Delta := by
    simpa only [Delta] using hDeltaNonneg
  have hDeltaDef' : Delta = traceTangencyCost f f1
      (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
      thetaDelta := by
    simpa only [Delta] using hDeltaDef
  have hDeltaBudget : Delta + (radius : Real) <= 2 * globalDelta := by
    simpa only [Delta, T, U, halfA, halfB, hfHalf, hf1Half] using
      facts.hactiveTangencyUpper q hq i hi
  have hDeltaUpper : Delta <= 2 * globalDelta := by
    nlinarith [N.fineDelta_pos]
  have hthetaDeltaCentered :
      thetaDelta ∈ centeredFractionIcc outerA outerB (1 / 2 : Real) := by
    simpa only [centeredFractionIcc, halfA, halfB] using hthetaDeltaHalf
  have hthetaDeltaOuter : thetaDelta ∈ Icc outerA outerB :=
    half_subset_whole hOuter hthetaDeltaCentered
  have hAB : outerA < outerB := by
    linarith [N.outerWidth_lower]
  have hqQuarterInterior := sixteenth_subset_Ioo_quarter hAB hqTheta
  have hqOuter : q.2 ∈ Icc outerA outerB :=
    quarter_subset_whole hOuter
      ⟨hqQuarterInterior.1.le, hqQuarterInterior.2.le⟩
  have hcoefficientUpper :
      tubePairCoefficientDistance T U <= 6 * tGlobal := by
    simpa only [T, U] using facts.hactiveCoefficientUpper q hq i hi
  have hcoefficientNonneg :
      0 <= tubePairCoefficientDistance T U := by
    unfold tubePairCoefficientDistance coefficientDistance
    positivity
  have hglobalDeltaLeSqrt :
      globalDelta <= Real.sqrt (tGlobal * globalDelta) := by
    have hsqrtNonneg := Real.sqrt_nonneg (tGlobal * globalDelta)
    have hsqrtSq :
        (Real.sqrt (tGlobal * globalDelta)) ^ 2 =
          tGlobal * globalDelta :=
      Real.sq_sqrt (mul_nonneg N.tGlobal_pos.le N.globalDelta_pos.le)
    have hDeltaSq :
        globalDelta ^ 2 <= tGlobal * globalDelta := by
      nlinarith [N.globalDelta_pos, N.globalDelta_le_tGlobal]
    nlinarith
  by_cases hsharp :
      Delta < tubePairCoefficientDistance T U / 1200
  · have hcoefficientPos :
        0 < tubePairCoefficientDistance T U := by
      by_contra hnot
      have hle : tubePairCoefficientDistance T U <= 0 := le_of_not_gt hnot
      nlinarith
    have hcurvatureStrict :=
      actualTubePair_small_tangency_forces_sharpCurvature
        T U f f1 f2 Delta thetaDelta hthetaDeltaOuter hDeltaDef' hsharp
          hparameter hft hf1Lower hf1Upper hf2
    have hcoefficientPosReduced :
        0 < coefficientDistance
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) := by
      simpa only [tubePairCoefficientDistance] using hcoefficientPos
    obtain ⟨theta0, htheta0, hcritical, hcriticalValue⟩ :=
      trace_sharp_curvature_small_tangency_exists_criticalPoint_value_bound
        f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) Delta thetaDelta N.outerWidth_lower
        hcoefficientPosReduced hthetaDeltaCentered hDeltaDef' (by
          simpa only [tubePairCoefficientDistance] using hsharp)
        (fun z _hz => hf z) (fun z _hz => hf1 z) hf2Continuous
        hparameter hf1Upper hf2 (by
          simpa only [tubePairCoefficientDistance] using hcurvatureStrict)
    have hkappa :
        0 < tubePairCoefficientDistance T U / 45 := by
      positivity
    have hcurvatureLower : forall z, z ∈ Icc outerA outerB ->
        tubePairCoefficientDistance T U / 45 <=
          |traceSecondDerivative f1 f2
            (tubePairDeltaB T U) (tubePairDeltaD T U) z| := by
      intro z hz
      exact le_of_lt (hcurvatureStrict z hz)
    have hqSublevel :
        |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
            (tubePairDeltaD T U) q.2| <= 5 * globalDelta := by
      have hraw := abs_tubePair_reducedTrace_le_fullGap_add_cError
        T U f q.2 (2 * (radius : Real)) ((radius : Real) / 2)
        (hparameter q.2 hqOuter)
        (by simpa only [T, U] using facts.hactiveFullWitness q hq i hi)
        (by simpa only [T, U] using facts.hactiveCBucket q hq i hi)
      exact hraw.trans (by
        nlinarith [N.fineDelta_le_globalDelta])
    have hqRaw : |q.2 - theta0| <=
        2 * Real.sqrt
          ((10 * Delta + 5 * globalDelta) /
            (tubePairCoefficientDistance T U / 45)) :=
      trace_sublevel_point_localized_near_criticalPoint
        f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) htheta0 hqOuter hkappa hcritical
        (fun z _hz => hf z) (fun z _hz => hf1 z) hf2Continuous
        hcurvatureLower hcriticalValue hqSublevel
    let slopeGap : Real -> Real := fun z =>
      tubeCinematicTraceFirstValue T f f1 z -
        tubeCinematicTraceFirstValue U f f1 z
    let secondGap : Real -> Real := fun z =>
      tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue U f1 f2 z
    have hderiv : forall z, z ∈ Icc outerA outerB ->
        HasDerivAt slopeGap (secondGap z) z := by
      intro z _hz
      dsimp only [slopeGap, secondGap]
      exact
        (hasDerivAt_cinematicTraceFirstValue f f1 f2
          (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
          (hf z) (hf1 z)).sub
        (hasDerivAt_cinematicTraceFirstValue f f1 f2
          (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
          (hf z) (hf1 z))
    have hsecondBound : forall z, z ∈ Icc outerA outerB ->
        |secondGap z| <=
          5 * tubePairCoefficientDistance T U := by
      intro z hz
      have hraw := abs_traceJet2_le_five_coefficientDistance
        (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
        (f1 z) (f2 z) z (hparameter z hz) (hf1Upper z hz) (hf2 z hz)
      have hrawBound :
          |traceSecondDerivative f1 f2 (tubePairDeltaB T U)
            (tubePairDeltaD T U) z| <=
              5 * tubePairCoefficientDistance T U := by
        simpa only [traceSecondDerivative, traceJet2,
          tubePairCoefficientDistance] using hraw
      calc
        |secondGap z| =
            |traceSecondDerivative f1 f2 (tubePairDeltaB T U)
              (tubePairDeltaD T U) z| := by
          dsimp only [secondGap]
          rw [tubeCinematicTraceSecondValue_sub_eq]
        _ <= 5 * tubePairCoefficientDistance T U := hrawBound
    have htransport :
        |slopeGap q.2 - slopeGap theta0| <=
          (5 * tubePairCoefficientDistance T U) * |q.2 - theta0| :=
      abs_sub_le_of_hasDerivAt_bound_on_Icc slopeGap secondGap
        hqOuter htheta0 hderiv hsecondBound
    have hcriticalActual :
        |slopeGap theta0| <= (radius : Real) / 2 := by
      dsimp only [slopeGap]
      rw [tubeCinematicTraceFirstValue_sub_eq, hcritical, add_zero]
      simpa only [T, U] using facts.hactiveCBucket q hq i hi
    let numerator : Real := 10 * Delta + 5 * globalDelta
    let rootRatio : Real :=
      Real.sqrt
        (numerator / (tubePairCoefficientDistance T U / 45))
    have hNumeratorNonneg : 0 <= numerator := by
      dsimp only [numerator]
      nlinarith [hDeltaNonneg', N.globalDelta_pos]
    have hNumeratorUpper : numerator <= 25 * globalDelta := by
      dsimp only [numerator]
      nlinarith
    have hratioNonneg :
        0 <= numerator / (tubePairCoefficientDistance T U / 45) := by
      positivity
    have hrootRatioNonneg : 0 <= rootRatio := by
      dsimp only [rootRatio]
      positivity
    have hrootRatioSq :
        rootRatio ^ 2 =
          numerator / (tubePairCoefficientDistance T U / 45) := by
      dsimp only [rootRatio]
      exact Real.sq_sqrt hratioNonneg
    have hcoefficientRootSq :
        tubePairCoefficientDistance T U * rootRatio ^ 2 =
          45 * numerator := by
      rw [hrootRatioSq]
      field_simp [ne_of_gt hcoefficientPos]
    have hcoefficientNumerator :
        tubePairCoefficientDistance T U * numerator <=
          150 * (tGlobal * globalDelta) := by
      calc
        tubePairCoefficientDistance T U * numerator <=
            (6 * tGlobal) * numerator :=
          mul_le_mul_of_nonneg_right hcoefficientUpper hNumeratorNonneg
        _ <= (6 * tGlobal) * (25 * globalDelta) :=
          mul_le_mul_of_nonneg_left hNumeratorUpper
            (mul_nonneg (by norm_num) N.tGlobal_pos.le)
        _ = 150 * (tGlobal * globalDelta) := by ring
    have hsqrtSq :
        (Real.sqrt (tGlobal * globalDelta)) ^ 2 =
          tGlobal * globalDelta :=
      Real.sq_sqrt (mul_nonneg N.tGlobal_pos.le N.globalDelta_pos.le)
    have hscaledSq :
        (10 * tubePairCoefficientDistance T U * rootRatio) ^ 2 <=
          (9000 * Real.sqrt (tGlobal * globalDelta)) ^ 2 := by
      calc
        (10 * tubePairCoefficientDistance T U * rootRatio) ^ 2 =
            100 * tubePairCoefficientDistance T U *
              (tubePairCoefficientDistance T U * rootRatio ^ 2) := by ring
        _ = 4500 * (tubePairCoefficientDistance T U * numerator) := by
          rw [hcoefficientRootSq]
          ring
        _ <= 4500 * (150 * (tGlobal * globalDelta)) :=
          mul_le_mul_of_nonneg_left hcoefficientNumerator (by norm_num)
        _ <= (9000 * Real.sqrt (tGlobal * globalDelta)) ^ 2 := by
          rw [mul_pow, hsqrtSq]
          norm_num
          nlinarith [mul_nonneg N.tGlobal_pos.le N.globalDelta_pos.le]
    have hscaled :
        10 * tubePairCoefficientDistance T U * rootRatio <=
          9000 * Real.sqrt (tGlobal * globalDelta) := by
      have hleftNonneg :
          0 <= 10 * tubePairCoefficientDistance T U * rootRatio := by
        positivity
      have hrightNonneg :
          0 <= 9000 * Real.sqrt (tGlobal * globalDelta) := by
        positivity
      nlinarith
    have htransportScaled :
        (5 * tubePairCoefficientDistance T U) * |q.2 - theta0| <=
          9000 * Real.sqrt (tGlobal * globalDelta) := by
      calc
        (5 * tubePairCoefficientDistance T U) * |q.2 - theta0| <=
            (5 * tubePairCoefficientDistance T U) * (2 * rootRatio) := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [numerator, rootRatio] using hqRaw
          · positivity
        _ = 10 * tubePairCoefficientDistance T U * rootRatio := by ring
        _ <= 9000 * Real.sqrt (tGlobal * globalDelta) := hscaled
    have hactualPoint :
        |slopeGap q.2| <=
          10000 * Real.sqrt (tGlobal * globalDelta) := by
      calc
        |slopeGap q.2| =
            |(slopeGap q.2 - slopeGap theta0) + slopeGap theta0| := by
          congr 1
          ring
        _ <= |slopeGap q.2 - slopeGap theta0| +
            |slopeGap theta0| := abs_add_le _ _
        _ <= (5 * tubePairCoefficientDistance T U) * |q.2 - theta0| +
            (radius : Real) / 2 :=
          add_le_add htransport hcriticalActual
        _ <= 9000 * Real.sqrt (tGlobal * globalDelta) +
            (radius : Real) / 2 :=
          add_le_add htransportScaled (le_refl ((radius : Real) / 2))
        _ <= 10000 * Real.sqrt (tGlobal * globalDelta) := by
          nlinarith [N.fineDelta_le_globalDelta, hglobalDeltaLeSqrt]
    simpa only [slopeGap, T, U, prop41Y1SharpSlopeConstant] using hactualPoint
  · have hDeltaLarge :
        tubePairCoefficientDistance T U / 1200 <= Delta :=
      le_of_not_gt hsharp
    have hcoefficientGlobal :
        tubePairCoefficientDistance T U <= 2400 * globalDelta := by
      nlinarith
    have hreduced :
        |traceFirstDerivative f f1
          (tubePairDeltaB T U) (tubePairDeltaD T U) q.2| <=
        4 * tubePairCoefficientDistance T U := by
      have hraw := abs_traceJet1_le_four_coefficientDistance
        (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
        (f q.2) (f1 q.2) q.2 (hparameter q.2 hqOuter)
        (hft q.2 hqOuter) (hf1Upper q.2 hqOuter)
      simpa only [traceFirstDerivative, tubePairCoefficientDistance] using hraw
    have hactualPoint :
        |tubeCinematicTraceFirstValue T f f1 q.2 -
            tubeCinematicTraceFirstValue U f f1 q.2| <=
          (radius : Real) / 2 +
            4 * tubePairCoefficientDistance T U := by
      rw [tubeCinematicTraceFirstValue_sub_eq]
      exact (abs_add_le _ _).trans
        (add_le_add
          (by simpa only [T, U] using facts.hactiveCBucket q hq i hi)
          hreduced)
    calc
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 q.2 -
          tubeCinematicTraceFirstValue (tubeAt q) f f1 q.2| =
          |tubeCinematicTraceFirstValue T f f1 q.2 -
            tubeCinematicTraceFirstValue U f f1 q.2| := by rfl
      _ <= (radius : Real) / 2 +
          4 * tubePairCoefficientDistance T U := hactualPoint
      _ <= 10000 * Real.sqrt (tGlobal * globalDelta) := by
        nlinarith [N.fineDelta_le_globalDelta, hglobalDeltaLeSqrt]
      _ = prop41Y1SharpSlopeConstant *
          Real.sqrt (tGlobal * globalDelta) := by
        norm_num [prop41Y1SharpSlopeConstant]

#print axioms
  ActualCenteredHalfY1ActiveGeometryFacts.actual_pointSlope_le_sharpScale

end

end FamilyStickyCinematicL32Prop41ActualY1SharpPointSlopeV1
