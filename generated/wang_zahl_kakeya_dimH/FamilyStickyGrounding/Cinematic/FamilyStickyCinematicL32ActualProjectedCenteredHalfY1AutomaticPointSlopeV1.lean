import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ActualProjectedY1PointCommonRectangleV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairAutomaticSharpCurvatureV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceSublevelLocalizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedY1PointCommonRectangleV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32Prop41ActualPairAutomaticSharpCurvatureV1
open FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32SharpCurvatureCriticalPointV1
open FamilyStickyCinematicL32TraceSublevelLocalizationV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairApproxTraceV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# Automatic localization of the physical Y1 parameter

The centered-half `Y1` tangency minimum is attained at `thetaDelta`, whereas
the physical incidence is recorded at `q.2`.  A lower coefficient scale for
one active tube relative to the selected center forces the sharp-curvature
branch.  Both parameters are then honest reduced-trace sublevel points around
the same critical point.  This supplies their square-root locality and closes
the previously external first-jet margin at `q.2`.

The only new geometric premise is the one-tube coefficient lower bound.  The
small-scale inequality is scalar and exactly guarantees that the internally
attained tangency cost is below `coefficient / 1200`.
-/

/-- Square-root radius obtained by localizing `q.2` with sublevel constant
`5` and the attained point with sublevel constant `2`, both at coefficient
scale `tGlobal / 2`. -/
noncomputable def activeY1PointLocalityRadius
    (globalDelta tGlobal : Real) : Real :=
  (prop41CriticalLocalizationFactor 2 5 +
      prop41CriticalLocalizationFactor 2 2) *
    Real.sqrt (globalDelta / (tGlobal / 2))

/-- The resulting actual first-jet budget at the physical parameter. -/
noncomputable def activeY1PointSlopeMargin
    (radius globalDelta tGlobal : Real) : Real :=
  (2 * globalDelta - radius / 2) +
    30 * tGlobal * activeY1PointLocalityRadius globalDelta tGlobal

/-- A pointwise full-graph gap and an approximate `c` bucket give a reduced
trace sublevel at the same parameter. -/
theorem abs_tubePair_reducedTrace_le_fullGap_add_cError
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (theta fullGap cError : Real)
    (htheta : |theta| <= 1)
    (hfull :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| <=
        fullGap)
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= cError) :
    |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) theta| <= fullGap + cError := by
  have hcErrorNonneg : 0 <= cError :=
    (abs_nonneg (tubeGraphC T - tubeGraphC U)).trans hcBucket
  have hlinear :
      |(tubeGraphC T - tubeGraphC U) * theta| <= cError := by
    rw [abs_mul]
    calc
      |tubeGraphC T - tubeGraphC U| * |theta| <= cError * |theta| :=
        mul_le_mul_of_nonneg_right hcBucket (abs_nonneg theta)
      _ <= cError * 1 := mul_le_mul_of_nonneg_left htheta hcErrorNonneg
      _ = cError := by ring
  have hidentity :=
    tube_cinematicTraceValue_sub_eq_linear_add_trace T U f theta
  have hrewrite :
      traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) theta =
        (cinematicTraceValue f
            (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
          cinematicTraceValue f
            (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta) -
          (tubeGraphC T - tubeGraphC U) * theta := by
    linarith
  rw [hrewrite]
  calc
    |(cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta) -
        (tubeGraphC T - tubeGraphC U) * theta| <=
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| +
        |(tubeGraphC T - tubeGraphC U) * theta| := by
      simpa using
        (abs_sub_le
          (cinematicTraceValue f
              (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
            cinematicTraceValue f
              (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta)
          0 ((tubeGraphC T - tubeGraphC U) * theta))
    _ <= fullGap + cError := add_le_add hfull hlinear

/-- For one active tube separated from its selected center by at least
`tGlobal / 2`, the exact attained `Y1` tangency point and the physical point
are localized at the canonical square-root scale.  The final conjunct is the
actual full first-jet bound at `q.2`; no slope, locality, root, endpoint-sign,
or curvature premise is supplied. -/
theorem ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedCritical_pointLocality_and_slope
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
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
    (hwidth : (1 / 2 : Real) <= outerB - outerA)
    (hglobalDelta : 0 < globalDelta) (htGlobal : 0 < tGlobal)
    (hsmallScale :
      2 * globalDelta - (radius : Real) < tGlobal / 2400)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (q : Real × Real) (hq : q ∈ E)
    (hqTheta : q.2 ∈ centeredFractionIcc outerA outerB (1 / 16 : Real))
    (i : iota) (hi : i ∈ activeAtPoint q)
    (hcoefficientLower :
      tGlobal / 2 <=
        tubePairCoefficientDistance (fine.tubes i) (tubeAt q)) :
    exists Delta thetaDelta theta0,
      0 <= Delta ∧
      Delta + (radius : Real) <= 2 * globalDelta ∧
      thetaDelta ∈ centeredFractionIcc outerA outerB (1 / 2 : Real) ∧
      Delta = traceTangencyCost f f1
        (tubePairDeltaA (fine.tubes i) (tubeAt q))
        (tubePairDeltaB (fine.tubes i) (tubeAt q))
        (tubePairDeltaD (fine.tubes i) (tubeAt q)) thetaDelta ∧
      theta0 ∈ Icc outerA outerB ∧
      traceFirstDerivative f f1
        (tubePairDeltaB (fine.tubes i) (tubeAt q))
        (tubePairDeltaD (fine.tubes i) (tubeAt q)) theta0 = 0 ∧
      |traceFunction f
          (tubePairDeltaA (fine.tubes i) (tubeAt q))
          (tubePairDeltaB (fine.tubes i) (tubeAt q))
          (tubePairDeltaD (fine.tubes i) (tubeAt q)) theta0| <=
        10 * Delta ∧
      |q.2 - thetaDelta| <=
        activeY1PointLocalityRadius globalDelta tGlobal ∧
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 q.2 -
          tubeCinematicTraceFirstValue (tubeAt q) f f1 q.2| <=
        activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal := by
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
  have hDeltaUpper : Delta <= 2 * globalDelta := by linarith
  have hradiusUpper : (radius : Real) <= 2 * globalDelta := by linarith
  have hthetaDeltaCentered :
      thetaDelta ∈ centeredFractionIcc outerA outerB (1 / 2 : Real) := by
    simpa only [centeredFractionIcc, halfA, halfB] using hthetaDeltaHalf
  have hthetaDeltaOuter : thetaDelta ∈ Icc outerA outerB :=
    half_subset_whole hOuter hthetaDeltaCentered
  have hAB : outerA < outerB := by linarith
  have hqQuarterInterior := sixteenth_subset_Ioo_quarter hAB hqTheta
  have hqOuter : q.2 ∈ Icc outerA outerB :=
    quarter_subset_whole hOuter
      ⟨hqQuarterInterior.1.le, hqQuarterInterior.2.le⟩
  have hcoefficientPos :
      0 < tubePairCoefficientDistance T U :=
    lt_of_lt_of_le (half_pos htGlobal) (by
      simpa only [T, U] using hcoefficientLower)
  have hDeltaSmall :
      Delta < tubePairCoefficientDistance T U / 1200 := by
    have hscale : tGlobal / 2400 <=
        tubePairCoefficientDistance T U / 1200 := by
      have hlower : tGlobal / 2 <= tubePairCoefficientDistance T U := by
        simpa only [T, U] using hcoefficientLower
      nlinarith
    exact lt_of_le_of_lt (show Delta <= 2 * globalDelta - (radius : Real) by
        linarith) (hsmallScale.trans_le hscale)
  have hcurvatureStrict :=
    actualTubePair_small_tangency_forces_sharpCurvature
      T U f f1 f2 Delta thetaDelta hthetaDeltaOuter hDeltaDef' hDeltaSmall
        hparameter hft hf1Lower hf1Upper hf2
  have hcoefficientPosReduced :
      0 < coefficientDistance
        (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U) := by
    simpa only [tubePairCoefficientDistance] using hcoefficientPos
  obtain ⟨theta0, htheta0, hcritical, hcriticalValue⟩ :=
    trace_sharp_curvature_small_tangency_exists_criticalPoint_value_bound
      f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) Delta thetaDelta hwidth hcoefficientPosReduced
      hthetaDeltaCentered hDeltaDef' (by
        simpa only [tubePairCoefficientDistance] using hDeltaSmall)
      (fun z _hz => hf z) (fun z _hz => hf1 z) hf2Continuous
      hparameter hf1Upper hf2 (by
        simpa only [tubePairCoefficientDistance] using hcurvatureStrict)
  have hkappa :
      0 < tubePairCoefficientDistance T U / 45 := by positivity
  have hcurvatureLower : forall z, z ∈ Icc outerA outerB ->
      tubePairCoefficientDistance T U / 45 <=
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| := by
    intro z hz
    exact le_of_lt (hcurvatureStrict z hz)
  have hthetaSublevel :
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <= 2 * globalDelta := by
    calc
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <= Delta := by
        rw [hDeltaDef', traceTangencyCost]
        exact le_add_of_nonneg_right (abs_nonneg _)
      _ <= 2 * globalDelta := hDeltaUpper
  have hthetaRaw : |thetaDelta - theta0| <=
      2 * Real.sqrt
        ((10 * Delta + 2 * globalDelta) /
          (tubePairCoefficientDistance T U / 45)) :=
    trace_sublevel_point_localized_near_criticalPoint
      f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) htheta0 hthetaDeltaOuter hkappa hcritical
      (fun z _hz => hf z) (fun z _hz => hf1 z) hf2Continuous
      hcurvatureLower hcriticalValue hthetaSublevel
  have hthetaLocalized : |thetaDelta - theta0| <=
      prop41CriticalLocalizationFactor 2 2 *
        Real.sqrt (globalDelta / (tGlobal / 2)) := by
    exact hthetaRaw.trans
      (two_mul_sqrt_critical_ratio_le_factor_mul_sqrt_delta_div_scale
        hglobalDelta (half_pos htGlobal) (by
          simpa only [T, U] using hcoefficientLower)
        hDeltaNonneg' (by norm_num) (by norm_num) hDeltaUpper)
  have hqSublevel :
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) q.2| <= 5 * globalDelta := by
    have hraw := abs_tubePair_reducedTrace_le_fullGap_add_cError
      T U f q.2 (2 * (radius : Real)) ((radius : Real) / 2)
      (hparameter q.2 hqOuter)
      (by simpa only [T, U] using facts.hactiveFullWitness q hq i hi)
      (by simpa only [T, U] using facts.hactiveCBucket q hq i hi)
    exact hraw.trans (by nlinarith)
  have hqRaw : |q.2 - theta0| <=
      2 * Real.sqrt
        ((10 * Delta + 5 * globalDelta) /
          (tubePairCoefficientDistance T U / 45)) :=
    trace_sublevel_point_localized_near_criticalPoint
      f f1 f2 (tubePairDeltaA T U) (tubePairDeltaB T U)
      (tubePairDeltaD T U) htheta0 hqOuter hkappa hcritical
      (fun z _hz => hf z) (fun z _hz => hf1 z) hf2Continuous
      hcurvatureLower hcriticalValue hqSublevel
  have hqLocalized : |q.2 - theta0| <=
      prop41CriticalLocalizationFactor 2 5 *
        Real.sqrt (globalDelta / (tGlobal / 2)) := by
    exact hqRaw.trans
      (two_mul_sqrt_critical_ratio_le_factor_mul_sqrt_delta_div_scale
        hglobalDelta (half_pos htGlobal) (by
          simpa only [T, U] using hcoefficientLower)
        hDeltaNonneg' (by norm_num) (by norm_num) hDeltaUpper)
  have hpointLocality : |q.2 - thetaDelta| <=
      activeY1PointLocalityRadius globalDelta tGlobal := by
    calc
      |q.2 - thetaDelta| =
          |(q.2 - theta0) + (theta0 - thetaDelta)| := by ring_nf
      _ <= |q.2 - theta0| + |theta0 - thetaDelta| := abs_add_le _ _
      _ <= prop41CriticalLocalizationFactor 2 5 *
            Real.sqrt (globalDelta / (tGlobal / 2)) +
          prop41CriticalLocalizationFactor 2 2 *
            Real.sqrt (globalDelta / (tGlobal / 2)) := by
        apply add_le_add hqLocalized
        simpa only [abs_sub_comm theta0 thetaDelta] using hthetaLocalized
      _ = activeY1PointLocalityRadius globalDelta tGlobal := by
        rw [activeY1PointLocalityRadius]
        ring
  have hfirstReduced :
      |traceFirstDerivative f f1 (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <= Delta := by
    rw [hDeltaDef', traceTangencyCost]
    exact le_add_of_nonneg_left (abs_nonneg _)
  have hactualTheta :
      |tubeCinematicTraceFirstValue T f f1 thetaDelta -
          tubeCinematicTraceFirstValue U f f1 thetaDelta| <=
        2 * globalDelta - (radius : Real) / 2 := by
    rw [tubeCinematicTraceFirstValue_sub_eq]
    calc
      |(tubeGraphC T - tubeGraphC U) +
          traceFirstDerivative f f1 (tubePairDeltaB T U)
            (tubePairDeltaD T U) thetaDelta| <=
        |tubeGraphC T - tubeGraphC U| +
          |traceFirstDerivative f f1 (tubePairDeltaB T U)
            (tubePairDeltaD T U) thetaDelta| := abs_add_le _ _
      _ <= (radius : Real) / 2 + Delta :=
        add_le_add (by
          simpa only [T, U] using facts.hactiveCBucket q hq i hi)
          hfirstReduced
      _ <= 2 * globalDelta - (radius : Real) / 2 := by linarith
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
        (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z (hf z) (hf1 z)).sub
      (hasDerivAt_cinematicTraceFirstValue f f1 f2
        (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z (hf z) (hf1 z))
  have hsecondBound : forall z, z ∈ Icc outerA outerB ->
      |secondGap z| <= 30 * tGlobal := by
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
      _ <= 5 * (6 * tGlobal) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [T, U] using
            facts.hactiveCoefficientUpper q hq i hi) (by norm_num)
      _ = 30 * tGlobal := by ring
  have htransport :
      |slopeGap q.2 - slopeGap thetaDelta| <=
        30 * tGlobal * |q.2 - thetaDelta| :=
    abs_sub_le_of_hasDerivAt_bound_on_Icc slopeGap secondGap
      hqOuter hthetaDeltaOuter hderiv hsecondBound
  have hactualPoint : |slopeGap q.2| <=
      activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal := by
    calc
      |slopeGap q.2| =
          |(slopeGap q.2 - slopeGap thetaDelta) + slopeGap thetaDelta| := by
        congr 1
        ring
      _ <= |slopeGap q.2 - slopeGap thetaDelta| +
          |slopeGap thetaDelta| := abs_add_le _ _
      _ <= 30 * tGlobal * |q.2 - thetaDelta| +
          (2 * globalDelta - (radius : Real) / 2) := by
        apply add_le_add htransport
        simpa only [slopeGap] using hactualTheta
      _ <= 30 * tGlobal * activeY1PointLocalityRadius globalDelta tGlobal +
          (2 * globalDelta - (radius : Real) / 2) := by
        gcongr
      _ = activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal := by
        rw [activeY1PointSlopeMargin]
        ring
  refine ⟨Delta, thetaDelta, theta0, hDeltaNonneg', hDeltaBudget,
    hthetaDeltaCentered, ?_, htheta0, ?_, ?_, hpointLocality, ?_⟩
  · simpa only [T, U] using hDeltaDef'
  · simpa only [T, U] using hcritical
  · simpa only [T, U] using hcriticalValue
  · simpa only [slopeGap, T, U] using hactualPoint

/-- The automatic point-slope theorem closes the last geometric input of the
positive-width common-rectangle producer.  What remains is a scalar width
margin and the displayed total vertical budget. -/
noncomputable def activeY1_point_to_localCanonicalQuarterCommonRectangle_of_coefficientLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1.FiniteProjectedShading
      (Real × Real) iota)
    (E : Set (Real × Real))
    (activeAtPoint : Real × Real -> Finset iota)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    {budgetFactor stripRadius : Real}
    (hwidth : (1 / 2 : Real) <= outerB - outerA)
    (hglobalDelta : 0 < globalDelta) (htGlobal : 0 < tGlobal)
    (hsmallScale :
      2 * globalDelta - (radius : Real) < tGlobal / 2400)
    (hcanonicalMargin :
      Real.sqrt (globalDelta / tGlobal) / 2 <=
        3 * (outerB - outerA) / 32)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (hstripRadius : 0 < stripRadius)
    (q : Real × Real) (hq : q ∈ E)
    (i : iota) (hi : i ∈ activeAtPoint q)
    (hcoefficientLower :
      tGlobal / 2 <=
        tubePairCoefficientDistance (fine.tubes i) (tubeAt q))
    (hbudget :
      2 * stripRadius +
          (2 * (radius : Real) +
            (activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal +
                30 * tGlobal *
                  (Real.sqrt (globalDelta / tGlobal) / 2)) *
              (Real.sqrt (globalDelta / tGlobal) / 2)) +
            (radius : Real) / 2 <=
        budgetFactor * globalDelta) :
    ActualPairLocalCanonicalQuarterCommonRectangle
      (fine.tubes i) (tubeAt q) f outerA outerB globalDelta tGlobal
      budgetFactor ((radius : Real) / 2) := by
  have hslope :
       |tubeCinematicTraceFirstValue (fine.tubes i) f f1 q.2 -
           tubeCinematicTraceFirstValue (tubeAt q) f f1 q.2| <=
         activeY1PointSlopeMargin (radius : Real) globalDelta tGlobal := by
     obtain ⟨_Delta, _thetaDelta, _theta0, _hDelta, _hDeltaBudget,
         _hthetaDelta, _hDeltaDef, _htheta0, _hcritical, _hcriticalValue,
         _hlocality, hslope⟩ :=
       FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1.ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedCritical_pointLocality_and_slope
         fine physical E activeAtPoint tubeAt f f1 f2 outerA outerB hOuter
         hf hf1 tGlobal globalDelta facts hwidth hglobalDelta htGlobal
         hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous q hq
         (pointSource.hpointTheta q hq) i hi hcoefficientLower
     exact hslope
  exact activeY1_point_to_localCanonicalQuarterCommonRectangle
    fine physical E activeAtPoint centerTube tubeAt f f1 f2 outerA outerB
    hOuter hf hf1 tGlobal globalDelta facts pointSource hglobalDelta htGlobal
    hcanonicalMargin hparameter hf1Upper hf2 hstripRadius q hq i hi hslope
    hbudget

#print axioms activeY1PointLocalityRadius
#print axioms activeY1PointSlopeMargin
#print axioms abs_tubePair_reducedTrace_le_fullGap_add_cError
#print axioms ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedCritical_pointLocality_and_slope
#print axioms activeY1_point_to_localCanonicalQuarterCommonRectangle_of_coefficientLower

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1
