import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelShapeV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped Interval

namespace FamilyStickyCinematicL32Prop41SublevelComponentInteriorV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32CriticalPointGrowthV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32SublevelLocalizationV1
open FamilyStickyCinematicL32SublevelShapeV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# A two-sided interior form of PYZ Lemma 3.8(2c)

In the application of Lemma 3.8(2c), the physical parameter lies at
`delta / 2` depth inside the `delta`-sublevel set.  A mere lower bound for
the total length of the component containing that parameter does not imply
that a centered interval is contained in the component.  This module proves
the stronger statement actually needed by the fine-rectangle construction:
an explicit two-sided centered interval belongs to the same connected
component.

The first theorem is the elementary Lipschitz core.  The second theorem
derives its Lipschitz budget from an actual critical point and two-sided
curvature bounds, giving the square-root scale from Lemma 3.8.  The final
theorems discharge the graph derivatives for the concrete project tubes and
turn the component inclusion into literal rectangle tangency.  No component
inclusion or rectangle tangency is accepted as a premise.
-/

/-- The explicit half-width used in the critical-curvature branch. -/
def criticalSublevelInteriorRadius
    (M kappa Delta delta : Real) : Real :=
  delta / (8 * M * Real.sqrt ((Delta + delta) / kappa))

/-- A point at depth `outer - inner` in a sublevel set has a centered
Lipschitz neighborhood in the same connected component.  The component is
Mathlib's genuine maximal connected component inside the restricted
sublevel set. -/
theorem centered_interval_subset_sublevelComponent_of_deriv_bound
    (h h1 : Real -> Real)
    {A B theta r inner outer L : Real}
    (hr : 0 <= r) (hL : 0 <= L)
    (hbase : Icc (theta - r) (theta + r) ⊆ Icc A B)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hfirstUpper : forall z, z ∈ Icc (theta - r) (theta + r) ->
      |h1 z| <= L)
    (hcenter : |h theta| <= inner)
    (hbudget : inner + L * r <= outer) :
    Icc (theta - r) (theta + r) ⊆
      connectedComponentIn (SublevelOn h outer (Icc A B)) theta := by
  have hthetaBase : theta ∈ Icc (theta - r) (theta + r) := by
    constructor <;> linarith
  have hthetaDomain : theta ∈ Icc A B := hbase hthetaBase
  have hsublevel : Icc (theta - r) (theta + r) ⊆
      SublevelOn h outer (Icc A B) := by
    intro z hz
    have hzDomain : z ∈ Icc A B := hbase hz
    have hdistance : |z - theta| <= r := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    have hoscillation := abs_sub_le_of_hasDerivAt_bound_on_Icc
      h h1 hz hthetaBase
      (fun w hw => hderiv w (hbase hw)) hfirstUpper
    have hvalue : |h z| <= outer := by
      calc
        |h z| = |(h z - h theta) + h theta| := by ring_nf
        _ <= |h z - h theta| + |h theta| := abs_add_le _ _
        _ <= L * |z - theta| + inner := add_le_add hoscillation hcenter
        _ <= L * r + inner := by
          have hscaled := mul_le_mul_of_nonneg_left hdistance hL
          linarith
        _ <= outer := by linarith
    refine ⟨hzDomain, ?_⟩
    exact (abs_le).1 hvalue
  exact isPreconnected_Icc.subset_connectedComponentIn
    hthetaBase hsublevel

/-- Critical-curvature form of the two-sided component interior theorem.

The physical point has value at most `delta / 2`.  Localization around the
critical point bounds its slope by
`2 * M * sqrt ((Delta + delta) / kappa)`.  Curvature then controls the slope
throughout the centered interval.  The displayed radius leaves a strict
quantitative margin on both sides of the physical parameter. -/
theorem centered_interval_subset_sublevelComponent_of_criticalCurvature
    (h h1 h2 : Real -> Real)
    {A B theta0 theta r M kappa Delta delta : Real}
    (htheta0Domain : theta0 ∈ Icc A B)
    (hthetaDomain : theta ∈ Icc A B)
    (hr : 0 <= r)
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hDelta : 0 <= Delta) (hdelta : 0 < delta)
    (hcritical : h1 theta0 = 0)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (hderiv1 : forall z, z ∈ Icc A B -> HasDerivAt h1 (h2 z) z)
    (h2Continuous : ContinuousOn h2 (Icc A B))
    (hcurvatureUpper : forall z, z ∈ Icc A B -> |h2 z| <= M)
    (hcurvatureLower : forall z, z ∈ Icc A B -> kappa <= |h2 z|)
    (hcriticalValue : |h theta0| <= Delta)
    (hcenter : |h theta| <= delta / 2)
    (hbase : Icc (theta - r) (theta + r) ⊆ Icc A B)
    (hradius : r <= criticalSublevelInteriorRadius M kappa Delta delta) :
    Icc (theta - r) (theta + r) ⊆
      connectedComponentIn (SublevelOn h delta (Icc A B)) theta := by
  let s : Real := Real.sqrt ((Delta + delta) / kappa)
  let rho : Real := criticalSublevelInteriorRadius M kappa Delta delta
  have hsumPos : 0 < Delta + delta := by linarith
  have hratioPos : 0 < (Delta + delta) / kappa := div_pos hsumPos hkappa
  have hsPos : 0 < s := by
    dsimp only [s]
    exact Real.sqrt_pos.2 hratioPos
  have hsNonneg : 0 <= s := hsPos.le
  have hrhoPos : 0 < rho := by
    dsimp only [rho, criticalSublevelInteriorRadius]
    positivity
  have hthetaPath : [[theta0, theta]] ⊆ Icc A B :=
    uIcc_subset_Icc htheta0Domain hthetaDomain
  have hlocalizedRaw : |theta - theta0| <=
      2 * Real.sqrt ((Delta + delta / 2) / kappa) :=
    sublevel_point_localized_near_criticalPoint
      h h1 h2 hkappa hcritical
      (fun z hz => hderiv z (hthetaPath hz))
      (fun z hz => hderiv1 z (hthetaPath hz))
      (h2Continuous.mono hthetaPath)
      (fun z hz => hcurvatureLower z (hthetaPath hz))
      hcriticalValue hcenter
  have hratioLe : (Delta + delta / 2) / kappa <=
      (Delta + delta) / kappa := by
    exact (div_le_div_iff_of_pos_right hkappa).2 (by linarith)
  have hsqrtLe : Real.sqrt ((Delta + delta / 2) / kappa) <= s := by
    dsimp only [s]
    exact Real.sqrt_le_sqrt hratioLe
  have hlocalized : |theta - theta0| <= 2 * s := by
    exact hlocalizedRaw.trans
      (mul_le_mul_of_nonneg_left hsqrtLe (by norm_num))
  have hfirstAt : |h1 theta| <= 2 * M * s := by
    have hoscillation := abs_sub_le_of_hasDerivAt_bound_on_uIcc
      h1 h2 right_mem_uIcc left_mem_uIcc
      (fun z hz => hderiv1 z (hthetaPath hz))
      (fun z hz => hcurvatureUpper z (hthetaPath hz))
    have hscaled := mul_le_mul_of_nonneg_left hlocalized hM.le
    calc
      |h1 theta| = |h1 theta - h1 theta0| := by rw [hcritical, sub_zero]
      _ <= M * |theta - theta0| := hoscillation
      _ <= M * (2 * s) := hscaled
      _ = 2 * M * s := by ring
  have hkappaLeM : kappa <= M := by
    exact (hcurvatureLower theta0 htheta0Domain).trans
      (hcurvatureUpper theta0 htheta0Domain)
  have hsSq : s ^ 2 = (Delta + delta) / kappa := by
    dsimp only [s]
    exact Real.sq_sqrt hratioPos.le
  have hdeltaLeMsSq : delta <= M * s ^ 2 := by
    have hidentity : kappa * s ^ 2 = Delta + delta := by
      rw [hsSq]
      field_simp
    have hscaled : kappa * s ^ 2 <= M * s ^ 2 :=
      mul_le_mul_of_nonneg_right hkappaLeM (sq_nonneg s)
    linarith
  have hrhoLeS : rho <= s := by
    have hdenomPos : 0 < 8 * M * s := by positivity
    apply (div_le_iff₀ hdenomPos).2
    change delta <= s * (8 * M * s)
    nlinarith [hdeltaLeMsSq, mul_nonneg hM.le (sq_nonneg s)]
  have hrLeS : r <= s := hradius.trans hrhoLeS
  have hfirstUpper : forall z, z ∈ Icc (theta - r) (theta + r) ->
      |h1 z| <=
      2 * M * s + M * r := by
    intro z hz
    have hzDomain : z ∈ Icc A B := hbase hz
    have hthetaToZ : [[theta, z]] ⊆ Icc A B :=
      uIcc_subset_Icc hthetaDomain hzDomain
    have hdistance : |z - theta| <= r := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    have hoscillation := abs_sub_le_of_hasDerivAt_bound_on_uIcc
      h1 h2 right_mem_uIcc left_mem_uIcc
      (fun w hw => hderiv1 w (hthetaToZ hw))
      (fun w hw => hcurvatureUpper w (hthetaToZ hw))
    have hscaled := mul_le_mul_of_nonneg_left hdistance hM.le
    calc
      |h1 z| = |(h1 z - h1 theta) + h1 theta| := by ring_nf
      _ <= |h1 z - h1 theta| + |h1 theta| := abs_add_le _ _
      _ <= M * |z - theta| + 2 * M * s :=
        add_le_add hoscillation hfirstAt
      _ <= M * r + 2 * M * s := add_le_add hscaled le_rfl
      _ = 2 * M * s + M * r := by ring
  have hMrho : 8 * M * s * rho = delta := by
    change 8 * M * s * (delta / (8 * M * s)) = delta
    field_simp
  have hbudget : delta / 2 + (2 * M * s + M * r) * r <= delta := by
    have hMsNonneg : 0 <= M * s := mul_nonneg hM.le hsNonneg
    have hMrLe : M * r <= M * s :=
      mul_le_mul_of_nonneg_left hrLeS hM.le
    have hlinearNonneg : 0 <= 2 * M * s + M * r := by positivity
    have hlinearLe : 2 * M * s + M * r <= 3 * M * s := by linarith
    have hproductLe : (2 * M * s + M * r) * r <=
        (3 * M * s) * rho := by
      exact mul_le_mul hlinearLe hradius hr (by positivity)
    nlinarith
  apply centered_interval_subset_sublevelComponent_of_deriv_bound
    h h1 hr (by positivity) hbase hderiv hfirstUpper hcenter hbudget

/-- Concrete tube-graph specialization.  All derivative identities are
discharged from the actual `C2` trace; the remaining inputs are scalar
critical-point and curvature facts. -/
theorem actualTube_centeredBase_subset_sublevelComponent_of_criticalCurvature
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    {A B theta0 theta r M kappa Delta delta : Real}
    (htheta0Domain : theta0 ∈ Icc A B)
    (hthetaDomain : theta ∈ Icc A B)
    (hr : 0 <= r)
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hDelta : 0 <= Delta) (hdelta : 0 < delta)
    (hcritical :
      tubeCinematicTraceFirstValue T f f1 theta0 -
        tubeCinematicTraceFirstValue U f f1 theta0 = 0)
    (h2Continuous : ContinuousOn
      (fun z => tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue U f1 f2 z) (Icc A B))
    (hcurvatureUpper : forall z, z ∈ Icc A B ->
      |tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue U f1 f2 z| <= M)
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue U f1 f2 z|)
    (hcriticalValue :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta0 -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta0| <=
        Delta)
    (hcenter :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| <=
        delta / 2)
    (hbase : Icc (theta - r) (theta + r) ⊆ Icc A B)
    (hradius : r <= criticalSublevelInteriorRadius M kappa Delta delta) :
    let graphGap : Real -> Real := fun z =>
      cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
    Icc (theta - r) (theta + r) ⊆
      connectedComponentIn (SublevelOn graphGap delta (Icc A B)) theta := by
  dsimp only
  apply centered_interval_subset_sublevelComponent_of_criticalCurvature
    (fun z =>
      cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z)
    (fun z => tubeCinematicTraceFirstValue T f f1 z -
      tubeCinematicTraceFirstValue U f f1 z)
    (fun z => tubeCinematicTraceSecondValue T f1 f2 z -
      tubeCinematicTraceSecondValue U f1 f2 z)
    htheta0Domain hthetaDomain hr hM hkappa hDelta hdelta hcritical
  · intro z _hz
    exact
      (hasDerivAt_cinematicTraceValue f f1
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
        (hf z)).sub
      (hasDerivAt_cinematicTraceValue f f1
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
        (hf z))
  · intro z _hz
    exact
      (hasDerivAt_cinematicTraceFirstValue f f1 f2
        (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z (hf z) (hf1 z)).sub
      (hasDerivAt_cinematicTraceFirstValue f f1 f2
        (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z (hf z) (hf1 z))
  · exact h2Continuous
  · exact hcurvatureUpper
  · exact hcurvatureLower
  · exact hcriticalValue
  · exact hcenter
  · exact hbase
  · exact hradius

/-- If the canonical centered base fits in the critical-component interior,
then the actual rectangle based on `U` is `5`-tangent to the actual graph of
`T`.  This is the carrier statement needed for the paper's `R_x`. -/
theorem actualTube_centeredRectangle_tangent_of_criticalCurvature
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    {A B theta0 theta fineDelta fineT M kappa Delta : Real}
    (htheta0Domain : theta0 ∈ Icc A B)
    (hthetaDomain : theta ∈ Icc A B)
    (hM : 0 < M) (hkappa : 0 < kappa)
    (hDelta : 0 <= Delta) (hfineDelta : 0 < fineDelta)
    (hcritical :
      tubeCinematicTraceFirstValue T f f1 theta0 -
        tubeCinematicTraceFirstValue U f f1 theta0 = 0)
    (h2Continuous : ContinuousOn
      (fun z => tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue U f1 f2 z) (Icc A B))
    (hcurvatureUpper : forall z, z ∈ Icc A B ->
      |tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue U f1 f2 z| <= M)
    (hcurvatureLower : forall z, z ∈ Icc A B ->
      kappa <= |tubeCinematicTraceSecondValue T f1 f2 z -
        tubeCinematicTraceSecondValue U f1 f2 z|)
    (hcriticalValue :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta0 -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta0| <=
        Delta)
    (hcenter :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| <=
        2 * fineDelta)
    (hbase : Icc
      (theta - Real.sqrt (fineDelta / fineT) / 2)
      (theta + Real.sqrt (fineDelta / fineT) / 2) ⊆ Icc A B)
    (hradius : Real.sqrt (fineDelta / fineT) / 2 <=
      criticalSublevelInteriorRadius M kappa Delta (4 * fineDelta)) :
    let R := centeredTubeC2GraphRectangle U f f1 f2 hf hf1
      theta fineDelta fineT
    R.carrier fineDelta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T))
        R.rectangle.base (5 * fineDelta) := by
  dsimp only
  let graphGap : Real -> Real := fun z =>
    cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
      cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
  let halfWidth : Real := Real.sqrt (fineDelta / fineT) / 2
  have hhalfWidth : 0 <= halfWidth := by
    dsimp only [halfWidth]
    positivity
  have hcenter' :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| <=
        (4 * fineDelta) / 2 := by
    nlinarith
  have hcomponent : Icc (theta - halfWidth) (theta + halfWidth) ⊆
      connectedComponentIn
        (SublevelOn graphGap (4 * fineDelta) (Icc A B)) theta := by
    simpa only [graphGap, halfWidth] using
      actualTube_centeredBase_subset_sublevelComponent_of_criticalCurvature
        T U f f1 f2 hf hf1 htheta0Domain hthetaDomain hhalfWidth hM hkappa
        hDelta (by positivity) hcritical h2Continuous hcurvatureUpper
        hcurvatureLower hcriticalValue (by simpa only [graphGap] using hcenter')
        hbase hradius
  have hbaseSublevel : forall z,
      z ∈ Icc (theta - halfWidth) (theta + halfWidth) ->
      |graphGap z| <= 4 * fineDelta := by
    intro z hz
    have hzComponent := hcomponent hz
    have hzSublevel := connectedComponentIn_subset
      (SublevelOn graphGap (4 * fineDelta) (Icc A B)) theta hzComponent
    exact (abs_le).2 hzSublevel.2
  rintro q ⟨hqBase, hqVertical⟩
  refine ⟨hqBase, ?_⟩
  have hgap : |graphGap q.2| <= 4 * fineDelta := by
    apply hbaseSublevel q.2
    simpa only [halfWidth, centeredTubeC2GraphRectangle,
      tubeC2GraphRectangle, GraphRectangle.base] using hqBase
  calc
    |q.1 - cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) q.2| =
      |(q.1 - cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) q.2) -
        graphGap q.2| := by
          dsimp only [graphGap]
          congr 1
          ring
    _ <= |q.1 - cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) q.2| +
        |graphGap q.2| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le
              (q.1 - cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
                (tubeGraphC U) (tubeGraphD U) q.2) 0 (graphGap q.2))
    _ <= fineDelta + 4 * fineDelta := add_le_add hqVertical hgap
    _ = 5 * fineDelta := by ring

/-- In the complementary small-coefficient regime, the normalized first-jet
bound supplies the two-sided component interior directly, without a critical
point.  The `c`-slice error is displayed separately because the repository's
coefficient distance is the reduced `(a,b,d)` distance. -/
theorem actualTube_centeredBase_subset_sublevelComponent_of_coefficientUpper
    {radius : NNReal} (T U : Tube radius)
    (f f1 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    {A B theta fineDelta fineT coefficientUpper cError : Real}
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hcoefficientUpperNonneg : 0 <= coefficientUpper)
    (hcErrorNonneg : 0 <= cError)
    (hcoefficientUpper : tubePairCoefficientDistance T U <= coefficientUpper)
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= cError)
    (hcenter :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| <=
        2 * fineDelta)
    (hbase : Icc
      (theta - Real.sqrt (fineDelta / fineT) / 2)
      (theta + Real.sqrt (fineDelta / fineT) / 2) ⊆ Icc A B)
    (hbudget :
      (cError + 4 * coefficientUpper) *
          (Real.sqrt (fineDelta / fineT) / 2) <=
        2 * fineDelta) :
    let graphGap : Real -> Real := fun z =>
      cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
    Icc
        (theta - Real.sqrt (fineDelta / fineT) / 2)
        (theta + Real.sqrt (fineDelta / fineT) / 2) ⊆
      connectedComponentIn
        (SublevelOn graphGap (4 * fineDelta) (Icc A B)) theta := by
  dsimp only
  let halfWidth : Real := Real.sqrt (fineDelta / fineT) / 2
  let graphGap : Real -> Real := fun z =>
    cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
      cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
  let firstGap : Real -> Real := fun z =>
    tubeCinematicTraceFirstValue T f f1 z -
      tubeCinematicTraceFirstValue U f f1 z
  have hhalfWidth : 0 <= halfWidth := by
    dsimp only [halfWidth]
    positivity
  have hfirstUpper : forall z,
      z ∈ Icc (theta - halfWidth) (theta + halfWidth) ->
      |firstGap z| <= cError + 4 * coefficientUpper := by
    intro z hz
    have hzDomain : z ∈ Icc A B := by
      apply hbase
      simpa only [halfWidth] using hz
    have hreduced :
        |traceFirstDerivative f f1
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| <=
        4 * coefficientUpper := by
      have hraw := abs_traceJet1_le_four_coefficientDistance
        (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
        (f z) (f1 z) z (hparameter z hzDomain) (hft z hzDomain)
        (hf1Upper z hzDomain)
      have hraw' :
          |traceFirstDerivative f f1
            (tubePairDeltaB T U) (tubePairDeltaD T U) z| <=
          4 * tubePairCoefficientDistance T U := by
        simpa only [traceFirstDerivative, tubePairCoefficientDistance] using hraw
      exact hraw'.trans
        (mul_le_mul_of_nonneg_left hcoefficientUpper (by norm_num))
    rw [show firstGap z =
        (tubeGraphC T - tubeGraphC U) +
          traceFirstDerivative f f1
            (tubePairDeltaB T U) (tubePairDeltaD T U) z by
      exact tubeCinematicTraceFirstValue_sub_eq T U f f1 z]
    exact (abs_add_le _ _).trans (add_le_add hcBucket hreduced)
  have hderiv : forall z, z ∈ Icc A B ->
      HasDerivAt graphGap (firstGap z) z := by
    intro z _hz
    dsimp only [graphGap, firstGap]
    exact
      (hasDerivAt_cinematicTraceValue f f1
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
        (hf z)).sub
      (hasDerivAt_cinematicTraceValue f f1
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
        (hf z))
  have hcenter' : |graphGap theta| <= 2 * fineDelta := by
    simpa only [graphGap] using hcenter
  have hbudget' :
      2 * fineDelta + (cError + 4 * coefficientUpper) * halfWidth <=
        4 * fineDelta := by
    dsimp only [halfWidth] at hbudget ⊢
    linarith
  simpa only [graphGap, halfWidth] using
    centered_interval_subset_sublevelComponent_of_deriv_bound
      graphGap firstGap hhalfWidth
      (add_nonneg hcErrorNonneg
        (mul_nonneg (by norm_num) hcoefficientUpperNonneg))
      (by simpa only [halfWidth] using hbase) hderiv hfirstUpper
      hcenter' hbudget'

/-- A `4 delta` graph sublevel bound on the canonical base is exactly the
missing geometric input for `5 delta` rectangle tangency. -/
theorem centeredTubeRectangle_tangent_to_other_of_baseSublevelFour
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (theta fineDelta fineT : Real)
    (hsublevel : forall z,
      z ∈ (centeredTubeC2GraphRectangle U f f1 f2 hf hf1
        theta fineDelta fineT).rectangle.base ->
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z| <=
        4 * fineDelta) :
    (centeredTubeC2GraphRectangle U f f1 f2 hf hf1
        theta fineDelta fineT).carrier fineDelta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T))
        (centeredTubeC2GraphRectangle U f f1 f2 hf hf1
          theta fineDelta fineT).rectangle.base (5 * fineDelta) := by
  rintro q ⟨hqBase, hqVertical⟩
  refine ⟨hqBase, ?_⟩
  let gap : Real :=
    cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) q.2 -
      cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) q.2
  have hgap : |gap| <= 4 * fineDelta := by
    simpa only [gap] using hsublevel q.2 hqBase
  calc
    |q.1 - cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) q.2| =
      |(q.1 - cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) q.2) -
        gap| := by
          dsimp only [gap]
          congr 1
          ring
    _ <= |q.1 - cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) q.2| +
        |gap| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le
              (q.1 - cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
                (tubeGraphC U) (tubeGraphD U) q.2) 0 gap)
    _ <= fineDelta + 4 * fineDelta := add_le_add hqVertical hgap
    _ = 5 * fineDelta := by ring

/-- Consumer-ready small-coefficient branch: coefficient normalization,
the actual `c`-bucket, point incidence, and one scalar scale budget imply
literal `5 delta` tangency of the active tube to the assigned canonical
rectangle. -/
theorem actualTube_centeredRectangle_tangent_of_coefficientUpper
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    {A B theta fineDelta fineT coefficientUpper cError : Real}
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hcoefficientUpperNonneg : 0 <= coefficientUpper)
    (hcErrorNonneg : 0 <= cError)
    (hcoefficientUpper : tubePairCoefficientDistance T U <= coefficientUpper)
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= cError)
    (hcenter :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| <=
        2 * fineDelta)
    (hbase : Icc
      (theta - Real.sqrt (fineDelta / fineT) / 2)
      (theta + Real.sqrt (fineDelta / fineT) / 2) ⊆ Icc A B)
    (hbudget :
      (cError + 4 * coefficientUpper) *
          (Real.sqrt (fineDelta / fineT) / 2) <=
        2 * fineDelta) :
    let R := centeredTubeC2GraphRectangle U f f1 f2 hf hf1
      theta fineDelta fineT
    R.carrier fineDelta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T))
        R.rectangle.base (5 * fineDelta) := by
  dsimp only
  let graphGap : Real -> Real := fun z =>
    cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z -
      cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
  let halfWidth : Real := Real.sqrt (fineDelta / fineT) / 2
  have hcomponent : Icc (theta - halfWidth) (theta + halfWidth) ⊆
      connectedComponentIn
        (SublevelOn graphGap (4 * fineDelta) (Icc A B)) theta := by
    simpa only [graphGap, halfWidth] using
      actualTube_centeredBase_subset_sublevelComponent_of_coefficientUpper
        T U f f1 hf hparameter hft hf1Upper hcoefficientUpperNonneg
        hcErrorNonneg hcoefficientUpper hcBucket hcenter hbase hbudget
  apply centeredTubeRectangle_tangent_to_other_of_baseSublevelFour
    T U f f1 f2 hf hf1 theta fineDelta fineT
  intro z hzBase
  have hzCentered : z ∈ Icc (theta - halfWidth) (theta + halfWidth) := by
    simpa only [halfWidth, centeredTubeC2GraphRectangle,
      tubeC2GraphRectangle, GraphRectangle.base] using hzBase
  have hzComponent := hcomponent hzCentered
  have hzSublevel := connectedComponentIn_subset
    (SublevelOn graphGap (4 * fineDelta) (Icc A B)) theta hzComponent
  simpa only [graphGap] using (show |graphGap z| <= 4 * fineDelta from
    (abs_le).2 hzSublevel.2)

/-- Direct actual-`Y1` specialization of the complementary branch
`d(T, tubeAt q) <= tGlobal / 2`.  All geometric inputs come from the
faithful active facts and point source; only the explicit fine-scale budget
remains scalar. -/
theorem activeY1_centeredFineRectangle_tangent_of_coefficientSmall
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (activeAtPoint : Real × Real -> Finset iota)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta fineT : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (htGlobal : 0 <= tGlobal)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hcanonicalMargin :
      Real.sqrt ((radius : Real) / fineT) / 2 <=
        3 * (outerB - outerA) / 32)
    (hbudget :
      ((radius : Real) / 2 + 4 * (tGlobal / 2)) *
          (Real.sqrt ((radius : Real) / fineT) / 2) <=
        2 * (radius : Real))
    (q : Real × Real) (hq : q ∈ E)
    (i : iota) (hi : i ∈ activeAtPoint q)
    (hcoefficientSmall :
      tubePairCoefficientDistance (fine.tubes i) (tubeAt q) <=
        tGlobal / 2) :
    let R := centeredTubeC2GraphRectangle (tubeAt q) f f1 f2 hf hf1
      q.2 (radius : Real) fineT
    R.carrier (radius : Real) ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
          (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
        R.rectangle.base (5 * (radius : Real)) := by
  dsimp only
  have hqTheta : q.2 ∈ centeredFractionIcc outerA outerB (1 / 16 : Real) :=
    pointSource.hpointTheta q hq
  have hmargins := mem_sixteenth_has_quarter_margin hqTheta
  have hbase : Icc
      (q.2 - Real.sqrt ((radius : Real) / fineT) / 2)
      (q.2 + Real.sqrt ((radius : Real) / fineT) / 2) ⊆
      Icc outerA outerB := by
    intro z hz
    apply quarter_subset_whole hOuter
    constructor
    · linarith [hz.1, hcanonicalMargin, hmargins.1]
    · linarith [hz.2, hcanonicalMargin, hmargins.2]
  apply actualTube_centeredRectangle_tangent_of_coefficientUpper
    (fine.tubes i) (tubeAt q) f f1 f2 hf hf1
    hparameter hft hf1Upper
    (div_nonneg htGlobal (by norm_num))
    (div_nonneg (NNReal.coe_nonneg radius) (by norm_num))
    hcoefficientSmall
    (facts.hactiveCBucket q hq i hi)
    (facts.hactiveFullWitness q hq i hi)
    hbase hbudget

#print axioms criticalSublevelInteriorRadius
#print axioms centered_interval_subset_sublevelComponent_of_deriv_bound
#print axioms centered_interval_subset_sublevelComponent_of_criticalCurvature
#print axioms actualTube_centeredBase_subset_sublevelComponent_of_criticalCurvature
#print axioms actualTube_centeredRectangle_tangent_of_criticalCurvature
#print axioms actualTube_centeredBase_subset_sublevelComponent_of_coefficientUpper
#print axioms centeredTubeRectangle_tangent_to_other_of_baseSublevelFour
#print axioms actualTube_centeredRectangle_tangent_of_coefficientUpper
#print axioms activeY1_centeredFineRectangle_tangent_of_coefficientSmall

end

end FamilyStickyCinematicL32Prop41SublevelComponentInteriorV1
