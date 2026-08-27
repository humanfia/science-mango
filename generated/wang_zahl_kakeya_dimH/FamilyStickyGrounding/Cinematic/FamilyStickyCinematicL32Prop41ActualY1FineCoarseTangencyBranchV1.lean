import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SublevelComponentInteriorV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped Interval

namespace FamilyStickyCinematicL32Prop41ActualY1FineCoarseTangencyBranchV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1
open FamilyStickyCinematicL32ActualProjectedY1PointCommonRectangleV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41SublevelComponentInteriorV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v

/-!
# The actual `Y1` fine/coarse tangency branch

The existing actual producer constructs the literal fine rectangle `R_q`,
its assigned coarse rectangle, and the inclusion `R_q ⊆ R̃_q`.  The
coefficient-lower analysis separately supplies a first-jet bound at the
physical parameter, while the sublevel-component module supplies the
complementary coefficient-upper branch.

This module joins the two branches.  Both branches produce the same literal
`5 * radius` graph-neighborhood statement for `R_q`; the conclusion also
retains the proved fine-to-coarse carrier inclusion.

There is currently no upstream definition binding `fineT` to the paper's
constant `C_R`.  Accordingly, the one genuinely missing scalar propagation
inequality is stored in `ActualY1FineCoarseTangencyNumerics`.  The canonical
fine-base margin is *not* a field: it is derived below from the already used
Prop. 4.1 small-scale inequality and fine-to-coarse base-scale comparison.
-/

/-- Half the base length of the literal fine rectangle. -/
noncomputable def actualY1FineHalfWidth
    (fineDelta fineT : Real) : Real :=
  Real.sqrt (fineDelta / fineT) / 2

theorem actualY1FineHalfWidth_nonneg (fineDelta fineT : Real) :
    0 <= actualY1FineHalfWidth fineDelta fineT := by
  rw [actualY1FineHalfWidth]
  positivity

/-- The direct coefficient-upper branch's linear propagation coefficient. -/
def actualY1FineSmallCoefficientPropagation
    (fineDelta tGlobal : Real) : Real :=
  fineDelta / 2 + 4 * (tGlobal / 2)

/-- The coefficient-lower branch's point-slope plus curvature propagation
coefficient. -/
noncomputable def actualY1FineLargeCoefficientPropagation
    (fineDelta globalDelta tGlobal fineT : Real) : Real :=
  activeY1PointSlopeMargin fineDelta globalDelta tGlobal +
    30 * tGlobal * actualY1FineHalfWidth fineDelta fineT

/-- One scalar coefficient dominates the propagation loss in both branches. -/
noncomputable def actualY1FineUnifiedPropagation
    (fineDelta globalDelta tGlobal fineT : Real) : Real :=
  max
    (actualY1FineSmallCoefficientPropagation fineDelta tGlobal)
    (actualY1FineLargeCoefficientPropagation
      fineDelta globalDelta tGlobal fineT)

/-- All scalar data required by the actual fine/coarse branch splice.

The final field is the only budget not currently generated from a repository
definition of the paper's `C_R`.  It is deliberately a single maximum, rather
than two unrelated assumptions attached to the two logical branches. -/
structure ActualY1FineCoarseTangencyNumerics
    (fineDelta globalDelta tGlobal fineT outerWidth : Real) : Prop where
  globalDelta_pos : 0 < globalDelta
  tGlobal_pos : 0 < tGlobal
  outerWidth_lower : (1 / 2 : Real) <= outerWidth
  fineDelta_le_globalDelta : fineDelta <= globalDelta
  fineBaseScale_le_coarseBaseScale :
    fineDelta / fineT <= globalDelta / tGlobal
  prop41_smallScale : 2 * globalDelta - fineDelta < tGlobal / 2400
  unifiedPropagation_budget :
    actualY1FineUnifiedPropagation
        fineDelta globalDelta tGlobal fineT *
      actualY1FineHalfWidth fineDelta fineT <= 2 * fineDelta

/-- The one maximum budget specializes to the coefficient-upper branch. -/
theorem ActualY1FineCoarseTangencyNumerics.smallCoefficient_budget
    {fineDelta globalDelta tGlobal fineT outerWidth : Real}
    (N : ActualY1FineCoarseTangencyNumerics
      fineDelta globalDelta tGlobal fineT outerWidth) :
    actualY1FineSmallCoefficientPropagation fineDelta tGlobal *
        actualY1FineHalfWidth fineDelta fineT <=
      2 * fineDelta := by
  exact
    (mul_le_mul_of_nonneg_right
      (le_max_left
        (actualY1FineSmallCoefficientPropagation fineDelta tGlobal)
        (actualY1FineLargeCoefficientPropagation
          fineDelta globalDelta tGlobal fineT))
      (actualY1FineHalfWidth_nonneg fineDelta fineT)).trans
    N.unifiedPropagation_budget

/-- The same maximum budget specializes to the coefficient-lower branch. -/
theorem ActualY1FineCoarseTangencyNumerics.largeCoefficient_budget
    {fineDelta globalDelta tGlobal fineT outerWidth : Real}
    (N : ActualY1FineCoarseTangencyNumerics
      fineDelta globalDelta tGlobal fineT outerWidth) :
    actualY1FineLargeCoefficientPropagation
        fineDelta globalDelta tGlobal fineT *
        actualY1FineHalfWidth fineDelta fineT <=
      2 * fineDelta := by
  exact
    (mul_le_mul_of_nonneg_right
      (le_max_right
        (actualY1FineSmallCoefficientPropagation fineDelta tGlobal)
        (actualY1FineLargeCoefficientPropagation
          fineDelta globalDelta tGlobal fineT))
      (actualY1FineHalfWidth_nonneg fineDelta fineT)).trans
    N.unifiedPropagation_budget

/-- The existing Prop. 4.1 small-scale inequality already forces the coarse
canonical half-width into the available `J/16`-to-`J/4` margin. -/
theorem coarse_canonicalMargin_of_prop41_smallScale
    {fineDelta globalDelta tGlobal outerWidth : Real}
    (hglobalDelta : 0 < globalDelta) (htGlobal : 0 < tGlobal)
    (hwidth : (1 / 2 : Real) <= outerWidth)
    (hfineDeltaGlobal : fineDelta <= globalDelta)
    (hsmallScale : 2 * globalDelta - fineDelta < tGlobal / 2400) :
    Real.sqrt (globalDelta / tGlobal) / 2 <=
      3 * outerWidth / 32 := by
  have hDeltaSmall : globalDelta / tGlobal < (1 / 2400 : Real) := by
    apply (div_lt_iff₀ htGlobal).2
    have hraw : globalDelta < tGlobal / 2400 := by
      nlinarith
    nlinarith
  have hratioNonneg : 0 <= globalDelta / tGlobal := by positivity
  have hsqrtSq : (Real.sqrt (globalDelta / tGlobal)) ^ 2 =
      globalDelta / tGlobal := Real.sq_sqrt hratioNonneg
  have hsqrtSmall : Real.sqrt (globalDelta / tGlobal) < (1 / 40 : Real) := by
    have hsqrtNonneg := Real.sqrt_nonneg (globalDelta / tGlobal)
    nlinarith
  nlinarith

/-- Fine-to-coarse base-scale comparison transports the preceding coarse
margin to the canonical fine rectangle. -/
theorem ActualY1FineCoarseTangencyNumerics.fine_canonicalMargin
    {fineDelta globalDelta tGlobal fineT outerWidth : Real}
    (N : ActualY1FineCoarseTangencyNumerics
      fineDelta globalDelta tGlobal fineT outerWidth) :
    actualY1FineHalfWidth fineDelta fineT <=
      3 * outerWidth / 32 := by
  have hsqrt : Real.sqrt (fineDelta / fineT) <=
      Real.sqrt (globalDelta / tGlobal) :=
    Real.sqrt_le_sqrt N.fineBaseScale_le_coarseBaseScale
  have hcoarse := coarse_canonicalMargin_of_prop41_smallScale
    N.globalDelta_pos N.tGlobal_pos N.outerWidth_lower
    N.fineDelta_le_globalDelta N.prop41_smallScale
  dsimp only [actualY1FineHalfWidth]
  linarith

/-- A graph-value and first-jet bound at the physical center, together with
the normalized coefficient/C2 estimate, give literal `5 delta` tangency on
the centered rectangle. -/
theorem actualTube_centeredRectangle_tangent_of_pointSlope
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    {A B theta fineDelta fineT coefficientUpper slopeMargin : Real}
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hcoefficientUpperNonneg : 0 <= coefficientUpper)
    (hcoefficientUpper : tubePairCoefficientDistance T U <= coefficientUpper)
    (hcenter :
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta| <=
        2 * fineDelta)
    (hslope :
      |tubeCinematicTraceFirstValue T f f1 theta -
        tubeCinematicTraceFirstValue U f f1 theta| <= slopeMargin)
    (hbase : Icc
      (theta - actualY1FineHalfWidth fineDelta fineT)
      (theta + actualY1FineHalfWidth fineDelta fineT) ⊆ Icc A B)
    (hbudget :
      (slopeMargin +
          5 * coefficientUpper * actualY1FineHalfWidth fineDelta fineT) *
          actualY1FineHalfWidth fineDelta fineT <=
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
  let firstGap : Real -> Real := fun z =>
    tubeCinematicTraceFirstValue T f f1 z -
      tubeCinematicTraceFirstValue U f f1 z
  let secondGap : Real -> Real := fun z =>
    tubeCinematicTraceSecondValue T f1 f2 z -
      tubeCinematicTraceSecondValue U f1 f2 z
  let halfWidth := actualY1FineHalfWidth fineDelta fineT
  have hhalfWidth : 0 <= halfWidth := by
    exact actualY1FineHalfWidth_nonneg fineDelta fineT
  have hthetaDomain : theta ∈ Icc A B := by
    apply hbase
    constructor <;> linarith
  have hcoefficientBound : forall z, z ∈ Icc A B ->
      |secondGap z| <= 5 * coefficientUpper := by
    intro z hz
    have hraw := abs_traceJet2_le_five_coefficientDistance
      (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
      (f1 z) (f2 z) z (hparameter z hz) (hf1Upper z hz) (hf2 z hz)
    have hraw' :
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| <=
            5 * tubePairCoefficientDistance T U := by
      simpa only [traceSecondDerivative, traceJet2,
        tubePairCoefficientDistance] using hraw
    have hbound := hraw'.trans
      (mul_le_mul_of_nonneg_left hcoefficientUpper (by norm_num))
    simpa only [secondGap, tubeCinematicTraceSecondValue_sub_eq] using hbound
  apply centeredTubeRectangle_tangent_to_other_of_baseSublevelFour
    T U f f1 f2 hf hf1 theta fineDelta fineT
  intro z hzBase
  have hzCentered : z ∈ Icc (theta - halfWidth) (theta + halfWidth) := by
    simpa only [halfWidth, actualY1FineHalfWidth,
      centeredTubeC2GraphRectangle, tubeC2GraphRectangle,
      GraphRectangle.base] using hzBase
  have hzDomain : z ∈ Icc A B := hbase hzCentered
  have hpath : [[theta, z]] ⊆ Icc A B :=
    uIcc_subset_Icc hthetaDomain hzDomain
  have hdistance : |z - theta| <= halfWidth := by
    rw [abs_le]
    constructor <;> linarith [hzCentered.1, hzCentered.2]
  have hTaylor := abs_value_le_anchor_add_linear_quadratic
    graphGap firstGap secondGap
    (theta0 := theta) (theta := z) (M := 5 * coefficientUpper)
    (mul_nonneg (by norm_num) hcoefficientUpperNonneg)
    (fun w hw => by
      dsimp only [graphGap, firstGap]
      exact
        (hasDerivAt_cinematicTraceValue f f1
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) w
          (hf w)).sub
        (hasDerivAt_cinematicTraceValue f f1
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) w
          (hf w)))
    (fun w hw => by
      dsimp only [firstGap, secondGap]
      exact
        (hasDerivAt_cinematicTraceFirstValue f f1 f2
          (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) w
          (hf w) (hf1 w)).sub
        (hasDerivAt_cinematicTraceFirstValue f f1 f2
          (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) w
          (hf w) (hf1 w)))
    (fun w hw => hcoefficientBound w (hpath hw))
  have hcenter' : |graphGap theta| <= 2 * fineDelta := by
    simpa only [graphGap] using hcenter
  have hslope' : |firstGap theta| <= slopeMargin := by
    simpa only [firstGap] using hslope
  have hslopeMarginNonneg : 0 <= slopeMargin :=
    (abs_nonneg (firstGap theta)).trans hslope'
  have hdistanceNonneg : 0 <= |z - theta| := abs_nonneg _
  have hlinear :
      |firstGap theta| * |z - theta| <= slopeMargin * halfWidth :=
    mul_le_mul hslope' hdistance hdistanceNonneg hslopeMarginNonneg
  have hsquare : |z - theta| * |z - theta| <= halfWidth * halfWidth :=
    mul_self_le_mul_self hdistanceNonneg hdistance
  have hquadratic :
      (5 * coefficientUpper) * (|z - theta| * |z - theta|) <=
        (5 * coefficientUpper) * (halfWidth * halfWidth) :=
    mul_le_mul_of_nonneg_left hsquare
      (mul_nonneg (by norm_num) hcoefficientUpperNonneg)
  have hbudget' :
      (slopeMargin + 5 * coefficientUpper * halfWidth) * halfWidth <=
        2 * fineDelta := by
    simpa only [halfWidth] using hbudget
  have hgap : |graphGap z| <= 4 * fineDelta := by
    nlinarith
  simpa only [graphGap] using hgap

/-- Coefficient-lower branch: the automatic physical-point slope theorem
and the unified numeric budget force `5 * radius` tangency of the literal
fine rectangle. -/
theorem activeY1_centeredFineRectangle_tangent_of_coefficientLarge
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
    (N : ActualY1FineCoarseTangencyNumerics (radius : Real)
      globalDelta tGlobal fineT (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (q : Real × Real) (hq : q ∈ E)
    (i : iota) (hi : i ∈ activeAtPoint q)
    (hcoefficientLarge :
      tGlobal / 2 <=
        tubePairCoefficientDistance (fine.tubes i) (tubeAt q)) :
    let R := centeredTubeC2GraphRectangle (tubeAt q) f f1 f2 hf hf1
      q.2 (radius : Real) fineT
    R.carrier (radius : Real) ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
          (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
        R.rectangle.base (5 * (radius : Real)) := by
  dsimp only
  obtain ⟨_Delta, _thetaDelta, _theta0, _hDeltaNonneg, _hDeltaBudget,
      _hthetaDelta, _hDeltaDef, _htheta0, _hcritical, _hcriticalValue,
      _hlocality, hslope⟩ :=
    FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AutomaticPointSlopeV1.ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedCritical_pointLocality_and_slope
      fine physical E activeAtPoint tubeAt f f1 f2 outerA outerB hOuter
      hf hf1 tGlobal globalDelta facts N.outerWidth_lower N.globalDelta_pos
      N.tGlobal_pos N.prop41_smallScale hparameter hft hf1Lower hf1Upper
      hf2 hf2Continuous q hq (pointSource.hpointTheta q hq) i hi
      hcoefficientLarge
  have hcanonicalMargin :
      actualY1FineHalfWidth (radius : Real) fineT <=
        3 * (outerB - outerA) / 32 := N.fine_canonicalMargin
  have hqTheta := pointSource.hpointTheta q hq
  have hmargins := mem_sixteenth_has_quarter_margin hqTheta
  have hbase : Icc
      (q.2 - actualY1FineHalfWidth (radius : Real) fineT)
      (q.2 + actualY1FineHalfWidth (radius : Real) fineT) ⊆
      Icc outerA outerB := by
    intro z hz
    apply quarter_subset_whole hOuter
    constructor
    · linarith [hz.1, hcanonicalMargin, hmargins.1]
    · linarith [hz.2, hcanonicalMargin, hmargins.2]
  apply actualTube_centeredRectangle_tangent_of_pointSlope
    (fine.tubes i) (tubeAt q) f f1 f2 hf hf1
    hparameter hf1Upper hf2
    (mul_nonneg (by norm_num) N.tGlobal_pos.le)
    (facts.hactiveCoefficientUpper q hq i hi)
    (facts.hactiveFullWitness q hq i hi) hslope hbase
  have hlargeBudget := N.largeCoefficient_budget
  rw [actualY1FineLargeCoefficientPropagation] at hlargeBudget
  convert hlargeBudget using 1; ring

/-- The coefficient dichotomy now has one common output: the active tube is
`5 * radius` tangent to the literal fine rectangle, and that fine rectangle
is contained in its assigned coarse rectangle. -/
theorem activeY1_fine_tangent_and_fine_subset_coarse_by_coefficientBranch
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
    (N : ActualY1FineCoarseTangencyNumerics (radius : Real)
      globalDelta tGlobal fineT (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (q : Real × Real) (hq : q ∈ E)
    (i : iota) (hi : i ∈ activeAtPoint q) :
    let fineR := centeredTubeC2GraphRectangle (tubeAt q) f f1 f2 hf hf1
      q.2 (radius : Real) fineT
    let coarseR := centeredTubeC2GraphRectangle (tubeAt q) f f1 f2 hf hf1
      q.2 globalDelta tGlobal
    fineR.carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
            (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
          fineR.rectangle.base (5 * (radius : Real)) ∧
      fineR.carrier (radius : Real) ⊆ coarseR.carrier globalDelta := by
  dsimp only
  constructor
  · by_cases hsmall :
        tubePairCoefficientDistance (fine.tubes i) (tubeAt q) < tGlobal / 2
    · have hsmallBudget :
          ((radius : Real) / 2 + 4 * (tGlobal / 2)) *
              (Real.sqrt ((radius : Real) / fineT) / 2) <=
            2 * (radius : Real) := by
        simpa only [actualY1FineSmallCoefficientPropagation,
          actualY1FineHalfWidth] using N.smallCoefficient_budget
      exact activeY1_centeredFineRectangle_tangent_of_coefficientSmall
        fine physical E activeAtPoint centerTube tubeAt f f1 f2 outerA outerB
        hOuter hf hf1 tGlobal globalDelta fineT facts pointSource
        N.tGlobal_pos.le hparameter hft hf1Upper N.fine_canonicalMargin
        hsmallBudget q hq i hi hsmall.le
    · exact activeY1_centeredFineRectangle_tangent_of_coefficientLarge
        fine physical E activeAtPoint centerTube tubeAt f f1 f2 outerA
        outerB hOuter hf hf1 tGlobal globalDelta fineT facts pointSource N
        hparameter hft hf1Lower hf1Upper hf2 hf2Continuous q hq i hi
        (le_of_not_gt hsmall)
  · exact centeredTubeC2GraphRectangle_carrier_subset
      (tubeAt q) f f1 f2 hf hf1 q.2 (radius : Real) fineT
      globalDelta tGlobal N.fineDelta_le_globalDelta
      N.fineBaseScale_le_coarseBaseScale

/-- Retained-good-pair form of the combined branch theorem.  This is the
direct consumer interface for `ActualY1FineCoarseRectangleProducerV1`. -/
theorem retainedY1Pair_fine_tangent_and_fine_subset_coarse
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta fineT : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (N : ActualY1FineCoarseTangencyNumerics (radius : Real)
      globalDelta tGlobal fineT (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (keep : iota -> fineLabel -> Prop) (i : iota) (r : fineLabel)
    (hpair : (i, r) ∈
      (y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt f f1 f2
        hf hf1 (radius : Real) fineT globalDelta tGlobal).retainedGoodPairs keep) :
    let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real) fineT globalDelta tGlobal
    (D.fineRectangleAt r).carrier (radius : Real) ⊆
        cinematicVerticalNeighborhood
          (cinematicTraceValue f
            (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
            (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)))
          (D.fineRectangleAt r).rectangle.base (5 * (radius : Real)) ∧
      (D.fineRectangleAt r).carrier (radius : Real) ⊆
        (D.coarseRectangleAt r).carrier globalDelta := by
  dsimp only
  have hretained := y1FineCoarseRectangleData_retainedPair_active
    fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1
      (radius : Real) fineT globalDelta tGlobal keep i r hpair
  have hqE : pointAt r ∈ E := hpointE r hretained.1
  simpa only [y1FineCoarseRectangleData] using
    activeY1_fine_tangent_and_fine_subset_coarse_by_coefficientBranch
      fine physical E Y1.activeAtPoint centerTube tubeAt f f1 f2 outerA
      outerB hOuter hf hf1 tGlobal globalDelta fineT facts pointSource N
      hparameter hft hf1Lower hf1Upper hf2 hf2Continuous (pointAt r) hqE i
      hretained.2.1

#print axioms actualY1FineHalfWidth
#print axioms actualY1FineHalfWidth_nonneg
#print axioms ActualY1FineCoarseTangencyNumerics
#print axioms ActualY1FineCoarseTangencyNumerics.fine_canonicalMargin
#print axioms actualTube_centeredRectangle_tangent_of_pointSlope
#print axioms activeY1_centeredFineRectangle_tangent_of_coefficientLarge
#print axioms activeY1_fine_tangent_and_fine_subset_coarse_by_coefficientBranch
#print axioms retainedY1Pair_fine_tangent_and_fine_subset_coarse

end

end FamilyStickyCinematicL32Prop41ActualY1FineCoarseTangencyBranchV1
