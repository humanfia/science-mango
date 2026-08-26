import FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubeC2GraphRectangleV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32OscillationProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CenteredFractionNestingV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32ActualProjectedY1PointCommonRectangleV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32CurvilinearRectangleSlopeSeparationV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# From one active point to a positive-width common graph strip

A common value at one parameter and a second-derivative bound do not control
the missing affine slope.  This module records that obstruction explicitly,
then proves the sharp local producer after adding exactly one first-jet
margin at the active parameter.  Actual tube derivative identities and the
normalized coefficient estimate generate the remaining C2 input.
-/

/-- Point agreement and even identically zero curvature place no finite
bound on the missing slope.  This is the precise obstruction in the current
`Y1` active payload. -/
theorem pointAgreement_zeroCurvature_does_not_bound_slope
    (slopeBound : Real) :
    exists h h1 h2 : Real -> Real,
      h 0 = 0 ∧
      (forall z, HasDerivAt h (h1 z) z) ∧
      (forall z, HasDerivAt h1 (h2 z) z) ∧
      (forall z, |h2 z| <= 0) ∧
      slopeBound < |h1 0| := by
  let N := |slopeBound| + 1
  refine ⟨(fun z => N * z), (fun _z => N), (fun _z => 0), ?_, ?_, ?_,
    ?_, ?_⟩
  · simp
  · intro z
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul N)
  · intro z
    exact hasDerivAt_const z N
  · intro z
    simp
  · have hN : 0 < N := by
      dsimp only [N]
      positivity
    rw [abs_of_pos hN]
    dsimp only [N]
    linarith [le_abs_self slopeBound]

/-- Consumer-ready local common rectangle data for one actual pair.  Its
base has strictly positive canonical scale, both endpoints lie in `J/4`,
and the full approximate-`c` trace budget is already included. -/
structure ActualPairLocalCanonicalQuarterCommonRectangle
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (A B delta t budgetFactor cError : Real) : Type where
  x : Real
  y : Real
  reference : Real -> Real
  baseRadius : Real
  graphRadius : Real
  hstrictWidth : x < y
  hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real)
  hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real)
  hrectangleWidth : Real.sqrt (delta / t) <= y - x
  hcBucket : |tubeGraphC T - tubeGraphC U| <= cError
  hbaseRadius : 0 <= baseRadius
  hfirst : cinematicVerticalNeighborhood reference (Icc x y) baseRadius ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T)) (Icc x y) graphRadius
  hsecond : cinematicVerticalNeighborhood reference (Icc x y) baseRadius ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U)) (Icc x y) graphRadius
  htraceRadius : 2 * graphRadius + cError <= budgetFactor * delta

/-- A single graph-value witness, one actual first-jet margin, and the
automatic coefficient-to-C2 bound produce a literal positive-width common
strip.  The reference is the midpoint of the two actual cinematic graphs;
the base is centered at `theta0` and has exact width `sqrt (delta/t)`.

The last scalar hypothesis is the complete vertical budget after Taylor
propagation.  It is strictly weaker than assuming either desired carrier
inclusion and exposes every loss. -/
noncomputable def actualTube_point_to_localCanonicalQuarterCommonRectangle
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real)
    {A B theta0 delta t budgetFactor cError anchorGap coefficientUpper
      slopeMargin stripRadius : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (htheta0 : theta0 ∈ centeredFractionIcc A B (1 / 16 : Real))
    (hcanonicalMargin :
      Real.sqrt (delta / t) / 2 <= 3 * (B - A) / 32)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hanchor :
      |cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) theta0 -
        cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) theta0| <= anchorGap)
    (hcoefficientUpperNonneg : 0 <= coefficientUpper)
    (hcoefficientUpper :
      tubePairCoefficientDistance T U <= coefficientUpper)
    (hslope :
      |tubeCinematicTraceFirstValue T f f1 theta0 -
        tubeCinematicTraceFirstValue U f f1 theta0| <= slopeMargin)
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= cError)
    (hstripRadius : 0 < stripRadius)
    (hbudget :
      2 * stripRadius +
          (anchorGap +
            (slopeMargin +
                5 * coefficientUpper * (Real.sqrt (delta / t) / 2)) *
              (Real.sqrt (delta / t) / 2)) + cError <=
        budgetFactor * delta) :
    ActualPairLocalCanonicalQuarterCommonRectangle
      T U f A B delta t budgetFactor cError := by
  let halfWidth : Real := Real.sqrt (delta / t) / 2
  let x : Real := theta0 - halfWidth
  let y : Real := theta0 + halfWidth
  let graphT : Real -> Real := cinematicTraceValue f
    (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)
  let graphU : Real -> Real := cinematicTraceValue f
    (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U)
  let firstT : Real -> Real := tubeCinematicTraceFirstValue T f f1
  let firstU : Real -> Real := tubeCinematicTraceFirstValue U f f1
  let secondT : Real -> Real := tubeCinematicTraceSecondValue T f1 f2
  let secondU : Real -> Real := tubeCinematicTraceSecondValue U f1 f2
  let gapBudget : Real := anchorGap +
    (slopeMargin + 5 * coefficientUpper * halfWidth) * halfWidth
  let reference : Real -> Real := fun z => (graphT z + graphU z) / 2
  let graphRadius : Real := stripRadius + gapBudget / 2
  have hratioPos : 0 < delta / t := div_pos hdelta ht
  have hhalfWidthPos : 0 < halfWidth := by
    dsimp only [halfWidth]
    exact half_pos (Real.sqrt_pos.2 hratioPos)
  have hhalfWidthMargin : halfWidth <= 3 * (B - A) / 32 := by
    simpa only [halfWidth] using hcanonicalMargin
  have hAB : A < B := by nlinarith [hhalfWidthPos, hhalfWidthMargin]
  have hmargins := mem_sixteenth_has_quarter_margin htheta0
  have hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real) := by
    constructor <;> dsimp only [x] <;> linarith
  have hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real) := by
    constructor <;> dsimp only [y] <;> linarith
  have htheta0Quarter :
      theta0 ∈ centeredFractionIcc A B (1 / 4 : Real) := by
    have hinside := sixteenth_subset_Ioo_quarter hAB htheta0
    exact ⟨hinside.1.le, hinside.2.le⟩
  have hquarterSubset : centeredFractionIcc A B (1 / 4 : Real) ⊆
      Icc A B := quarter_subset_whole hAB.le
  have hxOuter := hquarterSubset hxBase
  have hyOuter := hquarterSubset hyBase
  have htheta0Outer := hquarterSubset htheta0Quarter
  have hcomponentOuter : Icc x y ⊆ Icc A B :=
    Icc_subset_Icc hxOuter.1 hyOuter.2
  have hhalfWidthNonneg : 0 <= halfWidth := hhalfWidthPos.le
  have hanchorGapNonneg : 0 <= anchorGap :=
    (abs_nonneg (graphT theta0 - graphU theta0)).trans (by
      simpa only [graphT, graphU] using hanchor)
  have hslopeMarginNonneg : 0 <= slopeMargin :=
    (abs_nonneg (firstT theta0 - firstU theta0)).trans (by
      simpa only [firstT, firstU] using hslope)
  have hsecondDifference : forall z, z ∈ Icc A B ->
      |secondT z - secondU z| <= 5 * coefficientUpper := by
    intro z hz
    have hraw := abs_traceJet2_le_five_coefficientDistance
      (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)
      (f1 z) (f2 z) z (hparameter z hz) (hf1Upper z hz) (hf2 z hz)
    have hraw' :
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| <=
            5 * tubePairCoefficientDistance T U := by
      simpa only [traceSecondDerivative,
        FamilyStickyCinematicL32JetSeparationV1.traceJet2,
        tubePairCoefficientDistance] using hraw
    have hbound :
        |traceSecondDerivative f1 f2
          (tubePairDeltaB T U) (tubePairDeltaD T U) z| <=
            5 * coefficientUpper :=
      hraw'.trans (mul_le_mul_of_nonneg_left hcoefficientUpper (by norm_num))
    simpa only [secondT, secondU,
      tubeCinematicTraceSecondValue_sub_eq] using hbound
  have hgraphGap : forall theta, theta ∈ Icc x y ->
      |graphT theta - graphU theta| <= gapBudget := by
    intro theta htheta
    have hthetaOuter := hcomponentOuter htheta
    have hdistance : |theta - theta0| <= halfWidth := by
      rcases htheta with ⟨hthetaLeft, hthetaRight⟩
      rw [abs_le]
      constructor <;> dsimp only [x, y] at hthetaLeft hthetaRight ⊢ <;>
        linarith
    have hTaylor := abs_value_le_anchor_add_linear_quadratic
      (fun z => graphT z - graphU z)
      (fun z => firstT z - firstU z)
      (fun z => secondT z - secondU z)
      (theta0 := theta0) (theta := theta)
      (M := 5 * coefficientUpper)
      (mul_nonneg (by norm_num) hcoefficientUpperNonneg)
      (fun z hz => by
        have hzOuter := uIcc_subset_Icc htheta0Outer hthetaOuter hz
        exact
          (hasDerivAt_cinematicTraceValue f f1
            (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
            (hfDeriv z hzOuter)).sub
          (hasDerivAt_cinematicTraceValue f f1
            (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
            (hfDeriv z hzOuter)))
      (fun z hz => by
        have hzOuter := uIcc_subset_Icc htheta0Outer hthetaOuter hz
        exact
          (hasDerivAt_cinematicTraceFirstValue f f1 f2
            (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
            (hfDeriv z hzOuter) (hf1Deriv z hzOuter)).sub
          (hasDerivAt_cinematicTraceFirstValue f f1 f2
            (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) z
            (hfDeriv z hzOuter) (hf1Deriv z hzOuter)))
      (fun z hz =>
        hsecondDifference z
          (uIcc_subset_Icc htheta0Outer hthetaOuter hz))
    have hanchor' : |graphT theta0 - graphU theta0| <= anchorGap := by
      simpa only [graphT, graphU] using hanchor
    have hslope' : |firstT theta0 - firstU theta0| <= slopeMargin := by
      simpa only [firstT, firstU] using hslope
    have hdistanceNonneg : 0 <= |theta - theta0| := abs_nonneg _
    have hlinear :
        |firstT theta0 - firstU theta0| * |theta - theta0| <=
          slopeMargin * halfWidth :=
      mul_le_mul hslope' hdistance hdistanceNonneg hslopeMarginNonneg
    have hsquare : |theta - theta0| * |theta - theta0| <=
        halfWidth * halfWidth :=
      mul_self_le_mul_self hdistanceNonneg hdistance
    have hquadratic :
        (5 * coefficientUpper) *
            (|theta - theta0| * |theta - theta0|) <=
          (5 * coefficientUpper) * (halfWidth * halfWidth) :=
      mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (by norm_num) hcoefficientUpperNonneg)
    dsimp only [gapBudget]
    nlinarith
  have hmidpointT : forall theta, theta ∈ Icc x y ->
      |reference theta - graphT theta| <= gapBudget / 2 := by
    intro theta htheta
    have hgap := hgraphGap theta htheta
    have heq : reference theta - graphT theta =
        -(graphT theta - graphU theta) / 2 := by
      dsimp only [reference]
      ring
    rw [heq, abs_div, abs_neg]
    norm_num
    linarith
  have hmidpointU : forall theta, theta ∈ Icc x y ->
      |reference theta - graphU theta| <= gapBudget / 2 := by
    intro theta htheta
    have hgap := hgraphGap theta htheta
    have heq : reference theta - graphU theta =
        (graphT theta - graphU theta) / 2 := by
      dsimp only [reference]
      ring
    rw [heq, abs_div]
    norm_num
    linarith
  have hfirst : cinematicVerticalNeighborhood reference (Icc x y)
      stripRadius ⊆ cinematicVerticalNeighborhood graphT (Icc x y)
        graphRadius := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    calc
      |p.1 - graphT p.2| <=
          |p.1 - reference p.2| + |reference p.2 - graphT p.2| :=
        abs_sub_le _ _ _
      _ <= stripRadius + gapBudget / 2 :=
        add_le_add hp.2 (hmidpointT p.2 hp.1)
      _ = graphRadius := by rfl
  have hsecond : cinematicVerticalNeighborhood reference (Icc x y)
      stripRadius ⊆ cinematicVerticalNeighborhood graphU (Icc x y)
        graphRadius := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    calc
      |p.1 - graphU p.2| <=
          |p.1 - reference p.2| + |reference p.2 - graphU p.2| :=
        abs_sub_le _ _ _
      _ <= stripRadius + gapBudget / 2 :=
        add_le_add hp.2 (hmidpointU p.2 hp.1)
      _ = graphRadius := by rfl
  refine
    { x := x
      y := y
      reference := reference
      baseRadius := stripRadius
      graphRadius := graphRadius
      hstrictWidth := by
        dsimp only [x, y]
        linarith
      hxBase := hxBase
      hyBase := hyBase
      hrectangleWidth := by
        dsimp only [x, y, halfWidth]
        ring_nf
        exact le_rfl
      hcBucket := hcBucket
      hbaseRadius := hstripRadius.le
      hfirst := by simpa only [graphT] using hfirst
      hsecond := by simpa only [graphU] using hsecond
      htraceRadius := by
        dsimp only [graphRadius, gapBudget, halfWidth]
        linarith }

/-- Direct adapter for the current centered-half `Y1` payload.  All value,
`c`-bucket, and coefficient/C2 inputs are discharged from `facts`; the point
location comes from the existing literal point source.  The sole additional
geometric datum is the first-jet margin at `q.2`, which the audited payload
does not currently contain. -/
noncomputable def activeY1_point_to_localCanonicalQuarterCommonRectangle
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
    {budgetFactor slopeMargin stripRadius : Real}
    (hglobalDelta : 0 < globalDelta) (htGlobal : 0 < tGlobal)
    (hcanonicalMargin :
      Real.sqrt (globalDelta / tGlobal) / 2 <=
        3 * (outerB - outerA) / 32)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hstripRadius : 0 < stripRadius)
    (qpoint : Real × Real) (hqpoint : qpoint ∈ E)
    (i : iota) (hi : i ∈ activeAtPoint qpoint)
    (hslope :
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 qpoint.2 -
        tubeCinematicTraceFirstValue (tubeAt qpoint) f f1 qpoint.2| <=
          slopeMargin)
    (hbudget :
      2 * stripRadius +
          (2 * (radius : Real) +
            (slopeMargin +
                30 * tGlobal *
                  (Real.sqrt (globalDelta / tGlobal) / 2)) *
              (Real.sqrt (globalDelta / tGlobal) / 2)) +
            (radius : Real) / 2 <=
        budgetFactor * globalDelta) :
    ActualPairLocalCanonicalQuarterCommonRectangle
      (fine.tubes i) (tubeAt qpoint) f outerA outerB globalDelta tGlobal
      budgetFactor ((radius : Real) / 2) := by
  apply actualTube_point_to_localCanonicalQuarterCommonRectangle
    (fine.tubes i) (tubeAt qpoint) f f1 f2
      hglobalDelta htGlobal (pointSource.hpointTheta qpoint hqpoint)
      hcanonicalMargin
      (fun z hz => hf z) (fun z hz => hf1 z)
      hparameter hf1Upper hf2
      (facts.hactiveFullWitness qpoint hqpoint i hi)
      (show 0 <= 6 * tGlobal by positivity)
      (facts.hactiveCoefficientUpper qpoint hqpoint i hi)
      hslope (facts.hactiveCBucket qpoint hqpoint i hi) hstripRadius
  have hbudget' := hbudget
  ring_nf at hbudget' ⊢
  exact hbudget'

#print axioms pointAgreement_zeroCurvature_does_not_bound_slope

end

end FamilyStickyCinematicL32ActualProjectedY1PointCommonRectangleV1
