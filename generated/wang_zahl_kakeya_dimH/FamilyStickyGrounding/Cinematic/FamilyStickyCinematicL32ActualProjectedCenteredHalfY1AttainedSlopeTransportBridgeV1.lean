import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AttainedSlopeBridgeV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AttainedSlopeTransportBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AttainedSlopeBridgeV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# Honest transport of the attained centered-half slope to the physical point

The attained parameter need not equal the physical incidence parameter.
Transport therefore incurs the second-jet bound times their literal distance.
No current `Y1` field bounds that distance at the local rectangle scale.
-/

/-- The strongest direct pointwise slope bound supplied by the present
payload: a sharp attained-point margin plus the unavoidable transport loss
`30 * tGlobal * |q.2 - thetaDelta|`. -/
theorem ActualCenteredHalfY1ActiveGeometryFacts.exists_active_pointSlopeGap_le_attainedTransport
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
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (q : Real × Real) (hq : q ∈ E)
    (hqTheta : q.2 ∈ Icc outerA outerB)
    (i : iota) (hi : i ∈ activeAtPoint q) :
    exists thetaDelta,
      thetaDelta ∈ centeredFractionIcc outerA outerB (1 / 2 : Real) ∧
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 thetaDelta -
          tubeCinematicTraceFirstValue (tubeAt q) f f1 thetaDelta| <=
        2 * globalDelta - (radius : Real) / 2 ∧
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 q.2 -
          tubeCinematicTraceFirstValue (tubeAt q) f f1 q.2| <=
        (2 * globalDelta - (radius : Real) / 2) +
          30 * tGlobal * |q.2 - thetaDelta| := by
  obtain ⟨thetaDelta, hthetaDelta, _hvalue, _hfirst,
      hactualTheta⟩ :=
    FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AttainedSlopeBridgeV1.ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedSlopeGap_le
      fine physical E activeAtPoint tubeAt f f1 f2 outerA outerB hOuter
      hf hf1 tGlobal globalDelta facts q hq i hi
  have hthetaOuter : thetaDelta ∈ Icc outerA outerB :=
    half_subset_whole hOuter hthetaDelta
  let slopeGap : Real -> Real := fun z =>
    tubeCinematicTraceFirstValue (fine.tubes i) f f1 z -
      tubeCinematicTraceFirstValue (tubeAt q) f f1 z
  let secondGap : Real -> Real := fun z =>
    tubeCinematicTraceSecondValue (fine.tubes i) f1 f2 z -
      tubeCinematicTraceSecondValue (tubeAt q) f1 f2 z
  have hderiv : forall z, z ∈ Icc outerA outerB ->
      HasDerivAt slopeGap (secondGap z) z := by
    intro z _hz
    dsimp only [slopeGap, secondGap]
    exact
      (hasDerivAt_cinematicTraceFirstValue f f1 f2
        (tubeGraphB (fine.tubes i)) (tubeGraphC (fine.tubes i))
        (tubeGraphD (fine.tubes i)) z (hf z) (hf1 z)).sub
      (hasDerivAt_cinematicTraceFirstValue f f1 f2
        (tubeGraphB (tubeAt q)) (tubeGraphC (tubeAt q))
        (tubeGraphD (tubeAt q)) z (hf z) (hf1 z))
  have hsecondBound : forall z, z ∈ Icc outerA outerB ->
      |secondGap z| <= 30 * tGlobal := by
    intro z hz
    have hraw := abs_traceJet2_le_five_coefficientDistance
      (tubePairDeltaA (fine.tubes i) (tubeAt q))
      (tubePairDeltaB (fine.tubes i) (tubeAt q))
      (tubePairDeltaD (fine.tubes i) (tubeAt q))
      (f1 z) (f2 z) z (hparameter z hz) (hf1Upper z hz) (hf2 z hz)
    have hrawBound :
        |traceSecondDerivative f1 f2
          (tubePairDeltaB (fine.tubes i) (tubeAt q))
          (tubePairDeltaD (fine.tubes i) (tubeAt q)) z| <=
            5 * tubePairCoefficientDistance (fine.tubes i) (tubeAt q) := by
      simpa only [traceSecondDerivative, traceJet2,
        tubePairCoefficientDistance] using hraw
    calc
      |secondGap z| =
          |traceSecondDerivative f1 f2
            (tubePairDeltaB (fine.tubes i) (tubeAt q))
            (tubePairDeltaD (fine.tubes i) (tubeAt q)) z| := by
              dsimp only [secondGap]
              rw [tubeCinematicTraceSecondValue_sub_eq]
      _ <= 5 * tubePairCoefficientDistance (fine.tubes i) (tubeAt q) :=
        hrawBound
      _ <= 5 * (6 * tGlobal) :=
        mul_le_mul_of_nonneg_left
          (facts.hactiveCoefficientUpper q hq i hi) (by norm_num)
      _ = 30 * tGlobal := by ring
  have htransport :
      |slopeGap q.2 - slopeGap thetaDelta| <=
        30 * tGlobal * |q.2 - thetaDelta| :=
    abs_sub_le_of_hasDerivAt_bound_on_Icc slopeGap secondGap
      hqTheta hthetaOuter hderiv hsecondBound
  refine ⟨thetaDelta, hthetaDelta, hactualTheta, ?_⟩
  change |slopeGap q.2| <=
    (2 * globalDelta - (radius : Real) / 2) +
      30 * tGlobal * |q.2 - thetaDelta|
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
    _ = (2 * globalDelta - (radius : Real) / 2) +
        30 * tGlobal * |q.2 - thetaDelta| := by ring

#print axioms ActualCenteredHalfY1ActiveGeometryFacts.exists_active_pointSlopeGap_le_attainedTransport

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AttainedSlopeTransportBridgeV1
