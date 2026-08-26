import FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32OscillationProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubeC2GraphRectangleV1RepoV2

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AttainedSlopeBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CenteredFractionNestingV1
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32Lemma57TubeTangencyDistanceV1
open FamilyStickyCinematicL32OscillationProducerV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# What the centered-half attained tangency payload actually gives

The current `Y1` label controls the minimum of the reduced value--first-jet
cost on the centered half.  It does not say that the minimizing parameter is
the physical incidence parameter `q.2`.  This module records the strongest
direct slope conclusion at an attained minimizer and the honest transport
loss needed to return to `q.2`.
-/

/-- An upper bound for the attained value--slope cost gives separate value
and first-jet bounds at one actual attaining parameter. -/
theorem exists_attained_reducedValue_firstJet_le
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) {A B upper : Real}
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hupper : tubePairAttainedTangencyDistance T U f f1 f2 A B hAB
      hfDeriv hf1Deriv <= upper) :
    exists thetaDelta, thetaDelta ∈ Icc A B ∧
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <= upper ∧
      |traceFirstDerivative f f1 (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <= upper := by
  obtain ⟨thetaDelta, hthetaDelta, _hnonneg, hdef, _hminimum⟩ :=
    tubePairAttainedTangencyDistance_spec T U f f1 f2 A B hAB
      hfDeriv hf1Deriv
  refine ⟨thetaDelta, hthetaDelta, ?_, ?_⟩
  · calc
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <=
          traceTangencyCost f f1 (tubePairDeltaA T U)
            (tubePairDeltaB T U) (tubePairDeltaD T U) thetaDelta := by
              rw [traceTangencyCost]
              exact le_add_of_nonneg_right (abs_nonneg _)
      _ = tubePairAttainedTangencyDistance T U f f1 f2 A B hAB
          hfDeriv hf1Deriv := hdef.symm
      _ <= upper := hupper
  · calc
      |traceFirstDerivative f f1 (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <=
          traceTangencyCost f f1 (tubePairDeltaA T U)
            (tubePairDeltaB T U) (tubePairDeltaD T U) thetaDelta := by
              rw [traceTangencyCost]
              exact le_add_of_nonneg_left (abs_nonneg _)
      _ = tubePairAttainedTangencyDistance T U f f1 f2 A B hAB
          hfDeriv hf1Deriv := hdef.symm
      _ <= upper := hupper

/-- With an approximate-`c` bucket, the attained reduced first-jet bound
becomes an actual cinematic first-jet bound with exactly one `cError` loss. -/
theorem exists_attained_actualFirstJetGap_le
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 : Real -> Real) {A B upper cError : Real}
    (hAB : A <= B)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hupper : tubePairAttainedTangencyDistance T U f f1 f2 A B hAB
      hfDeriv hf1Deriv <= upper)
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= cError) :
    exists thetaDelta, thetaDelta ∈ Icc A B ∧
      |traceFunction f (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <= upper ∧
      |traceFirstDerivative f f1 (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <= upper ∧
      |tubeCinematicTraceFirstValue T f f1 thetaDelta -
          tubeCinematicTraceFirstValue U f f1 thetaDelta| <=
        cError + upper := by
  obtain ⟨thetaDelta, hthetaDelta, hvalue, hfirst⟩ :=
    exists_attained_reducedValue_firstJet_le T U f f1 f2 hAB
      hfDeriv hf1Deriv hupper
  refine ⟨thetaDelta, hthetaDelta, hvalue, hfirst, ?_⟩
  rw [tubeCinematicTraceFirstValue_sub_eq]
  calc
    |(tubeGraphC T - tubeGraphC U) +
        traceFirstDerivative f f1 (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| <=
      |tubeGraphC T - tubeGraphC U| +
        |traceFirstDerivative f f1 (tubePairDeltaB T U)
          (tubePairDeltaD T U) thetaDelta| := abs_add_le _ _
    _ <= cError + upper := add_le_add hcBucket hfirst

/-- The literal centered-half `Y1` payload yields a sharp actual first-jet
margin at some attained parameter.  The subtraction of `radius / 2` records
that the stored budget is `Delta + radius <= 2 * globalDelta` while the
approximate-`c` loss is only `radius / 2`. -/
theorem ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedSlopeGap_le
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
    (q : Real × Real) (hq : q ∈ E) (i : iota)
    (hi : i ∈ activeAtPoint q) :
    exists thetaDelta,
      thetaDelta ∈ centeredFractionIcc outerA outerB (1 / 2 : Real) ∧
      |traceFunction f (tubePairDeltaA (fine.tubes i) (tubeAt q))
          (tubePairDeltaB (fine.tubes i) (tubeAt q))
          (tubePairDeltaD (fine.tubes i) (tubeAt q)) thetaDelta| <=
        2 * globalDelta - (radius : Real) ∧
      |traceFirstDerivative f f1
          (tubePairDeltaB (fine.tubes i) (tubeAt q))
          (tubePairDeltaD (fine.tubes i) (tubeAt q)) thetaDelta| <=
        2 * globalDelta - (radius : Real) ∧
      |tubeCinematicTraceFirstValue (fine.tubes i) f f1 thetaDelta -
          tubeCinematicTraceFirstValue (tubeAt q) f f1 thetaDelta| <=
        2 * globalDelta - (radius : Real) / 2 := by
  let halfA := centeredFractionLeft outerA outerB (1 / 2 : Real)
  let halfB := centeredFractionRight outerA outerB (1 / 2 : Real)
  have hhalf : halfA <= halfB :=
    (centered_half_and_quarter_endpoints_ordered hOuter).1
  let hfHalf : forall z, z ∈ Icc halfA halfB -> HasDerivAt f (f1 z) z :=
    fun z _hz => hf z
  let hf1Half : forall z, z ∈ Icc halfA halfB -> HasDerivAt f1 (f2 z) z :=
    fun z _hz => hf1 z
  have hupper : tubePairAttainedTangencyDistance
      (fine.tubes i) (tubeAt q) f f1 f2 halfA halfB hhalf
        hfHalf hf1Half <= 2 * globalDelta - (radius : Real) := by
    have hstored : tubePairAttainedTangencyDistance
        (fine.tubes i) (tubeAt q) f f1 f2 halfA halfB hhalf
          hfHalf hf1Half + (radius : Real) <= 2 * globalDelta := by
      simpa only [halfA, halfB, hfHalf, hf1Half] using
        facts.hactiveTangencyUpper q hq i hi
    linarith
  obtain ⟨thetaDelta, hthetaDelta, hvalue, hfirst, hactual⟩ :=
    exists_attained_actualFirstJetGap_le
      (fine.tubes i) (tubeAt q) f f1 f2 hhalf hfHalf hf1Half hupper
      (facts.hactiveCBucket q hq i hi)
  refine ⟨thetaDelta, ?_, hvalue, hfirst, ?_⟩
  · simpa only [centeredFractionIcc, halfA, halfB] using hthetaDelta
  · exact hactual.trans_eq (by ring)

#print axioms exists_attained_reducedValue_firstJet_le
#print axioms exists_attained_actualFirstJetGap_le
#print axioms ActualCenteredHalfY1ActiveGeometryFacts.exists_active_attainedSlopeGap_le

end

end FamilyStickyCinematicL32ActualProjectedCenteredHalfY1AttainedSlopeBridgeV1
