import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairExactCShift3AutomaticV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualFamilyExactCUniformShift3V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairExactCShift3AutomaticV1
open FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Exact-slice actual-family uniform three-shift consumer

The data below records only the honest, item-dependent common rectangle.
Sharp curvature, the attained tangency parameter, endpoint signs, scalar
roots, three-shift labels, and the retained fiber are all generated inside
the theorem.
-/

/-- The item-dependent geometric data needed to invoke the automatic-sharp
exact-common-`c` pair theorem.  The analytic curve, ambient interval, and
scales stay global so that the resulting roots all use the same three shifts.
-/
structure AutomaticShift3PairData
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (A B delta t q : Real) : Type where
  x : Real
  y : Real
  reference : Real -> Real
  baseRadius : Real
  graphRadius : Real
  hxy : x <= y
  hxBase : x ∈ centeredFractionIcc A B (1 / 4 : Real)
  hyBase : y ∈ centeredFractionIcc A B (1 / 4 : Real)
  hrectangleWidth : Real.sqrt (delta / t) <= y - x
  hcommonC : tubeGraphC T = tubeGraphC U
  hcoefficientLower : t <= tubePairCoefficientDistance T U
  hbaseRadius : 0 <= baseRadius
  hfirst : cinematicVerticalNeighborhood reference (Icc x y) baseRadius ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T)) (Icc x y) graphRadius
  hsecond : cinematicVerticalNeighborhood reference (Icc x y) baseRadius ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U)) (Icc x y) graphRadius
  htraceRadius : 2 * graphRadius <= q * delta

/-- A finite family of exact-common-`c` actual pairs with honest pointwise
common rectangles admits one uniform three-shift translation on a nonempty
fiber retaining at least one third of all items.  Every retained translated
actual tube has two distinct ordered parameters at which its cinematic curve
agrees with that of its paired tube.

There is no curvature, tangency parameter, endpoint-sign, root, label, or
fiber input in this interface. -/
theorem exists_uniform_threeShift_actualFamily_automaticSharp_root_fiber
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (items : Finset alpha) (T U : alpha -> Tube radius)
    (f f1 f2 : Real -> Real)
    {A B delta t q lambda : Real}
    (hitems : items.Nonempty)
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hlambda : 0 < lambda)
    (hshiftDominates : 10 * prop41TangencyScaleFactor q < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (data : forall i, i ∈ items ->
      AutomaticShift3PairData (T i) (U i) f A B delta t q) :
    exists (k : Fin 3) (eta : Real) (fiber : Finset alpha),
      eta = threeShiftValue k ∧
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      fiber.Nonempty ∧
      fiber ⊆ items ∧
      items.card <= 3 * fiber.card ∧
      forall i, i ∈ fiber ->
        exists theta0 thetaLeft thetaRight : Real,
          thetaLeft ∈ Ioo A theta0 ∧
          traceFunction f
              (tubePairDeltaA (T i) (U i) + eta * (lambda * delta))
              (tubePairDeltaB (T i) (U i))
              (tubePairDeltaD (T i) (U i)) thetaLeft = 0 ∧
          cinematicTraceValue f
                (tubeGraphA
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                (tubeGraphB
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                (tubeGraphC
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                (tubeGraphD
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                thetaLeft -
              cinematicTraceValue f
                (tubeGraphA (U i)) (tubeGraphB (U i))
                (tubeGraphC (U i)) (tubeGraphD (U i)) thetaLeft = 0 ∧
          thetaRight ∈ Ioo theta0 B ∧
          traceFunction f
              (tubePairDeltaA (T i) (U i) + eta * (lambda * delta))
              (tubePairDeltaB (T i) (U i))
              (tubePairDeltaD (T i) (U i)) thetaRight = 0 ∧
          cinematicTraceValue f
                (tubeGraphA
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                (tubeGraphB
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                (tubeGraphC
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                (tubeGraphD
                  (traceTranslateTube (T i) (eta * (lambda * delta))))
                thetaRight -
              cinematicTraceValue f
                (tubeGraphA (U i)) (tubeGraphB (U i))
                (tubeGraphC (U i)) (tubeGraphD (U i)) thetaRight = 0 := by
  have hcommonC : forall i, i ∈ items ->
      tubeGraphC (T i) = tubeGraphC (U i) := by
    intro i hi
    exact (data i hi).hcommonC
  have hpointwise : forall i, i ∈ items ->
      exists eta : Real,
        eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
        HasScalarTwoSidedRootsAtShift
          (T i) (U i) f A B (lambda * delta) eta := by
    intro i hi
    let d := data i hi
    exact
      actualTubePair_commonCanonicalQuarterRectangle_exists_real_shift3_scalarRoots_automaticSharp
        (T i) (U i) f f1 f2 d.reference hdelta ht hq hlambda
        hshiftDominates hstrengthenedScale hwidth d.hxy d.hxBase
        d.hyBase d.hrectangleWidth d.hcommonC d.hcoefficientLower
        hfDeriv hf1Deriv hparameter hft hf1Lower hf1Upper hf2
        hf2Continuous d.hbaseRadius d.hfirst d.hsecond d.htraceRadius
  exact
    exists_uniform_threeShift_actualTube_root_fiber
      items T U f A B (lambda * delta) hitems hcommonC hpointwise

#print axioms exists_uniform_threeShift_actualFamily_automaticSharp_root_fiber

end

end FamilyStickyCinematicL32Prop41ActualFamilyExactCUniformShift3V1
