import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairRectangleShift3TraceRootsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualPairShift3PointwiseAdapterV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleShift3TraceRootsV1
open FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Pointwise adapter from integer shifts to the real three-shift interface

The actual-pair rectangle theorem records its uniform perturbation label as
an integer, while the finite pigeonhole interface labels scalar traces by a
real member of `{-1,0,1}`.  This module performs that cast once and preserves
the same two strictly separated root parameters.
-/

/-- Casting an integer known to be one of `-1`, `0`, or `1` gives a real
member of the corresponding three-element set. -/
theorem intCast_mem_real_threeShiftSet
    (eta : Int) (heta : eta = -1 ∨ eta = 0 ∨ eta = 1) :
    (eta : Real) ∈ ({(-1 : Real), 0, 1} : Set Real) := by
  rcases heta with heta | heta | heta <;> subst eta <;> norm_num

/-- Pure output conversion: an integer three-shift witness with two scalar
trace roots becomes exactly the real pointwise witness consumed by the
actual-tube three-shift pigeonhole theorem. -/
theorem exists_real_threeShift_scalarRoots_of_int_threeShift_scalarRoots
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (A B s : Real)
    (hroots :
      exists (eta : Int) (theta0 thetaLeft thetaRight : Real),
        (eta = -1 ∨ eta = 0 ∨ eta = 1) ∧
        thetaLeft ∈ Ioo A theta0 ∧
        traceFunction f
            (tubePairDeltaA T U + (eta : Real) * s)
            (tubePairDeltaB T U) (tubePairDeltaD T U) thetaLeft = 0 ∧
        thetaRight ∈ Ioo theta0 B ∧
        traceFunction f
            (tubePairDeltaA T U + (eta : Real) * s)
            (tubePairDeltaB T U) (tubePairDeltaD T U) thetaRight = 0) :
    exists eta : Real,
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      HasScalarTwoSidedRootsAtShift T U f A B s eta := by
  obtain ⟨eta, theta0, thetaLeft, thetaRight, heta,
      hthetaLeft, hrootLeft, hthetaRight, hrootRight⟩ := hroots
  refine ⟨(eta : Real), intCast_mem_real_threeShiftSet eta heta, ?_⟩
  exact ⟨theta0, thetaLeft, thetaRight, hthetaLeft,
    hrootLeft, hthetaRight, hrootRight⟩

/-- The full actual-pair rectangle theorem, exposed directly in the real
pointwise format needed by `exists_uniform_threeShift_actualTube_root_fiber`.
The shift scale is exactly `lambda * delta`; callers do not repeat any cast
or three-way case split. -/
theorem actualTubePair_commonCanonicalQuarterRectangle_exists_real_shift3_scalarRoots
    {radius : NNReal} (T U : Tube radius)
    (f f1 f2 reference : Real -> Real)
    {A B x y delta t q lambda baseRadius graphRadius : Real}
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
    (hcommonC : tubeGraphC T = tubeGraphC U)
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
    (htraceRadius : 2 * graphRadius <= q * delta) :
    exists eta : Real,
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      HasScalarTwoSidedRootsAtShift
        T U f A B (lambda * delta) eta := by
  obtain ⟨eta, theta0, thetaLeft, thetaRight, heta,
      _htheta0, _hcritical, _hendpoints, hthetaLeft, hrootLeft,
      hthetaRight, hrootRight⟩ :=
    actualTubePair_commonCanonicalQuarterRectangle_exists_int_shift3_two_sided_roots
      T U f f1 f2 reference hdelta ht hq hlambda hshiftDominates
      hstrengthenedScale hwidth hxy hxBase hyBase hrectangleWidth
      hcommonC hcoefficientLower hfDeriv hf1Deriv hparameter hft
      hf1Lower hf1Upper hf2 hf2Continuous hcurvatureStrict hbaseRadius
      hfirst hsecond htraceRadius
  exact exists_real_threeShift_scalarRoots_of_int_threeShift_scalarRoots
    T U f A B (lambda * delta)
      ⟨eta, theta0, thetaLeft, thetaRight, heta,
        hthetaLeft, hrootLeft, hthetaRight, hrootRight⟩

#print axioms intCast_mem_real_threeShiftSet
#print axioms exists_real_threeShift_scalarRoots_of_int_threeShift_scalarRoots
#print axioms actualTubePair_commonCanonicalQuarterRectangle_exists_real_shift3_scalarRoots

end

end FamilyStickyCinematicL32Prop41ActualPairShift3PointwiseAdapterV1
