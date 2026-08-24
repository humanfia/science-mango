import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TubePairApproxTraceV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Approximate fixed-`c` tube slices

Actual tube parameters generally lie in a narrow `c`-bucket rather than
having literally equal `c`.  The remaining linear term
`(c_T - c_U) * theta` is explicit and is absorbed into the trace-sublevel
radius on a bounded parameter interval.
-/

/-- Exact tube-pair curve difference before imposing a fixed-`c` slice. -/
theorem tube_cinematicTraceValue_sub_eq_linear_add_trace
    {radius : NNReal} (T U : Tube radius)
    (f : Real -> Real) (theta : Real) :
    cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
      cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta =
      (tubeGraphC T - tubeGraphC U) * theta +
        traceFunction f
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) theta := by
  simp only [cinematicTraceValue, traceFunction, FamilyStickyCinematicL32JetSeparationV1.traceJet0,
    tubePairDeltaA, tubePairDeltaB, tubePairDeltaD]
  ring

/-- Common-strip tangency in an `eta`-wide `c`-bucket gives the trace
sublevel `2*R + eta` on `|theta| <= 1`. -/
theorem common_strip_tangency_forces_approx_tubePair_trace_sublevel
    {radius : NNReal} (T U : Tube radius)
    (f reference : Real -> Real) (I : Set Real) (eta : Real)
    (hparameter : forall theta, theta ∈ I -> |theta| <= 1)
    (hcBucket : |tubeGraphC T - tubeGraphC U| <= eta)
    {baseRadius R : Real} (hbaseRadius : 0 <= baseRadius)
    (hfirst : cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T)) I R)
    (hsecond : cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U)) I R) :
    forall theta, theta ∈ I ->
      |traceFunction f
        (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) theta| <= 2 * R + eta := by
  have hvalue := common_strip_tangency_forces_value_sublevel
    reference
    (cinematicTraceValue f
      (tubeGraphA T) (tubeGraphB T)
      (tubeGraphC T) (tubeGraphD T))
    (cinematicTraceValue f
      (tubeGraphA U) (tubeGraphB U)
      (tubeGraphC U) (tubeGraphD U))
    I hbaseRadius hfirst hsecond
  intro theta htheta
  have hlinear :
      |(tubeGraphC T - tubeGraphC U) * theta| <= eta := by
    have heta : 0 <= eta := (abs_nonneg _).trans hcBucket
    rw [abs_mul]
    calc
      |tubeGraphC T - tubeGraphC U| * |theta| <=
          eta * |theta| :=
        mul_le_mul_of_nonneg_right hcBucket (abs_nonneg theta)
      _ <= eta * 1 :=
        mul_le_mul_of_nonneg_left (hparameter theta htheta) heta
      _ = eta := by ring
  have hidentity :=
    tube_cinematicTraceValue_sub_eq_linear_add_trace T U f theta
  have htraceRewrite :
      traceFunction f
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) theta =
        (cinematicTraceValue f
            (tubeGraphA T) (tubeGraphB T)
            (tubeGraphC T) (tubeGraphD T) theta -
          cinematicTraceValue f
            (tubeGraphA U) (tubeGraphB U)
            (tubeGraphC U) (tubeGraphD U) theta) -
          (tubeGraphC T - tubeGraphC U) * theta := by
    linarith
  rw [htraceRewrite]
  calc
    |(cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) theta) -
        (tubeGraphC T - tubeGraphC U) * theta| <=
      |cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) theta| +
        |(tubeGraphC T - tubeGraphC U) * theta| := by
      simpa using
        (abs_sub_le
          (cinematicTraceValue f
              (tubeGraphA T) (tubeGraphB T)
              (tubeGraphC T) (tubeGraphD T) theta -
            cinematicTraceValue f
              (tubeGraphA U) (tubeGraphB U)
              (tubeGraphC U) (tubeGraphD U) theta)
          0 ((tubeGraphC T - tubeGraphC U) * theta))
    _ <= 2 * R + eta := add_le_add (hvalue theta htheta) hlinear

#print axioms tube_cinematicTraceValue_sub_eq_linear_add_trace
#print axioms common_strip_tangency_forces_approx_tubePair_trace_sublevel

end


end FamilyStickyCinematicL32TubePairApproxTraceV1
