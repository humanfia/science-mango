import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGraphTangencyCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32LocalTangencyV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TubePairTraceV1

open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Actual project tube pairs as coefficient-difference traces

This is the thin carrier adapter between the project's concrete `Tube`
parameters and the PYZ trace modules.  Tubes in one fixed `c`-slice have
curve difference exactly equal to the Wang--Zahl trace with coefficient
differences in `(a,b,d)`.
-/

/-- The three reduced coefficient differences of an ordered tube pair. -/
def tubePairDeltaA {radius : NNReal} (T U : Tube radius) : Real :=
  tubeGraphA T - tubeGraphA U

def tubePairDeltaB {radius : NNReal} (T U : Tube radius) : Real :=
  tubeGraphB T - tubeGraphB U

def tubePairDeltaD {radius : NNReal} (T U : Tube radius) : Real :=
  tubeGraphD T - tubeGraphD U

/-- The reduced parameter distance used by the cinematic tangency theorem. -/
def tubePairCoefficientDistance {radius : NNReal}
    (T U : Tube radius) : Real :=
  coefficientDistance
    (tubePairDeltaA T U) (tubePairDeltaB T U) (tubePairDeltaD T U)

/-- In a fixed horizontal-slope slice, the difference of the two actual tube
curves is the literal coefficient-difference trace. -/
theorem tube_cinematicTraceValue_sub_eq_traceFunction
    {radius : NNReal} (T U : Tube radius)
    (f : Real -> Real)
    (hcommonC : tubeGraphC T = tubeGraphC U) (theta : Real) :
    cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
      cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta =
      traceFunction f
        (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) theta := by
  rw [← hcommonC]
  exact cinematicTraceValue_sub_eq_traceFunction
    f (tubeGraphA T) (tubeGraphB T)
      (tubeGraphA U) (tubeGraphB U)
      (tubeGraphC T) (tubeGraphD T) (tubeGraphD U) theta

/-- A common reference strip tangent to two actual tubes in one `c`-slice
produces the exact trace-sublevel premise consumed by Lemma 3.9. -/
theorem common_strip_tangency_forces_tubePair_trace_sublevel
    {radius : NNReal} (T U : Tube radius)
    (f reference : Real -> Real) (I : Set Real)
    (hcommonC : tubeGraphC T = tubeGraphC U)
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
        (tubePairDeltaD T U) theta| <= 2 * R := by
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
  rw [← tube_cinematicTraceValue_sub_eq_traceFunction T U f hcommonC]
  exact hvalue theta htheta

#print axioms tube_cinematicTraceValue_sub_eq_traceFunction
#print axioms common_strip_tangency_forces_tubePair_trace_sublevel

end

end FamilyStickyCinematicL32TubePairTraceV1
