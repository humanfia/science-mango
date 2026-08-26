import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32RolleBridgeV1
import FamilyStickyGrounding.FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

set_option autoImplicit false

open Set

noncomputable section

namespace FamilyStickyCinematicL32RectangleTangencyV1

open FamilyStickyCinematicL32RolleBridgeV1

/-!
# Clean actual cinematic graph and tangency core

This records only the explicit graph formula and the elementary common-strip
triangle inequality needed by the PYZ/Jordan path.  Actual-tube coordinates
are reused from the canonical coordinate adapter so their names have one
definition across the combined Family7 development.
-/

/-- The vertical `R`-neighborhood of a scalar graph over `I`. -/
def cinematicVerticalNeighborhood
    (g : Real -> Real) (I : Set Real) (R : Real) : Set (Real × Real) :=
  {q | q.2 ∈ I ∧ |q.1 - g q.2| <= R}

/-- If one reference strip lies in two graph neighborhoods, the two graph
values differ by at most twice the outer radius. -/
theorem common_strip_tangency_forces_value_sublevel
    (reference g k : Real -> Real) (I : Set Real)
    {baseRadius R : Real} (hbaseRadius : 0 <= baseRadius)
    (hg : cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood g I R)
    (hk : cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood k I R) :
    forall theta, theta ∈ I -> |g theta - k theta| <= 2 * R := by
  intro theta htheta
  have href : (reference theta, theta) ∈
      cinematicVerticalNeighborhood reference I baseRadius := by
    exact ⟨htheta, by simpa using hbaseRadius⟩
  have hgAt := (hg href).2
  have hkAt := (hk href).2
  calc
    |g theta - k theta| =
        |(g theta - reference theta) + (reference theta - k theta)| := by
      ring_nf
    _ <= |g theta - reference theta| +
        |reference theta - k theta| := abs_add_le _ _
    _ = |reference theta - g theta| +
        |reference theta - k theta| := by rw [abs_sub_comm (g theta)]
    _ <= R + R := add_le_add hgAt hkAt
    _ = 2 * R := by ring

/-- First coordinate of the actual Wang--Zahl cinematic curve. -/
def cinematicTraceValue
    (f : Real -> Real) (a b c d t : Real) : Real :=
  a + c * t + f t * (b + d * t)

/-- In a common `c`-slice, the graph difference is the reduced trace. -/
theorem cinematicTraceValue_sub_eq_traceFunction
    (f : Real -> Real)
    (a1 b1 a2 b2 c d1 d2 t : Real) :
    cinematicTraceValue f a1 b1 c d1 t -
        cinematicTraceValue f a2 b2 c d2 t =
      traceFunction f (a1 - a2) (b1 - b2) (d1 - d2) t := by
  simp only [cinematicTraceValue, traceFunction,
    FamilyStickyCinematicL32JetSeparationV1.traceJet0]
  ring

/-- Common-strip tangency for two explicit cinematic graphs produces the
literal trace sublevel estimate. -/
theorem common_strip_tangency_forces_trace_sublevel
    (f reference : Real -> Real) (I : Set Real)
    (a1 b1 a2 b2 c d1 d2 : Real)
    {baseRadius R : Real} (hbaseRadius : 0 <= baseRadius)
    (hfirst : cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f a1 b1 c d1) I R)
    (hsecond : cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f a2 b2 c d2) I R) :
    forall theta, theta ∈ I ->
      |traceFunction f (a1 - a2) (b1 - b2) (d1 - d2) theta| <=
        2 * R := by
  have hvalue := common_strip_tangency_forces_value_sublevel
    reference
    (cinematicTraceValue f a1 b1 c d1)
    (cinematicTraceValue f a2 b2 c d2)
    I hbaseRadius hfirst hsecond
  intro theta htheta
  rw [← cinematicTraceValue_sub_eq_traceFunction]
  exact hvalue theta htheta

end FamilyStickyCinematicL32RectangleTangencyV1

#print axioms FamilyStickyCinematicL32RectangleTangencyV1.cinematicTraceValue_sub_eq_traceFunction
#print axioms FamilyStickyCinematicL32RectangleTangencyV1.common_strip_tangency_forces_trace_sublevel
