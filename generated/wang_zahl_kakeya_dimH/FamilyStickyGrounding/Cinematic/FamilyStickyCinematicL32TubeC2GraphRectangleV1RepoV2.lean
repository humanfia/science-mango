import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairApproxTraceV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32TubeC2GraphRectangleV1

open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32TubePairApproxTraceV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Actual project tubes as C2 graph rectangles

The cinematic graph associated to a project tube is
`a + c*theta + f(theta)*(b+d*theta)`.  This module proves its first two
derivatives directly and packages any compact base interval as the concrete
`C2GraphRectangle` consumed by the PYZ rectangle-counting chain.  It also
identifies pairwise differences with the already frozen trace jets.
-/

/-- First derivative of one full cinematic tube graph. -/
def cinematicTraceFirstValue
    (f f1 : Real -> Real) (b c d theta : Real) : Real :=
  c + f1 theta * (b + d * theta) + f theta * d

/-- Second derivative of one full cinematic tube graph. -/
def cinematicTraceSecondValue
    (f1 f2 : Real -> Real) (b d theta : Real) : Real :=
  f2 theta * (b + d * theta) + 2 * d * f1 theta

/-- The displayed first jet is the actual derivative of the full graph. -/
theorem hasDerivAt_cinematicTraceValue
    (f f1 : Real -> Real) (a b c d theta : Real)
    (hf : HasDerivAt f (f1 theta) theta) :
    HasDerivAt (cinematicTraceValue f a b c d)
      (cinematicTraceFirstValue f f1 b c d theta) theta := by
  change HasDerivAt
    (fun z => a + c * z + f z * (b + d * z))
    (c + f1 theta * (b + d * theta) + f theta * d) theta
  have hlinear : HasDerivAt (fun z => a + c * z) c theta := by
    convert! ((hasDerivAt_id theta).const_mul c).const_add a using 1; ring
  have hinner : HasDerivAt (fun z => b + d * z) d theta := by
    convert! ((hasDerivAt_id theta).const_mul d).const_add b using 1; ring
  have hproduct : HasDerivAt (fun z => f z * (b + d * z))
      (f1 theta * (b + d * theta) + f theta * d) theta :=
    hf.mul hinner
  convert! hlinear.add hproduct using 1
  ring

/-- The displayed second jet is the actual derivative of the first jet. -/
theorem hasDerivAt_cinematicTraceFirstValue
    (f f1 f2 : Real -> Real) (b c d theta : Real)
    (hf : HasDerivAt f (f1 theta) theta)
    (hf1 : HasDerivAt f1 (f2 theta) theta) :
    HasDerivAt (cinematicTraceFirstValue f f1 b c d)
      (cinematicTraceSecondValue f1 f2 b d theta) theta := by
  change HasDerivAt
    (fun z => c + f1 z * (b + d * z) + f z * d)
    (f2 theta * (b + d * theta) + 2 * d * f1 theta) theta
  have hinner : HasDerivAt (fun z => b + d * z) d theta := by
    convert! ((hasDerivAt_id theta).const_mul d).const_add b using 1; ring
  have hproduct : HasDerivAt (fun z => f1 z * (b + d * z))
      (f2 theta * (b + d * theta) + f1 theta * d) theta :=
    hf1.mul hinner
  have hlast : HasDerivAt (fun z => f z * d) (f1 theta * d) theta :=
    hf.mul_const d
  have hconstant : HasDerivAt (fun _z : Real => c) 0 theta :=
    hasDerivAt_const theta c
  convert! (hconstant.add hproduct).add hlast using 1; ring

/-- Full first jet attached to an actual project tube. -/
def tubeCinematicTraceFirstValue {radius : NNReal}
    (T : Tube radius) (f f1 : Real -> Real) (theta : Real) : Real :=
  cinematicTraceFirstValue f f1
    (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta

/-- Full second jet attached to an actual project tube. -/
def tubeCinematicTraceSecondValue {radius : NNReal}
    (T : Tube radius) (f1 f2 : Real -> Real) (theta : Real) : Real :=
  cinematicTraceSecondValue f1 f2
    (tubeGraphB T) (tubeGraphD T) theta

/-- A project tube graph restricted to an actual closed base interval. -/
def tubeC2GraphRectangle {radius : NNReal}
    (T : Tube radius) (f f1 f2 : Real -> Real)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (left right : Real) (hleftRight : left <= right) : C2GraphRectangle where
  rectangle :=
    { graph := cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)
      left := left
      right := right
      left_le_right := hleftRight }
  first := tubeCinematicTraceFirstValue T f f1
  second := tubeCinematicTraceSecondValue T f1 f2
  graph_hasDeriv := fun z => by
    exact hasDerivAt_cinematicTraceValue f f1
      (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
      (hf z)
  first_hasDeriv := fun z => by
    exact hasDerivAt_cinematicTraceFirstValue f f1 f2
      (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) z
      (hf z) (hf1 z)

/-- First-jet difference of two actual tube graphs is the `c` difference
plus the reduced first trace jet. -/
theorem tubeCinematicTraceFirstValue_sub_eq
    {radius : NNReal} (T U : Tube radius)
    (f f1 : Real -> Real) (theta : Real) :
    tubeCinematicTraceFirstValue T f f1 theta -
        tubeCinematicTraceFirstValue U f f1 theta =
      (tubeGraphC T - tubeGraphC U) +
        traceFirstDerivative f f1
          (tubePairDeltaB T U) (tubePairDeltaD T U) theta := by
  simp only [tubeCinematicTraceFirstValue, cinematicTraceFirstValue,
    traceFirstDerivative,
    FamilyStickyCinematicL32JetSeparationV1.traceJet1,
    tubePairDeltaB, tubePairDeltaD]
  ring

/-- Second-jet difference of two actual tube graphs is the reduced second
trace jet; the linear `c` term has disappeared. -/
theorem tubeCinematicTraceSecondValue_sub_eq
    {radius : NNReal} (T U : Tube radius)
    (f1 f2 : Real -> Real) (theta : Real) :
    tubeCinematicTraceSecondValue T f1 f2 theta -
        tubeCinematicTraceSecondValue U f1 f2 theta =
      traceSecondDerivative f1 f2
        (tubePairDeltaB T U) (tubePairDeltaD T U) theta := by
  simp only [tubeCinematicTraceSecondValue, cinematicTraceSecondValue,
    traceSecondDerivative,
    FamilyStickyCinematicL32JetSeparationV1.traceJet2,
    tubePairDeltaB, tubePairDeltaD]
  ring

#print axioms cinematicTraceFirstValue
#print axioms cinematicTraceSecondValue
#print axioms hasDerivAt_cinematicTraceValue
#print axioms hasDerivAt_cinematicTraceFirstValue
#print axioms tubeC2GraphRectangle
#print axioms tube_cinematicTraceValue_sub_eq_linear_add_trace
#print axioms tubeCinematicTraceFirstValue_sub_eq
#print axioms tubeCinematicTraceSecondValue_sub_eq

end

end FamilyStickyCinematicL32TubeC2GraphRectangleV1
