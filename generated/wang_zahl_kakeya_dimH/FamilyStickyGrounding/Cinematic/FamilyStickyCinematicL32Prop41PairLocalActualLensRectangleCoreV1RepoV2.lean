import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubeC2GraphRectangleV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Clean pair-local lens/rectangle data for PYZ Proposition 4.1

No global reference graph occurs in this type.  The two tangencies belong to
the assigned pair, and exact two-root data are literal.  A reference graph is
constructed only when a comparison chooses a shared tube.

This core deliberately does not import the legacy global-reference lens
record or any downstream moon/counting module.
-/

/-- Roots of one literal actual tube pair on the working interval. -/
def pairLocalActualRootSet {radius : NNReal} (T U : Tube radius)
    (f : Real -> Real) (A B : Real) : Set Real :=
  {theta | theta ∈ Icc A B ∧
    cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) theta =
      cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U) theta}

/-- Pair-local actual lens data.  `exact_root_set` is precisely the
“intersect exactly twice” output of the PYZ shift lemma. -/
structure PairLocalActualLensRectangleData {radius : NNReal}
    (T U : Tube radius) (f : Real -> Real) (R : C2GraphRectangle)
    (A B delta t lambda0 : Real) where
  thetaLeft : Real
  thetaRight : Real
  theta_order : thetaLeft < thetaRight
  thetaLeft_mem : thetaLeft ∈ Icc A B
  thetaRight_mem : thetaRight ∈ Icc A B
  left_mem_quarter : R.rectangle.left ∈
    centeredFractionIcc A B (1 / 4 : Real)
  right_mem_quarter : R.rectangle.right ∈
    centeredFractionIcc A B (1 / 4 : Real)
  rectangle_width : Real.sqrt (delta / t) <=
    R.rectangle.right - R.rectangle.left
  common_c : tubeGraphC T = tubeGraphC U
  root_left :
    cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) thetaLeft =
      cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U) thetaLeft
  root_right :
    cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) thetaRight =
      cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U) thetaRight
  exact_root_set : pairLocalActualRootSet T U f A B =
    {thetaLeft, thetaRight}
  coefficient_lower : t <= tubePairCoefficientDistance T U
  tangent_first : R.carrier delta ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T)) R.rectangle.base
      (2 * lambda0 * delta)
  tangent_second : R.carrier delta ⊆
    cinematicVerticalNeighborhood
      (cinematicTraceValue f (tubeGraphA U) (tubeGraphB U)
        (tubeGraphC U) (tubeGraphD U)) R.rectangle.base
      (2 * lambda0 * delta)

/-- Closed parameter support between the two exact roots. -/
def PairLocalActualLensRectangleData.lensSupport
    {radius : NNReal} {T U : Tube radius} {f : Real -> Real}
    {R : C2GraphRectangle} {A B delta t lambda0 : Real}
    (D : PairLocalActualLensRectangleData T U f R
      A B delta t lambda0) : Set Real :=
  prop41PairRootSupport D.thetaLeft D.thetaRight

/-- Actual `C2` reference constructed from a chosen shared tube. -/
def pairLocalTubeReference {radius : NNReal} (T : Tube radius)
    (f f1 f2 : Real -> Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (A B : Real) (hAB : A <= B) : C2GraphRectangle :=
  tubeC2GraphRectangle T f f1 f2 hfDeriv hf1Deriv A B hAB

/-- Exact two-root records for the same pair have overlapping supports. -/
theorem PairLocalActualLensRectangleData.lensSupports_overlap_samePair
    {radius : NNReal} {T U : Tube radius} {f : Real -> Real}
    {R S : C2GraphRectangle} {A B delta t lambda0 : Real}
    (D1 : PairLocalActualLensRectangleData T U f R
      A B delta t lambda0)
    (D2 : PairLocalActualLensRectangleData T U f S
      A B delta t lambda0) :
    (D1.lensSupport ∩ D2.lensSupport).Nonempty := by
  have hroot : D1.thetaLeft ∈ pairLocalActualRootSet T U f A B :=
    ⟨D1.thetaLeft_mem, D1.root_left⟩
  rw [D2.exact_root_set] at hroot
  have hcases : D1.thetaLeft = D2.thetaLeft ∨
      D1.thetaLeft = D2.thetaRight := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hroot
  refine ⟨D1.thetaLeft, ?_, ?_⟩
  · exact ⟨le_rfl, D1.theta_order.le⟩
  · rcases hcases with hleft | hright
    · rw [hleft]
      exact ⟨le_rfl, D2.theta_order.le⟩
    · rw [hright]
      exact ⟨D2.theta_order.le, le_rfl⟩

#print axioms pairLocalActualRootSet
#print axioms PairLocalActualLensRectangleData
#print axioms PairLocalActualLensRectangleData.lensSupport
#print axioms pairLocalTubeReference
#print axioms PairLocalActualLensRectangleData.lensSupports_overlap_samePair

end

end FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
