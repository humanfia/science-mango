import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ActualTubeConstantShiftV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# A uniform honest actual-tube realization of the three trace shifts

Each item is allowed to produce its own pointwise witness among the three
scalar shifts.  Pigeonholing selects one common shift on a nonempty fiber
containing at least one third of all items.  Translating every first actual
tube in that fiber by the same ambient `x` displacement realizes the selected
scalar roots as literal zeros of the difference of the two cinematic curves.

No global label, retained fiber, or root is assumed.
-/

/-- The reduced scalar trace of one tube pair has a root on each side of an
interior separator after adding `eta * s` to its constant coefficient. -/
def HasScalarTwoSidedRootsAtShift
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (A B s eta : Real) : Prop :=
  exists theta0 thetaLeft thetaRight : Real,
    thetaLeft ∈ Ioo A theta0 ∧
    traceFunction f
        (tubePairDeltaA T U + eta * s)
        (tubePairDeltaB T U) (tubePairDeltaD T U) thetaLeft = 0 ∧
    thetaRight ∈ Ioo theta0 B ∧
    traceFunction f
        (tubePairDeltaA T U + eta * s)
        (tubePairDeltaB T U) (tubePairDeltaD T U) thetaRight = 0

/-- A scalar root after shifting the constant trace coefficient is the same
parameter at which the cinematic curves of the honestly translated first
tube and the unchanged second tube agree. -/
theorem actualTube_cinematicDifference_zero_of_scalarTrace_shift_root
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (shift theta : Real)
    (hcommonC : tubeGraphC T = tubeGraphC U)
    (hroot :
      traceFunction f
          (tubePairDeltaA T U + shift)
          (tubePairDeltaB T U) (tubePairDeltaD T U) theta = 0) :
    cinematicTraceValue f
          (tubeGraphA (traceTranslateTube T shift))
          (tubeGraphB (traceTranslateTube T shift))
          (tubeGraphC (traceTranslateTube T shift))
          (tubeGraphD (traceTranslateTube T shift)) theta -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U)
          (tubeGraphC U) (tubeGraphD U) theta = 0 := by
  rw [traceTranslateTube_cinematicTraceValue_sub_eq_traceFunction_add
    T U shift f hcommonC theta]
  calc
    traceFunction f
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) theta + shift =
        traceFunction f
          (tubePairDeltaA T U + shift) (tubePairDeltaB T U)
          (tubePairDeltaD T U) theta := by
      simp only [traceFunction, traceJet0]
      ring
    _ = 0 := hroot

/-- From pointwise three-shift scalar root witnesses, select one common label
and a nonempty fiber retaining at least one third of the finite carrier.  On
that fiber, the same honest translation `traceTranslateTube _ (eta * s)`
realizes both scalar roots as zeros of the corresponding actual cinematic
curve difference. -/
theorem exists_uniform_threeShift_actualTube_root_fiber
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (items : Finset alpha) (T U : alpha -> Tube radius)
    (f : Real -> Real) (A B s : Real)
    (hitems : items.Nonempty)
    (hcommonC : forall i, i ∈ items ->
      tubeGraphC (T i) = tubeGraphC (U i))
    (hpointwise : forall i, i ∈ items ->
      exists eta : Real,
        eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
        HasScalarTwoSidedRootsAtShift (T i) (U i) f A B s eta) :
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
              (tubePairDeltaA (T i) (U i) + eta * s)
              (tubePairDeltaB (T i) (U i))
              (tubePairDeltaD (T i) (U i)) thetaLeft = 0 ∧
          cinematicTraceValue f
                (tubeGraphA (traceTranslateTube (T i) (eta * s)))
                (tubeGraphB (traceTranslateTube (T i) (eta * s)))
                (tubeGraphC (traceTranslateTube (T i) (eta * s)))
                (tubeGraphD (traceTranslateTube (T i) (eta * s))) thetaLeft -
              cinematicTraceValue f
                (tubeGraphA (U i)) (tubeGraphB (U i))
                (tubeGraphC (U i)) (tubeGraphD (U i)) thetaLeft = 0 ∧
          thetaRight ∈ Ioo theta0 B ∧
          traceFunction f
              (tubePairDeltaA (T i) (U i) + eta * s)
              (tubePairDeltaB (T i) (U i))
              (tubePairDeltaD (T i) (U i)) thetaRight = 0 ∧
          cinematicTraceValue f
                (tubeGraphA (traceTranslateTube (T i) (eta * s)))
                (tubeGraphB (traceTranslateTube (T i) (eta * s)))
                (tubeGraphC (traceTranslateTube (T i) (eta * s)))
                (tubeGraphD (traceTranslateTube (T i) (eta * s))) thetaRight -
              cinematicTraceValue f
                (tubeGraphA (U i)) (tubeGraphB (U i))
                (tubeGraphC (U i)) (tubeGraphD (U i)) thetaRight = 0 := by
  let good : alpha -> Fin 3 -> Prop := fun i k =>
    HasScalarTwoSidedRootsAtShift
      (T i) (U i) f A B s (threeShiftValue k)
  have hgood : forall i, i ∈ items -> exists k : Fin 3, good i k := by
    intro i hi
    obtain ⟨eta, heta, hroots⟩ := hpointwise i hi
    obtain ⟨k, hk⟩ := exists_threeShiftLabel_of_mem heta
    refine ⟨k, ?_⟩
    dsimp only [good]
    simpa only [hk] using hroots
  obtain ⟨k, hkNonempty, hkCard, hkGood⟩ :=
    exists_uniform_threeShift_fiber items good hitems hgood
  let fiber : Finset alpha :=
    threeShiftFiber items
      (chosenThreeShiftLabel items good hgood) k
  have hfiberSubset : fiber ⊆ items := by
    intro i hi
    have hi' : i ∈ threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k := by
      simpa only [fiber] using hi
    exact (mem_threeShiftFiber_iff items
      (chosenThreeShiftLabel items good hgood) k i).mp hi' |>.1
  refine ⟨k, threeShiftValue k, fiber, rfl, threeShiftValue_mem k,
    ?_, hfiberSubset, ?_, ?_⟩
  · simpa only [fiber] using hkNonempty
  · simpa only [fiber] using hkCard
  · intro i hi
    have hi' : i ∈ threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k := by
      simpa only [fiber] using hi
    have hroots : HasScalarTwoSidedRootsAtShift
        (T i) (U i) f A B s (threeShiftValue k) := by
      exact hkGood i hi'
    obtain ⟨theta0, thetaLeft, thetaRight, hthetaLeft,
        hrootLeft, hthetaRight, hrootRight⟩ := hroots
    have hiItems : i ∈ items := hfiberSubset hi
    have hactualLeft :=
      actualTube_cinematicDifference_zero_of_scalarTrace_shift_root
        (T i) (U i) f (threeShiftValue k * s) thetaLeft
        (hcommonC i hiItems) hrootLeft
    have hactualRight :=
      actualTube_cinematicDifference_zero_of_scalarTrace_shift_root
        (T i) (U i) f (threeShiftValue k * s) thetaRight
        (hcommonC i hiItems) hrootRight
    exact ⟨theta0, thetaLeft, thetaRight, hthetaLeft, hrootLeft,
      hactualLeft, hthetaRight, hrootRight, hactualRight⟩

#print axioms actualTube_cinematicDifference_zero_of_scalarTrace_shift_root
#print axioms exists_uniform_threeShift_actualTube_root_fiber

end

end FamilyStickyCinematicL32Prop41ActualTubeThreeShiftPigeonholeV1
