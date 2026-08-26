import FamilyStickyGrounding.FamilyStickyActualTubeTranslationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TubePairTraceV1
import FamilyStickyGrounding.FamilyStickyWZ2ProjectionSliceRetentionV1
import Submission.Kakeya.Uniformity.TubeFamily

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32ActualTubeConstantShiftV1

open FamilyStickyActualTubeTranslationV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity

noncomputable section

/-!
# Actual tubes under a uniform constant cinematic shift

Translation in the ambient `x` coordinate is an honest Euclidean translation
of a project `Tube`.  In height-graph coordinates it adds one constant to the
`a` coefficient and leaves `b`, `c`, and `d` unchanged.  Consequently it adds
the same constant to the cinematic trace and enlarges a vertical graph
neighborhood by at most the absolute value of that constant.
-/

/-- Translate an actual project tube in the ambient `x` direction. -/
def traceTranslateTube {radius : NNReal} (T : Tube radius) (s : Real) :
    Tube radius :=
  translateTube T (point3 s 0 0)

/-- The shifted object is the literal Euclidean image of the original actual
tube carrier. -/
theorem traceTranslateTube_carrier
    {radius : NNReal} (T : Tube radius) (s : Real) :
    (traceTranslateTube T s).carrier =
      Set.image (fun p => point3 s 0 0 + p) T.carrier := by
  exact translateTube_carrier T (point3 s 0 0)

/-- Honest constant shifts preserve actual three-dimensional tube volume. -/
theorem traceTranslateTube_volume
    {radius : NNReal} (T : Tube radius) (s : Real) :
    volume (traceTranslateTube T s).carrier = volume T.carrier := by
  exact translateTube_volume T (point3 s 0 0)

@[simp] theorem traceTranslateTube_axis_base
    {radius : NNReal} (T : Tube radius) (s : Real) :
    (traceTranslateTube T s).axis.base = point3 s 0 0 + T.axis.base :=
  rfl

@[simp] theorem traceTranslateTube_axis_direction
    {radius : NNReal} (T : Tube radius) (s : Real) :
    (traceTranslateTube T s).axis.direction = T.axis.direction :=
  rfl

@[simp] theorem tubeGraphC_traceTranslateTube
    {radius : NNReal} (T : Tube radius) (s : Real) :
    tubeGraphC (traceTranslateTube T s) = tubeGraphC T := by
  rfl

@[simp] theorem tubeGraphD_traceTranslateTube
    {radius : NNReal} (T : Tube radius) (s : Real) :
    tubeGraphD (traceTranslateTube T s) = tubeGraphD T := by
  rfl

@[simp] theorem tubeGraphA_traceTranslateTube
    {radius : NNReal} (T : Tube radius) (s : Real) :
    tubeGraphA (traceTranslateTube T s) = tubeGraphA T + s := by
  simp only [tubeGraphA, traceTranslateTube_axis_base,
    tubeGraphC_traceTranslateTube]
  simp [point3]
  ring_nf

@[simp] theorem tubeGraphB_traceTranslateTube
    {radius : NNReal} (T : Tube radius) (s : Real) :
    tubeGraphB (traceTranslateTube T s) = tubeGraphB T := by
  simp only [tubeGraphB, traceTranslateTube_axis_base,
    tubeGraphD_traceTranslateTube]
  simp [point3]

/-- The cinematic graph of a horizontally translated actual tube is the
original graph plus the literal constant shift. -/
theorem cinematicTraceValue_traceTranslateTube
    {radius : NNReal} (T : Tube radius) (s : Real)
    (f : Real -> Real) (theta : Real) :
    cinematicTraceValue f
        (tubeGraphA (traceTranslateTube T s))
        (tubeGraphB (traceTranslateTube T s))
        (tubeGraphC (traceTranslateTube T s))
        (tubeGraphD (traceTranslateTube T s)) theta =
      cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta + s := by
  simp [cinematicTraceValue]
  ring_nf

/-- If `T` and `U` share their `c` coefficient, shifting `T` by `s` changes
their actual curve difference from the original reduced trace to that trace
plus `s`. -/
theorem traceTranslateTube_cinematicTraceValue_sub_eq_traceFunction_add
    {radius : NNReal} (T U : Tube radius) (s : Real)
    (f : Real -> Real)
    (hcommonC : tubeGraphC T = tubeGraphC U) (theta : Real) :
    cinematicTraceValue f
        (tubeGraphA (traceTranslateTube T s))
        (tubeGraphB (traceTranslateTube T s))
        (tubeGraphC (traceTranslateTube T s))
        (tubeGraphD (traceTranslateTube T s)) theta -
      cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta =
      traceFunction f
        (tubePairDeltaA T U) (tubePairDeltaB T U)
        (tubePairDeltaD T U) theta + s := by
  rw [cinematicTraceValue_traceTranslateTube]
  calc
    cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta + s -
        cinematicTraceValue f
          (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta =
        (cinematicTraceValue f
            (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
          cinematicTraceValue f
            (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta) + s := by
          ring_nf
    _ = traceFunction f
          (tubePairDeltaA T U) (tubePairDeltaB T U)
          (tubePairDeltaD T U) theta + s := by
      rw [tube_cinematicTraceValue_sub_eq_traceFunction T U f hcommonC]

/-- Enlarging the radius by `|s|` contains the vertical neighborhood of a
graph inside that of its constant translate. -/
theorem cinematicVerticalNeighborhood_subset_add_constant
    (g : Real -> Real) (I : Set Real) (R s : Real) :
    cinematicVerticalNeighborhood g I R ⊆
      cinematicVerticalNeighborhood (fun theta => g theta + s) I (R + |s|) := by
  rintro q ⟨hqI, hq⟩
  refine ⟨hqI, ?_⟩
  calc
    |q.1 - (g q.2 + s)| = |(q.1 - g q.2) + (-s)| := by ring_nf
    _ <= |q.1 - g q.2| + |-s| := abs_add_le _ _
    _ <= R + |s| := by simpa using add_le_add_right hq |s|

/-- Any geometric carrier already lying in a graph neighborhood remains in
the shifted graph neighborhood after paying the exact `|s|` radius loss. -/
theorem subset_cinematicVerticalNeighborhood_traceTranslateTube
    {radius : NNReal} (T : Tube radius) (s : Real)
    (f : Real -> Real) (I : Set Real) (R : Real)
    (S : Set (Real × Real))
    (hcontain : S ⊆ cinematicVerticalNeighborhood
      (cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)) I R) :
    S ⊆ cinematicVerticalNeighborhood
      (cinematicTraceValue f
        (tubeGraphA (traceTranslateTube T s))
        (tubeGraphB (traceTranslateTube T s))
        (tubeGraphC (traceTranslateTube T s))
        (tubeGraphD (traceTranslateTube T s))) I (R + |s|) := by
  rw [funext (cinematicTraceValue_traceTranslateTube T s f)]
  exact hcontain.trans (cinematicVerticalNeighborhood_subset_add_constant
    (cinematicTraceValue f
      (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)) I R s)

/-- A common reference rectangle/strip contained in the original actual
tube graph neighborhood remains contained after the honest tube translation,
at the expanded radius `R + |s|`. -/
theorem common_strip_subset_traceTranslateTube_neighborhood
    {radius : NNReal} (T : Tube radius) (s : Real)
    (f reference : Real -> Real) (I : Set Real)
    (baseRadius R : Real)
    (hcontain : cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)) I R) :
    cinematicVerticalNeighborhood reference I baseRadius ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f
          (tubeGraphA (traceTranslateTube T s))
          (tubeGraphB (traceTranslateTube T s))
          (tubeGraphC (traceTranslateTube T s))
          (tubeGraphD (traceTranslateTube T s))) I (R + |s|) := by
  exact subset_cinematicVerticalNeighborhood_traceTranslateTube
    T s f I R (cinematicVerticalNeighborhood reference I baseRadius) hcontain

/-- Apply one shared honest horizontal translation to every actual tube in a
uniform family.  Its authenticated uniform refinement is reused unchanged. -/
def traceTranslateUniformTubeFamily
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (s : Real) :
    UniformTubeFamily radius iota where
  tubes i := traceTranslateTube (fine.tubes i) s
  refinement := fine.refinement

@[simp] theorem traceTranslateUniformTubeFamily_tubes
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (s : Real) (i : iota) :
    (traceTranslateUniformTubeFamily fine s).tubes i =
      traceTranslateTube (fine.tubes i) s :=
  rfl

@[simp] theorem traceTranslateUniformTubeFamily_refinement
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (s : Real) :
    (traceTranslateUniformTubeFamily fine s).refinement = fine.refinement :=
  rfl

/-- The family-level interface exposes the same constant cinematic shift at
every index, with no index-dependent geometric callback. -/
theorem cinematicTraceValue_traceTranslateUniformTubeFamily
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (s : Real)
    (f : Real -> Real) (i : iota) (theta : Real) :
    cinematicTraceValue f
        (tubeGraphA ((traceTranslateUniformTubeFamily fine s).tubes i))
        (tubeGraphB ((traceTranslateUniformTubeFamily fine s).tubes i))
        (tubeGraphC ((traceTranslateUniformTubeFamily fine s).tubes i))
        (tubeGraphD ((traceTranslateUniformTubeFamily fine s).tubes i)) theta =
      cinematicTraceValue f
        (tubeGraphA (fine.tubes i)) (tubeGraphB (fine.tubes i))
        (tubeGraphC (fine.tubes i)) (tubeGraphD (fine.tubes i)) theta + s := by
  exact cinematicTraceValue_traceTranslateTube (fine.tubes i) s f theta

#print axioms traceTranslateTube_carrier
#print axioms traceTranslateTube_volume
#print axioms tubeGraphA_traceTranslateTube
#print axioms tubeGraphB_traceTranslateTube
#print axioms cinematicTraceValue_traceTranslateTube
#print axioms traceTranslateTube_cinematicTraceValue_sub_eq_traceFunction_add
#print axioms cinematicVerticalNeighborhood_subset_add_constant
#print axioms subset_cinematicVerticalNeighborhood_traceTranslateTube
#print axioms common_strip_subset_traceTranslateTube_neighborhood
#print axioms traceTranslateUniformTubeFamily_refinement
#print axioms cinematicTraceValue_traceTranslateUniformTubeFamily

end

end FamilyStickyCinematicL32ActualTubeConstantShiftV1
