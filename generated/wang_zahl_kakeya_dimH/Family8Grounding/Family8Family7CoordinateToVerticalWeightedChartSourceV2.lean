import Family8Grounding.Family8Family7CoordinateToVerticalFamilyV1
import FamilyStickyCinematicL32WZL3UniformTubeSourceV1
import Submission.Kakeya.Uniformity.Pigeonhole
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators NNReal InnerProductSpace

namespace Family8Family7CoordinateToVerticalWeightedChartSourceV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalFamilyV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# Lightweight weighted chart selection and coordinate transport

This successor deliberately imports only the finite weighted-fiber API.  It
does not import the much larger terminal hierarchy chart/bucket producer.
-/

theorem exists_verticalSourceCoordinate_abs_half
    (v : Space) (hv : ‖v‖ = 1) :
    ∃ k : Fin 3, (1 / 2 : Real) ≤ |v k| := by
  by_contra h
  push Not at h
  have h0 := h (0 : Fin 3)
  have h1 := h (1 : Fin 3)
  have h2 := h (2 : Fin 3)
  have h0sq : (v 0) ^ 2 < (1 / 4 : Real) := by
    nlinarith [abs_nonneg (v 0), sq_abs (v 0)]
  have h1sq : (v 1) ^ 2 < (1 / 4 : Real) := by
    nlinarith [abs_nonneg (v 1), sq_abs (v 1)]
  have h2sq : (v 2) ^ 2 < (1 / 4 : Real) := by
    nlinarith [abs_nonneg (v 2), sq_abs (v 2)]
  have hnorm := congrArg (fun x : Real ↦ x ^ 2) hv
  rw [EuclideanSpace.norm_eq] at hnorm
  rw [Real.sq_sqrt (by positivity)] at hnorm
  norm_num [Fin.sum_univ_succ] at hnorm
  change (v 0) ^ 2 + ((v 1) ^ 2 + (v 2) ^ 2) = 1 at hnorm
  nlinarith

noncomputable def verticalSourcePreferredCoordinate
    {radius : NNReal} (T : Tube radius) : Fin 3 :=
  Classical.choose (exists_verticalSourceCoordinate_abs_half
    T.axis.direction T.axis.norm_direction)

theorem verticalSourcePreferredCoordinate_abs_half
    {radius : NNReal} (T : Tube radius) :
    (1 / 2 : Real) ≤
      |T.axis.direction (verticalSourcePreferredCoordinate T)| :=
  Classical.choose_spec (exists_verticalSourceCoordinate_abs_half
    T.axis.direction T.axis.norm_direction)

def verticalSourceDirectionChartFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (F : UniformTubeFamily radius iota) (source : Finset iota)
    (k : Fin 3) : Finset iota :=
  dyadicFiber source
    (fun i ↦ verticalSourcePreferredCoordinate (F.tubes i)) k

@[simp] theorem mem_verticalSourceDirectionChartFiber_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (F : UniformTubeFamily radius iota) (source : Finset iota)
    (k : Fin 3) (i : iota) :
    i ∈ verticalSourceDirectionChartFiber F source k ↔
      i ∈ source ∧ verticalSourcePreferredCoordinate (F.tubes i) = k := by
  simp [verticalSourceDirectionChartFiber]

theorem direction_abs_half_of_mem_verticalSourceDirectionChartFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (F : UniformTubeFamily radius iota) (source : Finset iota)
    (k : Fin 3) {i : iota}
    (hi : i ∈ verticalSourceDirectionChartFiber F source k) :
    (1 / 2 : Real) ≤ |(F.tubes i).axis.direction k| := by
  have hk :=
    (mem_verticalSourceDirectionChartFiber_iff F source k i).mp hi |>.2
  simpa only [hk] using
    verticalSourcePreferredCoordinate_abs_half (F.tubes i)

def coordinateToVerticalChartSourceV2
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (source : Finset iota) :
    WZL3UniformTubeSource radius iota where
  family := coordinateToVerticalFamily k F
  source := verticalSourceDirectionChartFiber F source k
  source_direction_final_half i hi := by
    rw [coordinateToVerticalFamily_tubes,
      rigidTube_coordinateToVertical_direction_two]
    exact direction_abs_half_of_mem_verticalSourceDirectionChartFiber
      F source k hi

/-- A single coordinate permutation turns a weight-heavy source chart into a
literal fixed-vertical source, with the exact loss three. -/
theorem exists_coordinateToVerticalChartSourceV2_weight_retention
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (F : UniformTubeFamily radius iota) (source : Finset iota)
    (weight : iota → NNReal) :
    ∃ k : Fin 3,
      (∑ i ∈ source, weight i) ≤
        3 • ∑ i ∈ (coordinateToVerticalChartSourceV2 k F source).source,
          weight i := by
  obtain ⟨k, hweight⟩ := exists_large_weighted_fiber source
    (fun i ↦ verticalSourcePreferredCoordinate (F.tubes i)) weight
  refine ⟨k, ?_⟩
  simpa only [coordinateToVerticalChartSourceV2,
    verticalSourceDirectionChartFiber, Fintype.card_fin] using hweight

#print axioms exists_verticalSourceCoordinate_abs_half
#print axioms verticalSourcePreferredCoordinate
#print axioms verticalSourcePreferredCoordinate_abs_half
#print axioms verticalSourceDirectionChartFiber
#print axioms direction_abs_half_of_mem_verticalSourceDirectionChartFiber
#print axioms coordinateToVerticalChartSourceV2
#print axioms exists_coordinateToVerticalChartSourceV2_weight_retention

end

end Family8Family7CoordinateToVerticalWeightedChartSourceV2
