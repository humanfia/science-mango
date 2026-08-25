import FamilyStickyGrounding.FamilyStickyWZ2CinematicTubeContainmentV1
import Submission.Kakeya.ConvexGeometry.Tube

set_option autoImplicit false

open MeasureTheory

namespace FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2CinematicTubeContainmentV1
open Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Actual project tubes in WZ2 cinematic coordinates

This module connects the project's concrete `Tube` and `Shading` carriers to
the coordinate-line/cinematic-neighborhood producer.  For an axis with
nonzero vertical component it constructs the graph parameters `(a,b,c,d)`,
proves the exact axis identity, and extracts coordinate errors directly from
membership in the tube's compact closed thickening.

The representation and containment are conclusions, not callbacks.
-/

/-- Horizontal `x` slope when the tube axis is parametrized by height. -/
def tubeGraphC {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.direction 0 / T.axis.direction 2

/-- Horizontal `y` slope when the tube axis is parametrized by height. -/
def tubeGraphD {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.direction 1 / T.axis.direction 2

/-- `x` intercept of the height-parametrized tube axis. -/
def tubeGraphA {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.base 0 - tubeGraphC T * T.axis.base 2

/-- `y` intercept of the height-parametrized tube axis. -/
def tubeGraphB {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.base 1 - tubeGraphD T * T.axis.base 2

/-- Height reached at the standard unit-segment parameter `s`. -/
def tubeAxisHeight {delta : NNReal} (T : Tube delta) (s : Real) : Real :=
  T.axis.base 2 + s * T.axis.direction 2

/-- The interval of heights attained by the tube axis. -/
def tubeAxisHeightSet {delta : NNReal} (T : Tube delta) : Set Real :=
  tubeAxisHeight T '' Set.Icc 0 1

/-- A uniform absolute bound for the `y` coordinate along the axis. -/
def tubeAxisYBound {delta : NNReal} (T : Tube delta) : Real :=
  |T.axis.base 1| + |T.axis.direction 1|

/-- An axis with nonzero vertical component is exactly the graph line with
the constructed `(a,b,c,d)` parameters. -/
theorem tubeAxisPoint_eq_parameterLinePoint
    {delta : NNReal} (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0) (s : Real) :
    T.axis.base + s • T.axis.direction =
      parameterLinePoint (tubeGraphA T) (tubeGraphB T)
        (tubeGraphC T) (tubeGraphD T) (tubeAxisHeight T s) := by
  ext i
  fin_cases i <;>
    simp [parameterLinePoint, point3, tubeGraphA, tubeGraphB,
      tubeGraphC, tubeGraphD, tubeAxisHeight] <;>
    field_simp <;>
    ring

/-- The graph's `y` coordinate is the literal `y` coordinate of the standard
axis parametrization. -/
theorem tubeGraphY_eq_axisY
    {delta : NNReal} (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0) (s : Real) :
    tubeGraphB T + tubeGraphD T * tubeAxisHeight T s =
      T.axis.base 1 + s * T.axis.direction 1 := by
  have h := congrArg (fun p : Space => p 1)
    (tubeAxisPoint_eq_parameterLinePoint T hvertical s)
  simpa [parameterLinePoint, point3] using h.symm

/-- The explicit `tubeAxisYBound` controls the graph on every attained
height. -/
theorem abs_tubeGraphY_le_axisYBound
    {delta : NNReal} (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0)
    {t : Real} (ht : t ∈ tubeAxisHeightSet T) :
    |tubeGraphB T + tubeGraphD T * t| <= tubeAxisYBound T := by
  rcases ht with ⟨s, hs, rfl⟩
  rw [tubeGraphY_eq_axisY T hvertical]
  calc
    |T.axis.base 1 + s * T.axis.direction 1| <=
        |T.axis.base 1| + |s * T.axis.direction 1| := abs_add_le _ _
    _ = |T.axis.base 1| + |s| * |T.axis.direction 1| := by
      rw [abs_mul]
    _ <= |T.axis.base 1| + 1 * |T.axis.direction 1| := by
      gcongr
      simpa [abs_of_nonneg hs.1] using hs.2
    _ = tubeAxisYBound T := by simp [tubeAxisYBound]

/-- The actual compact closed tube carrier is contained in the corresponding
coordinate-line tube with the same radius. -/
theorem tubeCarrier_subset_coordinateLineTube
    {delta : NNReal} (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0) :
    T.carrier ⊆
      coordinateLineTube (tubeAxisHeightSet T)
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)
        (delta : Real) := by
  intro p hp
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 <= (delta : Real) by positivity)] at hp
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hp
  obtain ⟨y, hyAxis, hdist⟩ := hp
  rw [T.axis.carrier_eq_image] at hyAxis
  obtain ⟨s, hs, rfl⟩ := hyAxis
  let t := tubeAxisHeight T s
  have ht : t ∈ tubeAxisHeightSet T := ⟨s, hs, rfl⟩
  have haxis := tubeAxisPoint_eq_parameterLinePoint T hvertical s
  have hcoordinate (i : Fin 3) :
      |p i -
        (parameterLinePoint (tubeGraphA T) (tubeGraphB T)
          (tubeGraphC T) (tubeGraphD T) t) i| <= (delta : Real) := by
    rw [← haxis]
    simpa only [Real.dist_eq] using
      (PiLp.dist_apply_le p (T.axis.base + s • T.axis.direction) i).trans hdist
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · simpa [parameterLinePoint, point3] using hcoordinate (0 : Fin 3)
  · simpa [parameterLinePoint, point3] using hcoordinate (1 : Fin 3)
  · simpa [parameterLinePoint, point3] using hcoordinate (2 : Fin 3)

/-- The project tube carrier therefore projects into a controlled cinematic
box neighborhood. -/
theorem twistedProjection_image_tubeCarrier_subset
    {delta : NNReal} (T : Tube delta)
    (hvertical : T.axis.direction 2 ≠ 0)
    (f : Real -> Real) (F L : Real)
    (hF : 0 <= F) (hL : 0 <= L)
    (hfBound : forall z, |f z| <= F)
    (hfLip : forall z t, |f z - f t| <= L * |z - t|) :
    twistedProjection f '' T.carrier ⊆
      cinematicBoxNeighborhood f (tubeAxisHeightSet T)
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)
        ((delta : Real) + F * delta +
          L * delta * tubeAxisYBound T) := by
  apply twistedProjection_image_subset_cinematicBoxNeighborhood
      f (tubeAxisHeightSet T)
      (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T)
      (delta : Real) F L (tubeAxisYBound T) T.carrier
      (tubeCarrier_subset_coordinateLineTube T hvertical)
      (by positivity) hF hL
      (by
        unfold tubeAxisYBound
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)) hfBound hfLip
  intro t ht
  exact abs_tubeGraphY_le_axisYBound T hvertical ht

/-- A family of actual project tubes, viewed as the convex family expected by
the project's `Shading` structure. -/
def tubeBodyFamily {iota : Type*} {delta : NNReal}
    (tubes : iota -> Tube delta) : ConvexFamily iota :=
  fun i => (tubes i).body

/-- Every shading carrier of an actual tube family lies in the automatically
constructed coordinate-line tube. -/
theorem shadingCarrier_subset_coordinateLineTube
    {iota : Type*} {delta : NNReal} (tubes : iota -> Tube delta)
    (Y : Shading (tubeBodyFamily tubes)) (i : iota)
    (hvertical : (tubes i).axis.direction 2 ≠ 0) :
    Y.carrier i ⊆
      coordinateLineTube (tubeAxisHeightSet (tubes i))
        (tubeGraphA (tubes i)) (tubeGraphB (tubes i))
        (tubeGraphC (tubes i)) (tubeGraphD (tubes i))
        (delta : Real) := by
  apply (Y.carrier_subset i).trans
  exact tubeCarrier_subset_coordinateLineTube (tubes i) hvertical

/-- Actual shaded tube pieces project into their controlled cinematic
neighborhoods, with no carrier-containment callback. -/
theorem twistedProjection_image_shadingCarrier_subset
    {iota : Type*} {delta : NNReal} (tubes : iota -> Tube delta)
    (Y : Shading (tubeBodyFamily tubes)) (i : iota)
    (hvertical : (tubes i).axis.direction 2 ≠ 0)
    (f : Real -> Real) (F L : Real)
    (hF : 0 <= F) (hL : 0 <= L)
    (hfBound : forall z, |f z| <= F)
    (hfLip : forall z t, |f z - f t| <= L * |z - t|) :
    twistedProjection f '' Y.carrier i ⊆
      cinematicBoxNeighborhood f (tubeAxisHeightSet (tubes i))
        (tubeGraphA (tubes i)) (tubeGraphB (tubes i))
        (tubeGraphC (tubes i)) (tubeGraphD (tubes i))
        ((delta : Real) + F * delta +
          L * delta * tubeAxisYBound (tubes i)) := by
  exact (Set.image_mono (Y.carrier_subset i)).trans
    (twistedProjection_image_tubeCarrier_subset
      (tubes i) hvertical f F L hF hL hfBound hfLip)

#print axioms tubeAxisPoint_eq_parameterLinePoint
#print axioms tubeGraphY_eq_axisY
#print axioms abs_tubeGraphY_le_axisYBound
#print axioms tubeCarrier_subset_coordinateLineTube
#print axioms twistedProjection_image_tubeCarrier_subset
#print axioms shadingCarrier_subset_coordinateLineTube
#print axioms twistedProjection_image_shadingCarrier_subset

end

end FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
