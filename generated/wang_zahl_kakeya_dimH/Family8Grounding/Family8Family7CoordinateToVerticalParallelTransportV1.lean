import Family8Grounding.Family8Family7CoordinateToVerticalFamilyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped NNReal

namespace Family8Family7CoordinateToVerticalParallelTransportV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8GeneralizedFrostmanMultiplicityV1
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalFamilyV1

noncomputable section

universe u

/-! # Same-index transport of the extremal same-scale geometry -/

@[simp] theorem essentiallyParallelAtScale_coordinateToVertical_iff
    {radius : NNReal} (k : Fin 3) (T U : Tube radius) :
    EssentiallyParallelAtScale
        (rigidTube (coordinateToVerticalRigidMotion k) T)
        (rigidTube (coordinateToVerticalRigidMotion k) U) ↔
      EssentiallyParallelAtScale T U := by
  simp only [EssentiallyParallelAtScale,
    rigidTube_coordinateToVertical_direction]
  have hangle : InnerProductGeometry.angle
      (coordinateToVerticalLinearIsometry k T.axis.direction)
      (coordinateToVerticalLinearIsometry k U.axis.direction) =
      InnerProductGeometry.angle T.axis.direction U.axis.direction := by
    exact (coordinateToVerticalLinearIsometry k).toLinearIsometry.angle_map
      T.axis.direction U.axis.direction
  rw [hangle]

/-- Moving only the left tube is equivalent to moving the right tube by the
inverse rigid motion. -/
theorem essentiallyParallelAtScale_rigidTube_left_iff
    {radius : NNReal} (R : RigidMotion) (T U : Tube radius) :
    EssentiallyParallelAtScale (rigidTube R T) U ↔
      EssentiallyParallelAtScale T (rigidTube R.symm U) := by
  simp only [EssentiallyParallelAtScale, rigidTube_axis,
    rigidUnitSegment_direction]
  have hangle : InnerProductGeometry.angle
      (R.linearIsometryEquiv T.axis.direction) U.axis.direction =
      InnerProductGeometry.angle T.axis.direction
        (R.symm.linearIsometryEquiv U.axis.direction) := by
    have hmap := R.linearIsometryEquiv.symm.toLinearIsometry.angle_map
      (R.linearIsometryEquiv T.axis.direction) U.axis.direction
    have hlinear : R.symm.linearIsometryEquiv =
        R.linearIsometryEquiv.symm := by
      ext x
      rfl
    rw [hlinear]
    simpa using hmap.symm
  rw [hangle]

/-- Apply the same coordinate permutation to every parent tube of a literal
same-scale cover.  The fine indices and parent map remain unchanged. -/
def coordinateToVerticalTubeScaleCover
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily radius iota} {active : Finset iota}
    (k : Fin 3) (C : @TubeScaleCover radius radius iota _ fine active) :
    @TubeScaleCover radius radius iota _
      (coordinateToVerticalFamily k fine) active where
  count := C.count
  tubes q := rigidTube (coordinateToVerticalRigidMotion k) (C.tubes q)
  parent := C.parent
  carrier_subset := by
    intro i hi
    rw [coordinateToVerticalFamily_tubes,
      rigidTube_coordinateToVertical_carrier,
      rigidTube_coordinateToVertical_carrier]
    exact Set.image_mono (C.carrier_subset i hi)

@[simp] theorem coordinateToVerticalTubeScaleCover_count
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily radius iota} {active : Finset iota}
    (k : Fin 3) (C : @TubeScaleCover radius radius iota _ fine active) :
    (coordinateToVerticalTubeScaleCover k C).count = C.count :=
  rfl

@[simp] theorem coordinateToVerticalTubeScaleCover_parallelCluster
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily radius iota} {active : Finset iota}
    (k : Fin 3) (C : @TubeScaleCover radius radius iota _ fine active)
    (U : Tube radius) :
    (coordinateToVerticalTubeScaleCover k C).parallelCluster
        (rigidTube (coordinateToVerticalRigidMotion k) U) =
      C.parallelCluster U := by
  classical
  unfold TubeScaleCover.parallelCluster
  apply Finset.filter_congr
  intro q _hq
  exact essentiallyParallelAtScale_coordinateToVertical_iff k (C.tubes q) U

/-- The transported cover inherits the original parallel-cluster loss for
every (not necessarily visibly transported) query tube. -/
theorem coordinateToVerticalTubeScaleCover_cluster_card_le
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily radius iota} {active : Finset iota}
    (k : Fin 3) (C : @TubeScaleCover radius radius iota _ fine active)
    {parallelLoss : Nat}
    (hcluster : ∀ U : Tube radius,
      (C.parallelCluster U).card ≤ parallelLoss)
    (U : Tube radius) :
    ((coordinateToVerticalTubeScaleCover k C).parallelCluster U).card ≤
      parallelLoss := by
  have heq :
      (coordinateToVerticalTubeScaleCover k C).parallelCluster U =
        C.parallelCluster
          (rigidTube (coordinateToVerticalRigidMotion k).symm U) := by
    classical
    unfold TubeScaleCover.parallelCluster
    apply Finset.filter_congr
    intro q _hq
    exact essentiallyParallelAtScale_rigidTube_left_iff
      (coordinateToVerticalRigidMotion k) (C.tubes q) U
  rw [heq]
  exact hcluster _

#print axioms essentiallyParallelAtScale_coordinateToVertical_iff
#print axioms essentiallyParallelAtScale_rigidTube_left_iff
#print axioms coordinateToVerticalTubeScaleCover
#print axioms coordinateToVerticalTubeScaleCover_parallelCluster
#print axioms coordinateToVerticalTubeScaleCover_cluster_card_le

end

end Family8Family7CoordinateToVerticalParallelTransportV1
