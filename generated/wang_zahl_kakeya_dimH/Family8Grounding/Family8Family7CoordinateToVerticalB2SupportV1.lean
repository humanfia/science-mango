import Family8Grounding.Family8Family7CoordinateToVerticalFamilyV1
import Mathlib.Tactic

/-!
# Radius-two support under the vertical coordinate permutation

The coordinate-to-vertical map is a linear isometry fixing the origin.
Consequently any memberwise `B(0,2)` support certificate transports exactly
to the coordinate family.  This geometric lemma is independent of all
FirstCrossing density and graph-selection modules.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8Family7CoordinateToVerticalB2SupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalTubeTransportV1

noncomputable section

universe u

/-- A common radius-two support bound is preserved memberwise by the exact
coordinate permutation used by the Family7 vertical chart. -/
theorem coordinateToVerticalFamily_carrier_subset_closedBall_two
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    (hB2 : ∀ i,
      (F.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2) :
    ∀ i,
      ((coordinateToVerticalFamily axis F).tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro i _x hx
  rw [coordinateToVerticalFamily_tubes,
    rigidTube_coordinateToVertical_carrier] at hx
  obtain ⟨x, hxF, rfl⟩ := hx
  have hxBall := hB2 i hxF
  rw [Metric.mem_closedBall] at hxBall ⊢
  calc
    dist (coordinateToVerticalRigidMotion axis x) 0 =
        dist (coordinateToVerticalRigidMotion axis x)
          (coordinateToVerticalRigidMotion axis 0) := by
      rw [coordinateToVerticalRigidMotion_zero]
    _ = dist x 0 :=
      (coordinateToVerticalRigidMotion axis).isometry.dist_eq x 0
    _ ≤ 2 := hxBall

#print axioms coordinateToVerticalFamily_carrier_subset_closedBall_two

end
end Family8Family7CoordinateToVerticalB2SupportV1
