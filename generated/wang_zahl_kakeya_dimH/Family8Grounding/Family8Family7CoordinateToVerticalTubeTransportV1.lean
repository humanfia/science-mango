import Family8Grounding.Family8GeneralizedFrostmanMultiplicityV1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8Family7CoordinateToVerticalTubeTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8GeneralizedFrostmanMultiplicityV1

noncomputable section

/-!
# Move an honest direction chart to the fixed vertical coordinate

The projected PYZ stack is hard-coded to coordinate `2`.  This file gives
the missing deterministic transport for the preceding three-coordinate
chart pigeonhole: one global coordinate permutation sends the selected
coordinate `k` to output coordinate `2`.  It is an ambient rigid motion, so
actual tube carriers and volumes are transported exactly.
-/

/-- Swap the selected source coordinate with the fixed vertical coordinate. -/
def coordinateToVerticalPermutation (k : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap k 2

/-- The coordinate permutation as a linear isometric equivalence of the
ambient Euclidean space. -/
def coordinateToVerticalLinearIsometry (k : Fin 3) :
    Space ≃ₗᵢ[Real] Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 Real Real
    (coordinateToVerticalPermutation k)

/-- The same coordinate permutation in the repository's rigid-motion API. -/
def coordinateToVerticalRigidMotion (k : Fin 3) : RigidMotion :=
  (coordinateToVerticalLinearIsometry k).toAffineIsometryEquiv

@[simp] theorem coordinateToVerticalLinearIsometry_apply
    (k j : Fin 3) (x : Space) :
    coordinateToVerticalLinearIsometry k x j =
      x ((coordinateToVerticalPermutation k).symm j) :=
  rfl

@[simp] theorem coordinateToVerticalLinearIsometry_apply_two
    (k : Fin 3) (x : Space) :
    coordinateToVerticalLinearIsometry k x 2 = x k := by
  simp [coordinateToVerticalPermutation]

@[simp] theorem coordinateToVerticalRigidMotion_apply
    (k : Fin 3) (x : Space) :
    coordinateToVerticalRigidMotion k x =
      coordinateToVerticalLinearIsometry k x :=
  rfl

@[simp] theorem coordinateToVerticalRigidMotion_zero (k : Fin 3) :
    coordinateToVerticalRigidMotion k 0 = 0 := by
  simp [coordinateToVerticalRigidMotion]

@[simp] theorem rigidTube_coordinateToVertical_direction
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    (rigidTube (coordinateToVerticalRigidMotion k) T).axis.direction =
      coordinateToVerticalLinearIsometry k T.axis.direction := by
  rfl

@[simp] theorem rigidTube_coordinateToVertical_direction_two
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    (rigidTube (coordinateToVerticalRigidMotion k) T).axis.direction 2 =
      T.axis.direction k := by
  rw [rigidTube_coordinateToVertical_direction]
  exact coordinateToVerticalLinearIsometry_apply_two k T.axis.direction

theorem rigidTube_coordinateToVertical_carrier
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    (rigidTube (coordinateToVerticalRigidMotion k) T).carrier =
      coordinateToVerticalRigidMotion k '' T.carrier :=
  rigidTube_carrier _ _

theorem rigidTube_coordinateToVertical_volume
    {radius : NNReal} (k : Fin 3) (T : Tube radius) :
    volume (rigidTube (coordinateToVerticalRigidMotion k) T).carrier =
      volume T.carrier :=
  rigidTube_volume _ _

#print axioms coordinateToVerticalPermutation
#print axioms coordinateToVerticalLinearIsometry
#print axioms coordinateToVerticalRigidMotion
#print axioms coordinateToVerticalLinearIsometry_apply_two
#print axioms rigidTube_coordinateToVertical_direction_two
#print axioms rigidTube_coordinateToVertical_carrier
#print axioms rigidTube_coordinateToVertical_volume

end

end Family8Family7CoordinateToVerticalTubeTransportV1
