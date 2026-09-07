import Family8Grounding.Family8Family7CoordinateToVerticalTubeTransportV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped NNReal

namespace Family8Family7CoordinateToVerticalFamilyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8GeneralizedFrostmanMultiplicityV1

noncomputable section

universe u

/-! # Same-index tube-family coordinate transport -/

/-- Apply the selected coordinate permutation to every actual tube, retaining
the original index type and refinement metadata. -/
def coordinateToVerticalFamily
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota) :
    UniformTubeFamily radius iota where
  tubes i := rigidTube (coordinateToVerticalRigidMotion k) (F.tubes i)
  refinement := F.refinement

@[simp] theorem coordinateToVerticalFamily_tubes
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota) (i : iota) :
    (coordinateToVerticalFamily k F).tubes i =
      rigidTube (coordinateToVerticalRigidMotion k) (F.tubes i) :=
  rfl

@[simp] theorem coordinateToVerticalFamily_refinement
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota) :
    (coordinateToVerticalFamily k F).refinement = F.refinement :=
  rfl

@[simp] theorem coordinateToVerticalFamily_direction_two
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota) (i : iota) :
    ((coordinateToVerticalFamily k F).tubes i).axis.direction 2 =
      (F.tubes i).axis.direction k := by
  exact rigidTube_coordinateToVertical_direction_two k (F.tubes i)

#print axioms coordinateToVerticalFamily
#print axioms coordinateToVerticalFamily_tubes
#print axioms coordinateToVerticalFamily_refinement
#print axioms coordinateToVerticalFamily_direction_two

end

end Family8Family7CoordinateToVerticalFamilyV1
