import Family8Grounding.Family8Family7CoordinateToVerticalFamilyV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7CoordinateToVerticalShadingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalFamilyV1
open Family8Family7CoordinateToVerticalTubeTransportV1

noncomputable section

universe u

/-! # Same-index actual-shading coordinate transport -/

/-- Transport every actual shading carrier by the same global coordinate
permutation used for its tube. -/
def coordinateToVerticalShading
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) :
    Shading (coordinateToVerticalFamily k F).bodyFamily where
  carrier i := coordinateToVerticalRigidMotion k '' Y.carrier i
  measurable_carrier i :=
    (coordinateToVerticalRigidMotion k).toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i)
  carrier_subset i := by
    rw [UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
      coordinateToVerticalFamily_tubes,
      rigidTube_coordinateToVertical_carrier]
    exact Set.image_mono (Y.carrier_subset i)

@[simp] theorem coordinateToVerticalShading_carrier
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (i : iota) :
    (coordinateToVerticalShading k F Y).carrier i =
      coordinateToVerticalRigidMotion k '' Y.carrier i :=
  rfl

#print axioms coordinateToVerticalShading
#print axioms coordinateToVerticalShading_carrier

end

end Family8Family7CoordinateToVerticalShadingV1
