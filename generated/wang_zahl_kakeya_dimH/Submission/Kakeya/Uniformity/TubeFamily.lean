import Submission.Kakeya.ConvexGeometry.Family
import Submission.Kakeya.ConvexGeometry.Tube
import Submission.Kakeya.Uniformity.Refinement

namespace Submission.Kakeya.Uniformity

open Submission.Kakeya.ConvexGeometry

/-!
# Uniform tube families

A uniform tube family keeps the geometric tube indexed by each member together
with a certified uniform refinement of the same index type.  The indexed
presentation preserves repetitions when the tubes are viewed as convex bodies.
-/

/-- A geometric tube family equipped with a certified uniform index refinement. -/
structure UniformTubeFamily (δ : NNReal) (ι : Type*) [DecidableEq ι] where
  tubes : ι → Tube δ
  refinement : UniformRefinement ι

namespace UniformTubeFamily

/-- Forget tube axes while retaining the authenticated convex bodies. -/
def bodyFamily {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) : ConvexFamily ι :=
  fun i ↦ (family.tubes i).body

theorem bodyFamily_apply {δ : NNReal} {ι : Type*} [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (i : ι) :
    family.bodyFamily i = (family.tubes i).body := by
  rfl

end UniformTubeFamily

end Submission.Kakeya.Uniformity
