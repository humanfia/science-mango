import Family8Grounding.Family8Family7WeightedVerticalGraphCBucketV1
import FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Family8Family7WeightedVerticalGraphCBucketActualBridgeV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open Family8Family7WeightedVerticalGraphCBucketV1

noncomputable section

universe u

/-! # Definitional bridge to the native-high stack's bucket name -/

@[simp] theorem verticalGraphCBucket_eq_actualProjectedTubeCBucket
    {radius : NNReal} (eta : Real) (T : Tube radius) :
    verticalGraphCBucket eta T = actualProjectedTubeCBucket eta T :=
  rfl

theorem actualProjectedTubeCBucket_eq_of_mem_verticalSourceGraphCBucketFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (eta : Real) (S : WZL3UniformTubeSource radius iota)
    (label : Int) {i : iota}
    (hi : i ∈ verticalSourceGraphCBucketFiber eta S label) :
    actualProjectedTubeCBucket eta (S.family.tubes i) = label := by
  rw [← verticalGraphCBucket_eq_actualProjectedTubeCBucket]
  exact (mem_verticalSourceGraphCBucketFiber_iff eta S label i).1 hi |>.2

#print axioms verticalGraphCBucket_eq_actualProjectedTubeCBucket
#print axioms actualProjectedTubeCBucket_eq_of_mem_verticalSourceGraphCBucketFiber

end

end Family8Family7WeightedVerticalGraphCBucketActualBridgeV1
