import Family8Grounding.Family8Family7GenericNativeHighGeometryV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

namespace Family8Family7GenericNativeHighGeometryOfBucketV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7GenericNativeHighGeometryV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! # Minimal native-high geometry from a genuine common graph-c bucket -/

def genericNativeHighGeometryOfBucket
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ physical.ambient →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket) :
    GenericNativeHighGeometry D where
  bucket := bucket
  hbucket := hbucket
  mesh := fun _ => radius
  ballRadius := fun _ => radius
  hballRadiusLower := fun _ => le_rfl

@[simp] theorem genericNativeHighGeometryOfBucket_ballRadius
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (bucket : Int)
    (hbucket : ∀ i, i ∈ physical.ambient →
      actualProjectedTubeCBucket ((radius : Real) / 2)
        (S.family.tubes i) = bucket)
    (c : D.HighCenter) :
    (genericNativeHighGeometryOfBucket D bucket hbucket).ballRadius c = radius :=
  rfl

#print axioms genericNativeHighGeometryOfBucket
#print axioms genericNativeHighGeometryOfBucket_ballRadius

end

end Family8Family7GenericNativeHighGeometryOfBucketV1
