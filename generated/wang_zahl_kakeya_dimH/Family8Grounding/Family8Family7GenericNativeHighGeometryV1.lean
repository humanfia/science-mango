import Family8Grounding.Family8ShadingAwareGenericNativeBranchCoreV2
import FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighGeometryV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# Minimal native-high geometry over an arbitrary physical core

Only the fields read by the pattern-first weighted critical-scale route are
retained.  In particular this is not a port of the old monolithic
`NativeHighGeometry` and carries no branch conclusion.
-/

abbrev GenericNativeHighCenter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) :=
  D.HighCenter

abbrev GenericNativeHighPayloadCandidate
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (c : GenericNativeHighCenter D) :=
  D.HighPayloadCandidate c

structure GenericNativeHighGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) where
  bucket : Int
  hbucket : ∀ i, i ∈ physical.ambient →
    actualProjectedTubeCBucket ((radius : Real) / 2)
      (S.family.tubes i) = bucket
  mesh : GenericNativeHighCenter D → Real
  ballRadius : GenericNativeHighCenter D → Real
  hballRadiusLower : ∀ c, (radius : Real) ≤ ballRadius c

#print axioms GenericNativeHighCenter
#print axioms GenericNativeHighPayloadCandidate
#print axioms GenericNativeHighGeometry

end

end Family8Family7GenericNativeHighGeometryV1
