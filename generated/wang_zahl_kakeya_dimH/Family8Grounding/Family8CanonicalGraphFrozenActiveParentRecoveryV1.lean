import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Mathlib.Tactic

/-!
# Recover the selected active parent from a canonical graph identity

The raw graph certificate records a nonempty graph contained in the selected
sticky-cover fibre.  Hence its selected parent is automatically active.  This
connector recovers that literal provenance without strengthening the identity
record or asking for a new equality.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalGraphFrozenActiveParentRecoveryV1

open Submission.Kakeya.ConvexFactoring
open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- The selected parent of a canonical graph identity is active, because the
certificate supplies a nonempty graph contained in its literal fibre. -/
theorem SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {F : UniformTubeFamily tau fineIndex}
    {T : StickyScaleCover F rho}
    {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
    {Y : Shading F.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    R.k ∈ T.activeCoarse := by
  obtain ⟨Q⟩ := R.graphCertificate
  obtain ⟨i, hiGraph⟩ := Q.graph_nonempty
  have hiFiber : i ∈ T.fiber R.k := Q.graph_subset hiGraph
  have hi := (T.mem_fiber i R.k).mp hiFiber
  simpa only [hi.2] using T.parent_mem i hi.1

#print axioms SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse

end
end Family8CanonicalGraphFrozenActiveParentRecoveryV1
