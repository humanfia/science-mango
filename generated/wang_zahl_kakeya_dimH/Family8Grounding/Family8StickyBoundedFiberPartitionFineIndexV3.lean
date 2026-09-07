import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1

/-!
# Fine-index identity for the bounded Sticky fibre partition, V3

V1 and V2 used a dot projection after a parenthesized constructor application,
which Lean parsed as another function argument.  Neither predecessor is
imported.  This successor spells out the projection function completely.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8StickyBoundedFiberPartitionFineIndexV3

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8StickyBoundedFiberPartitionCoreV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

@[simp]
theorem boundedFiberCoarseTubePartition_asConvexFactorization_fine
    (S : StickyScaleCover fine rho)
    (hscale : delta ≤ rho)
    (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ M) :
    ((CoarseTubePartition.asConvexFactorization
      (boundedFiberCoarseTubePartition S hscale hcoarse M hM)).index.fine) =
        S.activeFine :=
  rfl

#print axioms
  boundedFiberCoarseTubePartition_asConvexFactorization_fine

end

end Family8StickyBoundedFiberPartitionFineIndexV3
