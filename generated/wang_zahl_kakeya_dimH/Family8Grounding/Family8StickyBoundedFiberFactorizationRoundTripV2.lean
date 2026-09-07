import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyBoundedFiberFactorizationRoundTripV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleCoverAdjacentStepBridgeV2
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover

noncomputable section

/-!
# Exact factorization round trip for the bounded-fibre partition

The failed V1 draft referred to a non-generated structure extensionality
name and is intentionally not imported.  Here the two constructors are
unfolded: all data fields coincide definitionally, and proof irrelevance
closes the remaining containment witness.
-/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

theorem boundedFiber_asConvexFactorization_eq_toConvexFactorization
    (S : StickyScaleCover fine rho)
    (hscale : delta ≤ rho)
    (hcoarse : S.activeCoarse.Nonempty)
    (M : Nat)
    (hM : ∀ k, k ∈ S.activeCoarse → (S.fiber k).card ≤ M) :
    (boundedFiberCoarseTubePartition S hscale hcoarse M hM).asConvexFactorization =
      toConvexFactorization S := by
  rfl

#print axioms boundedFiber_asConvexFactorization_eq_toConvexFactorization

end
end Family8StickyBoundedFiberFactorizationRoundTripV2
