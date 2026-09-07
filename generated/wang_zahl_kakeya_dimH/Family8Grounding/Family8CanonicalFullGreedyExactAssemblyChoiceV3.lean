import Family8Grounding.Family8CanonicalFullGreedyPartitionChoiceV4
import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly

/-!
# A canonical exact assembly on the fixed full greedy partition, V3

The greedy partition and multiplicity assembly are frozen in separate files.
This keeps the dependent choice small and exposes its two level bounds as
independent projections.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalFullGreedyExactAssemblyChoiceV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CanonicalFullGreedyPartitionChoiceV4
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal finite-cardinality loss of the exact multiplicity assembly. -/
def canonicalFullGreedyAssemblyLoss
    (S : StickyScaleCover fine rho) : Nat :=
  ((Fintype.card (ActiveParentIndex S) + 1) *
      (Fintype.card (ActiveParentIndex S) + 1)) *
    (Fintype.card
      (Option (Fin (blocks S.activeCoarseFamily
        (canonicalFullGreedyPartition S)).length)) + 1)

/-- The small exact-assembly existence package on the already frozen `P`. -/
theorem exists_canonicalFullGreedyExactAssembly
    (S : StickyScaleCover fine rho) (Y : Shading S.activeCoarseFamily) :
    ∃ A : ExactAssembly
        (greedyParentFactorization S (canonicalFullGreedyPartition S)) Y
        (canonicalFullGreedyAssemblyLoss S),
      A.fineLevel ≤ Fintype.card (ActiveParentIndex S) ∧
      A.outerLevel ≤ Fintype.card
        (Option (Fin (blocks S.activeCoarseFamily
          (canonicalFullGreedyPartition S)).length)) := by
  simpa only [canonicalFullGreedyAssemblyLoss] using
    (exists_greedyExactAssembly (canonicalFullGreedyPartition S) Y)

/-- A fixed exact assembly on the fixed full greedy partition. -/
noncomputable def canonicalFullGreedyExactAssembly
    (S : StickyScaleCover fine rho) (Y : Shading S.activeCoarseFamily) :
    ExactAssembly
      (greedyParentFactorization S (canonicalFullGreedyPartition S)) Y
      (canonicalFullGreedyAssemblyLoss S) :=
  Classical.choose (exists_canonicalFullGreedyExactAssembly S Y)

/-- Both certified level bounds of the fixed assembly. -/
theorem canonicalFullGreedyExactAssembly_spec
    (S : StickyScaleCover fine rho) (Y : Shading S.activeCoarseFamily) :
    (canonicalFullGreedyExactAssembly S Y).fineLevel ≤
        Fintype.card (ActiveParentIndex S) ∧
      (canonicalFullGreedyExactAssembly S Y).outerLevel ≤
        Fintype.card
          (Option (Fin (blocks S.activeCoarseFamily
            (canonicalFullGreedyPartition S)).length)) :=
  Classical.choose_spec (exists_canonicalFullGreedyExactAssembly S Y)

theorem canonicalFullGreedyExactAssembly_fineLevel_le
    (S : StickyScaleCover fine rho) (Y : Shading S.activeCoarseFamily) :
    (canonicalFullGreedyExactAssembly S Y).fineLevel ≤
      Fintype.card (ActiveParentIndex S) :=
  (canonicalFullGreedyExactAssembly_spec S Y).1

theorem canonicalFullGreedyExactAssembly_outerLevel_le
    (S : StickyScaleCover fine rho) (Y : Shading S.activeCoarseFamily) :
    (canonicalFullGreedyExactAssembly S Y).outerLevel ≤
      Fintype.card
        (Option (Fin (blocks S.activeCoarseFamily
          (canonicalFullGreedyPartition S)).length)) :=
  (canonicalFullGreedyExactAssembly_spec S Y).2

#print axioms canonicalFullGreedyAssemblyLoss
#print axioms exists_canonicalFullGreedyExactAssembly
#print axioms canonicalFullGreedyExactAssembly
#print axioms canonicalFullGreedyExactAssembly_spec
#print axioms canonicalFullGreedyExactAssembly_fineLevel_le
#print axioms canonicalFullGreedyExactAssembly_outerLevel_le

end
end Family8CanonicalFullGreedyExactAssemblyChoiceV3
