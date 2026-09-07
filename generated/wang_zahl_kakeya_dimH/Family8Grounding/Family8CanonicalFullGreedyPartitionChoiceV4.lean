import Family8Grounding.Family8SelectedParentGreedyBlockFiberIdentityV2
import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity

/-!
# A canonical full greedy partition of the active parents, V4

This file freezes only the finite greedy choice.  Keeping the choice separate
from the later multiplicity assembly prevents downstream proofs from
re-elaborating one large nested existential.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalFullGreedyPartitionChoiceV4

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The small existence package from which the canonical choice is frozen. -/
theorem exists_fullGreedyPartition
    (S : StickyScaleCover fine rho) :
    ∃ P : GreedyDensityPartition S.activeCoarseFamily
        (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
        (hullContainer S.activeCoarseFamily) Finset.univ,
      P.coveredIndices = Finset.univ ∧
      P.length ≤ (Finset.univ : Finset (ActiveParentIndex S)).card ∧
      AllWinnerGlobalCross S.activeCoarseFamily Finset.univ P :=
  exists_fullConvexGreedyDensityPartition S.activeCoarseFamily Finset.univ

/-- A fixed full greedy hull-density partition of the active parents of `S`. -/
noncomputable def canonicalFullGreedyPartition
    (S : StickyScaleCover fine rho) :
    GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ :=
  Classical.choose (exists_fullGreedyPartition S)

/-- The three certified fields of the fixed greedy choice. -/
theorem canonicalFullGreedyPartition_spec
    (S : StickyScaleCover fine rho) :
    (canonicalFullGreedyPartition S).coveredIndices = Finset.univ ∧
      (canonicalFullGreedyPartition S).length ≤
        (Finset.univ : Finset (ActiveParentIndex S)).card ∧
      AllWinnerGlobalCross S.activeCoarseFamily Finset.univ
        (canonicalFullGreedyPartition S) :=
  Classical.choose_spec (exists_fullGreedyPartition S)

@[simp] theorem canonicalFullGreedyPartition_coveredIndices
    (S : StickyScaleCover fine rho) :
    (canonicalFullGreedyPartition S).coveredIndices = Finset.univ :=
  (canonicalFullGreedyPartition_spec S).1

theorem canonicalFullGreedyPartition_length_le
    (S : StickyScaleCover fine rho) :
    (canonicalFullGreedyPartition S).length ≤
      Fintype.card (ActiveParentIndex S) := by
  simpa using (canonicalFullGreedyPartition_spec S).2.1

theorem canonicalFullGreedyPartition_allWinnerGlobalCross
    (S : StickyScaleCover fine rho) :
    AllWinnerGlobalCross S.activeCoarseFamily Finset.univ
      (canonicalFullGreedyPartition S) :=
  (canonicalFullGreedyPartition_spec S).2.2

#print axioms exists_fullGreedyPartition
#print axioms canonicalFullGreedyPartition
#print axioms canonicalFullGreedyPartition_spec
#print axioms canonicalFullGreedyPartition_coveredIndices
#print axioms canonicalFullGreedyPartition_length_le
#print axioms canonicalFullGreedyPartition_allWinnerGlobalCross

end
end Family8CanonicalFullGreedyPartitionChoiceV4
