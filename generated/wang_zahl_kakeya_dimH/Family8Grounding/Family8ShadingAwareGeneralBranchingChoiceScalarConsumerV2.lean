import Family8Grounding.Family8ShadingAwareGeneralBranchingChoiceV3
import Family8Grounding.Family8GeneralBranchingDiscreteLongIntervalBootstrapV2

/-!
# Scalar consumer for a compact shading-aware branching choice, V2

V1 omitted the namespace exporting the exact-partition sticky cover and is
not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open scoped ENNReal NNReal

namespace Family8ShadingAwareGeneralBranchingChoiceScalarConsumerV2

open Submission.Kakeya.ConvexFactoring
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8GeneralBranchingDiscreteLongIntervalBootstrapV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ShadingAwareGeneralBranchingChoiceV3

noncomputable section

variable {delta b globalDelta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The generic source-budget endpoint reads only the frozen choice fields. -/
theorem ShadingAwareGeneralBranchingChoice.longInterval_scalarComparison
    (Q : ShadingAwareGeneralBranchingChoice delta b index)
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (sourceA : NNReal)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta <= 1)
    (hglobalB : globalDelta <= b)
    (hbUpper : b <= globalDelta ^ (1 - P.epsilon))
    (hbHalf : b <= (2 : NNReal)⁻¹)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hFineBudget :
      8192 * (Q.partition.branchingLoss : NNReal) ^ 2 * sourceA <=
        globalDelta ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          (Q.partition.fineIndices.card : NNReal) * (delta ^ 2 / 2))
    (hBranchBudget :
      8192 * (Q.partition.branchingLoss : NNReal) * sourceA * b ^ 2 <=
        globalDelta ^
            (-longIntervalDeltaLoss P.epsilon
              (10 * P.eta j / (P.epsilon * beta))) *
          (Q.partition.branching : NNReal) * (delta ^ 2 / 2))
    (hglobalSmall : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) Q.datum.family.bodyFamily) :
    longIntervalKatzTaoRHSENNReal globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Q.partition))
        P.epsilon (10 * P.eta j / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Q.partition))
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  exact
    longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_generalBranchingSourceBudgets
      Q.datum Q.admissible Q.coarse Q.partition P j sourceA
      hglobal hglobalOne hglobalB hbUpper hbHalf hbeta hgamma
      hFineBudget hBranchBudget hglobalSmall hsourceKT

#print axioms ShadingAwareGeneralBranchingChoice.longInterval_scalarComparison

end
end Family8ShadingAwareGeneralBranchingChoiceScalarConsumerV2
