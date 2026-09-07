import Family8Grounding.Family8StickyDensityAwareCanonicalLogSelectedDatumV2
import Family8Grounding.Family8GeneralBranchingDiscreteLongIntervalBootstrapV2

/-!
# Canonical selected partition into the general-branching long bootstrap

This split successor consumes the two already-projected source budgets.  It
performs only the same-object application to the existing general-branching
scalar theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyDensityAwareCanonicalGeneralBranchingScalarConnectorV3

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8GeneralBranchingDiscreteLongIntervalBootstrapV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyDensityAwareCanonicalLogSelectedDatumV2
open Family8StickyDensityAwareCanonicalLogPartitionV2
open Family8StickyDensityAwareCanonicalLogRestrictedFamiliesV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta b globalDelta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The exact two canonical source budgets feed the general-branching scalar
endpoint on the literal selected datum and partition. -/
theorem densityAwareSelected_longInterval_scalarComparison_of_sourceBudgets
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family b)
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hscale : delta ≤ b) (hactive : S.activeFine.Nonempty)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hglobalB : globalDelta ≤ b)
    (hbUpper : b ≤ globalDelta ^ (1 - P.epsilon))
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (hFineBudget :
      8192 * ((densityAwareLogPartition
          S sourceA hsourceA hD.delta_pos
            (hglobal.trans_le hglobalB) hscale hactive).branchingLoss : NNReal) ^ 2 *
          sourceA ≤
        globalDelta ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          ((densityAwareLogPartition
            S sourceA hsourceA hD.delta_pos
              (hglobal.trans_le hglobalB) hscale hactive).fineIndices.card : NNReal) *
          (delta ^ 2 / 2))
    (hBranchBudget :
      8192 * ((densityAwareLogPartition
          S sourceA hsourceA hD.delta_pos
            (hglobal.trans_le hglobalB) hscale hactive).branchingLoss : NNReal) *
          sourceA * b ^ 2 ≤
        globalDelta ^
            (-longIntervalDeltaLoss P.epsilon
              (10 * P.eta j / (P.epsilon * beta))) *
          ((densityAwareLogPartition
            S sourceA hsourceA hD.delta_pos
              (hglobal.trans_le hglobalB) hscale hactive).branching : NNReal) *
          (delta ^ 2 / 2))
    (hglobalSmall : globalDelta ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily) :
    longIntervalKatzTaoRHSENNReal
        globalDelta b
        (activeCoarseCardScaleMass
          (exactPartitionStickyCover
            (densityAwareLogPartition S sourceA hsourceA hD.delta_pos
              (hglobal.trans_le hglobalB) hscale hactive)))
        P.epsilon (10 * P.eta j / (P.epsilon * beta)) beta ≤
      longIntervalFrostmanTargetENNReal
        globalDelta b
        (activeCoarseCardScaleMass
          (exactPartitionStickyCover
            (densityAwareLogPartition S sourceA hsourceA hD.delta_pos
              (hglobal.trans_le hglobalB) hscale hactive)))
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  let hB : 0 < b := hglobal.trans_le hglobalB
  have hDsel :=
    Family8StickyDensityAwareCanonicalLogSelectedDatumV2.ActualTubeDatum.IsAdmissible.densityAwareSelected
      hD S sourceA hsourceA hD.delta_pos hB hactive
  apply
    longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_generalBranchingSourceBudgets
      (densityAwareSelectedActualDatum
        D S sourceA hsourceA hD.delta_pos hB hactive)
      hDsel
      (densityAwareSelectedCoarseFamily
        S sourceA hsourceA hD.delta_pos hB hactive)
      (densityAwareLogPartition
        S sourceA hsourceA hD.delta_pos hB hscale hactive)
      P j sourceA hglobal hglobalOne hglobalB hbUpper hbHalf
      hbeta hgamma hFineBudget hBranchBudget hglobalSmall
  exact (densityAwareSelectedActualDatum_isKatzTao_iff
    D S sourceA hsourceA hD.delta_pos hB hactive
      (sourceA : ENNReal)).2 hsourceKT

#print axioms
  densityAwareSelected_longInterval_scalarComparison_of_sourceBudgets

end
end Family8StickyDensityAwareCanonicalGeneralBranchingScalarConnectorV3
