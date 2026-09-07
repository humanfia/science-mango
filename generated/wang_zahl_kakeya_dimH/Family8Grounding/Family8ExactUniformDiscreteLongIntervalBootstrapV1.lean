import Family8Grounding.Family8ExactUniformLowerParentMassV2
import Family8Grounding.Family8DiscreteLongIntervalEndpointBootstrapV1

/-!
# Exact-uniform discrete long-interval bootstrap

An exact-uniform selected partition supplies the Katz--Tao input of the
single-endpoint bootstrap directly.  This successor keeps the coefficient in
`NNReal`, so the remaining hypotheses are scalar bounds and the canonical
Frostman estimate for the very same selected coarse family.  No all-real
coherent cover is introduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactUniformDiscreteLongIntervalBootstrapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

variable {delta b : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily b (Fin coarseCard)}

/-- The exact branching lower parent-mass density, represented in `NNReal`. -/
def exactBranchingParentMassDensityNNReal
    (Ppart : CoarseTubePartition fine coarse) : NNReal :=
  (Ppart.branching : NNReal) * (delta ^ 2 / 2) / (8 * b ^ 2)

theorem exactBranchingParentMassDensityNNReal_pos
    (Ppart : CoarseTubePartition fine coarse)
    (hloss : Ppart.branchingLoss = 1)
    (hcoarse : Ppart.coarseIndices.Nonempty)
    (hdelta : 0 < delta) (hb : 0 < b) :
    0 < exactBranchingParentMassDensityNNReal Ppart := by
  have hbranch : 0 < Ppart.branching :=
    Family8ExactUniformLowerParentMassV2.branching_pos_of_coarseIndices_nonempty
      Ppart hloss hcoarse
  unfold exactBranchingParentMassDensityNNReal
  positivity

theorem coe_exactBranchingParentMassDensityNNReal
    (Ppart : CoarseTubePartition fine coarse) (hb : 0 < b) :
    (exactBranchingParentMassDensityNNReal Ppart : ENNReal) =
      Family8ExactUniformLowerParentMassV2.exactBranchingParentMassDensity
        Ppart := by
  unfold exactBranchingParentMassDensityNNReal
    Family8ExactUniformLowerParentMassV2.exactBranchingParentMassDensity
  rw [ENNReal.coe_div (by positivity : (8 * b ^ 2 : NNReal) ≠ 0)]
  rw [ENNReal.coe_mul]
  rw [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
  rfl

/-- The exact-uniform coarse Katz--Tao coefficient in `NNReal`. -/
def exactUniformCoarseKatzTaoNNReal (sourceA : NNReal)
    (Ppart : CoarseTubePartition fine coarse) : NNReal :=
  sourceA / exactBranchingParentMassDensityNNReal Ppart

theorem coe_exactUniformCoarseKatzTaoNNReal
    (sourceA : NNReal) (Ppart : CoarseTubePartition fine coarse)
    (hloss : Ppart.branchingLoss = 1)
    (hcoarse : Ppart.coarseIndices.Nonempty)
    (hdelta : 0 < delta) (hb : 0 < b) :
    (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) =
      (sourceA : ENNReal) *
        (Family8ExactUniformLowerParentMassV2.exactBranchingParentMassDensity
          Ppart)⁻¹ := by
  have hlower : 0 < exactBranchingParentMassDensityNNReal Ppart :=
    exactBranchingParentMassDensityNNReal_pos
      Ppart hloss hcoarse hdelta hb
  unfold exactUniformCoarseKatzTaoNNReal
  rw [ENNReal.coe_div hlower.ne']
  rw [coe_exactBranchingParentMassDensityNNReal Ppart hb]
  rfl

/-- Exact uniformity discharges the Katz--Tao premise of the literal selected
endpoint.  Thus only the same-endpoint canonical Frostman bound and the final
scalar absorption remain. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformDiscreteEndpoint
    {globalDelta : NNReal} {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (coarse : UniformTubeFamily b (Fin coarseCard))
    (Ppart : CoarseTubePartition D.family coarse)
    (hloss : Ppart.branchingLoss = 1)
    (hcoarse : Ppart.coarseIndices.Nonempty)
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (sourceA : NNReal)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta <= 1)
    (hglobalB : globalDelta <= b)
    (hbUpper : b <= globalDelta ^ (1 - P.epsilon))
    (hbHalf : b <= (2 : NNReal)⁻¹)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hC : canonicalFrostmanConstant
        (exactPartitionStickyCover Ppart).activeCoarseFamily
        closedBallFourBody <=
      (globalDelta : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
    (hglobalSmall : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily)
    (hAKT : 1024 * exactUniformCoarseKatzTaoNNReal sourceA Ppart <=
      globalDelta ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta j / (P.epsilon * beta)))) :
    longIntervalKatzTaoRHSENNReal
        globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Ppart))
        P.epsilon (10 * P.eta j / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Ppart))
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  have hb : 0 < b := hglobal.trans_le hglobalB
  apply
    Family8DiscreteLongIntervalEndpointBootstrapV1.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_discreteEndpoint
      D hD (exactPartitionStickyCover Ppart) P j
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart)
      hglobal hglobalOne hglobalB hbUpper hbHalf hcoarse
      hbeta hgamma hC hglobalSmall
  · rw [coe_exactUniformCoarseKatzTaoNNReal
      sourceA Ppart hloss hcoarse hD.delta_pos hb]
    exact
      Family8ExactUniformLowerParentMassV2.exactPartitionStickyCover_isKatzTaoAtScale_of_source
        Ppart hloss hcoarse hD.delta_pos hb hD.delta_le_half hbHalf hsourceKT
  · exact hAKT

#print axioms exactBranchingParentMassDensityNNReal
#print axioms exactBranchingParentMassDensityNNReal_pos
#print axioms coe_exactBranchingParentMassDensityNNReal
#print axioms exactUniformCoarseKatzTaoNNReal
#print axioms coe_exactUniformCoarseKatzTaoNNReal
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformDiscreteEndpoint

end
end Family8ExactUniformDiscreteLongIntervalBootstrapV1
