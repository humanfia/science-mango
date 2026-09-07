import Family8Grounding.Family8IdentityRadiusLossOnePartitionV2
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1

/-!
# The identity long-core cover carries the loss-one partition

For the concrete identity coherent cover, the canonical buffered global
cover reduces definitionally to the identity-radius scale cover.  Therefore
the exact branching-one partition is available on the literal long-core
endpoint, without transporting any arbitrary cover compatibility.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped ENNReal NNReal

namespace Family8IdentityCoreCanonicalBufferedLossOneAdapterV1

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8IdentityRadiusLossOnePartitionV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The long-core global cover for the identity coherent cover is literally
the identity-radius cover at its canonical buffered radius. -/
theorem identityCore_canonicalBufferedGlobalCover_eq_identityRadiusScaleCover
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    canonicalBufferedGlobalCover
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf =
      identityRadiusScaleCover D.family (canonicalBufferedRadius W)
        ((S.delta_le_tau W.m).trans
          (tau_le_canonicalBufferedRadius
            W hD.delta_pos P.epsilon_pos.le)) := by
  rfl

/-- The exact loss-one partition on the literal identity long-core endpoint. -/
def identityCoreCanonicalBufferedLossOnePartition
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    CoarseTubePartition D.family
      (canonicalBufferedGlobalCover
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf).coarse := by
  let hscale : delta <= canonicalBufferedRadius W :=
    (S.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
  let hcoarse :
      (canonicalBufferedGlobalCover
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeCoarse.Nonempty :=
    canonicalBufferedGlobalCover_activeCoarse_nonempty
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf hfine
  exact identityRadiusLossOnePartition D.family hscale hcoarse

@[simp] theorem identityCoreCanonicalBufferedLossOnePartition_branching
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    (identityCoreCanonicalBufferedLossOnePartition
      D hD S P W hepsilonHalf hfine).branching = 1 := by
  rfl

@[simp] theorem identityCoreCanonicalBufferedLossOnePartition_branchingLoss
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    (identityCoreCanonicalBufferedLossOnePartition
      D hD S P W hepsilonHalf hfine).branchingLoss = 1 := by
  rfl

/-- Forgetting the loss-one fields recovers the exact canonical long-core
global cover, definitionally. -/
theorem exactPartitionStickyCover_identityCoreCanonicalBufferedLossOnePartition
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family (identityRadiusCoherentCover D.family)
        P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    Family8CoarseTubePartitionExactUniformStickyFiberV4.exactPartitionStickyCover
        (identityCoreCanonicalBufferedLossOnePartition
          D hD S P W hepsilonHalf hfine) =
      canonicalBufferedGlobalCover
        W hD.delta_pos P.epsilon_pos.le hepsilonHalf := by
  rfl

#print axioms
  identityCore_canonicalBufferedGlobalCover_eq_identityRadiusScaleCover
#print axioms identityCoreCanonicalBufferedLossOnePartition
#print axioms identityCoreCanonicalBufferedLossOnePartition_branching
#print axioms identityCoreCanonicalBufferedLossOnePartition_branchingLoss
#print axioms
  exactPartitionStickyCover_identityCoreCanonicalBufferedLossOnePartition

end
end Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
