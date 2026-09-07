import Family8Grounding.Family8StickyDensityAwareCanonicalLogSelectedDatumV2
import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

/-!
# Same-object selected hierarchy over a normalized long core

First freeze the density-aware logarithmic partition of the core's canonical
buffered global cover.  Forgetting only its branching bounds gives the exact
selected lower cover.  An identity-radius cover of that selected coarse
family then supplies a literal upper cover at radius one, with precisely the
dependent type consumed by the Equation (45)/(46) pipeline.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyDensityAwareCanonicalLogPartitionV2
open Family8StickyDensityAwareCanonicalLogSelectedDatumV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The canonical buffered global cover has nonempty active fine set whenever
the source refinement is nonempty. -/
theorem coreCanonicalBufferedGlobalCover_activeFine_nonempty
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeFine.Nonempty := by
  rw [(canonicalBufferedGlobalCover
    W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeFine_eq_refined]
  exact hfine

/-- The canonical density-aware logarithmic partition on the core's actual
global buffered cover. -/
def coreDensityAwareLogPartition
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :=
  densityAwareLogPartition
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    sourceA hsourceA hD.delta_pos
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    ((Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius
        W hD.delta_pos P.epsilon_pos.le))
    (coreCanonicalBufferedGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)

/-- The source actual datum retagged by exactly the fine family of the frozen
canonical partition. -/
def coreDensityAwareSelectedActualDatum
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    ActualTubeDatum delta index :=
  densityAwareSelectedActualDatum D
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    sourceA hsourceA hD.delta_pos
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    (coreCanonicalBufferedGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)

/-- Forgetting the two branching bounds gives the literal selected lower
cover, based on the same selected actual datum. -/
def coreDensityAwareSelectedStickyCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    StickyScaleCover
      (coreDensityAwareSelectedActualDatum
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).family
      (canonicalBufferedRadius W) :=
  exactPartitionStickyCover
    (coreDensityAwareLogPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)

/-- The selected hierarchy's upper step.  Its source is definitionally the
active selected coarse family of the lower cover, exactly as required by the
greedy Equation (45) interface. -/
def coreDensityAwareSelectedUpperIdentityCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    let S1 := coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine
    StickyScaleCover (S1.coarse.restrictTo S1.activeCoarse) 1 := by
  let S1 := coreDensityAwareSelectedStickyCover
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine
  exact identityRadiusScaleCover
    (S1.coarse.restrictTo S1.activeCoarse) 1
    (canonicalBufferedRadius_le_one
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)

@[simp] theorem coreDensityAwareSelectedStickyCover_activeFine
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).activeFine =
      (coreDensityAwareLogPartition
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).fineIndices :=
  rfl

@[simp] theorem coreDensityAwareSelectedStickyCover_activeCoarse
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty) :
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).activeCoarse =
      (coreDensityAwareLogPartition
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).coarseIndices :=
  rfl

#print axioms coreCanonicalBufferedGlobalCover_activeFine_nonempty
#print axioms coreDensityAwareLogPartition
#print axioms coreDensityAwareSelectedActualDatum
#print axioms coreDensityAwareSelectedStickyCover
#print axioms coreDensityAwareSelectedUpperIdentityCover
#print axioms coreDensityAwareSelectedStickyCover_activeFine
#print axioms coreDensityAwareSelectedStickyCover_activeCoarse

end
end Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
