import Family8Grounding.Family8StickyShadingAwareCanonicalLogSelectedDatumV1
import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

/-!
# Same-object shading-aware selected hierarchy over a normalized long core

The weighted selector is run on the actual source shading of the canonical
buffered global cover.  Its literal partition supplies the selected lower
cover, and an identity cover of the selected coarse family supplies the upper
scale-one cover.  Every object below is definitionally tied to that one
shading-aware choice.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareCanonicalLogSelectedDatumV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The actual active shading mass on the canonical buffered global cover. -/
noncomputable def coreShadingAwareActiveShadingMass
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon ≤ 1 / 2) : ENNReal :=
  shadingMassOn D.shading
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf).activeFine

/-- The canonical buffered global cover has nonempty active fine set whenever
the source refinement is nonempty. -/
theorem coreShadingAwareGlobalCover_activeFine_nonempty
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

/-- The literal shading-aware logarithmic partition on the canonical global
cover. -/
def coreShadingAwareLogPartition
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :=
  shadingAwareLogPartition
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    ((Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
    (coreShadingAwareGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)
    (by
      simpa only [coreShadingAwareActiveShadingMass] using hmass)

/-- The source actual datum retagged by exactly the shading-aware selected
fine family. -/
def coreShadingAwareSelectedActualDatum
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    ActualTubeDatum delta index :=
  shadingAwareSelectedActualDatum D
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    (coreShadingAwareGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)
    (by
      simpa only [coreShadingAwareActiveShadingMass] using hmass)

/-- Forgetting the two branching bounds gives the literal selected lower
cover on the same partition. -/
def coreShadingAwareSelectedStickyCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    StickyScaleCover
      (coreShadingAwareSelectedActualDatum
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).family
      (canonicalBufferedRadius W) :=
  exactPartitionStickyCover
    (coreShadingAwareLogPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)

/-- The selected hierarchy's literal upper cover at radius one. -/
def coreShadingAwareSelectedUpperIdentityCover
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    let S1 := coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
    StickyScaleCover (S1.coarse.restrictTo S1.activeCoarse) 1 := by
  let S1 := coreShadingAwareSelectedStickyCover
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  exact identityRadiusScaleCover
    (S1.coarse.restrictTo S1.activeCoarse) 1
    (canonicalBufferedRadius_le_one
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)

@[simp] theorem coreShadingAwareSelectedStickyCover_activeFine
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).activeFine =
      (coreShadingAwareLogPartition
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).fineIndices :=
  rfl

@[simp] theorem coreShadingAwareSelectedStickyCover_activeCoarse
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      D hD C Sseq P W hepsilonHalf ≠ 0) :
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).activeCoarse =
      (coreShadingAwareLogPartition
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass).coarseIndices :=
  rfl

#print axioms coreShadingAwareActiveShadingMass
#print axioms coreShadingAwareGlobalCover_activeFine_nonempty
#print axioms coreShadingAwareLogPartition
#print axioms coreShadingAwareSelectedActualDatum
#print axioms coreShadingAwareSelectedStickyCover
#print axioms coreShadingAwareSelectedUpperIdentityCover
#print axioms coreShadingAwareSelectedStickyCover_activeFine
#print axioms coreShadingAwareSelectedStickyCover_activeCoarse

end
end Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
