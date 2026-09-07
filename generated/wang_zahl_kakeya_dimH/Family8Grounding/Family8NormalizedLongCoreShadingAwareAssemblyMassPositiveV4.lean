import Family8Grounding.Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Family8Grounding.Family8FullGreedyCanonicalMassDensityAssemblyV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1

/-!
# Positive mass in the shading-aware exact assembly, V4

Actual shading retention from the weighted logarithmic selector is transported
through the literal active-fine restriction, parent aggregation, and the full
greedy exact assembly.  No nonzero-mass callback is left downstream.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareAssemblyMassPositiveV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8FullGreedyCanonicalMassDensityAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The fixed shading-aware exact assembly refinement has nonzero mass. -/
theorem coreShadingAwareSelectedGreedyExactAssembly_refinementMass_ne_zero
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
    (coreShadingAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
      ).refinement.shading.shadingMass ≠ 0 := by
  let Ppart := coreShadingAwareLogPartition
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  have hretain := shadingAwareLogPartition_shadingMass_withinFactor
    (canonicalBufferedGlobalCover
      W hD.delta_pos P.epsilon_pos.le hepsilonHalf)
    D.shading (sourceA : ENNReal)
    (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    ((Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
    (coreShadingAwareGlobalCover_activeFine_nonempty
      D hD C Sseq P W hepsilonHalf hfine)
    (by simpa only [coreShadingAwareActiveShadingMass] using hmass)
  have hselected : shadingMassOn D.shading Ppart.fineIndices ≠ 0 := by
    change WithinFactor (2 * (Nat.log 2 (Fintype.card index) + 1))
      (coreShadingAwareActiveShadingMass
        D hD C Sseq P W hepsilonHalf)
      (shadingMassOn D.shading Ppart.fineIndices) at hretain
    intro hzero
    unfold WithinFactor at hretain
    rw [hzero, nsmul_zero] at hretain
    exact hmass (bot_unique hretain)
  let S1 := coreShadingAwareSelectedStickyCover
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  let D1 := coreShadingAwareSelectedActualDatum
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  have hactive :
      (IndexedShadingRefinement.restrictTo D1.shading S1.activeFine
        ).shading.shadingMass ≠ 0 := by
    rw [shadingMass_restrictTo_eq_sum]
    change (∑ i ∈ Ppart.fineIndices, volume (D.shading.carrier i)) ≠ 0
    simpa only [shadingMassOn] using hselected
  let Y := coreShadingAwareSelectedParentShading
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  have hY : Y.shadingMass ≠ 0 := by
    dsimp only [Y, coreShadingAwareSelectedParentShading]
    exact parentAggregatedShading_shadingMass_ne_zero_of_restrictTo
      S1 D1.shading hactive
  let G := coreShadingAwareSelectedGreedyPartition
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  let A := coreShadingAwareSelectedGreedyExactAssembly
    D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  have hsource :
      (IndexedShadingRefinement.restrictTo Y
        (convexFactorization S1.activeCoarseFamily G).index.fine
        ).shading.shadingMass ≠ 0 := by
    rw [fullGreedy_sourceActive_mass_eq G Y]
    exact hY
  change A.refinement.shading.shadingMass ≠ 0
  exact refinement_shadingMass_ne_zero A hsource

#print axioms
  coreShadingAwareSelectedGreedyExactAssembly_refinementMass_ne_zero

end
end Family8NormalizedLongCoreShadingAwareAssemblyMassPositiveV4
