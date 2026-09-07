import Family8Grounding.Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8ExactPartitionBalancedSourceFactorFloorV1
import Family8Grounding.Family8ExactAssemblySourceAverageRetentionV1
import Family8Grounding.Family8SharpKatzTaoOrGreedyHighConcentrationV1
import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import FamilyStickyGrounding.FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
import Mathlib.Tactic

/-!
# Source-to-refinement triple on the shading-aware long-core hierarchy, V7

The selector, selected parent partition, and full greedy exact assembly stay
on one object, ending at the refinement consumed by buffered Eq45/Eq46.
V1--V6 are elaboration drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FullRefinementShadingAwareSelectedGreedyTripleV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CanonicalFullGreedyExactAssemblyChoiceV3
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8ExactAssemblySourceAverageRetentionV1.ExactAssembly
open Family8ExactPartitionBalancedSourceFactorFloorV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyKatzTaoParentAggregatedMultiplicityConsumerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem fullRefinement_averageMultiplicity_le_selectedCap_mul_assemblyLoss_mul_refinement
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : (fullRefinementDatum D).family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C Sseq P W hepsilonHalf ≠ 0) :
    let E := fullRefinementDatum D
    let hE := fullRefinementDatum_isAdmissible hD
    let Ppart := coreShadingAwareLogPartition
      E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
    let S1 := coreShadingAwareSelectedStickyCover
      E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
    let assemblyLoss := canonicalFullGreedyAssemblyLoss S1
    let A := coreShadingAwareSelectedGreedyExactAssembly
      E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
    D.shading.averageMultiplicity <=
      (((2 * (Nat.log 2 (Fintype.card index) + 1)) *
          (Ppart.branchingLoss * Ppart.branching) : Nat) : ENNReal) *
        ((assemblyLoss : ENNReal) * A.refinement.shading.averageMultiplicity) := by
  dsimp only
  let E := fullRefinementDatum D
  let hE := fullRefinementDatum_isAdmissible hD
  let G := canonicalBufferedGlobalCover
    W hD.delta_pos P.epsilon_pos.le hepsilonHalf
  let Ppart := coreShadingAwareLogPartition
    E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  let S1 := coreShadingAwareSelectedStickyCover
    E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  let assemblyLoss := canonicalFullGreedyAssemblyLoss S1
  let A := coreShadingAwareSelectedGreedyExactAssembly
    E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
  let L : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  let M : Nat := Ppart.branchingLoss * Ppart.branching
  have hGfine : G.activeFine = Finset.univ := by
    rw [G.activeFine_eq_refined, fullRefinementDatum_refined]
  have hretain := shadingAwareLogPartition_shadingMass_withinFactor
    G E.shading (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
      ((Sseq.delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le))
      (coreShadingAwareGlobalCover_activeFine_nonempty
        E hE C Sseq P W hepsilonHalf hfine)
      (by simpa only [coreShadingAwareActiveShadingMass] using hmass)
  have hmassRetained : E.shading.shadingMass <=
      (L : ENNReal) *
        (restrictActualTubeDatum E Ppart.fineIndices).shading.shadingMass := by
    change WithinFactor L
      (shadingMassOn E.shading G.activeFine)
      (shadingMassOn E.shading Ppart.fineIndices) at hretain
    unfold WithinFactor at hretain
    rw [hGfine] at hretain
    rw [restrictActualTubeDatum_shadingMass]
    change (∑ i, volume (E.shading.carrier i)) <=
      (L : ENNReal) *
        ∑ i ∈ Ppart.fineIndices, volume (E.shading.carrier i)
    simpa [shadingMassOn, L] using hretain
  have hrestrictionEq :
      (restrictActualTubeDatum E Ppart.fineIndices).shading.averageMultiplicity =
        (activeFineShading S1 E.shading).averageMultiplicity := by
    rfl
  have hselected : E.shading.averageMultiplicity <=
      (L : ENNReal) *
        (activeFineShading S1 E.shading).averageMultiplicity := by
    have hrestricted :=
      source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
        E Ppart.fineIndices (L : ENNReal) hmassRetained
    rwa [hrestrictionEq] at hrestricted
  have hparent : (activeFineShading S1 E.shading).averageMultiplicity <=
      (M : ENNReal) *
        (parentAggregatedShading S1 E.shading).averageMultiplicity := by
    simpa only [nsmul_eq_mul, M, S1, Ppart] using
      (activeFineShading_averageMultiplicity_le_nsmul_parent
        S1 E.shading M
          (activeIndexFiber_card_le_partition_loss_mul_branching Ppart))
  have hassembly :
      (parentAggregatedShading S1 E.shading).averageMultiplicity <=
        (assemblyLoss : ENNReal) * A.refinement.shading.averageMultiplicity := by
    have hretained := restrictTo_source_averageMultiplicity_le_loss_mul_refinement A
    have hfull :
        (greedyParentFactorization S1
          (coreShadingAwareSelectedGreedyPartition
            E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
          ).index.fine = Finset.univ := by
      rfl
    change
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S1 E.shading)
        (greedyParentFactorization S1
          (coreShadingAwareSelectedGreedyPartition
            E hE C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
          ).index.fine).shading.averageMultiplicity <=
        (assemblyLoss : ENNReal) * A.refinement.shading.averageMultiplicity
      at hretained
    rw [hfull, restrictTo_univ_averageMultiplicity] at hretained
    exact hretained
  have hsource : D.shading.averageMultiplicity <=
      (L : ENNReal) * ((M : ENNReal) *
        ((assemblyLoss : ENNReal) * A.refinement.shading.averageMultiplicity)) := by
    rw [← fullRefinementDatum_averageMultiplicity D]
    exact hselected.trans
      (mul_le_mul' le_rfl (hparent.trans (mul_le_mul' le_rfl hassembly)))
  simpa only [Nat.cast_mul, L, M, mul_assoc] using hsource

#print axioms
  fullRefinement_averageMultiplicity_le_selectedCap_mul_assemblyLoss_mul_refinement

end
end Family8FullRefinementShadingAwareSelectedGreedyTripleV7
