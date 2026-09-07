import Family8Grounding.Family8NormalizedLongCoreDensityAwareCanonicalSelectedFrostmanV4
import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedInputV1
import Mathlib.Tactic

/-!
# Canonical buffered Equation (45) input on the same long-core hierarchy, V2

This module packages the already frozen `D1/S1/U1/P1/A1` objects into the
buffered input `I`.  The selected-source Frostman field is produced by the
canonical theorem, under the explicit and honest premise that the fixed
exact-assembly refinement has nonzero shading mass.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreDensityAwareCanonicalBufferedInputV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreDensityAwareCanonicalConflictChoiceV1
open Family8NormalizedLongCoreDensityAwareCanonicalSelectedFrostmanV4
open Family8NormalizedLongCoreDensityAwareGreedyAssemblyV2
open Family8NormalizedLongCoreDensityAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedInputV1
open Family8ParameterLadderV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The half-radius hypothesis is exactly the doubled-radius compatibility
needed for the identity upper cover at scale one. -/
theorem coreDensityAware_two_mul_canonicalBufferedRadius_le_one
    (D : ActualTubeDatum delta index) (_hD : D.IsAdmissible)
    (_C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family _C P.N P.epsilon P.eta Sseq)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹) :
    2 * canonicalBufferedRadius W ≤ (1 : NNReal) := by
  calc
    2 * canonicalBufferedRadius W ≤ 2 * (2 : NNReal)⁻¹ :=
      mul_le_mul' le_rfl hrhoHalf
    _ = 1 := by norm_num

/-- The literal buffered input on `S1 -> U1`, with the same greedy partition,
assembly shading, conflict loss, and conflict selection frozen upstream. -/
noncomputable def coreDensityAwareCanonicalBufferedInput
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      D.family C P.N P.epsilon P.eta Sseq)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hfine : D.family.refinement.refined.Nonempty)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹)
    (hrefinementMass :
      (coreDensityAwareSelectedGreedyExactAssembly
        D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading.shadingMass ≠ 0) :=
  canonicalEq45BufferedInput
    (coreDensityAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine).refinement.shading
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    hrhoHalf
    (coreDensityAware_two_mul_canonicalBufferedRadius_le_one
      D hD C Sseq P W hrhoHalf)
    (coreDensityAwareCanonicalSelectedFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareCanonicalSelectedFrostmanConstant_ne_top
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine)
    (coreDensityAwareCanonicalSelectedFrostman
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine
      hrhoHalf hrefinementMass)

#print axioms coreDensityAware_two_mul_canonicalBufferedRadius_le_one
#print axioms coreDensityAwareCanonicalBufferedInput

end
end Family8NormalizedLongCoreDensityAwareCanonicalBufferedInputV2
