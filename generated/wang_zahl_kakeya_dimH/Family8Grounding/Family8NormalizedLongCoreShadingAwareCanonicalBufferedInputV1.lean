import Family8Grounding.Family8NormalizedLongCoreShadingAwareCanonicalSelectedFrostmanV1
import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedInputV1
import Mathlib.Tactic

/-!
# Canonical buffered Equation (45) input on the shading-aware hierarchy

This packages the literal `S1/U1/P1/A1/W1` chain.  Its selected Frostman field
and exact-assembly nonzero mass are both generated upstream, so the only new
geometric input is the genuine half-radius inequality.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedLongCoreShadingAwareCanonicalBufferedInputV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreShadingAwareCanonicalConflictChoiceV1
open Family8NormalizedLongCoreShadingAwareCanonicalSelectedFrostmanV1
open Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
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
set_option maxHeartbeats 3400000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem coreShadingAware_two_mul_canonicalBufferedRadius_le_one
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

/-- Literal buffered Eq. (45) input on the fixed shading-aware hierarchy. -/
noncomputable def coreShadingAwareCanonicalBufferedInput
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
      D hD C Sseq P W hepsilonHalf ≠ 0)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹) :=
  canonicalEq45BufferedInput
    (coreShadingAwareSelectedStickyCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedUpperIdentityCover
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyPartition
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareSelectedGreedyExactAssembly
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass
      ).refinement.shading
    (canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le)
    hrhoHalf
    (coreShadingAware_two_mul_canonicalBufferedRadius_le_one
      D hD C Sseq P W hrhoHalf)
    (coreShadingAwareCanonicalSelectedFrostmanConstant
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareCanonicalSelectedFrostmanConstant_ne_top
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass)
    (coreShadingAwareCanonicalSelectedFrostman
      D hD C Sseq P W sourceA hsourceA hepsilonHalf hfine hmass hrhoHalf)

#print axioms coreShadingAware_two_mul_canonicalBufferedRadius_le_one
#print axioms coreShadingAwareCanonicalBufferedInput

end
end Family8NormalizedLongCoreShadingAwareCanonicalBufferedInputV1
