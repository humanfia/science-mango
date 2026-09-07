import Family8Grounding.Family8FullRefinementShadingAwareSelectedGreedyTripleV7
import Family8Grounding.Family8NormalizedLongCoreFirstOuterParentTransportV2
import Family8Grounding.Family8ParentAggregatedAverageMultiplicityMonotonicityV2

/-!
# Regrouped long-core source triple, V3

This is a low-memory composition of the genuine source-to-`tau` Katz--Tao
parent transport with the canonical shading-aware selector/greedy assembly.
The intermediate parent average is at most the original source average, so
all finite selector, branching, and assembly losses may honestly be grouped
with the first factor.  V1--V2 are namespace drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreShadingAwareRegroupedTripleV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalFullGreedyExactAssemblyChoiceV3
open Family8FullRefinementActualDatumV1
open Family8FullRefinementShadingAwareSelectedGreedyTripleV7
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreShadingAwareGreedyAssemblyV1
open Family8NormalizedLongCoreShadingAwareSelectedHierarchyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- The source average is bounded by the genuine first Katz--Tao cap times
the complete canonical shading-aware selector/branching/assembly product.
This is the exact algebraic grouping needed before inserting a separately
bounded positive `tau`-to-middle average. -/
theorem fullRefinement_averageMultiplicity_le_firstCap_mul_selectedCap_mul_assemblyLoss_mul_refinement
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    {etaKT : Real} (hKT : KatzTaoHypotheses D etaKT)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hfine : (fullRefinementDatum D).family.refinement.refined.Nonempty)
    (hmass : coreShadingAwareActiveShadingMass
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P W hepsilonHalf ≠ 0) :
    let firstCap : ENNReal :=
      Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT))
    let Ppart := coreShadingAwareLogPartition
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P W sourceA hsourceA hepsilonHalf hfine hmass
    let S1 := coreShadingAwareSelectedStickyCover
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P W sourceA hsourceA hepsilonHalf hfine hmass
    let assemblyLoss := canonicalFullGreedyAssemblyLoss S1
    let A := coreShadingAwareSelectedGreedyExactAssembly
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S P W sourceA hsourceA hepsilonHalf hfine hmass
    D.shading.averageMultiplicity <=
      firstCap *
        ((((2 * (Nat.log 2 (Fintype.card index) + 1)) *
            (Ppart.branchingLoss * Ppart.branching) : Nat) : ENNReal) *
          ((assemblyLoss : ENNReal) * A.refinement.shading.averageMultiplicity)) := by
  dsimp only
  let E := fullRefinementDatum D
  let S0 := sourceTauCover E C S W.m
  let firstCap : ENNReal :=
    Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
      delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT))
  let Ppart := coreShadingAwareLogPartition
    E (fullRefinementDatum_isAdmissible hD)
      C S P W sourceA hsourceA hepsilonHalf hfine hmass
  let S1 := coreShadingAwareSelectedStickyCover
    E (fullRefinementDatum_isAdmissible hD)
      C S P W sourceA hsourceA hepsilonHalf hfine hmass
  let assemblyLoss := canonicalFullGreedyAssemblyLoss S1
  let A := coreShadingAwareSelectedGreedyExactAssembly
    E (fullRefinementDatum_isAdmissible hD)
      C S P W sourceA hsourceA hepsilonHalf hfine hmass
  have hfirst : D.shading.averageMultiplicity <=
      firstCap * (parentAggregatedShading S0 E.shading).averageMultiplicity := by
    simpa only [firstCap, S0, E] using
      (Family8NormalizedLongCoreFirstOuterParentTransportV2.NormalizedLongIntervalCoreWitness.fullRefinement_averageMultiplicity_le_firstCap_mul_sourceTauParent
        D hD C S P W hKT)
  have htau : (parentAggregatedShading S0 E.shading).averageMultiplicity <=
      D.shading.averageMultiplicity := by
    calc
      (parentAggregatedShading S0 E.shading).averageMultiplicity <=
          (activeFineShading S0 E.shading).averageMultiplicity :=
        Family8ParentAggregatedAverageMultiplicityMonotonicityV2.StickyScaleCover.parentAggregatedShading_averageMultiplicity_le_activeFineShading
          S0 E.shading
      _ = D.shading.averageMultiplicity := by
        simpa only [S0, E] using
          (fullRefinement_sourceTau_activeFine_averageMultiplicity D C S W.m)
  have hselected : D.shading.averageMultiplicity <=
      (((2 * (Nat.log 2 (Fintype.card index) + 1)) *
          (Ppart.branchingLoss * Ppart.branching) : Nat) : ENNReal) *
        ((assemblyLoss : ENNReal) * A.refinement.shading.averageMultiplicity) := by
    simpa only [Ppart, S1, assemblyLoss, A, E] using
      (fullRefinement_averageMultiplicity_le_selectedCap_mul_assemblyLoss_mul_refinement
        D hD C S P W sourceA hsourceA hepsilonHalf hfine hmass)
  exact hfirst.trans <|
    (mul_le_mul' le_rfl htau).trans (mul_le_mul' le_rfl hselected)

#print axioms
  fullRefinement_averageMultiplicity_le_firstCap_mul_selectedCap_mul_assemblyLoss_mul_refinement

end
end Family8NormalizedLongCoreShadingAwareRegroupedTripleV3
