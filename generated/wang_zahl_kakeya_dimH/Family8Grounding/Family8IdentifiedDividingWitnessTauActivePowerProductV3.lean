import Family8Grounding.Family8IdentifiedDividingWitnessActiveLogLossV3
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessTauActivePowerProductV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8ComparableMultiplicityBucketsV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8IdentifiedDividingWitnessActiveLogLossV3.Witness
open Family8NormalizedCrossingSourceTauShadingV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-!
# Original-scale power loss on the canonical tau-active frozen product

The assembly constructor itself does not require the reindexed tau-parent
datum to be admissible. We apply it directly to the canonical buffered cover
on the active tau-parent subtype, then absorb its literal logarithmic loss
using the original admissible source cardinality. This bypasses the separate
`TauActiveCoarseAdmissibility` seam while retaining one literal assembly and
one surviving final fibre.

V1 and V2 are failed import/namespace drafts and are not imported.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem canonicalBufferedTauActiveCover_restrictedMass_ne_zero
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (tauScaleCover D C S W).activeFine).shading.shadingMass ≠ 0) :
    (IndexedShadingRefinement.restrictTo
      (tauActiveCoarseDatum D C S W).shading
      (canonicalBufferedTauActiveCover
        D hD C S W P.epsilon_pos.le hepsilonHalf).activeFine).shading.shadingMass ≠
        0 := by
  rw [canonicalBufferedTauActiveCover_activeFine,
    restrictTo_univ_shadingMass]
  exact parentAggregatedShading_shadingMass_ne_zero_of_restrictTo
    (tauScaleCover D C S W) D.shading hsourceTau

theorem canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon ≤ 1 / 2) :
    let U := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    (activeFineShading U
      (tauActiveCoarseDatum D C S W).shading).averageMultiplicity =
      (tauActiveCoarseDatum D C S W).shading.averageMultiplicity := by
  dsimp only
  unfold Shading.averageMultiplicity
  rw [Family8AllFrostmanStickyUnionProducerV1.activeFineShading_shadingMass_eq_of_activeFine_eq_univ
      _ _ (canonicalBufferedTauActiveCover_activeFine
        D hD C S W P.epsilon_pos.le hepsilonHalf),
    Family8AllFrostmanStickyUnionProducerV1.activeFineShading_shadedUnion_eq_of_activeFine_eq_univ
      _ _ (canonicalBufferedTauActiveCover_activeFine
        D hD C S W P.epsilon_pos.le hepsilonHalf)]

theorem exists_canonicalBuffered_tauActive_frozenPowerProduct
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (tauScaleCover D C S W).activeFine).shading.shadingMass ≠ 0)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta ≤
      activeFrozenComparableLossAbsorptionThreshold lossEta) :
    let U := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    let hscale : S.tau W.m ≤ canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
    let Y := (tauActiveCoarseDatum D C S W).shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        D hD C S P W hepsilonHalf hsourceTau
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition
          (activeFineRestrictedScaleCover U) hscale
          (activeFineRestrictedShading U Y)
          (activeFineRestrictedSourceMass_ne_zero U Y hsource)).asConvexFactorization
        (activeFineRestrictedShading U Y) 1,
      A.loss = frozenComparableLoss {i // i ∈ U.activeFine}
        (Fin U.activeCoarse.card) ∧
      ∃ k : Fin U.activeCoarse.card,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        Y.averageMultiplicity ≤
          (4 * (delta : ENNReal) ^ (-lossEta)) *
            (A.frozenCoarse.averageMultiplicity *
              (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  obtain ⟨A, hLoss, hAverage, k, hFiberVolume, hProduct⟩ :=
    exists_activeIndex_frozenComparableAssembly
      (canonicalBufferedTauActiveCover
        D hD C S W P.epsilon_pos.le hepsilonHalf)
      (tau_le_canonicalBufferedRadius
        W hD.delta_pos P.epsilon_pos.le)
      (tauActiveCoarseDatum D C S W).shading 1 (by norm_num)
      (canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        D hD C S P W hepsilonHalf hsourceTau)
  have hLossPower :
      (frozenComparableLoss {i // i ∈
          (canonicalBufferedTauActiveCover
            D hD C S W P.epsilon_pos.le hepsilonHalf).activeFine}
          (Fin (canonicalBufferedTauActiveCover
            D hD C S W P.epsilon_pos.le hepsilonHalf).activeCoarse.card) : ENNReal) ≤
        (delta : ENNReal) ^ (-lossEta) :=
    canonicalBuffered_activeFrozenLoss_le_original_rpow
      D hD C S P W hepsilonHalf hlossEta hdelta
  have hAveragePower :
      (tauActiveCoarseDatum D C S W).shading.averageMultiplicity ≤
        (delta : ENNReal) ^ (-lossEta) *
          (actualRefinementShading A).averageMultiplicity := by
    rw [← canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
      D hD C S P W hepsilonHalf]
    exact hAverage.trans (mul_le_mul' hLossPower le_rfl)
  refine ⟨A, hLoss, k, hFiberVolume, ?_⟩
  calc
    (tauActiveCoarseDatum D C S W).shading.averageMultiplicity ≤
        (delta : ENNReal) ^ (-lossEta) *
          (actualRefinementShading A).averageMultiplicity := hAveragePower
    _ ≤ (delta : ENNReal) ^ (-lossEta) *
          (4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity)) :=
      mul_le_mul' le_rfl hProduct
    _ = (4 * (delta : ENNReal) ^ (-lossEta)) *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
      ac_rfl

#print axioms canonicalBufferedTauActiveCover_restrictedMass_ne_zero
#print axioms canonicalBufferedTauActiveCover_activeFine_averageMultiplicity
#print axioms exists_canonicalBuffered_tauActive_frozenPowerProduct

end Witness

end
end Family8IdentifiedDividingWitnessTauActivePowerProductV3
