import Family8Grounding.Family8FrozenComparableLogLossSourceCardTransferV2
import Family8Grounding.Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3
import Family8Grounding.Family8ParameterLadderV1

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessActiveLogLossV3

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
open Family8FrozenComparableActualAverageMassDensityV1
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8FrozenComparableLogLossSourceCardTransferV2
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-!
# Original-scale absorption for the identified tau-to-buffered active loss

The lower index type of the canonical buffered cover is the active `tau`
parent subtype. Parent surjectivity bounds it by the original fine index
type, so the cross-index source-card theorem absorbs its two literal active
logarithms at the original `delta`, without admissibility of raw parents.

V1 and V2 were namespace/import drafts and are deliberately not imported.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem tauActiveCoarseDatum_indexCard_le_source
    (D : ActualTubeDatum delta index)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S) :
    Fintype.card {k // k ∈
        (tauScaleCover D C S W).activeCoarse} ≤
      Fintype.card index := by
  rw [Fintype.card_coe]
  calc
    (tauScaleCover D C S W).activeCoarse.card ≤
        (tauScaleCover D C S W).activeFine.card :=
      Family8StickyActiveIndexFrozenComparableAssemblyV5.activeCoarse_card_le_activeFine_card
        (tauScaleCover D C S W)
    _ ≤ Fintype.card index := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card
          (Finset.subset_univ (tauScaleCover D C S W).activeFine)

theorem canonicalBuffered_activeFrozenLoss_le_original_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      D.family C P.N P.epsilon P.eta S)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta ≤
      activeFrozenComparableLossAbsorptionThreshold lossEta) :
    let U := canonicalBufferedTauActiveCover
      D hD C S W P.epsilon_pos.le hepsilonHalf
    (frozenComparableLoss {i // i ∈ U.activeFine}
        (Fin U.activeCoarse.card) : ENNReal) ≤
      (delta : ENNReal) ^ (-lossEta) := by
  dsimp only
  exact activeFrozenComparableLoss_le_rpow_of_indexCard_le_source
    D hD
      (canonicalBufferedTauActiveCover
        D hD C S W P.epsilon_pos.le hepsilonHalf)
      (tauActiveCoarseDatum_indexCard_le_source D C S P W)
      hlossEta hdelta

#print axioms tauActiveCoarseDatum_indexCard_le_source
#print axioms canonicalBuffered_activeFrozenLoss_le_original_rpow

end Witness

end
end Family8IdentifiedDividingWitnessActiveLogLossV3
