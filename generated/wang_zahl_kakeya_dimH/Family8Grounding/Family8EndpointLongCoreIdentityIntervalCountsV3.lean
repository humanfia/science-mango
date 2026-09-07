import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Mathlib.Tactic

/-!
# Endpoint identity-interval cardinalities, V3

For the full-refinement datum, every radius of the identity coherent cover
has exactly one parent per source index.  The canonical tau-to-buffered cover
and its active-fine reindexing therefore both retain the original index
cardinality.  V1 and V2 are failed namespace/linter drafts and are not
imported.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8EndpointLongCoreIdentityIntervalCountsV3

open Submission.Kakeya.Uniformity
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The literal endpoint tau-to-buffered cover has one coarse coordinate for
each original source index. -/
theorem endpointLongCore_tauActiveCover_coarseCard_eq_indexCard
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    (canonicalBufferedTauActiveCover (fullRefinementDatum D)
      (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) W
      P.epsilon_pos.le hepsilonHalf).coarseCard = Fintype.card index := by
  rfl

/-- The fully active reindexing keeps the same endpoint coarse cardinality. -/
theorem endpointLongCore_activeFineRestricted_coarseCard_eq_indexCard
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    let U0 := canonicalBufferedTauActiveCover (fullRefinementDatum D)
      (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) W
      P.epsilon_pos.le hepsilonHalf
    (activeFineRestrictedScaleCover U0).coarseCard = Fintype.card index := by
  dsimp only [activeFineRestrictedScaleCover,
    canonicalBufferedTauActiveCover, canonicalBufferedIntervalCover,
    CoherentStickyMultiscaleCover.intervalScaleCover,
    identityRadiusCoherentCover, identityRadiusScaleCover]
  rw [Finset.card_map, fullRefinementDatum_refined, Finset.card_univ]

#print axioms endpointLongCore_tauActiveCover_coarseCard_eq_indexCard
#print axioms endpointLongCore_activeFineRestricted_coarseCard_eq_indexCard

end
end Family8EndpointLongCoreIdentityIntervalCountsV3
