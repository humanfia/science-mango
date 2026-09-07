import Family8Grounding.Family8LocalCardRetainedNormalizedLongCoreWitnessV1
import Family8Grounding.Family8SelectedTrueSplitEtaXPowerShortestProducerV1

/-!
# Retained LongCore to the selected-stage X power

This is the thin public adapter from a pointwise local-card-retained
LongCore to the weakest same-object X-power theorem.  Non-largeness and the
uniform local-card invariant are construction details of the retained
witness; the consumer sees only that witness and a power envelope for its
stored natural bound.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

namespace Family8LocalCardRetainedSelectedTrueSplitEtaXPowerAdapterV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8LocalCardRetainedNormalizedLongCoreWitnessV1
open Family8LocalCardRetainedNormalizedLongCoreWitnessV1.LocalCardRetainedNormalizedLongCoreWitness
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon cardEta : Real}
  {eta : Nat -> Real}

/-- The retained witness discharges the exact selected-stage local-card
premise of the weakest X-power producer.  The cover `U` is constructed from
`R.core` in both the statement and the invoked theorem, so no witness or
cover is reselected. -/
theorem canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_retained
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (R : LocalCardRetainedNormalizedLongCoreWitness
      D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hNPower : (R.n : ENNReal) <=
      (delta : ENNReal) ^ (-cardEta)) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S R.core hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-cardEta) := by
  exact
    Family8SelectedTrueSplitEtaXPowerShortestProducerV1.canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_adjacentActiveFineCard
      D hD C S R.core hepsilon hepsilonHalf R.local_card_le hNPower

#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_retained

end
end Family8LocalCardRetainedSelectedTrueSplitEtaXPowerAdapterV1
