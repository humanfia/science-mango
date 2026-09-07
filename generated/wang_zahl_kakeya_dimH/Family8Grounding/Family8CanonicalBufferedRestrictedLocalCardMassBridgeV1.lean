import Family8Grounding.Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import FamilyStickyGrounding.FamilyStickyScaleChainLocalCardAutomaticBoundsV2
import Mathlib.Tactic

/-!
# Canonical buffered restricted local-card mass bridge

This file contains only the finite-cardinality and radius-squared transport
needed by the canonical buffered cover.  It assumes the literal adjacent
active-fine cardinality bound and does not introduce a Katz--Tao certificate
or any global power estimate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8CanonicalBufferedRestrictedLocalCardMassBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N n : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The adjacent active-fine count bounds the active parents of the actual
active-fine-restricted canonical buffered cover. -/
theorem canonicalBufferedTauActiveRestricted_activeCoarse_card_le_of_adjacentActiveFineCard
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hlocal : adjacentIntervalActiveFineCard C S W.m <= n) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    U.activeCoarse.card <= n := by
  dsimp only
  let I := canonicalBufferedIntervalCover W hD.delta_pos
    hepsilon hepsilonHalf
  have hparent : I.activeCoarse.card <= I.activeFine.card :=
    FamilyStickyScaleChainActualStrictLossWithConstantV1.StickyScaleCover.activeCoarse_card_le_activeFine_card
      I
  change
    (canonicalBufferedGlobalCover W hD.delta_pos
      hepsilon hepsilonHalf).activeCoarse.card <=
      adjacentIntervalActiveFineCard C S W.m at hparent
  rw [canonicalBufferedTauActiveRestricted_activeCoarse_card_eq_global
    D hD C S W hepsilon hepsilonHalf]
  exact hparent.trans hlocal

/-- Multiplying the preceding parent-card bound by a buffered radius squared
at most one gives the exact normalized mass bound used downstream. -/
theorem canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_natCast_of_adjacentActiveFineCard
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hlocal : adjacentIntervalActiveFineCard C S W.m <= n)
    (hrho : canonicalBufferedRadius W <= 1) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <= (n : ENNReal) := by
  dsimp only
  let U0 := canonicalBufferedTauActiveCover
    D hD C S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  have hcard : U.activeCoarse.card <= n := by
    dsimp only [U, U0]
    exact
      canonicalBufferedTauActiveRestricted_activeCoarse_card_le_of_adjacentActiveFineCard
        D hD C S W hepsilon hepsilonHalf hlocal
  simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
    ENNReal.coe_natCast, ENNReal.coe_pow]
  calc
    (U.activeCoarse.card : ENNReal) *
        (canonicalBufferedRadius W : ENNReal) ^ 2 <=
      (n : ENNReal) * (1 : ENNReal) ^ 2 := by
        have hcardE : (U.activeCoarse.card : ENNReal) <= (n : ENNReal) := by
          exact_mod_cast hcard
        have hrhoE : (canonicalBufferedRadius W : ENNReal) <= 1 := by
          exact_mod_cast hrho
        have hrhoSq : (canonicalBufferedRadius W : ENNReal) ^ 2 <=
            (1 : ENNReal) ^ 2 := pow_le_pow_left' hrhoE 2
        exact mul_le_mul hcardE hrhoSq bot_le bot_le
    _ = (n : ENNReal) := by simp

#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarse_card_le_of_adjacentActiveFineCard
#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_natCast_of_adjacentActiveFineCard

end
end Family8CanonicalBufferedRestrictedLocalCardMassBridgeV1
