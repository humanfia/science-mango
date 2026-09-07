import Family8Grounding.Family8CanonicalBufferedRestrictedLocalCardMassBridgeV1
import FamilyStickyGrounding.FamilyStickyScaleChainLocalCardBudgetInvariantV2
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Non-large local-card producer for the selected split-eta X power

This file isolates the shortest non-circular route to the normalized parent
cardinality bound.  At the selected interval, a `NonLargeLocalCardBudget`
bounds the active family at `tau`.  Parent surjectivity from `tau` to the
canonical buffered radius bounds the buffered parent count by the same
fixed natural number `n`; the radius is at most one, so

`activeCoarseCardScaleMass <= n`.

One finite-constant small-delta threshold then absorbs `n` into the requested
negative power.  No Katz--Tao certificate, Frostman cancellation, or
all-scale hypothesis is used.  The non-large certificate is kept as an
explicit premise because `NormalizedLongIntervalCoreWitness` currently
forgets it.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000

open scoped ENNReal NNReal

namespace Family8SelectedTrueSplitEtaXPowerShortestProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8CanonicalBufferedRestrictedLocalCardMassBridgeV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {depth N n : Nat} {epsilon gapEpsilon cardEta : Real}
  {eta : Nat -> Real}

/-- On the one-interval endpoint sequence, failure of the all-large branch
recovers the non-large certificate at any chosen witness index. -/
theorem not_isLarge_at_of_not_allStepsLarge_finOne
    (S : FiniteScaleSequence delta 1) (m : Fin 1)
    (hNotAll : Not (S.AllStepsLarge gapEpsilon)) :
    Not (S.IsLarge gapEpsilon m) := by
  intro hm
  apply hNotAll
  intro k
  simpa only [show k = m from Subsingleton.elim _ _] using hm

/-- Parent surjectivity transports the local cardinality budget at the
selected non-large lower endpoint to the canonical buffered global cover. -/
theorem canonicalBufferedGlobalCover_activeCoarse_card_le_of_nonLargeLocalCardBudget
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2)
    (hNonLarge : Not (S.IsLarge gapEpsilon W.m))
    (hbudget : NonLargeLocalCardBudget C S gapEpsilon n) :
    (canonicalBufferedGlobalCover W hdelta
      hepsilon hepsilonHalf).activeCoarse.card <= n := by
  have hlocal : adjacentIntervalActiveFineCard C S W.m <= n :=
    hbudget W.m hNonLarge
  let I := canonicalBufferedIntervalCover W hdelta
    hepsilon hepsilonHalf
  have hparent : I.activeCoarse.card <= I.activeFine.card :=
    StickyScaleCover.activeCoarse_card_le_activeFine_card I
  change
    (canonicalBufferedGlobalCover W hdelta
      hepsilon hepsilonHalf).activeCoarse.card <=
      adjacentIntervalActiveFineCard C S W.m at hparent
  exact hparent.trans hlocal

/-- Since the canonical buffered radius is at most one, the fixed parent
cardinality bound also bounds the normalized mass `#parents * rho^2`. -/
theorem canonicalBufferedGlobalCover_activeCoarseCardScaleMass_le_natCast_of_nonLargeLocalCardBudget
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta S)
    (hdelta : 0 < delta) (hepsilon : 0 <= epsilon)
    (hepsilonHalf : epsilon <= 1 / 2)
    (hNonLarge : Not (S.IsLarge gapEpsilon W.m))
    (hbudget : NonLargeLocalCardBudget C S gapEpsilon n) :
    (activeCoarseCardScaleMass
        (canonicalBufferedGlobalCover W hdelta
          hepsilon hepsilonHalf) : ENNReal) <= (n : ENNReal) := by
  have hcard :=
    canonicalBufferedGlobalCover_activeCoarse_card_le_of_nonLargeLocalCardBudget
      C S W hdelta hepsilon hepsilonHalf hNonLarge hbudget
  have hrho : canonicalBufferedRadius W <= 1 :=
    canonicalBufferedRadius_le_one W hdelta hepsilon hepsilonHalf
  simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
    ENNReal.coe_natCast, ENNReal.coe_pow]
  calc
    ((canonicalBufferedGlobalCover W hdelta
          hepsilon hepsilonHalf).activeCoarse.card : ENNReal) *
        (canonicalBufferedRadius W : ENNReal) ^ 2 <=
      (n : ENNReal) * (1 : ENNReal) ^ 2 := by
        gcongr
        exact_mod_cast hrho
    _ = (n : ENNReal) := by simp

/-- The same bound on the actual consumer object: the active-fine-restricted
tau-to-buffered cover has exactly the global buffered parent count. -/
theorem canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_natCast_of_nonLargeLocalCardBudget
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hNonLarge : Not (S.IsLarge gapEpsilon W.m))
    (hbudget : NonLargeLocalCardBudget C S gapEpsilon n) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <= (n : ENNReal) := by
  exact
    canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_natCast_of_adjacentActiveFineCard
      D hD C S W hepsilon hepsilonHalf
      (hbudget W.m hNonLarge)
      (canonicalBufferedRadius_le_one W hD.delta_pos
        hepsilon hepsilonHalf)

/-- Weakest quantitative producer on the actual consumer object.  It needs
only the selected-stage local-card bound and a caller-supplied power envelope
for that natural number.  In particular, it does not prescribe how `n` is
chosen or force its absorption threshold into a uniform top-level `delta0`. -/
theorem canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_adjacentActiveFineCard
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hlocal : adjacentIntervalActiveFineCard C S W.m <= n)
    (hNPower : (n : ENNReal) <=
      (delta : ENNReal) ^ (-cardEta)) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-cardEta) := by
  exact
    (canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_natCast_of_adjacentActiveFineCard
      D hD C S W hepsilon hepsilonHalf hlocal
      (canonicalBufferedRadius_le_one W hD.delta_pos
        hepsilon hepsilonHalf)).trans hNPower

/-- Invariant-level wrapper for the preceding selected-stage theorem.  The
non-large certificate is used only to query the independent local-card
budget at `W.m`. -/
theorem canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_nonLargeLocalCardBudget_and_natCastPower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hNonLarge : Not (S.IsLarge gapEpsilon W.m))
    (hbudget : NonLargeLocalCardBudget C S gapEpsilon n)
    (hNPower : (n : ENNReal) <=
      (delta : ENNReal) ^ (-cardEta)) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-cardEta) := by
  exact
    canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_adjacentActiveFineCard
      D hD C S W hepsilon hepsilonHalf
      (hbudget W.m hNonLarge) hNPower

/-- The complete local-card X producer.  Its only quantitative inputs are
the selected non-large certificate, its fixed local-card budget, positivity
of the exponent, and the explicit finite-constant threshold. -/
theorem canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_nonLargeLocalCardBudget
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    (hNonLarge : Not (S.IsLarge gapEpsilon W.m))
    (hbudget : NonLargeLocalCardBudget C S gapEpsilon n)
    (hcardEta : 0 < cardEta)
    (hsmall : delta <=
      finiteConstantSmallDeltaThreshold (n : ENNReal) cardEta) :
    let U0 := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (activeCoarseCardScaleMass U : ENNReal) <=
      (delta : ENNReal) ^ (-cardEta) := by
  exact
    canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_nonLargeLocalCardBudget_and_natCastPower
      D hD C S W hepsilon hepsilonHalf hNonLarge hbudget
      (finiteConstant_le_delta_negativePower
        (ENNReal.natCast_ne_top n) hcardEta hD.delta_pos hsmall)

#print axioms
  not_isLarge_at_of_not_allStepsLarge_finOne
#print axioms
  canonicalBufferedGlobalCover_activeCoarse_card_le_of_nonLargeLocalCardBudget
#print axioms
  canonicalBufferedGlobalCover_activeCoarseCardScaleMass_le_natCast_of_nonLargeLocalCardBudget
#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_natCast_of_nonLargeLocalCardBudget
#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_adjacentActiveFineCard
#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_nonLargeLocalCardBudget_and_natCastPower
#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_nonLargeLocalCardBudget

end
end Family8SelectedTrueSplitEtaXPowerShortestProducerV1
