import Family8Grounding.Family8NormalizedLongCoreTauActiveSameCoarseCoverEqV1
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2

/-!
# Canonical normalized-LongCore restricted/global parent-card identity

Active-fine restriction reindexes the active buffered parents by a literal
`Fin` type.  The underlying tau-active cover has exactly the interval
cover's active parents, and coherence identifies those parents with the
canonical global cover.  Consequently the restricted cover's active-coarse
cardinality is exactly the global Equation (66) third count.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1

open LeanEval.Analysis.WangZahlKakeya
open Family8KatzTaoFrostmanPropertiesV1
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveSameCoarseCoverEqV1
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseCoverV1.StickyScaleCover

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- The active-coarse count of the active-fine-restricted canonical
tau-to-buffered cover is the literal active-coarse count of the canonical
global delta-to-buffered cover. -/
@[simp]
theorem canonicalBufferedTauActiveRestricted_activeCoarse_card_eq_global
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness
      D.family C N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    let U := canonicalBufferedTauActiveCover
      D hD C S W hepsilon hepsilonHalf
    (activeFineRestrictedScaleCover U).activeCoarse.card =
      (canonicalBufferedGlobalCover W hD.delta_pos
        hepsilon hepsilonHalf).activeCoarse.card := by
  dsimp only
  let U := canonicalBufferedTauActiveCover
    D hD C S W hepsilon hepsilonHalf
  let I := canonicalBufferedIntervalCover W hD.delta_pos
    hepsilon hepsilonHalf
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hepsilon hepsilonHalf
  have hU : U = activeFineSameCoarseCover I := by
    simpa only [U, I] using
      canonicalBufferedTauActiveCover_eq_activeFineSameCoarseCover
        D hD C S W hepsilon hepsilonHalf
  have hUG : U.activeCoarse.card = G.activeCoarse.card := by
    rw [hU, activeFineSameCoarseCover_activeCoarse]
    rfl
  calc
    (activeFineRestrictedScaleCover U).activeCoarse.card =
        U.activeCoarse.card := by
      change (Finset.univ : Finset (Fin U.activeCoarse.card)).card =
        U.activeCoarse.card
      simp only [Finset.card_univ, Fintype.card_fin]
    _ = G.activeCoarse.card := hUG

#print axioms
  canonicalBufferedTauActiveRestricted_activeCoarse_card_eq_global

end
end Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1
