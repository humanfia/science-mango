import Family8Grounding.Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5
import Family8Grounding.Family8DoubledParentConflictWeightedRetentionV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8PaperConflictOwnerGlobalActiveOwnerDoubledParentDegreeV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open Family8PaperConflictOwnerParentFrameFiniteCodeV8
open Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5

attribute [local instance]
  Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5.instFintypeScaleCoverActiveOwner
  Family8PaperConflictOwnerGlobalActiveOwnerStickyScaleCoverV5.instDecidableEqScaleCoverActiveOwner

noncomputable section

/-!
# The honest coarse-card degree bound for the canonical owner cover

The parent-frame construction currently controls the *number* of global
coarse labels, but it proves neither separation of their doubled carriers nor
a bounded multiplicity for a fine tube among those doubled carriers.  Thus the
strongest unconditional degree estimate available for this concrete cover is
the total-coarse-card estimate below.  Its explicit bound is the genuine
parent-frame catalogue bound; it is intentionally not advertised as a
scale-independent loss.
-/

/-- Any upper bound for the total number of coarse labels is also an upper
bound for every closed doubled-parent conflict neighbourhood. -/
theorem closedDoubledParentConflictDegreeBound_of_coarseCard_le
    {delta radius : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    (T : StickyScaleCover fine radius) (K : Nat)
    (hcoarse : T.coarseCard ≤ K) :
    ClosedDoubledParentConflictDegreeBound T (K : ENNReal) := by
  intro k hk neighbours hneighbours
  have hsubset : neighbours ⊆ T.activeCoarse := by
    intro l hl
    exact ((hneighbours l).mp hl).1
  have hactive : neighbours.card ≤ T.activeCoarse.card :=
    Finset.card_le_card hsubset
  have huniv : T.activeCoarse.card ≤ T.coarseCard := by
    simpa using (Finset.card_le_univ T.activeCoarse)
  exact_mod_cast hactive.trans (huniv.trans hcoarse)

/-- The canonical deduplicated active-owner cover carries a completely
explicit doubled-parent degree bound.  The factor
`parentFrameCodeCount rho` comes from the honest finite parent-frame code;
the remaining `S.coarseCard` reflects the absence of cross-parent doubled
carrier exclusion in the current geometric construction. -/
theorem exists_activeOwner_stickyScaleCover_with_doubledParentDegree
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ T : StickyScaleCover (activeOwnerFine C S) (5 * rho),
      T.coarseCard ≤ S.coarseCard * parentFrameCodeCount rho ∧
      ClosedDoubledParentConflictDegreeBound T
        ((S.coarseCard * parentFrameCodeCount rho : Nat) : ENNReal) := by
  obtain ⟨T, hT⟩ := exists_activeOwner_stickyScaleCover C S hdeltaSmall
    hdeltaRho hrhoPos hrhoOne
  exact ⟨T, hT,
    closedDoubledParentConflictDegreeBound_of_coarseCard_le T
      (S.coarseCard * parentFrameCodeCount rho) hT⟩

#print axioms closedDoubledParentConflictDegreeBound_of_coarseCard_le
#print axioms exists_activeOwner_stickyScaleCover_with_doubledParentDegree

end
end Family8PaperConflictOwnerGlobalActiveOwnerDoubledParentDegreeV3
