import Family8Grounding.Family8PaperConflictOwnerGlobalCoarseCoverV3

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal BigOperators

namespace Family8PaperConflictOwnerGlobalStickyScaleCoverV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8PaperConflictOwnerParentFrameFiniteCodeV8
open Family8PaperConflictOwnerGlobalCoarseCoverV3
open Family8PaperEssentialDistinctOwnerClusterRetentionV3

noncomputable section

local instance instFintypeScaleCoverOwnerOccurrence
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    Fintype (ScaleCoverOwnerOccurrence C S) := by
  unfold ScaleCoverOwnerOccurrence
  infer_instance

local instance instDecidableEqScaleCoverOwnerOccurrence
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    DecidableEq (ScaleCoverOwnerOccurrence C S) := Classical.decEq _

/-!
# The global owner cover as an honest sticky scale cover

The fine indices are tagged owner occurrences, so repeated owners in distinct
old parent fibres remain distinct.  On the coarse side only labels actually
hit by an occurrence are activated.  This gives literal parent surjectivity
without assuming that the global label fills every unused code.
-/

/-- The fine tube family indexed by tagged owner occurrences. -/
noncomputable def ownerOccurrenceFine
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    UniformTubeFamily delta (ScaleCoverOwnerOccurrence C S) where
  tubes := fun p => fine.tubes p.owner
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem ownerOccurrenceFine_tubes
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (p : ScaleCoverOwnerOccurrence C S) :
    (ownerOccurrenceFine C S).tubes p = fine.tubes p.owner :=
  rfl

@[simp]
theorem ownerOccurrenceFine_refined
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :
    (ownerOccurrenceFine C S).refinement.refined = Finset.univ :=
  rfl

/-- The global owner-cell cover becomes a genuine `StickyScaleCover` after
discarding unused coarse codes.  Its stored coarse cardinality retains the
global quantitative bound. -/
theorem exists_ownerOccurrence_stickyScaleCover
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ T : StickyScaleCover (ownerOccurrenceFine C S) (5 * rho),
      T.coarseCard ≤ S.coarseCard * parentFrameCodeCount rho := by
  classical
  obtain ⟨n, coarse0, label, hn, hcontain⟩ :=
    exists_scaleCoverOwnerOccurrence_globalCoarseCover C S hdeltaSmall
      hdeltaRho hrhoPos hrhoOne
  let occupied : Finset (Fin n) :=
    (Finset.univ : Finset (ScaleCoverOwnerOccurrence C S)).image label
  let coarse : UniformTubeFamily (5 * rho) (Fin n) :=
    { tubes := coarse0.tubes
      refinement := UniformRefinement.ofFinset occupied }
  let T : StickyScaleCover (ownerOccurrenceFine C S) (5 * rho) :=
    { coarseCard := n
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := occupied
      parent := label
      activeFine_eq_refined := by rfl
      activeCoarse_eq_refined := by rfl
      parent_mem := by
        intro p _hp
        exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
      parent_surjective := by
        intro k hk
        obtain ⟨p, _hp, hpk⟩ := Finset.mem_image.mp hk
        exact ⟨p, Finset.mem_univ p, hpk⟩
      carrier_subset := by
        intro p _hp
        simpa only [ownerOccurrenceFine_tubes] using hcontain p }
  exact ⟨T, hn⟩

#print axioms ownerOccurrenceFine_tubes
#print axioms exists_ownerOccurrence_stickyScaleCover

end
end Family8PaperConflictOwnerGlobalStickyScaleCoverV4
