import Family8Grounding.Family8PaperConflictOwnerParentFrameCoarseCoverV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal BigOperators

namespace Family8PaperConflictOwnerGlobalCoarseCoverV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8PaperConflictOwnerParentFrameFiniteCodeV8
open Family8PaperConflictOwnerParentFrameCoarseCoverV6
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Global aggregation of the owner-cell coarse covers

The local coarse families are aggregated over the old parents by a dependent
sum and then reindexed by a finite interval.  The source is deliberately the
type of tagged owner occurrences.  If the same selected owner occurs in two
old source fibres, both occurrences remain; no injectivity or deduplication
assumption is used.
-/

/-- An owner occurrence tagged by the old parent fibre in which it occurs. -/
def ScaleCoverOwnerOccurrence
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) :=
  Σ k : Fin S.coarseCard, ↥(C.sourceOwnerImage (S.fiber k))

/-- The underlying owner; this projection is intentionally not claimed to be
injective. -/
def ScaleCoverOwnerOccurrence.owner
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    {C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight}
    {S : StickyScaleCover fine rho}
    (p : ScaleCoverOwnerOccurrence C S) : index := p.2.1

/-- The local package supplied at one old parent. -/
structure ParentOwnerLocalCoarseCover
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (fine : UniformTubeFamily delta index)
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) where
  card : Nat
  coarse : UniformTubeFamily (5 * rho) (Fin card)
  label : ↥(C.sourceOwnerImage (S.fiber k)) → Fin card
  card_le : card ≤ parentFrameCodeCount rho
  carrier_subset : ∀ p, (fine.tubes p.1).carrier ⊆
    (coarse.tubes (label p)).carrier

/-- Every old parent admits a local package; an empty source fibre simply
produces an empty occupied-code family. -/
theorem nonempty_parentOwnerLocalCoarseCover
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : Fin S.coarseCard) :
    Nonempty (ParentOwnerLocalCoarseCover fine C S k) := by
  obtain ⟨n, _representative, coarse, label, hn, _hcoarse, hcontain⟩ :=
    exists_scaleCover_ownerImage_parentFrameCoarseCover C S hdeltaSmall
      hdeltaRho hrhoPos hrhoOne k
  exact ⟨{
    card := n
    coarse := coarse
    label := label
    card_le := hn
    carrier_subset := hcontain }⟩

/-- Global finite aggregation of the old-parent owner-cell covers.

Its source is the full sigma of tagged owner occurrences, so repeated owners
are counted honestly.  The output covers those occurrences and has total
cardinality at most `oldCoarseCard * parentFrameCodeCount rho`. -/
theorem exists_scaleCoverOwnerOccurrence_globalCoarseCover
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1) :
    ∃ n : Nat, ∃ coarse : UniformTubeFamily (5 * rho) (Fin n),
      ∃ label : ScaleCoverOwnerOccurrence C S → Fin n,
        n ≤ S.coarseCard * parentFrameCodeCount rho ∧
        ∀ p, (fine.tubes p.owner).carrier ⊆
          (coarse.tubes (label p)).carrier := by
  classical
  let L : ∀ k : Fin S.coarseCard, ParentOwnerLocalCoarseCover fine C S k :=
    fun k => Classical.choice
      (nonempty_parentOwnerLocalCoarseCover C S hdeltaSmall hdeltaRho
        hrhoPos hrhoOne k)
  let GlobalCode := Σ k : Fin S.coarseCard, Fin (L k).card
  let e : GlobalCode ≃ Fin (Fintype.card GlobalCode) :=
    Fintype.equivFin GlobalCode
  let coarse : UniformTubeFamily (5 * rho) (Fin (Fintype.card GlobalCode)) :=
    { tubes := fun q =>
        (L (e.symm q).1).coarse.tubes (e.symm q).2
      refinement := UniformRefinement.ofFinset Finset.univ }
  let label : ScaleCoverOwnerOccurrence C S →
      Fin (Fintype.card GlobalCode) := fun p =>
    e ⟨p.1, (L p.1).label p.2⟩
  have hcard : Fintype.card GlobalCode ≤
      S.coarseCard * parentFrameCodeCount rho := by
    calc
      Fintype.card GlobalCode =
          ∑ k : Fin S.coarseCard, (L k).card := by
        simp only [GlobalCode, Fintype.card_sigma, Fintype.card_fin]
      _ ≤ ∑ _k : Fin S.coarseCard, parentFrameCodeCount rho := by
        exact Finset.sum_le_sum fun k _hk => (L k).card_le
      _ = S.coarseCard * parentFrameCodeCount rho := by simp
  refine ⟨Fintype.card GlobalCode, coarse, label, hcard, ?_⟩
  intro p
  have hp := (L p.1).carrier_subset p.2
  change (fine.tubes p.2.1).carrier ⊆
    ((L (e.symm (e ⟨p.1, (L p.1).label p.2⟩)).1).coarse.tubes
      (e.symm (e ⟨p.1, (L p.1).label p.2⟩)).2).carrier
  rw [e.symm_apply_apply]
  exact hp

#print axioms nonempty_parentOwnerLocalCoarseCover
#print axioms exists_scaleCoverOwnerOccurrence_globalCoarseCover

end
end Family8PaperConflictOwnerGlobalCoarseCoverV3
