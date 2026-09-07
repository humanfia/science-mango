import Family8Grounding.Family8StickyScaleCoverDyadicParentRestrictionV2
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators

namespace Family8StickyScaleCoverDyadicParentRestrictionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8StickyScaleCoverDyadicParentRestrictionV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32Lemma55OwnerClusterDyadicRefinementV1

noncomputable section

/-!
# Honest sticky cover from the heterogeneous dyadic parent class

This layer reindexes the V2 dyadic selection as an actual fine family and an
actual `StickyScaleCover`.  Its fibres are canonically equivalent to the old
selected parent fibres.
-/

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}

abbrev ParentDyadicRefinement (S : StickyScaleCover fine rho) :=
  ParentClusterDyadicRefinement S.activeFine S.activeCoarse S.parent

/-- Fine indices retained above the selected dyadic class of parents. -/
abbrev ParentDyadicFineIndex (S : StickyScaleCover fine rho)
    (R : ParentDyadicRefinement S) :=
  ↥(parentClusterUnion S.activeFine R.selectedPivots S.parent)

local instance instFintypeParentDyadicFineIndex
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S) :
    Fintype (ParentDyadicFineIndex S R) :=
  Finset.fintypeCoeSort
    (parentClusterUnion S.activeFine R.selectedPivots S.parent)

local instance instDecidableEqParentDyadicFineIndex
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S) :
    DecidableEq (ParentDyadicFineIndex S R) := Classical.decEq _

namespace ParentDyadicFineIndex

theorem data (S : StickyScaleCover fine rho)
    (R : ParentDyadicRefinement S) (i : ParentDyadicFineIndex S R) :
    i.1 ∈ S.activeFine ∧ S.parent i.1 ∈ R.selectedPivots := by
  have hi := i.2
  change i.1 ∈ parentClusterUnion
    S.activeFine R.selectedPivots S.parent at hi
  exact Finset.mem_filter.mp hi

end ParentDyadicFineIndex

/-- The honest restricted fine family, with every retained index active. -/
noncomputable abbrev parentDyadicFine (S : StickyScaleCover fine rho)
    (R : ParentDyadicRefinement S) :
    UniformTubeFamily delta (ParentDyadicFineIndex S R) :=
  { tubes := fun i ↦ fine.tubes i.1
    refinement := UniformRefinement.ofFinset Finset.univ }

@[simp]
theorem parentDyadicFine_tubes (S : StickyScaleCover fine rho)
    (R : ParentDyadicRefinement S) (i : ParentDyadicFineIndex S R) :
    (parentDyadicFine S R).tubes i = fine.tubes i.1 :=
  rfl

/-- Reindex the selected old parents.  Each selected parent is occupied, so
the new parent map is literally surjective. -/
noncomputable abbrev parentDyadicScaleCover (S : StickyScaleCover fine rho)
    (R : ParentDyadicRefinement S) :
    StickyScaleCover (parentDyadicFine S R) rho := by
  classical
  let e : {k // k ∈ R.selectedPivots} ≃ Fin R.selectedPivots.card :=
    R.selectedPivots.equivFin
  let coarse : UniformTubeFamily rho (Fin R.selectedPivots.card) :=
    { tubes := fun q ↦ S.coarse.tubes (e.symm q).1
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := R.selectedPivots.card
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun i ↦
        e ⟨S.parent i.1, (ParentDyadicFineIndex.data S R i).2⟩
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := by
        intro q _hq
        have hkActive : (e.symm q).1 ∈ S.activeCoarse :=
          R.selectedPivots_subset (e.symm q).2
        obtain ⟨i, hiActive, hiParent⟩ :=
          S.parent_surjective (e.symm q).1 hkActive
        have hiSelected : S.parent i ∈ R.selectedPivots := by
          rw [hiParent]
          exact (e.symm q).2
        let p : ParentDyadicFineIndex S R :=
          ⟨i, Finset.mem_filter.mpr ⟨hiActive, hiSelected⟩⟩
        refine ⟨p, Finset.mem_univ p, ?_⟩
        change e ⟨S.parent i, hiSelected⟩ = q
        have hp :
            (⟨S.parent i, hiSelected⟩ : {k // k ∈ R.selectedPivots}) =
              e.symm q := by
          apply Subtype.ext
          exact hiParent
        rw [hp, e.apply_symm_apply]
      carrier_subset := by
        intro i _hi
        have hsource :=
          S.carrier_subset i.1 (ParentDyadicFineIndex.data S R i).1
        change (fine.tubes i.1).carrier ⊆
          (S.coarse.tubes
            (e.symm
              (e ⟨S.parent i.1,
                (ParentDyadicFineIndex.data S R i).2⟩)).1).carrier
        rw [e.symm_apply_apply]
        exact hsource }

@[simp]
theorem parentDyadicScaleCover_coarse_tubes
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S)
    (q : Fin R.selectedPivots.card) :
    (parentDyadicScaleCover S R).coarse.tubes q =
      S.coarse.tubes (R.selectedPivots.equivFin.symm q).1 :=
  rfl

/-- Callback-free specialization of the V2 heterogeneous pigeonhole
producer to the literal parent map. -/
theorem exists_parentDyadicRefinement
    (S : StickyScaleCover fine rho) (hactive : S.activeFine.Nonempty) :
    Nonempty (ParentDyadicRefinement S) := by
  exact exists_parentCluster_dyadic_refinement
    S.activeFine S.activeCoarse S.parent hactive
      (fun i hi ↦ S.parent_mem i hi)

/-- A new fibre is canonically equivalent to the corresponding old parent
fibre. -/
noncomputable def parentDyadicScaleCover_fiberEquiv
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S)
    (q : Fin R.selectedPivots.card) :
    {p // p ∈ (parentDyadicScaleCover S R).fiber q} ≃
      {i // i ∈ S.fiber (R.selectedPivots.equivFin.symm q).1} := by
  classical
  let e : {k // k ∈ R.selectedPivots} ≃ Fin R.selectedPivots.card :=
    R.selectedPivots.equivFin
  let T := parentDyadicScaleCover S R
  refine
    { toFun := fun p ↦ ⟨p.1.1, ?_⟩
      invFun := fun i ↦ ⟨⟨i.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hp := (T.mem_fiber p.1 q).mp p.2
    rw [S.mem_fiber]
    refine ⟨(ParentDyadicFineIndex.data S R p.1).1, ?_⟩
    have hparent := hp.2
    change e ⟨S.parent p.1.1,
      (ParentDyadicFineIndex.data S R p.1).2⟩ = q at hparent
    have heq :
        (⟨S.parent p.1.1,
          (ParentDyadicFineIndex.data S R p.1).2⟩ :
            {k // k ∈ R.selectedPivots}) = e.symm q := by
      apply e.injective
      rw [hparent, e.apply_symm_apply]
    exact congrArg Subtype.val heq
  · have hi := (S.mem_fiber i.1 (e.symm q).1).mp i.2
    exact Finset.mem_filter.mpr
      ⟨hi.1, by simpa only [hi.2] using (e.symm q).2⟩
  · unfold StickyScaleCover.fiber
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hi := (S.mem_fiber i.1 (e.symm q).1).mp i.2
    change e ⟨S.parent i.1,
      by simpa only [hi.2] using (e.symm q).2⟩ = q
    have heq :
        (⟨S.parent i.1, by simpa only [hi.2] using (e.symm q).2⟩ :
          {k // k ∈ R.selectedPivots}) = e.symm q := by
      apply Subtype.ext
      exact hi.2
    rw [heq, e.apply_symm_apply]
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro i
    apply Subtype.ext
    rfl

theorem parentDyadicScaleCover_fiber_card_eq
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S)
    (q : Fin R.selectedPivots.card) :
    ((parentDyadicScaleCover S R).fiber q).card =
      (S.fiber (R.selectedPivots.equivFin.symm q).1).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (parentDyadicScaleCover_fiberEquiv S R q)

/-- Every new occupied fibre lies in the selected dyadic interval. -/
theorem parentDyadicScaleCover_fiber_bounds
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S)
    (q : Fin R.selectedPivots.card) :
    2 ^ R.level ≤ ((parentDyadicScaleCover S R).fiber q).card ∧
      ((parentDyadicScaleCover S R).fiber q).card < 2 * 2 ^ R.level := by
  rw [parentDyadicScaleCover_fiber_card_eq S R q]
  simpa only [StickyScaleCover.fiber, parentClusterCard] using
    R.clusterCard_bounds (R.selectedPivots.equivFin.symm q).1
      (R.selectedPivots.equivFin.symm q).2

/-- The retained subtype realizes exactly the dyadic bucket loss. -/
theorem activeFine_card_le_bucketLoss_mul_restrictedFine_card
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S) :
    S.activeFine.card ≤ ownerClusterBucketLoss S.activeFine *
      Fintype.card (ParentDyadicFineIndex S R) := by
  have hcard : Fintype.card (ParentDyadicFineIndex S R) =
      (parentClusterUnion S.activeFine R.selectedPivots S.parent).card := by
    exact Fintype.card_coe _
  simpa only [hcard] using R.full_card_le_loss_mul_retained_card

/-- The selected dyadic class gives literal Definition 2.12
`2`-uniformity. -/
theorem parentDyadicScaleCover_isCUniform_two
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S) :
    IsCUniform (parentDyadicScaleCover S R) 2 := by
  apply isCUniform_two_of_dyadic_fiber_card
    (parentDyadicScaleCover S R) R.level
  · intro q _hq
    exact (parentDyadicScaleCover_fiber_bounds S R q).1
  · intro q _hq
    exact (parentDyadicScaleCover_fiber_bounds S R q).2

/-- Doubled-parent partitioning is inherited by restriction and reindexing. -/
theorem parentDyadicScaleCover_isDoubledParentPartitioning
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S)
    (hpartition : IsDoubledParentPartitioning S) :
    IsDoubledParentPartitioning (parentDyadicScaleCover S R) := by
  classical
  let e : {k // k ∈ R.selectedPivots} ≃ Fin R.selectedPivots.card :=
    R.selectedPivots.equivFin
  let T := parentDyadicScaleCover S R
  intro q _hq r _hr hqr
  rw [Finset.disjoint_left]
  intro i hiq hir
  have hiq' := (mem_doubledFiber T i q).mp hiq
  have hir' := (mem_doubledFiber T i r).mp hir
  have hOldNe : (e.symm q).1 ≠ (e.symm r).1 := by
    intro hEq
    apply hqr
    apply e.symm.injective
    exact Subtype.ext hEq
  have hOldQ : i.1 ∈ doubledFiber S (e.symm q).1 := by
    rw [mem_doubledFiber]
    refine ⟨(ParentDyadicFineIndex.data S R i).1, ?_⟩
    have hgeom := hiq'.2
    dsimp only [T] at hgeom
    rw [parentDyadicFine_tubes,
      parentDyadicScaleCover_coarse_tubes] at hgeom
    exact hgeom
  have hOldR : i.1 ∈ doubledFiber S (e.symm r).1 := by
    rw [mem_doubledFiber]
    refine ⟨(ParentDyadicFineIndex.data S R i).1, ?_⟩
    have hgeom := hir'.2
    dsimp only [T] at hgeom
    rw [parentDyadicFine_tubes,
      parentDyadicScaleCover_coarse_tubes] at hgeom
    exact hgeom
  exact (Finset.disjoint_left.mp
    (hpartition (e.symm q).1
      (R.selectedPivots_subset (e.symm q).2)
      (e.symm r).1 (R.selectedPivots_subset (e.symm r).2) hOldNe)
    hOldQ hOldR).elim

/-- Paper-essential distinctness is inherited by the restricted fine
subtype. -/
theorem parentDyadicFine_pairwise_paperEssentiallyDistinct
    (S : StickyScaleCover fine rho) (R : ParentDyadicRefinement S)
    (hpairwise : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Set.Pairwise (Set.univ : Set (ParentDyadicFineIndex S R)) fun i j ↦
      PaperEssentiallyDistinct
        ((parentDyadicFine S R).tubes i)
        ((parentDyadicFine S R).tubes j) := by
  intro i _hi j _hj hij
  rw [parentDyadicFine_tubes, parentDyadicFine_tubes]
  apply hpairwise (Set.mem_univ i.1) (Set.mem_univ j.1)
  intro hval
  exact hij (Subtype.ext hval)

/-- Canonical combined producer: one honest restricted cover, retained
cardinality, dyadic fibre bounds, and C-uniformity. -/
theorem exists_parentDyadicRestrictedScaleCover
    (S : StickyScaleCover fine rho) (hactive : S.activeFine.Nonempty) :
    ∃ R : ParentDyadicRefinement S,
      S.activeFine.card ≤ ownerClusterBucketLoss S.activeFine *
          Fintype.card (ParentDyadicFineIndex S R) ∧
      (∀ q, q ∈ (parentDyadicScaleCover S R).activeCoarse →
        2 ^ R.level ≤ ((parentDyadicScaleCover S R).fiber q).card ∧
          ((parentDyadicScaleCover S R).fiber q).card <
            2 * 2 ^ R.level) ∧
      IsCUniform (parentDyadicScaleCover S R) 2 := by
  obtain ⟨R⟩ := exists_parentDyadicRefinement S hactive
  refine ⟨R,
    activeFine_card_le_bucketLoss_mul_restrictedFine_card S R, ?_,
    parentDyadicScaleCover_isCUniform_two S R⟩
  intro q _hq
  exact parentDyadicScaleCover_fiber_bounds S R q

#print axioms exists_parentDyadicRefinement
#print axioms parentDyadicScaleCover_fiber_card_eq
#print axioms activeFine_card_le_bucketLoss_mul_restrictedFine_card
#print axioms parentDyadicScaleCover_isCUniform_two
#print axioms parentDyadicScaleCover_isDoubledParentPartitioning
#print axioms parentDyadicFine_pairwise_paperEssentiallyDistinct
#print axioms exists_parentDyadicRestrictedScaleCover

end

end Family8StickyScaleCoverDyadicParentRestrictionV3
