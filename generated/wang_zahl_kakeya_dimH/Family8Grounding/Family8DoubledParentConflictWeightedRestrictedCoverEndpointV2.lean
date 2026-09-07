import Family8Grounding.Family8DoubledParentConflictWeightedRetentionV3
import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Quantitative doubled-parent restricted cover

This is the canonical consumer of the honest quantitative `2A` selection.
It retains exactly the fine tubes assigned to the selected old parents.
Consequently the selected cover is literally doubled-parent partitioning,
and both C-uniformity and paper essential distinctness descend without an
additional loss.  Cardinality and arbitrary-mass retention are the two
inequalities already carried by the same weighted selection.
-/

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}
  {S : StickyScaleCover fine rho}
variable {weight : Fin S.coarseCard → ENNReal} {B : ENNReal}

def WeightedSelectedAssignedFine
    (W : DoubledParentConflictWeightedSelection S weight B) :=
  {i : index // i ∈ S.activeFine ∧ S.parent i ∈ W.selected}

noncomputable instance weightedSelectedAssignedFineFintype
    (W : DoubledParentConflictWeightedSelection S weight B) :
    Fintype (WeightedSelectedAssignedFine W) :=
  Fintype.ofInjective (fun i : WeightedSelectedAssignedFine W ↦ i.1)
    Subtype.val_injective

noncomputable instance weightedSelectedAssignedFineDecidableEq
    (W : DoubledParentConflictWeightedSelection S weight B) :
    DecidableEq (WeightedSelectedAssignedFine W) := Classical.decEq _

noncomputable def weightedSelectedAssignedFineFamily
    (W : DoubledParentConflictWeightedSelection S weight B) :
    UniformTubeFamily delta (WeightedSelectedAssignedFine W) := by
  classical
  exact
    { tubes := fun i ↦ fine.tubes i.1
      refinement := UniformRefinement.ofFinset Finset.univ }

@[simp]
theorem weightedSelectedAssignedFineFamily_tubes
    (W : DoubledParentConflictWeightedSelection S weight B)
    (i : WeightedSelectedAssignedFine W) :
    (weightedSelectedAssignedFineFamily W).tubes i = fine.tubes i.1 := rfl

/-- Reindex the selected old parents and retain exactly their assigned fine
tubes. -/
noncomputable def weightedSelectedParentScaleCover
    (W : DoubledParentConflictWeightedSelection S weight B) :
    StickyScaleCover (weightedSelectedAssignedFineFamily W) rho := by
  classical
  let e : {k // k ∈ W.selected} ≃ Fin W.selected.card :=
    W.selected.equivFin
  let coarse : UniformTubeFamily rho (Fin W.selected.card) :=
    { tubes := fun q ↦ S.coarse.tubes (e.symm q).1
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := W.selected.card
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun i ↦ e ⟨S.parent i.1, i.2.2⟩
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := by
        intro q _hq
        have hkActive : (e.symm q).1 ∈ S.activeCoarse :=
          W.selected_subset (e.symm q).2
        obtain ⟨i, hiActive, hiParent⟩ :=
          S.parent_surjective (e.symm q).1 hkActive
        have hiSelected : S.parent i ∈ W.selected := by
          rw [hiParent]
          exact (e.symm q).2
        let p : WeightedSelectedAssignedFine W :=
          ⟨i, hiActive, hiSelected⟩
        refine ⟨p, Finset.mem_univ p, ?_⟩
        change e ⟨S.parent i, hiSelected⟩ = q
        have hp :
            (⟨S.parent i, hiSelected⟩ : {k // k ∈ W.selected}) =
              e.symm q := by
          apply Subtype.ext
          exact hiParent
        rw [hp, e.apply_symm_apply]
      carrier_subset := by
        intro i _hi
        have hsource := S.carrier_subset i.1 i.2.1
        change (fine.tubes i.1).carrier ⊆
          (S.coarse.tubes
            (e.symm (e ⟨S.parent i.1, i.2.2⟩)).1).carrier
        rw [e.symm_apply_apply]
        exact hsource }

/-- Literal Definition 2.10 partitioning of the selected cover. -/
theorem weightedSelectedParentScaleCover_isDoubledParentPartitioning
    (W : DoubledParentConflictWeightedSelection S weight B) :
    IsDoubledParentPartitioning (weightedSelectedParentScaleCover W) := by
  classical
  apply isDoubledParentPartitioning_of_pairwise_noDoubledParentConflict
  intro k _hk l _hl hkl hconflict
  let e : {k // k ∈ W.selected} ≃ Fin W.selected.card :=
    W.selected.equivFin
  have hsourceNe : (e.symm k).1 ≠ (e.symm l).1 := by
    intro hEq
    apply hkl
    apply e.symm.injective
    exact Subtype.ext hEq
  apply W.selected_pairwise (e.symm k).2 (e.symm l).2 hsourceNe
  obtain ⟨i, _hi, hik, hil⟩ := hconflict
  refine ⟨i.1, i.2.1, ?_, ?_⟩
  · change (fine.tubes i.1).carrier ⊆
      twoFoldTubeCarrier (S.coarse.tubes (e.symm k).1) at hik ⊢
    exact hik
  · change (fine.tubes i.1).carrier ⊆
      twoFoldTubeCarrier (S.coarse.tubes (e.symm l).1) at hil ⊢
    exact hil

/-- Exact equivalence between a selected-cover fibre and its old parent
fibre. -/
noncomputable def weightedSelectedParentScaleCover_fiberEquiv
    (W : DoubledParentConflictWeightedSelection S weight B)
    (q : Fin W.selected.card) :
    {p // p ∈ (weightedSelectedParentScaleCover W).fiber q} ≃
      {i // i ∈ S.fiber (W.selected.equivFin.symm q).1} := by
  classical
  let e : {k // k ∈ W.selected} ≃ Fin W.selected.card :=
    W.selected.equivFin
  let T := weightedSelectedParentScaleCover W
  refine
    { toFun := fun p ↦ ⟨p.1.1, ?_⟩
      invFun := fun i ↦ ⟨⟨i.1, ?_, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hp := (T.mem_fiber p.1 q).mp p.2
    rw [S.mem_fiber]
    refine ⟨p.1.2.1, ?_⟩
    have hparent := hp.2
    change e ⟨S.parent p.1.1, p.1.2.2⟩ = q at hparent
    have heq :
        (⟨S.parent p.1.1, p.1.2.2⟩ : {k // k ∈ W.selected}) =
          e.symm q := by
      apply e.injective
      rw [hparent, e.apply_symm_apply]
    exact congrArg Subtype.val heq
  · exact ((S.mem_fiber i.1 (e.symm q).1).mp i.2).1
  · have hi := (S.mem_fiber i.1 (e.symm q).1).mp i.2
    rw [hi.2]
    exact (e.symm q).2
  · unfold WeightedSelectedAssignedFine
    apply ((weightedSelectedParentScaleCover W).mem_fiber _ q).2
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [weightedSelectedParentScaleCover]
    have hi := (S.mem_fiber i.1 (e.symm q).1).mp i.2
    have heq :
        (⟨S.parent i.1, by simpa only [hi.2] using (e.symm q).2⟩ :
          {k // k ∈ W.selected}) = e.symm q := by
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

theorem weightedSelectedParentScaleCover_fiber_card_eq
    (W : DoubledParentConflictWeightedSelection S weight B)
    (q : Fin W.selected.card) :
    ((weightedSelectedParentScaleCover W).fiber q).card =
      (S.fiber (W.selected.equivFin.symm q).1).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (weightedSelectedParentScaleCover_fiberEquiv W q)

/-- C-uniformity is inherited with no additional loss. -/
theorem isCUniform_weightedSelectedParentScaleCover
    (W : DoubledParentConflictWeightedSelection S weight B) {C : ENNReal}
    (huniform : IsCUniform S C) :
    IsCUniform (weightedSelectedParentScaleCover W) C := by
  intro k _hk l _hl
  rw [weightedSelectedParentScaleCover_fiber_card_eq W k,
    weightedSelectedParentScaleCover_fiber_card_eq W l]
  exact huniform (W.selected.equivFin.symm k).1
    (W.selected_subset (W.selected.equivFin.symm k).2)
    (W.selected.equivFin.symm l).1
    (W.selected_subset (W.selected.equivFin.symm l).2)

/-- Global paper essential distinctness descends to the retained fine
family. -/
theorem weightedSelectedAssignedFineFamily_pairwise_paperEssentiallyDistinct
    (W : DoubledParentConflictWeightedSelection S weight B)
    (hpairwise : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Set.Pairwise (Set.univ : Set (WeightedSelectedAssignedFine W))
      fun i j ↦ PaperEssentiallyDistinct
        ((weightedSelectedAssignedFineFamily W).tubes i)
        ((weightedSelectedAssignedFineFamily W).tubes j) := by
  intro i _hi j _hj hij
  rw [weightedSelectedAssignedFineFamily_tubes,
    weightedSelectedAssignedFineFamily_tubes]
  apply hpairwise (Set.mem_univ i.1) (Set.mem_univ j.1)
  intro hval
  exact hij (Subtype.ext hval)

/-- John unit-rescaling geometry restricts by pure parent reindexing. -/
noncomputable def UnitRescalingGeometry.restrictToWeightedSelection
    (R : UnitRescalingGeometry S)
    (W : DoubledParentConflictWeightedSelection S weight B) :
    UnitRescalingGeometry (weightedSelectedParentScaleCover W) := by
  classical
  let oldParent :
      {q // q ∈ (weightedSelectedParentScaleCover W).activeCoarse} →
        {k // k ∈ S.activeCoarse} := fun q ↦
    ⟨(W.selected.equivFin.symm q.1).1,
      W.selected_subset (W.selected.equivFin.symm q.1).2⟩
  refine
    { johnWitness := fun q ↦ ?_
      unitRescaling := fun q ↦ R.unitRescaling (oldParent q)
      johnOuter_image_eq_unitBall := fun q ↦ ?_ }
  · simpa only [weightedSelectedParentScaleCover] using
      R.johnWitness (oldParent q)
  · simpa [weightedSelectedParentScaleCover] using
      R.johnOuter_image_eq_unitBall (oldParent q)

/-- Canonical quantitative endpoint: one actual restricted scale cover has
literal partitioning, unchanged C-uniformity and paper distinctness, while
its selected old parents retain both cardinality and the requested mass. -/
structure WeightedRestrictedCoverEndpoint
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B C : ENNReal) where
  selection : DoubledParentConflictWeightedSelection S weight B
  doubled_parent_partitioning :
    IsDoubledParentPartitioning
      (weightedSelectedParentScaleCover selection)
  c_uniform : IsCUniform (weightedSelectedParentScaleCover selection) C
  fine_pairwise_paperEssentiallyDistinct :
    Set.Pairwise
      (Set.univ : Set (WeightedSelectedAssignedFine selection))
      fun i j ↦ PaperEssentiallyDistinct
        ((weightedSelectedAssignedFineFamily selection).tubes i)
        ((weightedSelectedAssignedFineFamily selection).tubes j)

theorem exists_weightedRestrictedCoverEndpoint
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B C : ENNReal)
    (hneighbour : ClosedDoubledParentConflictDegreeBound S B)
    (huniform : IsCUniform S C)
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Nonempty (WeightedRestrictedCoverEndpoint S weight B C) := by
  obtain ⟨W⟩ :=
    exists_doubledParentConflictWeightedSelection S weight B hneighbour
  exact ⟨
    { selection := W
      doubled_parent_partitioning :=
        weightedSelectedParentScaleCover_isDoubledParentPartitioning W
      c_uniform := isCUniform_weightedSelectedParentScaleCover W huniform
      fine_pairwise_paperEssentiallyDistinct :=
        weightedSelectedAssignedFineFamily_pairwise_paperEssentiallyDistinct
          W hpaper }⟩

#print axioms weightedSelectedParentScaleCover_isDoubledParentPartitioning
#print axioms weightedSelectedParentScaleCover_fiberEquiv
#print axioms weightedSelectedParentScaleCover_fiber_card_eq
#print axioms isCUniform_weightedSelectedParentScaleCover
#print axioms weightedSelectedAssignedFineFamily_pairwise_paperEssentiallyDistinct
#print axioms UnitRescalingGeometry.restrictToWeightedSelection
#print axioms exists_weightedRestrictedCoverEndpoint

end ScaleCover
end
end Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2
