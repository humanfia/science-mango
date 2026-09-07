import Family8Grounding.Family8DoubledParentConflictRestrictedCoverV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8DoubledParentConflictRestrictedCoverPreservationV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictRestrictedCoverV3.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

attribute [local instance]
  Family8DoubledParentConflictRestrictedCoverV3.ScaleCover.selectedAssignedFineFintype
attribute [local instance]
  Family8DoubledParentConflictRestrictedCoverV3.ScaleCover.selectedAssignedFineDecidableEq

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}
  {S : StickyScaleCover fine rho}
variable {weight : Fin S.coarseCard → ENNReal}

/-- Exact equivalence between a selected-parent fibre and the corresponding
old fibre. -/
noncomputable def selectedParentScaleCover_fiberEquiv
    (Q : DoubledParentConflictClustering S weight)
    (q : Fin Q.selected.card) :
    {p // p ∈ (selectedParentScaleCover Q).fiber q} ≃
      {i // i ∈ S.fiber (Q.selected.equivFin.symm q).1} := by
  classical
  let e : {k // k ∈ Q.selected} ≃ Fin Q.selected.card :=
    Q.selected.equivFin
  let T := selectedParentScaleCover Q
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
        (⟨S.parent p.1.1, p.1.2.2⟩ : {k // k ∈ Q.selected}) =
          e.symm q := by
      apply e.injective
      rw [hparent, e.apply_symm_apply]
    exact congrArg Subtype.val heq
  · exact ((S.mem_fiber i.1 (e.symm q).1).mp i.2).1
  · have hi := (S.mem_fiber i.1 (e.symm q).1).mp i.2
    rw [hi.2]
    exact (e.symm q).2
  · unfold SelectedAssignedFine
    apply ((selectedParentScaleCover Q).mem_fiber _ q).2
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [selectedParentScaleCover]
    have hi := (S.mem_fiber i.1 (e.symm q).1).mp i.2
    have heq :
        (⟨S.parent i.1, by simpa only [hi.2] using (e.symm q).2⟩ :
          {k // k ∈ Q.selected}) = e.symm q := by
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

theorem selectedParentScaleCover_fiber_card_eq
    (Q : DoubledParentConflictClustering S weight)
    (q : Fin Q.selected.card) :
    ((selectedParentScaleCover Q).fiber q).card =
      (S.fiber (Q.selected.equivFin.symm q).1).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_congr (selectedParentScaleCover_fiberEquiv Q q)

/-- C-uniformity is inherited with no change of constant. -/
theorem isCUniform_selectedParentScaleCover
    (Q : DoubledParentConflictClustering S weight) {C : ENNReal}
    (huniform : IsCUniform S C) :
    IsCUniform (selectedParentScaleCover Q) C := by
  intro k _hk l _hl
  rw [selectedParentScaleCover_fiber_card_eq Q k,
    selectedParentScaleCover_fiber_card_eq Q l]
  exact huniform (Q.selected.equivFin.symm k).1
    (Q.selected_subset (Q.selected.equivFin.symm k).2)
    (Q.selected.equivFin.symm l).1
    (Q.selected_subset (Q.selected.equivFin.symm l).2)

/-- Global paper essential distinctness descends to the restricted fine
family. -/
theorem selectedAssignedFineFamily_pairwise_paperEssentiallyDistinct
    (Q : DoubledParentConflictClustering S weight)
    (hpairwise : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Set.Pairwise (Set.univ : Set (SelectedAssignedFine Q)) fun i j ↦
      PaperEssentiallyDistinct
        ((selectedAssignedFineFamily Q).tubes i)
        ((selectedAssignedFineFamily Q).tubes j) := by
  intro i _hi j _hj hij
  rw [selectedAssignedFineFamily_tubes,
    selectedAssignedFineFamily_tubes]
  apply hpairwise (Set.mem_univ i.1) (Set.mem_univ j.1)
  intro hval
  exact hij (Subtype.ext hval)

#print axioms selectedParentScaleCover_fiberEquiv
#print axioms selectedParentScaleCover_fiber_card_eq
#print axioms isCUniform_selectedParentScaleCover
#print axioms selectedAssignedFineFamily_pairwise_paperEssentiallyDistinct

end ScaleCover
end
end Family8DoubledParentConflictRestrictedCoverPreservationV4
