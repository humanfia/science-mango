import Family8Grounding.Family8DoubledParentConflictClusteringV2
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8DoubledParentConflictRestrictedCoverV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}
  {S : StickyScaleCover fine rho}
variable {weight : Fin S.coarseCard → ENNReal}

def SelectedAssignedFine
    (Q : DoubledParentConflictClustering S weight) :=
  {i : index // i ∈ S.activeFine ∧ S.parent i ∈ Q.selected}

noncomputable local instance selectedAssignedFineFintype
    (Q : DoubledParentConflictClustering S weight) :
    Fintype (SelectedAssignedFine Q) :=
  Fintype.ofInjective (fun i : SelectedAssignedFine Q ↦ i.1)
    Subtype.val_injective

noncomputable local instance selectedAssignedFineDecidableEq
    (Q : DoubledParentConflictClustering S weight) :
    DecidableEq (SelectedAssignedFine Q) := Classical.decEq _

noncomputable def selectedAssignedFineFamily
    (Q : DoubledParentConflictClustering S weight) :
    UniformTubeFamily delta (SelectedAssignedFine Q) := by
  classical
  exact
    { tubes := fun i ↦ fine.tubes i.1
      refinement := UniformRefinement.ofFinset Finset.univ }

@[simp]
theorem selectedAssignedFineFamily_tubes
    (Q : DoubledParentConflictClustering S weight)
    (i : SelectedAssignedFine Q) :
    (selectedAssignedFineFamily Q).tubes i = fine.tubes i.1 := rfl

/-- Reindex selected old parents and retain exactly their assigned fine
tubes. -/
noncomputable def selectedParentScaleCover
    (Q : DoubledParentConflictClustering S weight) :
    StickyScaleCover (selectedAssignedFineFamily Q) rho := by
  classical
  let e : {k // k ∈ Q.selected} ≃ Fin Q.selected.card :=
    Q.selected.equivFin
  let coarse : UniformTubeFamily rho (Fin Q.selected.card) :=
    { tubes := fun q ↦ S.coarse.tubes (e.symm q).1
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := Q.selected.card
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
          Q.selected_subset (e.symm q).2
        obtain ⟨i, hiActive, hiParent⟩ :=
          S.parent_surjective (e.symm q).1 hkActive
        have hiSelected : S.parent i ∈ Q.selected := by
          rw [hiParent]
          exact (e.symm q).2
        let p : SelectedAssignedFine Q := ⟨i, hiActive, hiSelected⟩
        refine ⟨p, Finset.mem_univ p, ?_⟩
        change e ⟨S.parent i, hiSelected⟩ = q
        have hp : (⟨S.parent i, hiSelected⟩ : {k // k ∈ Q.selected}) =
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

/-- The produced restricted cover satisfies literal Definition 2.10
doubled-parent partitioning. -/
theorem selectedParentScaleCover_isDoubledParentPartitioning
    (Q : DoubledParentConflictClustering S weight) :
    IsDoubledParentPartitioning (selectedParentScaleCover Q) := by
  classical
  apply isDoubledParentPartitioning_of_pairwise_noDoubledParentConflict
  intro k _hk l _hl hkl hconflict
  let e : {k // k ∈ Q.selected} ≃ Fin Q.selected.card :=
    Q.selected.equivFin
  have hsourceNe : (e.symm k).1 ≠ (e.symm l).1 := by
    intro hEq
    apply hkl
    apply e.symm.injective
    exact Subtype.ext hEq
  apply Q.selected_pairwise (e.symm k).2 (e.symm l).2 hsourceNe
  obtain ⟨i, _hi, hik, hil⟩ := hconflict
  refine ⟨i.1, i.2.1, ?_, ?_⟩
  · change (fine.tubes i.1).carrier ⊆
      twoFoldTubeCarrier (S.coarse.tubes (e.symm k).1) at hik ⊢
    exact hik
  · change (fine.tubes i.1).carrier ⊆
      twoFoldTubeCarrier (S.coarse.tubes (e.symm l).1) at hil ⊢
    exact hil

#print axioms selectedAssignedFineFamily_tubes
#print axioms selectedParentScaleCover_isDoubledParentPartitioning

end ScaleCover
end
end Family8DoubledParentConflictRestrictedCoverV3
