import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Submission.Kakeya.ConvexGeometry.Shading
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFineSubtypeScaleCoverV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Literal selected-fine subtype Sticky cover

An arbitrary genuine subfamily of the active fine indices is reindexed as a
new uniform tube family.  Its coarse indices are exactly the image of the old
parent map.  Hence all new fine and coarse indices are active, the new parent
map is surjective, and carrier containment is inherited without loss.

This construction is especially useful for an assembly refinement: discarded
fine indices disappear from the family-volume denominator instead of being
kept as empty shaded pieces.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Old coarse values occupied by a selected fine set. -/
def selectedFineParentValues (S : StickyScaleCover fine rho)
    (selected : Finset index) : Finset (Fin S.coarseCard) :=
  selected.image S.parent

abbrev SelectedFineIndex (selected : Finset index) := ↥selected

abbrev SelectedFineParentIndex (S : StickyScaleCover fine rho)
    (selected : Finset index) := ↥(selectedFineParentValues S selected)

/-- The literal selected uniform tube family. -/
noncomputable abbrev selectedFineFamily
    (_S : StickyScaleCover fine rho) (selected : Finset index) :
    UniformTubeFamily delta (SelectedFineIndex selected) :=
  { tubes := fun i => fine.tubes i.1
    refinement := UniformRefinement.ofFinset Finset.univ }

@[simp] theorem selectedFineFamily_tubes
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (i : SelectedFineIndex selected) :
    (selectedFineFamily S selected).tubes i = fine.tubes i.1 :=
  rfl

/-- Reindex a shading on the same literal selected fine family. -/
def selectedFineShading (S : StickyScaleCover fine rho)
    (selected : Finset index) (Y : Shading fine.bodyFamily) :
    Shading (selectedFineFamily S selected).bodyFamily where
  carrier := fun i => Y.carrier i.1
  measurable_carrier := fun i => Y.measurable_carrier i.1
  carrier_subset := fun i => by
    simpa only [UniformTubeFamily.bodyFamily, selectedFineFamily_tubes] using
      Y.carrier_subset i.1

@[simp] theorem selectedFineShading_carrier
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (Y : Shading fine.bodyFamily) (i : SelectedFineIndex selected) :
    (selectedFineShading S selected Y).carrier i = Y.carrier i.1 :=
  rfl

/-- The honest Sticky cover on an arbitrary selected active fine subtype. -/
noncomputable abbrev selectedFineScaleCover
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine) :
    StickyScaleCover (selectedFineFamily S selected) rho := by
  classical
  let e : {k // k ∈ selectedFineParentValues S selected} ≃ Fin (selectedFineParentValues S selected).card := (selectedFineParentValues S selected).equivFin
  let coarse : UniformTubeFamily rho (Fin (selectedFineParentValues S selected).card) :=
    { tubes := fun q => S.coarse.tubes (e.symm q).1
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := (selectedFineParentValues S selected).card
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun i => e ⟨S.parent i.1, by
        apply Finset.mem_image.mpr
        exact ⟨i.1, i.2, rfl⟩⟩
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := by
        intro q _hq
        let p : {k // k ∈ selectedFineParentValues S selected} := e.symm q
        obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp p.2
        let ii : SelectedFineIndex selected := ⟨i, hi⟩
        refine ⟨ii, Finset.mem_univ ii, ?_⟩
        change e ⟨S.parent i, by
          apply Finset.mem_image.mpr
          exact ⟨i, hi, rfl⟩⟩ = q
        have heq :
            (⟨S.parent i, by
              apply Finset.mem_image.mpr
              exact ⟨i, hi, rfl⟩⟩ : {k // k ∈ selectedFineParentValues S selected}) = p := by
          apply Subtype.ext
          exact hip
        rw [heq, e.apply_symm_apply]
      carrier_subset := by
        intro i _hi
        have hsource := S.carrier_subset i.1 (hselected i.2)
        change (fine.tubes i.1).carrier ⊆
          (S.coarse.tubes
            (e.symm (e ⟨S.parent i.1, by
              apply Finset.mem_image.mpr
              exact ⟨i.1, i.2, rfl⟩⟩)).1).carrier
        rw [e.symm_apply_apply]
        exact hsource }

/-- The new parent body is exactly the occupied old parent body. -/
@[simp] theorem selectedFineScaleCover_coarse_tubes
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (q : Fin (selectedFineParentValues S selected).card) :
    (selectedFineScaleCover S selected hselected).coarse.tubes q =
      S.coarse.tubes
        ((selectedFineParentValues S selected).equivFin.symm q).1 :=
  rfl

/-- The new parent map records exactly the old parent value. -/
theorem selectedFineScaleCover_parent_oldValue
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (i : SelectedFineIndex selected) :
    ((selectedFineParentValues S selected).equivFin.symm
      ((selectedFineScaleCover S selected hselected).parent i)).1 =
        S.parent i.1 := by
  exact congrArg Subtype.val
    ((selectedFineParentValues S selected).equivFin.symm_apply_apply
      ⟨S.parent i.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩)

/-- Membership in a new fibre is exactly equality of the original parent
value. -/
theorem mem_selectedFineScaleCover_fiber_iff
    (S : StickyScaleCover fine rho) (selected : Finset index)
    (hselected : selected ⊆ S.activeFine)
    (i : SelectedFineIndex selected)
    (q : Fin (selectedFineParentValues S selected).card) :
    i ∈ (selectedFineScaleCover S selected hselected).fiber q ↔
      S.parent i.1 =
        ((selectedFineParentValues S selected).equivFin.symm q).1 := by
  rw [StickyScaleCover.mem_fiber]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro h
    calc
      S.parent i.1 =
          ((selectedFineParentValues S selected).equivFin.symm
            ((selectedFineScaleCover S selected hselected).parent i)).1 :=
        (selectedFineScaleCover_parent_oldValue S selected hselected i).symm
      _ = ((selectedFineParentValues S selected).equivFin.symm q).1 :=
        congrArg Subtype.val
          (congrArg (selectedFineParentValues S selected).equivFin.symm h)
  · intro h
    apply (selectedFineParentValues S selected).equivFin.symm.injective
    apply Subtype.ext
    exact (selectedFineScaleCover_parent_oldValue
      S selected hselected i).trans h

#print axioms selectedFineParentValues
#print axioms selectedFineShading
#print axioms selectedFineScaleCover_coarse_tubes
#print axioms selectedFineScaleCover_parent_oldValue
#print axioms mem_selectedFineScaleCover_fiber_iff

end
end Family8StickySelectedFineSubtypeScaleCoverV1
