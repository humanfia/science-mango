import Family8Grounding.Family8StickySelectedFineSubtypeScaleCoverV1
import Mathlib.Tactic

/-!
# Cardinality cap transport through the literal selected-fine cover

The selected-fine cover only reindexes a subfamily.  Each of its fibres
injects into the corresponding original fibre, so every further finite
selection inherits the original pointwise fibre cap without loss.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedFineFiberCardCapTransportV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A fibre of the selected-fine reindexing injects into its literal old
parent fibre. -/
theorem selectedFineScaleCover_fiber_card_le_parent_fiber
    (S : StickyScaleCover fine rho)
    (selected : Finset index) (hselected : selected ⊆ S.activeFine)
    (q : Fin (selectedFineParentValues S selected).card) :
    ((selectedFineScaleCover S selected hselected).fiber q).card <=
      (S.fiber
        ((selectedFineParentValues S selected).equivFin.symm q).1).card := by
  classical
  let T := selectedFineScaleCover S selected hselected
  let oldParent :=
    ((selectedFineParentValues S selected).equivFin.symm q).1
  let f : {i // i ∈ T.fiber q} -> {i // i ∈ S.fiber oldParent} :=
    fun i => ⟨i.1.1, by
      apply (S.mem_fiber i.1.1 oldParent).2
      exact ⟨hselected i.1.2,
        (mem_selectedFineScaleCover_fiber_iff
          S selected hselected i.1 q).1 i.2⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hv : i.1.1 = j.1.1 :=
      congrArg (fun z : {i // i ∈ S.fiber oldParent} => z.1) hij
    exact Subtype.ext (Subtype.ext hv)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

/-- The old parent represented by a selected-fine coarse index is active. -/
theorem selectedFineScaleCover_parent_mem_activeCoarse
    (S : StickyScaleCover fine rho)
    (selected : Finset index) (hselected : selected ⊆ S.activeFine)
    (q : Fin (selectedFineParentValues S selected).card) :
    ((selectedFineParentValues S selected).equivFin.symm q).1 ∈
      S.activeCoarse := by
  have hmem :=
    ((selectedFineParentValues S selected).equivFin.symm q).2
  obtain ⟨i, hi, hparent⟩ := Finset.mem_image.mp hmem
  rw [← hparent]
  exact S.parent_mem i (hselected hi)

/-- Any finite sub-selection of a selected-fine fibre inherits a pointwise
cap on the original active fibres. -/
theorem selectedFineScaleCover_selected_card_le_parent_cap
    (S : StickyScaleCover fine rho)
    (selected : Finset index) (hselected : selected ⊆ S.activeFine)
    (q : Fin (selectedFineParentValues S selected).card)
    (picked : Finset {i // i ∈
      (selectedFineScaleCover S selected hselected).fiber q})
    (M : Nat)
    (hM : forall k, k ∈ S.activeCoarse -> (S.fiber k).card <= M) :
    picked.card <= M := by
  calc
    picked.card <=
        ((selectedFineScaleCover S selected hselected).fiber q).card := by
      simpa only [Fintype.card_coe] using Finset.card_le_univ picked
    _ <= (S.fiber
        ((selectedFineParentValues S selected).equivFin.symm q).1).card :=
      selectedFineScaleCover_fiber_card_le_parent_fiber
        S selected hselected q
    _ <= M := hM _
      (selectedFineScaleCover_parent_mem_activeCoarse
        S selected hselected q)

#print axioms selectedFineScaleCover_fiber_card_le_parent_fiber
#print axioms selectedFineScaleCover_parent_mem_activeCoarse
#print axioms selectedFineScaleCover_selected_card_le_parent_cap

end
end Family8SelectedFineFiberCardCapTransportV2
