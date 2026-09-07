import Family8Grounding.Family8DoubledParentConflictIncidenceDegreeV3
import Submission.Kakeya.ConvexFactoring.NonConcentration
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace Family8DoubledParentsAssignedFineInjectionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictIncidenceDegreeV3.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}

/-- Active parents whose doubled carrier contains one fixed fine tube,
packaged as a finite type. -/
def IncidentParent (S : StickyScaleCover fine rho) (i : index) :=
  {k : Fin S.coarseCard // k ∈ doubledParentsContainingFine S i}

noncomputable local instance incidentParentFintype
    (S : StickyScaleCover fine rho) (i : index) :
    Fintype (IncidentParent S i) :=
  Finset.fintypeCoeSort (doubledParentsContainingFine S i)

/-- Choose one genuinely assigned active fine tube from each incident active
parent.  Parent surjectivity supplies this choice. -/
noncomputable def incidentAssignedFine
    (S : StickyScaleCover fine rho) (i : index)
    (k : IncidentParent S i) : index :=
  Classical.choose
    (S.parent_surjective k.1
      ((mem_doubledParentsContainingFine S i k.1).mp k.2).1)

theorem incidentAssignedFine_mem_activeFine
    (S : StickyScaleCover fine rho) (i : index)
    (k : IncidentParent S i) :
    incidentAssignedFine S i k ∈ S.activeFine :=
  (Classical.choose_spec
    (S.parent_surjective k.1
      ((mem_doubledParentsContainingFine S i k.1).mp k.2).1)).1

theorem incidentAssignedFine_parent
    (S : StickyScaleCover fine rho) (i : index)
    (k : IncidentParent S i) :
    S.parent (incidentAssignedFine S i k) = k.1 :=
  (Classical.choose_spec
    (S.parent_surjective k.1
      ((mem_doubledParentsContainingFine S i k.1).mp k.2).1)).2

/-- Distinct incident parents have distinct selected assigned fine tubes. -/
theorem incidentAssignedFine_injective
    (S : StickyScaleCover fine rho) (i : index) :
    Function.Injective (incidentAssignedFine S i) := by
  intro k l hkl
  apply Subtype.ext
  have hparent := congrArg S.parent hkl
  simpa only [incidentAssignedFine_parent] using hparent

/-- If every selected assigned tube lies in one convex test, the genuine
cross-parent incidence cardinality injects into that test's contained-index
set. -/
theorem doubledParentsContainingFine_card_le_containedIndices
    (S : StickyScaleCover fine rho) (i : index)
    (K : ConvexBody Space)
    (hcontained : ∀ k : IncidentParent S i,
      (fine.tubes (incidentAssignedFine S i k)).carrier ⊆ (K : Set Space)) :
    (doubledParentsContainingFine S i).card ≤
      (containedIndices fine.bodyFamily K).card := by
  classical
  let f : IncidentParent S i →
      {j : index // j ∈ containedIndices fine.bodyFamily K} := fun k =>
    ⟨incidentAssignedFine S i k, by
      rw [mem_containedIndices]
      exact hcontained k⟩
  have hf : Function.Injective f := by
    intro k l hkl
    apply incidentAssignedFine_injective S i
    exact congrArg Subtype.val hkl
  have hcard := Fintype.card_le_of_injective f hf
  change Fintype.card ↥(doubledParentsContainingFine S i) ≤
    Fintype.card ↥(containedIndices fine.bodyFamily K) at hcard
  calc
    (doubledParentsContainingFine S i).card =
        Fintype.card ↥(doubledParentsContainingFine S i) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card ↥(containedIndices fine.bodyFamily K) := hcard
    _ = (containedIndices fine.bodyFamily K).card := Fintype.card_coe _

#print axioms incidentAssignedFine_mem_activeFine
#print axioms incidentAssignedFine_parent
#print axioms incidentAssignedFine_injective
#print axioms doubledParentsContainingFine_card_le_containedIndices

end ScaleCover
end
end Family8DoubledParentsAssignedFineInjectionV3
