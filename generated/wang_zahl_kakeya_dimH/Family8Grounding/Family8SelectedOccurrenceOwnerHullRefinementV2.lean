import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV15
import Family8Grounding.Family8TubeClosedThickeningInsideTwoFoldV2
import Mathlib.Tactic

/-!
# Genuine parent-specific hull refinement of selected occurrences

A global greedy block need not be parent-pure.  For each occurrence we retain
the literal subfibre whose actual sticky parent equals the representative's
parent, and take the closed convex hull of those fine bodies.  The chosen fine
witness makes this subfibre nonempty.  Thus the new body is genuinely
parent-specific (not a copied global winning hull), lies in the actual parent
tube, and its admissible thickenings lie in the full doubled parent.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceOwnerHullRefinementV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceActiveParentOwnerV9
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8TubeClosedThickeningInsideTwoFoldV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho a b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)

/-- The literal representative-owner part of one global greedy block. -/
def occurrenceOwnerSubfiber
    (k : Fin (blocks fine.bodyFamily P).length) : Finset index :=
  (blockAt fine.bodyFamily P k).fiber.filter fun i =>
    C.parent i = occurrenceActiveParent C P k

@[simp] theorem mem_occurrenceOwnerSubfiber
    (k : Fin (blocks fine.bodyFamily P).length) (i : index) :
    i ∈ occurrenceOwnerSubfiber C P k ↔
      i ∈ (blockAt fine.bodyFamily P k).fiber ∧
        C.parent i = occurrenceActiveParent C P k := by
  simp [occurrenceOwnerSubfiber]

/-- The representative witness ensures the parent-specific subfibre is never
empty. -/
theorem occurrenceOwnerSubfiber_nonempty
    (k : Fin (blocks fine.bodyFamily P).length) :
    (occurrenceOwnerSubfiber C P k).Nonempty := by
  refine ⟨occurrenceFineWitness C P k, ?_⟩
  rw [mem_occurrenceOwnerSubfiber]
  exact ⟨occurrenceFineWitness_mem C P k, rfl⟩

/-- The new occurrence body is the actual closed convex hull of only those
fine bodies having the representative's parent. -/
def occurrenceOwnerHull
    (k : Fin (blocks fine.bodyFamily P).length) : ConvexBody Space :=
  hullContainer fine.bodyFamily (occurrenceOwnerSubfiber C P k)

/-- Parent purity of the refined subfibre is definitional. -/
theorem occurrenceOwnerSubfiber_parent_eq
    (k : Fin (blocks fine.bodyFamily P).length)
    (i : index) (hi : i ∈ occurrenceOwnerSubfiber C P k) :
    C.parent i = occurrenceActiveParent C P k :=
  (mem_occurrenceOwnerSubfiber C P k i).mp hi |>.2

/-- Every refined owner hull lies in its actual coarse parent tube. -/
theorem occurrenceOwnerHull_subset_parent
    (k : Fin (blocks fine.bodyFamily P).length) :
    (occurrenceOwnerHull C P k : Set Space) ⊆
      (C.coarse.tubes (occurrenceActiveParent C P k)).carrier := by
  have hsubset :
      (hullContainer fine.bodyFamily (occurrenceOwnerSubfiber C P k) :
          Set Space) ⊆
        ((C.coarse.tubes (occurrenceActiveParent C P k)).body : Set Space) := by
    apply hullContainer_subset fine.bodyFamily
      (occurrenceOwnerSubfiber_nonempty C P k)
    intro i hi
    have hi' := (mem_occurrenceOwnerSubfiber C P k i).mp hi
    have hiActive : i ∈ C.activeFine :=
      blockAt_fiber_subset_active fine.bodyFamily P k hi'.1
    have hparent := C.carrier_subset i hiActive
    rw [hi'.2] at hparent
    exact hparent
  exact hsubset

/-- The family of genuine parent-specific occurrence hulls on a selected
occurrence set. -/
abbrev selectedOccurrenceOwnerHullFamily
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P R} :=
  fun q => occurrenceOwnerHull C P (selectedOccurrencePosition C R q)

theorem selectedOccurrenceOwnerHullFamily_subset_parent
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    (selectedOccurrenceOwnerHullFamily C P R q : Set Space) ⊆
      (C.coarse.tubes (selectedOccurrenceActiveParent C R q)).carrier := by
  exact occurrenceOwnerHull_subset_parent C P
    (selectedOccurrencePosition C R q)

/-- For a parent-specific hull family, the formerly explicit geometric seam
`AdmissibleThickeningInsideOwner` follows from `theta*b <= rho`. -/
theorem admissibleThickeningInsideOwner_of_ownerHullFamily
    (hrho : 0 < rho) (hb : b ≤ rho)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (D : ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P R} a b)
    (hfamily : D.family = selectedOccurrenceOwnerHullFamily C P R) :
    AdmissibleThickeningInsideOwner C R D
      (selectedOccurrenceActiveParent C R) := by
  intro theta _hthetaLower hthetaUpper q
  have hthetaB : theta * b ≤ rho := by
    calc
      theta * b ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ ≤ rho := hb
  apply cthickening_subset_twoFoldTubeCarrier_of_subset_of_le hrho
    (C.coarse.tubes (selectedOccurrenceActiveParent C R q))
  · rw [hfamily]
    exact selectedOccurrenceOwnerHullFamily_subset_parent C P R q
  · exact hthetaB

#print axioms occurrenceOwnerSubfiber_nonempty
#print axioms occurrenceOwnerSubfiber_parent_eq
#print axioms occurrenceOwnerHull_subset_parent
#print axioms selectedOccurrenceOwnerHullFamily_subset_parent
#print axioms admissibleThickeningInsideOwner_of_ownerHullFamily

end


end Family8SelectedOccurrenceOwnerHullRefinementV2
