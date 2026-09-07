import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV5
import Mathlib.Tactic

/-!
# The actual parent on the exact selected-occurrence subtype

This successor decodes the `Option`-valued selected coarse index back to its
literal greedy position, and transports the active parent and a genuine fine
witness to the exact selected outer family used by Equation (45).
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceActiveParentOwnerV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceDensityFrostmanV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- Decode the literal greedy position carried by a selected occurrence. -/
noncomputable def selectedOccurrencePosition
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    Fin (blocks fine.bodyFamily P).length :=
  Classical.choose ((mem_selectedOccurrenceIndices P R q.1).mp q.2)

theorem selectedOccurrencePosition_mem
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    selectedOccurrencePosition C R q ∈ R :=
  (Classical.choose_spec
    ((mem_selectedOccurrenceIndices P R q.1).mp q.2)).1

theorem some_selectedOccurrencePosition_eq
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    some (selectedOccurrencePosition C R q) = q.1 :=
  (Classical.choose_spec
    ((mem_selectedOccurrenceIndices P R q.1).mp q.2)).2

theorem selectedOccurrence_eq_indexOf
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    q = selectedOccurrenceIndexOf P R (selectedOccurrencePosition C R q)
      (selectedOccurrencePosition_mem C R q) := by
  apply Subtype.ext
  exact (some_selectedOccurrencePosition_eq C R q).symm

/-- The actual active `T_rho` owner on the exact selected-occurrence type. -/
noncomputable def selectedOccurrenceActiveParent
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) : Fin C.coarseCard :=
  occurrenceActiveParent C P (selectedOccurrencePosition C R q)

theorem selectedOccurrenceActiveParent_mem_activeCoarse
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    selectedOccurrenceActiveParent C R q ∈ C.activeCoarse :=
  occurrenceActiveParent_mem_activeCoarse C P _

/-- The literal fine witness of a selected occurrence is contained in its
actual winning-hull body. -/
theorem selectedOccurrenceFineWitness_carrier_subset_body
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    (fine.tubes (occurrenceFineWitness C P
      (selectedOccurrencePosition C R q))).carrier ⊆
      (selectedOccurrenceOuterFamily P R q : Set Space) := by
  let k := selectedOccurrencePosition C R q
  have hk : k ∈ R := selectedOccurrencePosition_mem C R q
  have hq : q = selectedOccurrenceIndexOf P R k hk := by
    simpa only [k] using selectedOccurrence_eq_indexOf C R q
  have hfamily : selectedOccurrenceOuterFamily P R q =
      (blockAt fine.bodyFamily P k).body := by
    rw [hq]
    exact selectedOccurrenceOuterFamily_indexOf P R k hk
  change (fine.tubes (occurrenceFineWitness C P k)).carrier ⊆
    (selectedOccurrenceOuterFamily P R q : Set Space)
  rw [hfamily]
  exact (blockAt fine.bodyFamily P k).contained _
    (occurrenceFineWitness_mem C P k)

/-- Parent-purity specializes to every fine source member of an exact
selected occurrence. -/
theorem parent_eq_selectedOccurrenceActiveParent_of_mem
    (hpure : ParentPure C P)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R})
    (i : index)
    (hi : i ∈ (blockAt fine.bodyFamily P
      (selectedOccurrencePosition C R q)).fiber) :
    C.parent i = selectedOccurrenceActiveParent C R q :=
  hpure _ i hi

#print axioms selectedOccurrencePosition_mem
#print axioms selectedOccurrence_eq_indexOf
#print axioms selectedOccurrenceActiveParent_mem_activeCoarse
#print axioms selectedOccurrenceFineWitness_carrier_subset_body
#print axioms parent_eq_selectedOccurrenceActiveParent_of_mem

end

end Family8SelectedOccurrenceActiveParentOwnerV7
