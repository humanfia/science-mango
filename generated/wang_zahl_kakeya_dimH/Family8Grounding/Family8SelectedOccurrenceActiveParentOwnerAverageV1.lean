import Family8Grounding.Family8SelectedOccurrenceActiveParentOwnerV15
import Family8Grounding.Family8SelectedOccurrenceAverageRetentionV1
import Mathlib.Tactic

/-!
# Exact average loss for actual-parent occurrence selection

The doubled-conflict-free parent selection retains actual selected-occurrence
shaded mass up to its certified ENNReal loss.  Since its occurrence set is a
literal subset of the input set, the corresponding shaded-union inclusion
transports this to the same loss for average multiplicity.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceActiveParentOwnerAverageV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8SelectedOccurrenceActiveParentOwnerV5
open Family8SelectedOccurrenceDensityFrostmanV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa → ConvexBody Space} {active : Finset iota}

/-- Selected occurrence shaded unions are monotone in the literal occurrence
set. -/
theorem selectedOccurrenceOuterShading_shadedUnion_mono
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F)
    (S T : Finset (Fin (blocks F P).length))
    (hST : S ⊆ T) :
    (selectedOccurrenceOuterShading P Y S).shadedUnion ⊆
      (selectedOccurrenceOuterShading P Y T).shadedUnion := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, hkS, hkq⟩ :=
    (mem_selectedOccurrenceIndices P S q.1).mp q.2
  have hq : q = selectedOccurrenceIndexOf P S k hkS := by
    apply Subtype.ext
    exact hkq.symm
  rw [hq, selectedOccurrenceOuterShading_carrier_indexOf] at hxq
  refine Set.mem_iUnion.mpr
    ⟨selectedOccurrenceIndexOf P T k (hST hkS), ?_⟩
  simpa using hxq

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)

/-- The owner-selected occurrences are a literal subfamily. -/
theorem occurrencesOwnedBy_subset
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard)) :
    occurrencesOwnedBy C P R B ⊆ R := by
  intro k hk
  exact (mem_occurrencesOwnedBy C P R B k).mp hk |>.1

/-- The exact mass-selection loss also transports the selected outer average
from `R` to the actual-owner subfamily. -/
theorem selectedOwner_occurrenceAverage_retention
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMassByActiveParent C P Y R) loss) :
    (selectedOccurrenceOuterShading P Y R).averageMultiplicity ≤
      loss * (selectedOccurrenceOuterShading P Y
        (occurrencesOwnedBy C P R W.selected)).averageMultiplicity := by
  have hmass := selectedOwner_occurrenceShadedMass_retention C P Y R loss W
  have hunion := selectedOccurrenceOuterShading_shadedUnion_mono P Y
    (occurrencesOwnedBy C P R W.selected) R
      (occurrencesOwnedBy_subset C P R W.selected)
  unfold Shading.averageMultiplicity
  calc
    (selectedOccurrenceOuterShading P Y R).shadingMass /
          volume (selectedOccurrenceOuterShading P Y R).shadedUnion ≤
        (loss * (selectedOccurrenceOuterShading P Y
          (occurrencesOwnedBy C P R W.selected)).shadingMass) /
          volume (selectedOccurrenceOuterShading P Y R).shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ (loss * (selectedOccurrenceOuterShading P Y
          (occurrencesOwnedBy C P R W.selected)).shadingMass) /
          volume (selectedOccurrenceOuterShading P Y
            (occurrencesOwnedBy C P R W.selected)).shadedUnion := by
      exact ENNReal.div_le_div_left (measure_mono hunion) _
    _ = loss *
          ((selectedOccurrenceOuterShading P Y
              (occurrencesOwnedBy C P R W.selected)).shadingMass /
            volume (selectedOccurrenceOuterShading P Y
              (occurrencesOwnedBy C P R W.selected)).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms selectedOccurrenceOuterShading_shadedUnion_mono
#print axioms occurrencesOwnedBy_subset
#print axioms selectedOwner_occurrenceAverage_retention

end


end Family8SelectedOccurrenceActiveParentOwnerAverageV1
