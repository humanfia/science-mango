import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
import Mathlib.Tactic

/-!
# Average retention for the genuine quality-owner refinement

The refined owner selection retains exact mass and has a smaller shaded
union.  Together with finite-argmax refinement this gives the explicit
average loss `fibreCardCap * conflictLoss`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxOwnerAverageRetentionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
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
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)
  (Y : Shading fine.bodyFamily)

/-- Refined quality-owner shaded unions are monotone in the occurrence set. -/
theorem selectedOccurrenceMaxOwnerHullShading_shadedUnion_mono
    (S T : Finset (Fin (blocks fine.bodyFamily P).length))
    (hST : S ⊆ T) :
    (selectedOccurrenceMaxOwnerHullShading C P Y S).shadedUnion ⊆
      (selectedOccurrenceMaxOwnerHullShading C P Y T).shadedUnion := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  let k := selectedOccurrencePosition C S q
  have hkS : k ∈ S := selectedOccurrencePosition_mem C S q
  have hxk : x ∈ occurrenceMaxOwnerCarrier C P Y k := by
    exact hxq
  let qT := selectedOccurrenceIndexOf P T k (hST hkS)
  refine Set.mem_iUnion.mpr ⟨qT, ?_⟩
  have hposT : selectedOccurrencePosition C T qT = k :=
    Option.some.inj (some_selectedOccurrencePosition_eq C T qT)
  change x ∈ occurrenceMaxOwnerCarrier C P Y
    (selectedOccurrencePosition C T qT)
  rw [hposT]
  exact hxk

/-- Max-owner-selected occurrences form a literal subfamily. -/
theorem occurrencesMaxOwnedBy_subset
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (B : Finset (Fin C.coarseCard)) :
    occurrencesMaxOwnedBy C P Y R B ⊆ R := by
  intro k hk
  exact (mem_occurrencesMaxOwnedBy C P Y R B k).mp hk |>.1

/-- Exact refined mass retention gives the same average conflict loss. -/
theorem selectedMaxOwner_refinedAverage_retention
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R) loss) :
    (selectedOccurrenceMaxOwnerHullShading C P Y R).averageMultiplicity ≤
      loss * (selectedOccurrenceMaxOwnerHullShading C P Y
        (occurrencesMaxOwnedBy C P Y R W.selected)).averageMultiplicity := by
  have hmass := selectedMaxOwner_refinedShadedMass_retention C P Y R loss W
  have hunion := selectedOccurrenceMaxOwnerHullShading_shadedUnion_mono
    C P Y (occurrencesMaxOwnedBy C P Y R W.selected) R
      (occurrencesMaxOwnedBy_subset C P Y R W.selected)
  unfold Shading.averageMultiplicity
  calc
    (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass /
          volume (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion ≤
        (loss * (selectedOccurrenceMaxOwnerHullShading C P Y
          (occurrencesMaxOwnedBy C P Y R W.selected)).shadingMass) /
          volume (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ (loss * (selectedOccurrenceMaxOwnerHullShading C P Y
          (occurrencesMaxOwnedBy C P Y R W.selected)).shadingMass) /
          volume (selectedOccurrenceMaxOwnerHullShading C P Y
            (occurrencesMaxOwnedBy C P Y R W.selected)).shadedUnion := by
      exact ENNReal.div_le_div_left (measure_mono hunion) _
    _ = loss *
          ((selectedOccurrenceMaxOwnerHullShading C P Y
              (occurrencesMaxOwnedBy C P Y R W.selected)).shadingMass /
            volume (selectedOccurrenceMaxOwnerHullShading C P Y
              (occurrencesMaxOwnedBy C P Y R W.selected)).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Complete loss from old selected shading to the genuine max-owner hull
shading: literal fibre-card cap times conflict-selection loss. -/
theorem selectedOccurrenceOuterShading_average_le_card_mul_conflict_mul_maxOwner
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R) loss) :
    (selectedOccurrenceOuterShading P Y R).averageMultiplicity ≤
      ((M : ENNReal) * loss) *
        (selectedOccurrenceMaxOwnerHullShading C P Y
          (occurrencesMaxOwnedBy C P Y R W.selected)).averageMultiplicity := by
  have hrefined := selectedMaxOwner_refinedAverage_retention C P Y R loss W
  calc
    (selectedOccurrenceOuterShading P Y R).averageMultiplicity ≤
        (M : ENNReal) *
          (selectedOccurrenceMaxOwnerHullShading C P Y R).averageMultiplicity :=
      selectedOccurrenceOuterShading_average_le_maxOwnerHull C P Y R M hcard
    _ ≤ (M : ENNReal) *
        (loss * (selectedOccurrenceMaxOwnerHullShading C P Y
          (occurrencesMaxOwnedBy C P Y R W.selected)).averageMultiplicity) := by
      gcongr
    _ = ((M : ENNReal) * loss) *
        (selectedOccurrenceMaxOwnerHullShading C P Y
          (occurrencesMaxOwnedBy C P Y R W.selected)).averageMultiplicity := by
      ac_rfl

#print axioms selectedOccurrenceMaxOwnerHullShading_shadedUnion_mono
#print axioms occurrencesMaxOwnedBy_subset
#print axioms selectedMaxOwner_refinedAverage_retention
#print axioms selectedOccurrenceOuterShading_average_le_card_mul_conflict_mul_maxOwner

end

end Family8SelectedOccurrenceMaxOwnerAverageRetentionV3
