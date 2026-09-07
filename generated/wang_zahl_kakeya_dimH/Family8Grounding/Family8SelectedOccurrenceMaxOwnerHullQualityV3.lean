import Family8Grounding.Family8SelectedOccurrenceOwnerHullUniqueOwnerV2
import Mathlib.Tactic

/-!
# Quality-selected actual-owner hull refinement

An arbitrary representative owner can retain arbitrarily little shading.
For each global greedy occurrence, choose a literal fine member of maximal
shaded-carrier volume and use its actual sticky parent.  The full occurrence
carrier is then bounded by the block cardinality times the carrier retained
in that genuine parent-specific subfibre.  This is a constructed finite
argmax, not a mass-retention callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxOwnerHullQualityV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
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
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)
  (Y : Shading fine.bodyFamily)

/-- A fine member of a block whose shaded carrier has maximal volume within
that block. -/
noncomputable def occurrenceMaxShadedWitness
    (k : Fin (blocks fine.bodyFamily P).length) : index :=
  Classical.choose (Finset.exists_max_image
    (blockAt fine.bodyFamily P k).fiber
    (fun i => volume (Y.carrier i))
    (blockAt fine.bodyFamily P k).fiber_nonempty)

theorem occurrenceMaxShadedWitness_mem
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceMaxShadedWitness C P Y k ∈
      (blockAt fine.bodyFamily P k).fiber :=
  (Classical.choose_spec (Finset.exists_max_image
    (blockAt fine.bodyFamily P k).fiber
    (fun i => volume (Y.carrier i))
    (blockAt fine.bodyFamily P k).fiber_nonempty)).1

theorem occurrenceShadedVolume_le_maxWitness
    (k : Fin (blocks fine.bodyFamily P).length)
    (i : index) (hi : i ∈ (blockAt fine.bodyFamily P k).fiber) :
    volume (Y.carrier i) ≤
      volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)) :=
  (Classical.choose_spec (Finset.exists_max_image
    (blockAt fine.bodyFamily P k).fiber
    (fun i => volume (Y.carrier i))
    (blockAt fine.bodyFamily P k).fiber_nonempty)).2 i hi

/-- The actual parent chosen by shaded-carrier quality. -/
noncomputable def occurrenceMaxOwner
    (k : Fin (blocks fine.bodyFamily P).length) : Fin C.coarseCard :=
  C.parent (occurrenceMaxShadedWitness C P Y k)

/-- The part of the global block having the quality-selected actual parent. -/
def occurrenceMaxOwnerSubfiber
    (k : Fin (blocks fine.bodyFamily P).length) : Finset index :=
  (blockAt fine.bodyFamily P k).fiber.filter fun i =>
    C.parent i = occurrenceMaxOwner C P Y k

@[simp] theorem mem_occurrenceMaxOwnerSubfiber
    (k : Fin (blocks fine.bodyFamily P).length) (i : index) :
    i ∈ occurrenceMaxOwnerSubfiber C P Y k ↔
      i ∈ (blockAt fine.bodyFamily P k).fiber ∧
        C.parent i = occurrenceMaxOwner C P Y k := by
  simp [occurrenceMaxOwnerSubfiber]

theorem occurrenceMaxOwnerSubfiber_nonempty
    (k : Fin (blocks fine.bodyFamily P).length) :
    (occurrenceMaxOwnerSubfiber C P Y k).Nonempty := by
  refine ⟨occurrenceMaxShadedWitness C P Y k, ?_⟩
  rw [mem_occurrenceMaxOwnerSubfiber]
  exact ⟨occurrenceMaxShadedWitness_mem C P Y k, rfl⟩

/-- The genuine parent-specific closed convex hull for the quality owner. -/
def occurrenceMaxOwnerHull
    (k : Fin (blocks fine.bodyFamily P).length) : ConvexBody Space :=
  hullContainer fine.bodyFamily (occurrenceMaxOwnerSubfiber C P Y k)

/-- Literal refined shaded carrier: the finite union over the selected actual
parent subfibre. -/
def occurrenceMaxOwnerCarrier
    (k : Fin (blocks fine.bodyFamily P).length) : Set Space :=
  ⋃ i : {i // i ∈ occurrenceMaxOwnerSubfiber C P Y k}, Y.carrier i.1

theorem measurableSet_occurrenceMaxOwnerCarrier
    (k : Fin (blocks fine.bodyFamily P).length) :
    MeasurableSet (occurrenceMaxOwnerCarrier C P Y k) :=
  MeasurableSet.iUnion fun i => Y.measurable_carrier i.1

theorem occurrenceMaxOwnerCarrier_subset_hull
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceMaxOwnerCarrier C P Y k ⊆
      (occurrenceMaxOwnerHull C P Y k : Set Space) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact body_subset_hullContainer fine.bodyFamily i.2
    (occurrenceMaxOwnerSubfiber_nonempty C P Y k)
      (Y.carrier_subset i.1 hxi)

theorem occurrenceMaxOwnerHull_subset_parent
    (k : Fin (blocks fine.bodyFamily P).length) :
    (occurrenceMaxOwnerHull C P Y k : Set Space) ⊆
      (C.coarse.tubes (occurrenceMaxOwner C P Y k)).carrier := by
  have hsubset :
      (hullContainer fine.bodyFamily
          (occurrenceMaxOwnerSubfiber C P Y k) : Set Space) ⊆
        ((C.coarse.tubes (occurrenceMaxOwner C P Y k)).body : Set Space) := by
    apply hullContainer_subset fine.bodyFamily
      (occurrenceMaxOwnerSubfiber_nonempty C P Y k)
    intro i hi
    have hi' := (mem_occurrenceMaxOwnerSubfiber C P Y k i).mp hi
    have hiActive : i ∈ C.activeFine :=
      blockAt_fiber_subset_active fine.bodyFamily P k hi'.1
    have hparent := C.carrier_subset i hiActive
    rw [hi'.2] at hparent
    exact hparent
  exact hsubset

/-- The maximal witness carrier is literally retained in the quality-owner
carrier. -/
theorem maxWitnessCarrier_subset_occurrenceMaxOwnerCarrier
    (k : Fin (blocks fine.bodyFamily P).length) :
    Y.carrier (occurrenceMaxShadedWitness C P Y k) ⊆
      occurrenceMaxOwnerCarrier C P Y k := by
  intro x hx
  refine Set.mem_iUnion.mpr
    ⟨⟨occurrenceMaxShadedWitness C P Y k, ?_⟩, hx⟩
  rw [mem_occurrenceMaxOwnerSubfiber]
  exact ⟨occurrenceMaxShadedWitness_mem C P Y k, rfl⟩

/-- Per occurrence, the old outer shaded carrier loses at most the literal
block cardinality under the quality-owner refinement. -/
theorem occurrenceOuterCarrier_volume_le_card_mul_maxOwnerCarrier
    (k : Fin (blocks fine.bodyFamily P).length) :
    volume (((convexFactorization fine.bodyFamily P).inducedShading Y).carrier
        (some k)) ≤
      (((blockAt fine.bodyFamily P k).fiber.card : Nat) : ENNReal) *
        volume (occurrenceMaxOwnerCarrier C P Y k) := by
  let B := (blockAt fine.bodyFamily P k).fiber
  have hcarrierSubset :
      ((convexFactorization fine.bodyFamily P).inducedShading Y).carrier
          (some k) ⊆ ⋃ i : {i // i ∈ B}, Y.carrier i.1 := by
    intro x hx
    have hx' := (ConvexFactorization.mem_inducedShading_carrier_iff
      (convexFactorization fine.bodyFamily P) Y (some k) x).mp hx
    obtain ⟨i, hiFiber, hxi⟩ := hx'.2
    have hiB : i ∈ B := by
      change i ∈ (indexFactorization fine.bodyFamily P).fiber (some k) at hiFiber
      simpa only [B, indexFactorization_fiber_eq_blockAt] using hiFiber
    exact Set.mem_iUnion.mpr ⟨⟨i, hiB⟩, hxi⟩
  calc
    volume (((convexFactorization fine.bodyFamily P).inducedShading Y).carrier
        (some k)) ≤ volume (⋃ i : {i // i ∈ B}, Y.carrier i.1) :=
      measure_mono hcarrierSubset
    _ ≤ ∑ i : {i // i ∈ B}, volume (Y.carrier i.1) :=
      measure_iUnion_fintype_le volume fun i : {i // i ∈ B} => Y.carrier i.1
    _ = ∑ i ∈ B, volume (Y.carrier i) := by
      symm
      exact Finset.sum_subtype _ (fun _i => Iff.rfl) _
    _ ≤ B.card • volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)) :=
      Finset.sum_le_card_nsmul B (fun i => volume (Y.carrier i))
        (volume (Y.carrier (occurrenceMaxShadedWitness C P Y k)))
        (fun i hi => occurrenceShadedVolume_le_maxWitness C P Y k i hi)
    _ ≤ B.card • volume (occurrenceMaxOwnerCarrier C P Y k) :=
      nsmul_le_nsmul_right
        (measure_mono
          (maxWitnessCarrier_subset_occurrenceMaxOwnerCarrier C P Y k)) B.card
    _ = ((B.card : Nat) : ENNReal) *
        volume (occurrenceMaxOwnerCarrier C P Y k) := by
      simp [nsmul_eq_mul]

#print axioms occurrenceMaxShadedWitness_mem
#print axioms occurrenceShadedVolume_le_maxWitness
#print axioms occurrenceMaxOwnerSubfiber_nonempty
#print axioms occurrenceMaxOwnerCarrier_subset_hull
#print axioms occurrenceMaxOwnerHull_subset_parent
#print axioms occurrenceOuterCarrier_volume_le_card_mul_maxOwnerCarrier

end


end Family8SelectedOccurrenceMaxOwnerHullQualityV3
