import Family8Grounding.Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1

/-!
# Selected mass as a sum over occupied same-core occurrences

This file exposes the exact finite partition identity already used internally
by the same-core weighted-pigeonhole proof.  Each selected index is assigned
to its chosen occupied greedy occurrence, and the mass of that fibre is the
literal mass of `sameCoreOccurrenceBlockShading`.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8RestrictedSelectedMassOccupiedSameCoreSumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The restricted selected shading mass is partitioned exactly by the
occupied chosen occurrence labels. -/
theorem restrictActualTubeDatum_shadingMass_eq_sum_occupied_sameCoreOccurrenceBlockShading
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : forall i, i ∈ selected ->
      exists q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber /\
        CoreHighConcentrationOccurrence D P A q) :
    (restrictActualTubeDatum D selected).shading.shadingMass =
      ∑ q ∈ occupiedCoreHighOccurrences D P A selected hcover,
        (sameCoreOccurrenceBlockShading
          D P A selected hcover q).shadingMass := by
  classical
  have hmaps : ∀ i ∈ (Finset.univ : Finset {i // i ∈ selected}),
      chosenCoreHighOccurrence D P A selected hcover i ∈
        occupiedCoreHighOccurrences D P A selected hcover := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hpartition :
      (∑ i ∈ (Finset.univ : Finset {i // i ∈ selected}),
          volume (D.shading.carrier i.1)) =
        ∑ q ∈ occupiedCoreHighOccurrences D P A selected hcover,
          ∑ i ∈ dyadicFiber
              (Finset.univ : Finset {i // i ∈ selected})
              (chosenCoreHighOccurrence D P A selected hcover) q,
            volume (D.shading.carrier i.1) := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset {i // i ∈ selected}))
      (t := occupiedCoreHighOccurrences D P A selected hcover)
      (g := chosenCoreHighOccurrence D P A selected hcover)
      hmaps (fun i => volume (D.shading.carrier i.1))).symm
  have hselectedMass :
      (restrictActualTubeDatum D selected).shading.shadingMass =
        ∑ i ∈ (Finset.univ : Finset {i // i ∈ selected}),
          volume (D.shading.carrier i.1) := by
    rw [restrictActualTubeDatum_shadingMass]
    exact (Finset.sum_attach selected
      (fun i => volume (D.shading.carrier i))).symm
  rw [hselectedMass, hpartition]
  apply Finset.sum_congr rfl
  intro q hq
  exact (sameCoreOccurrenceBlockShading_mass_eq
    D P A selected hcover q).symm

#print axioms
  restrictActualTubeDatum_shadingMass_eq_sum_occupied_sameCoreOccurrenceBlockShading

end

end Family8RestrictedSelectedMassOccupiedSameCoreSumV1
