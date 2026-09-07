import Family8Grounding.Family8DoubledParentConflictExactDegreeBudgetV1
import Family8Grounding.Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
import Mathlib.Tactic

/-!
# Actual canonical selected input for Equation (45)

The common-scale constructor was previously never instantiated.  This module
builds its literal upper-cover input: the doubled-parent selection uses the
exact finite conflict degree, and the fibre cap is the actual active-parent
index cardinality.  Consequently the conflict loss, selected witness count,
and fibre cap all have the same automatic finite envelope.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictExactDegreeBudgetV1.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (S : StickyScaleCover fine rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  (Y : Shading S.activeCoarseFamily)

/-- The actual upper cover is active on every lower active-parent index. -/
theorem actualUpperCover_activeFine_eq_univ :
    U.activeFine = (Finset.univ : Finset (ActiveParentIndex S)) := by
  calc
    U.activeFine =
        (S.coarse.restrictTo S.activeCoarse).refinement.refined :=
      U.activeFine_eq_refined
    _ = Finset.univ := S.coarse.restrictTo_refined S.activeCoarse

/-- The upper greedy partition, transported along the literal all-active equality. -/
noncomputable def actualUpperPartition :
    GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates U.activeFine)
      (hullContainer S.activeCoarseFamily) U.activeFine := by
  simpa only [actualUpperCover_activeFine_eq_univ S U] using P

/-- The literal finite loss used for the canonical Eq. (45) conflict
selection on the upper cover. -/
noncomputable def canonicalEq45ConflictLoss : ENNReal :=
  doubledParentConflictExactDegreeBudget U

/-- Callback-free largest-mass selection at the exact doubled-parent degree. -/
noncomputable def canonicalEq45ConflictSelection :
    DoubledParentConflictWeightedSelection U
      (occurrenceMaxOwnerMass U (actualUpperPartition S U P)
        Y Finset.univ)
      (canonicalEq45ConflictLoss S U) :=
  Classical.choice
    (exists_doubledParentConflictWeightedSelection_exactDegree U
      (occurrenceMaxOwnerMass U (actualUpperPartition S U P)
        Y Finset.univ))

/-- The active-parent cardinality is a valid cap for every greedy block
fibre of the upper partition. -/
theorem actualUpperPartition_block_fibre_card_le_activeParentCard
    (k : Fin (blocks S.activeCoarseFamily
      (actualUpperPartition S U P)).length) :
    (blockAt S.activeCoarseFamily (actualUpperPartition S U P) k).fiber.card ≤
      Fintype.card (ActiveParentIndex S) := by
  exact Finset.card_le_univ _

/-- Surjectivity of the upper parent map bounds its active coarse set. -/
theorem upper_activeCoarse_card_le_activeFine_card :
    U.activeCoarse.card ≤ U.activeFine.card := by
  let parent : {i // i ∈ U.activeFine} → {k // k ∈ U.activeCoarse} :=
    fun i => ⟨U.parent i.1, U.parent_mem i.1 i.2⟩
  have hsurj : Function.Surjective parent := by
    intro k
    obtain ⟨i, hi, hparent⟩ := U.parent_surjective k.1 k.2
    refine ⟨⟨i, hi⟩, ?_⟩
    apply Subtype.ext
    exact hparent
  have hcard := Fintype.card_le_of_surjective parent hsurj
  simpa only [Fintype.card_coe] using hcard

/-- The exact conflict-degree loss is bounded by the same active-parent
cardinality: active upper parents inject through their assigned fine parents. -/
theorem canonicalEq45ConflictLoss_le_activeParentCard :
    canonicalEq45ConflictLoss S U ≤
      (Fintype.card (ActiveParentIndex S) : ENNReal) := by
  calc
    canonicalEq45ConflictLoss S U ≤ (U.activeCoarse.card : ENNReal) :=
      exactDegreeBudget_le_activeCoarse_card U
    _ ≤ (U.activeFine.card : ENNReal) := by
      exact_mod_cast upper_activeCoarse_card_le_activeFine_card S U
    _ ≤ (Fintype.card (ActiveParentIndex S) : ENNReal) := by
      exact_mod_cast Finset.card_le_univ U.activeFine

/-- The actual common-witness family chosen below has at most one member per
active parent. -/
theorem canonicalEq45SelectedWitness_card_le_activeParentCard :
    Fintype.card {q // q ∈ selectedOccurrenceIndices
      (actualUpperPartition S U P)
      (occurrencesMaxOwnedBy U (actualUpperPartition S U P) Y Finset.univ
        (canonicalEq45ConflictSelection S U P Y).selected)} ≤
      Fintype.card (ActiveParentIndex S) := by
  let R := occurrencesMaxOwnedBy U (actualUpperPartition S U P) Y Finset.univ
    (canonicalEq45ConflictSelection S U P Y).selected
  exact Fintype.card_le_of_injective
    (fun q : {q // q ∈ selectedOccurrenceIndices (actualUpperPartition S U P) R} ↦
      occurrenceMaxShadedWitness U (actualUpperPartition S U P) Y
        (selectedOccurrencePosition U R q))
    (selectedOccurrenceMaxWitness_injective U Y R)

#print axioms actualUpperCover_activeFine_eq_univ
#print axioms actualUpperPartition
#print axioms canonicalEq45ConflictSelection
#print axioms actualUpperPartition_block_fibre_card_le_activeParentCard
#print axioms canonicalEq45ConflictLoss_le_activeParentCard
#print axioms canonicalEq45SelectedWitness_card_le_activeParentCard

end
end Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
