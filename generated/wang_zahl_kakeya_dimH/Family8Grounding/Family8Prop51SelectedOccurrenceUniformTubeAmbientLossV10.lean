import Family8Grounding.Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8

/-!
# Active-cardinality-explicit selected source Frostman certificate

The canonical selected source pays only the number of tubes in the actual
active family, rather than the cardinality of the ambient index type.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV10

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceAverageRetentionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8Prop51SelectedOccurrenceAmbientMassRatioV1
open Family8Prop51SelectedOccurrenceAmbientMassPositiveV2
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {delta : NNReal} {index kappa : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset index}

theorem prop51SelectedOccurrences_source_fine_frostman_activeCardinality
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (Y : Shading fine.bodyFamily) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C fine.bodyFamily active K)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    IsFrostmanOn
      (C * max 1 (16 * (active.card : ENNReal)))
      fine.bodyFamily (prop51SelectedFineIndices P Y base M) K := by
  have hselectedContained : ∀ i ∈ prop51SelectedFineIndices P Y base M,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := by
    intro i hi
    exact hglobal.1 i
      (selectedOccurrenceFineIndices_subset_active P
        (prop51SelectedOccurrences P Y base M) hi)
  have hcanonical :=
    prop51SelectedOccurrences_source_fine_frostman_canonical
      P Y base M K hglobal hfull hselectedContained
  exact hcanonical.mono (mul_le_mul' le_rfl
    (prop51SelectedAmbientMassLoss_le_max_activeCardinality
      P Y base M K hglobal hfull hdeltaHalf))

#print axioms prop51SelectedOccurrences_source_fine_frostman_activeCardinality

end
end Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV10
