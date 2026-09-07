import Family8Grounding.Family8GreedyHighPrefixSameOccurrenceWeightedMassV1

/-!
# Cardinality of occupied certified high occurrences

The occupied labels are the image of the selected source subtype under the
chosen-occurrence map.  Thus their literal cardinality costs at most the
number of selected source indices, which in turn is at most the ambient
finite index cardinality.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8GreedyHighPrefixSameOccurrenceOccupiedCardV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8GreedyHighPrefixSameOccurrenceWeightedMassV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Only labels hit by the selected source subtype are charged. -/
theorem occupiedCertifiedHighOccurrences_card_le_selected
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q) :
    (occupiedCertifiedHighOccurrences D P A selected hcover).card <=
      selected.card := by
  classical
  calc
    (occupiedCertifiedHighOccurrences D P A selected hcover).card <=
        (Finset.univ : Finset {i // i ∈ selected}).card := by
      rw [occupiedCertifiedHighOccurrences]
      exact Finset.card_image_le
    _ = selected.card := by simp

/-- The occupied-label loss is also bounded by the original ambient source
cardinality, through the same selected set and without extra hypotheses. -/
theorem occupiedCertifiedHighOccurrences_card_le_fintypeCard
    (D : ActualTubeDatum delta index)
    (P : GreedyDensityPartition D.family.bodyFamily
      (hullCandidates (Finset.univ : Finset index))
      (hullContainer D.family.bodyFamily) Finset.univ)
    (A : ENNReal) (selected : Finset index)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks D.family.bodyFamily P).length,
        i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
        ActualHighConcentrationOccurrence D P A q) :
    (occupiedCertifiedHighOccurrences D P A selected hcover).card <=
      Fintype.card index := by
  exact (occupiedCertifiedHighOccurrences_card_le_selected
    D P A selected hcover).trans (Finset.card_le_univ selected)

#print axioms occupiedCertifiedHighOccurrences_card_le_selected
#print axioms occupiedCertifiedHighOccurrences_card_le_fintypeCard

end
end Family8GreedyHighPrefixSameOccurrenceOccupiedCardV1
