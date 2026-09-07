import Family8Grounding.Family8BufferedCommonScaleTubePlankV1
import Family8Grounding.Family8SelectedOccurrenceMaxWitnessCommonScaleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8BufferedCommonScaleTubePlankV1
open Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

abbrev selectedOccurrenceMaxWitnessBufferedFamily
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P R} :=
  affineImageFamily (bufferedCommonScaleEquiv delta)
    (selectedOccurrenceMaxWitnessFamily C Y R)

def selectedOccurrenceMaxWitnessBufferedShading
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Shading (selectedOccurrenceMaxWitnessBufferedFamily C Y R) :=
  affineImageShading (bufferedCommonScaleEquiv delta)
    (selectedOccurrenceMaxWitnessShading C Y R)

@[simp] theorem selectedOccurrenceMaxWitnessBufferedFamily_apply
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    selectedOccurrenceMaxWitnessBufferedFamily C Y R q =
      bufferedCommonScaleTubeBody
        (fine.tubes (occurrenceMaxShadedWitness C P Y
          (selectedOccurrencePosition C R q))) := rfl

theorem selectedOccurrenceMaxWitnessBuffered_all_isPlank
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    IsPlank 16 (bufferedCommonWidth delta) (bufferedCommonWidth delta)
      (selectedOccurrenceMaxWitnessBufferedFamily C Y R q) := by
  rw [selectedOccurrenceMaxWitnessBufferedFamily_apply]
  exact bufferedCommonScaleTube_isPlank _ hdelta hdeltaHalf

theorem selectedOccurrenceMaxWitnessBuffered_averageMultiplicity
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceMaxWitnessBufferedShading C Y R).averageMultiplicity =
      (selectedOccurrenceMaxWitnessShading C Y R).averageMultiplicity :=
  affineImageShading_averageMultiplicity (bufferedCommonScaleEquiv delta)
    (selectedOccurrenceMaxWitnessShading C Y R)

theorem selectedOccurrenceMaxWitnessBuffered_isFrostmanIn
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (ambient : ConvexBody Space) {CF : ENNReal}
    (hsource : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P R) ambient)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsFrostmanIn (CF * (16 * (M : ENNReal)))
      (selectedOccurrenceMaxWitnessBufferedFamily C Y R)
      (affineImageConvexBody (bufferedCommonScaleEquiv delta) ambient) := by
  apply IsFrostmanIn.affineImage (bufferedCommonScaleEquiv delta)
  exact selectedOccurrenceMaxWitness_isFrostmanIn C Y R M hcard ambient
    hsource hdeltaHalf

def selectedOccurrenceMaxWitnessBufferedDatum
    (Y : Shading fine.bodyFamily)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody (bufferedCommonScaleEquiv delta) ambient))
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceMaxWitnessFamily C Y R q : Set Space) ⊆
        (ambient : Set Space)) :
    ShadedConvexPlankFamily {q // q ∈ selectedOccurrenceIndices P R}
      (bufferedCommonWidth delta) (bufferedCommonWidth delta) where
  family := selectedOccurrenceMaxWitnessBufferedFamily C Y R
  shading := selectedOccurrenceMaxWitnessBufferedShading C Y R
  comparisonConstant := 16
  all_isPlank := selectedOccurrenceMaxWitnessBuffered_all_isPlank
    C Y R hdelta hdeltaHalf
  ambient := affineImageConvexBody (bufferedCommonScaleEquiv delta) ambient
  ambientComparisonConstant := ambientComparisonConstant
  ambient_is_unit_scale := ambient_is_unit_scale
  contained_in_ambient q := Set.image_mono (contained_in_ambient q)

theorem selectedOccurrenceOuter_average_le_card_conflict_card_mul_buffered
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (M : Nat)
    (hcard : ∀ k ∈ R0, (blockAt fine.bodyFamily P k).fiber.card ≤ M) :
    (selectedOccurrenceOuterShading P Y R0).averageMultiplicity ≤
      (((M : ENNReal) * loss) * (M : ENNReal)) *
        (selectedOccurrenceMaxWitnessBufferedShading C Y
          (occurrencesMaxOwnedBy C P Y R0 W.selected)).averageMultiplicity := by
  let R := occurrencesMaxOwnedBy C P Y R0 W.selected
  have h := selectedOccurrenceOuter_average_le_card_conflict_card_mul_witness
    C Y R0 loss W M hcard
  rw [selectedOccurrenceMaxWitnessCommonScale_averageMultiplicity] at h
  rw [selectedOccurrenceMaxWitnessBuffered_averageMultiplicity]
  exact h

#print axioms selectedOccurrenceMaxWitnessBuffered_all_isPlank
#print axioms selectedOccurrenceMaxWitnessBuffered_isFrostmanIn
#print axioms selectedOccurrenceMaxWitnessBufferedDatum
#print axioms selectedOccurrenceOuter_average_le_card_conflict_card_mul_buffered

end
end Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleDatumV1
