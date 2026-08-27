import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeMassBlockProducerV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualGPrimeMassBudgetNumericsV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeMassBlockProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u v w

/-!
# Readable numerical sufficient conditions for the actual G-prime mass block

The source budget in the preceding module contains the cardinality of the
coarse rectangle image.  That image has at most as many elements as the fine
label source.  Consequently, for a nonempty fine-label family, it is enough
that one active fibre pays for one rich block, one selected degree block, and
the logarithmic bucket loss.  This module records that paper-facing scalar
condition and its active-degree and E2 consequences.
-/

/-- The assigned coarse rectangles form an image of the fine labels. -/
theorem coarseRectangleFamily_card_le_fineLabels_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel) :
    D.coarseRectangleFamily.card <= D.fineLabels.card := by
  classical
  unfold CoarseRectangleIncidenceData.coarseRectangleFamily
  exact Finset.card_image_le

/-- A single readable degree-dominance inequality implies the full source
mass budget.  Nonemptiness is needed only to charge the final isolated degree
block to one copy of the fine-label family. -/
theorem activeDegreeRichRetainedMassBudget_of_dominance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (activeDegreeLower richness degreeUpper : Nat)
    (hfine : D.fineLabels.Nonempty)
    (hdominance : coarseDegreeBucketLoss D *
      ((richness + 1) * degreeUpper) <= activeDegreeLower) :
    ActiveDegreeRichRetainedMassBudget D activeDegreeLower richness
      degreeUpper := by
  have hcoarse : D.coarseRectangleFamily.card <= D.fineLabels.card :=
    coarseRectangleFamily_card_le_fineLabels_card D
  have hone : 1 <= D.fineLabels.card := Finset.one_le_card.mpr hfine
  have hrect :
      D.coarseRectangleFamily.card * (richness * degreeUpper) <=
        D.fineLabels.card * (richness * degreeUpper) :=
    Nat.mul_le_mul_right _ hcoarse
  have hdegree : degreeUpper <= D.fineLabels.card * degreeUpper := by
    calc
      degreeUpper = 1 * degreeUpper := by simp
      _ <= D.fineLabels.card * degreeUpper :=
        Nat.mul_le_mul_right degreeUpper hone
  unfold ActiveDegreeRichRetainedMassBudget
  calc
    coarseDegreeBucketLoss D *
          (D.coarseRectangleFamily.card * (richness * degreeUpper) +
            degreeUpper) <=
        coarseDegreeBucketLoss D *
          (D.fineLabels.card * (richness * degreeUpper) +
            D.fineLabels.card * degreeUpper) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hrect hdegree)
    _ = D.fineLabels.card *
        (coarseDegreeBucketLoss D *
          ((richness + 1) * degreeUpper)) := by ring
    _ <= D.fineLabels.card * activeDegreeLower :=
      Nat.mul_le_mul_left _ hdominance

/-- Active-degree form with no opaque mass-budget callback. -/
theorem degreeUpper_le_automaticRichRetainedMassLower_of_activeDegreeDominance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (activeDegreeLower richness degreeUpper : Nat)
    (hfine : D.fineLabels.Nonempty)
    (hactiveDegree : forall r, r ∈ D.fineLabels ->
      activeDegreeLower <=
        (D.shading.activeAtPoint (D.pointAt r)).card)
    (hdominance : coarseDegreeBucketLoss D *
      ((richness + 1) * degreeUpper) <= activeDegreeLower) :
    degreeUpper <=
      automaticRichRetainedMassLower D richness degreeUpper := by
  exact
    degreeUpper_le_automaticRichRetainedMassLower_of_activeDegreeBudget D
      activeDegreeLower richness degreeUpper hactiveDegree
      (activeDegreeRichRetainedMassBudget_of_dominance D activeDegreeLower
        richness degreeUpper hfine hdominance)

/-- E2-cell form of the same readable condition. -/
theorem degreeUpper_le_automaticRichRetainedMassLower_of_E2Dominance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (label : Int) (richness degreeUpper : Nat)
    (hfine : D.fineLabels.Nonempty)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hdominance : coarseDegreeBucketLoss D *
      ((richness + 1) * degreeUpper) <= pyzE2DegreeLower label) :
    degreeUpper <=
      automaticRichRetainedMassLower D richness degreeUpper := by
  exact degreeUpper_le_automaticRichRetainedMassLower_of_E2Budget D label
    richness degreeUpper hcell hactive
    (activeDegreeRichRetainedMassBudget_of_dominance D
      (pyzE2DegreeLower label) richness degreeUpper hfine hdominance)

/-- Positivity of the canonical separated-pair lower bound from a literal
active-degree lower bound and one scalar dominance inequality. -/
theorem automatic_bucket_separatedPairLower_pos_of_activeDegreeDominance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket activeDegreeLower : Nat)
    (hbasePos : 0 < comparableBase bucket)
    (hfine : D.fineLabels.Nonempty)
    (hactiveDegree : forall r, r ∈ D.fineLabels ->
      activeDegreeLower <=
        (D.shading.activeAtPoint (D.pointAt r)).card)
    (hdominance : coarseDegreeBucketLoss D *
      ((automaticCanonicalRichness N ballRadius + 1) *
        (2 * comparableBase bucket)) <= activeDegreeLower) :
    0 < canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket) := by
  apply automatic_bucket_separatedPairLower_pos_of_activeDegreeBudget
    N D ballRadius bucket activeDegreeLower hbasePos hactiveDegree
  exact activeDegreeRichRetainedMassBudget_of_dominance D activeDegreeLower
    (automaticCanonicalRichness N ballRadius) (2 * comparableBase bucket)
    hfine hdominance

#print axioms coarseRectangleFamily_card_le_fineLabels_card
#print axioms activeDegreeRichRetainedMassBudget_of_dominance
#print axioms degreeUpper_le_automaticRichRetainedMassLower_of_activeDegreeDominance
#print axioms degreeUpper_le_automaticRichRetainedMassLower_of_E2Dominance
#print axioms automatic_bucket_separatedPairLower_pos_of_activeDegreeDominance

end

end FamilyStickyCinematicL32Prop41ActualGPrimeMassBudgetNumericsV1
