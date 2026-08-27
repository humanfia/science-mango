import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualGPrimeMassBlockProducerV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

noncomputable section

universe u v w

/-!
# Source-mass budgets for the actual G-prime block

The positive separated-pair endpoint needs one complete selected degree
block to survive the rich/poor rectangle subtraction.  This module rewrites
that residual condition as a source-side budget.  It also connects the
budget to the actual active-degree and E2 degree lower bounds already
present in the incidence data pipeline.
-/

/-- The logarithmic bucket count is always positive. -/
theorem coarseDegreeBucketLoss_pos
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel) :
    0 < coarseDegreeBucketLoss D := by
  unfold coarseDegreeBucketLoss
  omega

/-- A source budget that pays for every poor rectangle and leaves one full
degree block after logarithmic bucket selection. -/
def AutomaticRichRetainedMassBudget
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (richness degreeUpper : Nat) : Prop :=
  coarseDegreeBucketLoss D *
      (D.coarseRectangleFamily.card * (richness * degreeUpper) +
        degreeUpper) <= D.goodPairs.card

/-- The source budget implies the exact full-block condition consumed by
the positive separated-pair producer. -/
theorem degreeUpper_le_automaticRichRetainedMassLower_of_budget
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (richness degreeUpper : Nat)
    (hbudget : AutomaticRichRetainedMassBudget D richness degreeUpper) :
    degreeUpper <=
      automaticRichRetainedMassLower D richness degreeUpper := by
  have hsum :
      D.coarseRectangleFamily.card * (richness * degreeUpper) +
          degreeUpper <=
        D.goodPairs.card / coarseDegreeBucketLoss D := by
    rw [Nat.le_div_iff_mul_le (coarseDegreeBucketLoss_pos D)]
    rw [Nat.mul_comm]
    exact hbudget
  unfold automaticRichRetainedMassLower
  omega

/-- The same budget expressed at a uniform active-degree lower bound. -/
def ActiveDegreeRichRetainedMassBudget
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (activeDegreeLower richness degreeUpper : Nat) : Prop :=
  coarseDegreeBucketLoss D *
      (D.coarseRectangleFamily.card * (richness * degreeUpper) +
        degreeUpper) <= D.fineLabels.card * activeDegreeLower

/-- A literal active-degree lower bound transports the active source budget
to the retained-mass full-block condition. -/
theorem degreeUpper_le_automaticRichRetainedMassLower_of_activeDegreeBudget
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (activeDegreeLower richness degreeUpper : Nat)
    (hactiveDegree : forall r, r ∈ D.fineLabels ->
      activeDegreeLower <=
        (D.shading.activeAtPoint (D.pointAt r)).card)
    (hbudget : ActiveDegreeRichRetainedMassBudget D activeDegreeLower
      richness degreeUpper) :
    degreeUpper <=
      automaticRichRetainedMassLower D richness degreeUpper := by
  apply degreeUpper_le_automaticRichRetainedMassLower_of_budget
  unfold AutomaticRichRetainedMassBudget
  exact hbudget.trans
    (fineLabels_mul_activeDegreeLower_le_goodPairs_card D activeDegreeLower
      hactiveDegree)

/-- An E2 dyadic cell supplies the active-degree lower bound used above. -/
theorem degreeUpper_le_automaticRichRetainedMassLower_of_E2Budget
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (label : Int) (richness degreeUpper : Nat)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hbudget : ActiveDegreeRichRetainedMassBudget D
      (pyzE2DegreeLower label) richness degreeUpper) :
    degreeUpper <=
      automaticRichRetainedMassLower D richness degreeUpper := by
  apply degreeUpper_le_automaticRichRetainedMassLower_of_budget
  unfold AutomaticRichRetainedMassBudget
  exact hbudget.trans
    (fineLabels_mul_pyzE2DegreeLower_le_goodPairs_card D label hcell hactive)

/-- Source-budget form of positivity for the automatic G-prime separated
pair lower bound. -/
theorem automatic_bucket_separatedPairLower_pos_of_budget
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (hbasePos : 0 < comparableBase bucket)
    (hbudget : AutomaticRichRetainedMassBudget D
      (automaticCanonicalRichness N ballRadius)
      (2 * comparableBase bucket)) :
    0 < canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket) := by
  apply automatic_bucket_separatedPairLower_pos N D ballRadius bucket
    hbasePos
  exact degreeUpper_le_automaticRichRetainedMassLower_of_budget D
    (automaticCanonicalRichness N ballRadius)
    (2 * comparableBase bucket) hbudget

/-- Active-degree source-budget form of the same positivity conclusion. -/
theorem automatic_bucket_separatedPairLower_pos_of_activeDegreeBudget
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket activeDegreeLower : Nat)
    (hbasePos : 0 < comparableBase bucket)
    (hactiveDegree : forall r, r ∈ D.fineLabels ->
      activeDegreeLower <=
        (D.shading.activeAtPoint (D.pointAt r)).card)
    (hbudget : ActiveDegreeRichRetainedMassBudget D activeDegreeLower
      (automaticCanonicalRichness N ballRadius)
      (2 * comparableBase bucket)) :
    0 < canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket) := by
  apply automatic_bucket_separatedPairLower_pos N D ballRadius bucket
    hbasePos
  exact
    degreeUpper_le_automaticRichRetainedMassLower_of_activeDegreeBudget D
      activeDegreeLower (automaticCanonicalRichness N ballRadius)
      (2 * comparableBase bucket) hactiveDegree hbudget

#print axioms coarseDegreeBucketLoss_pos
#print axioms degreeUpper_le_automaticRichRetainedMassLower_of_budget
#print axioms degreeUpper_le_automaticRichRetainedMassLower_of_activeDegreeBudget
#print axioms degreeUpper_le_automaticRichRetainedMassLower_of_E2Budget
#print axioms automatic_bucket_separatedPairLower_pos_of_budget
#print axioms automatic_bucket_separatedPairLower_pos_of_activeDegreeBudget

end

end FamilyStickyCinematicL32Prop41ActualGPrimeMassBlockProducerV1
