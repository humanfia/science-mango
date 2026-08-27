import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeSharpPoorMassProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeE2MassConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualGPrimeSharpE2MassConnectorV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeMassBudgetNumericsV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSharpPoorMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeE2MassConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

noncomputable section

universe u v w

/-!
# E2 dominance after the exact poor-fibre subtraction

The automatic rich threshold is `nearCap + 1`.  A poor rectangle therefore
has at most `nearCap` curves, so the source budget needs to pay

`bucketLoss * (richness * degreeUpper)`,

not `bucketLoss * ((richness + 1) * degreeUpper)`.  The latter was an
artifact of replacing a strict natural-number inequality by a weak one.
-/

/-- The sharp E2 dominance condition leaves one full degree block after the
exact `nearCap` poor-rectangle subtraction. -/
theorem automaticPred_massBlock_of_E2Dominance
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat) (label : Int)
    (hgood : D.goodPairs.Nonempty)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
    (hdominance : coarseDegreeBucketLoss D *
      (automaticCanonicalRichness N ballRadius *
        (2 * comparableBase bucket)) <= pyzE2DegreeLower label) :
    2 * comparableBase bucket <=
      automaticRichRetainedMassLower D
        (automaticCanonicalNearCap N ballRadius)
        (2 * comparableBase bucket) := by
  have hfine : D.fineLabels.Nonempty :=
    fineLabels_nonempty_of_goodPairs_nonempty D hgood
  apply degreeUpper_le_automaticRichRetainedMassLower_of_E2Dominance
    D label (automaticCanonicalNearCap N ballRadius)
      (2 * comparableBase bucket) hfine hcell hactive
  simpa only [automaticCanonicalRichness] using hdominance

/-- The formerly failing endpoint is now exact: the sharp budget is `1024`,
whereas the coarse predecessor-free budget was `1028`. -/
theorem sharpDominance_closes_1024_endpoint :
    2 * (256 * 2) <= pyzE2DegreeLower 11 /\
      not (2 * ((256 + 1) * 2) <= pyzE2DegreeLower 11) := by
  norm_num [pyzE2DegreeLower,
    FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1.dyadicCeilUpper]

#print axioms automaticPred_massBlock_of_E2Dominance
#print axioms sharpDominance_closes_1024_endpoint

end

end FamilyStickyCinematicL32Prop41ActualGPrimeSharpE2MassConnectorV1
