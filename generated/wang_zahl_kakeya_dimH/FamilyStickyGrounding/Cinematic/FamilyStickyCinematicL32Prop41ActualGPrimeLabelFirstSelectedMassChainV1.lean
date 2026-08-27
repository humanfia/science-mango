import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstUniformPackageV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstSelectedMassChainV1

open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstBilateralSupportBoundaryV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1

noncomputable section

universe u v

/-!
# Quantitative G-prime label-first mass chain

The fine-separated G-prime selector already gives a lower bound for the
same-fine cross-edge mass.  The label-first sampler already retains one eighth
of the bilateral labels, and the subsequent three-shift pigeonhole already
retains one third of the sampling survivors.  The missing finite-counting step
is that the edge mass at one bilateral label is bounded by the product of the
two canonical metric-ball cardinalities.

This module supplies that step and composes the existing inequalities.  It
does not assert that the sampled or three-shift-selected rectangles cover the
original E2 set; the spatial E2 cover belongs to the raw occupied-label family
before sampling.
-/

/-- Every retained fine-label fibre inside one G-prime ball has cardinality at
most that of the literal canonical metric ball. -/
theorem actualGPrimeRetainedFineMetricNeighbors_card_le_metricBall
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (center : iota)
    (ballRadius : Real) (r : fineLabel) :
    (actualGPrimeRetainedFineMetricNeighbors
      N D keep center ballRadius r).card <=
      (finiteFamilyMetricBall
        N.family N.distance ballRadius center).card := by
  classical
  let neighbors := actualGPrimeRetainedFineMetricNeighbors
    N D keep center ballRadius r
  let ball := finiteFamilyMetricBall
    N.family N.distance ballRadius center
  have himageSubset : neighbors.image (fun i => i.1) ⊆ ball := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hjData := (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep center ballRadius r j).mp hj
    exact Finset.mem_filter.mpr ⟨j.2, hjData.2⟩
  calc
    neighbors.card = (neighbors.image (fun i => i.1)).card := by
      symm
      exact Finset.card_image_of_injective _ Subtype.val_injective
    _ <= ball.card := Finset.card_le_card himageSubset

/-- The same-fine cross-edge mass is supported only on genuine bilateral
labels, and every summand is bounded by the product of the two metric-ball
cardinalities. -/
theorem actualGPrimeCommonFineEdgeMass_le_bilateral_mul_ballCards
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) :
    actualGPrimeCommonFineEdgeMass N D keep left right ballRadius <=
      (actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius).card *
      (finiteFamilyMetricBall
        N.family N.distance ballRadius left).card *
      (finiteFamilyMetricBall
        N.family N.distance ballRadius right).card := by
  classical
  let leftBall := finiteFamilyMetricBall
    N.family N.distance ballRadius left
  let rightBall := finiteFamilyMetricBall
    N.family N.distance ballRadius right
  let leftFiber : fineLabel -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r
  let rightFiber : fineLabel -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r
  have hleft : forall r, (leftFiber r).card <= leftBall.card := by
    intro r
    exact actualGPrimeRetainedFineMetricNeighbors_card_le_metricBall
      N D keep left ballRadius r
  have hright : forall r, (rightFiber r).card <= rightBall.card := by
    intro r
    exact actualGPrimeRetainedFineMetricNeighbors_card_le_metricBall
      N D keep right ballRadius r
  calc
    actualGPrimeCommonFineEdgeMass N D keep left right ballRadius =
        ∑ r ∈ D.fineLabels, (leftFiber r).card * (rightFiber r).card := by
      rfl
    _ <= ∑ r ∈ D.fineLabels,
        if (leftFiber r).Nonempty ∧ (rightFiber r).Nonempty then
          leftBall.card * rightBall.card
        else 0 := by
      apply Finset.sum_le_sum
      intro r _hr
      by_cases hbilateral :
          (leftFiber r).Nonempty ∧ (rightFiber r).Nonempty
      · simp only [hbilateral]
        exact Nat.mul_le_mul (hleft r) (hright r)
      · simp only [hbilateral, if_false]
        by_cases hleftNonempty : (leftFiber r).Nonempty
        · have hrightEmpty : rightFiber r = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            intro hrightNonempty
            exact hbilateral ⟨hleftNonempty, hrightNonempty⟩
          simp [hrightEmpty]
        · have hleftEmpty : leftFiber r = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hleftNonempty
          simp [hleftEmpty]
    _ = (actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius).card *
        leftBall.card * rightBall.card := by
      simp only [actualGPrimeBilateralRetainedFineLabels,
        leftFiber, rightFiber]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ac_rfl

/-- The one-eighth label-first survival and one-third three-shift retention
compose to an exact factor-24 cardinal loss. -/
theorem actualGPrimeBilateralRetainedFineLabels_card_le_twentyFour_mul_selected
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstPaperFineUniformPackage fine N D keep
      left right ballRadius omega f outerA outerB globalDelta tGlobal) :
    (actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).card <= 24 * P.selected.card := by
  have hsurvival :
      ((actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius).card : Real) / 8 <=
      ((Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega)).card : Real) := by
    simpa only [Finset.card_univ, Fintype.card_coe] using P.label_survival
  have hthreeShift :
      ((Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega)).card : Real) <=
      3 * (P.selected.card : Real) := by
    exact_mod_cast P.threeShift_cardinal_retention
  have hreal :
      ((actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius).card : Real) <=
      24 * (P.selected.card : Real) := by
    linarith
  exact_mod_cast hreal

/-- Denominator-free finite selected-mass chain.  The left side is the
fine-label separated-pair lower mass from the G-prime selector; the right side
contains only explicit finite cardinalities and the forced sampling loss 24. -/
theorem ActualGPrimeFineSeparatedBallPairOutcome.mass_le_selected
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat)
    (G : ActualGPrimeFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstPaperFineUniformPackage fine N D keep
      G.left G.right ballRadius omega f outerA outerB globalDelta tGlobal) :
    D.fineLabels.card *
        (degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius)) <=
      (richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card *
      (finiteFamilyMetricBall
        N.family N.distance ballRadius G.left).card *
      (finiteFamilyMetricBall
        N.family N.distance ballRadius G.right).card *
      24 * P.selected.card := by
  let pairCount :=
    (richSeparatedCenterPairs N.family
      (canonicalTenRadiusSeparated N ballRadius)
      (fun _ _ => True)).card
  let leftCard := (finiteFamilyMetricBall
    N.family N.distance ballRadius G.left).card
  let rightCard := (finiteFamilyMetricBall
    N.family N.distance ballRadius G.right).card
  let bilateralCard := (actualGPrimeBilateralRetainedFineLabels
    N D keep G.left G.right ballRadius).card
  have hedge : actualGPrimeCommonFineEdgeMass
      N D keep G.left G.right ballRadius <=
      bilateralCard * leftCard * rightCard := by
    exact actualGPrimeCommonFineEdgeMass_le_bilateral_mul_ballCards
      N D keep G.left G.right ballRadius
  have hbilateral : bilateralCard <= 24 * P.selected.card := by
    exact actualGPrimeBilateralRetainedFineLabels_card_le_twentyFour_mul_selected
      fine N D keep G.left G.right ballRadius omega f outerA outerB
        globalDelta tGlobal P
  have hscaled :
      bilateralCard * leftCard * rightCard <=
        (24 * P.selected.card) * leftCard * rightCard := by
    gcongr
  calc
    D.fineLabels.card *
          (degreeLower *
            (degreeLower - automaticCanonicalNearCap N ballRadius)) <=
        pairCount * actualGPrimeCommonFineEdgeMass
          N D keep G.left G.right ballRadius := G.average_edge_mass
    _ <= pairCount * (bilateralCard * leftCard * rightCard) := by
      gcongr
    _ <= pairCount * ((24 * P.selected.card) * leftCard * rightCard) := by
      gcongr
    _ = pairCount * leftCard * rightCard * 24 * P.selected.card := by
      ring

/-- Analytic real-valued form obtained by substituting the two canonical
nonconcentration ball bounds carried by the G-prime outcome itself. -/
theorem ActualGPrimeFineSeparatedBallPairOutcome.mass_le_selected_analyticCap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat)
    (G : ActualGPrimeFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (P : ActualGPrimeLabelFirstPaperFineUniformPackage fine N D keep
      G.left G.right ballRadius omega f outerA outerB globalDelta tGlobal) :
    (D.fineLabels.card *
        (degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius)) : Nat) <=
      ((richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius)
          (fun _ _ => True)).card : Real) *
      ((ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real)) *
      ((ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real)) *
      24 * (P.selected.card : Real) := by
  let pairCount :=
    (richSeparatedCenterPairs N.family
      (canonicalTenRadiusSeparated N ballRadius)
      (fun _ _ => True)).card
  let leftCard := (finiteFamilyMetricBall
    N.family N.distance ballRadius G.left).card
  let rightCard := (finiteFamilyMetricBall
    N.family N.distance ballRadius G.right).card
  let cap : Real :=
    (ballRadius / N.criticalScale) ^ N.exponent *
      ((N.criticalBall.card : Nat) : Real)
  have hnat := _root_.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstSelectedMassChainV1.ActualGPrimeFineSeparatedBallPairOutcome.mass_le_selected
    fine N D keep ballRadius degreeLower G omega f outerA outerB globalDelta
      tGlobal P
  have hreal :
      (D.fineLabels.card *
          (degreeLower *
            (degreeLower - automaticCanonicalNearCap N ballRadius)) : Nat) <=
        (pairCount : Real) * (leftCard : Real) * (rightCard : Real) *
          24 * (P.selected.card : Real) := by
    exact_mod_cast hnat
  have hleft : (leftCard : Real) <= cap := by
    exact G.left_ball_card
  have hright : (rightCard : Real) <= cap := by
    exact G.right_ball_card
  have hcap : 0 <= cap := (Nat.cast_nonneg leftCard).trans hleft
  calc
    (D.fineLabels.card *
          (degreeLower *
            (degreeLower - automaticCanonicalNearCap N ballRadius)) : Nat) <=
        (pairCount : Real) * (leftCard : Real) * (rightCard : Real) *
          24 * (P.selected.card : Real) := hreal
    _ <= (pairCount : Real) * cap * cap * 24 *
          (P.selected.card : Real) := by
      gcongr

#print axioms actualGPrimeRetainedFineMetricNeighbors_card_le_metricBall
#print axioms actualGPrimeCommonFineEdgeMass_le_bilateral_mul_ballCards
#print axioms actualGPrimeBilateralRetainedFineLabels_card_le_twentyFour_mul_selected
#print axioms ActualGPrimeFineSeparatedBallPairOutcome.mass_le_selected
#print axioms ActualGPrimeFineSeparatedBallPairOutcome.mass_le_selected_analyticCap

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstSelectedMassChainV1
