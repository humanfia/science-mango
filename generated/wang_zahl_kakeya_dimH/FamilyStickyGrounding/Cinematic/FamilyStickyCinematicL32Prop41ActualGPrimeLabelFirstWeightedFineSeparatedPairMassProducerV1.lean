import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairENNRealSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1

open scoped BigOperators ENNReal

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstBilateralSupportBoundaryV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairENNRealSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1

noncomputable section

universe u v

/-!
# Weighted fine-label-first G-prime centre selection

The old G-prime selector maximizes an unweighted incidence count.  It cannot
be assigned first-hit volume weights after the choice.  Here the label weight
is inserted before the Fubini exchange and before the centre-pair maximum.
-/

/-- Label-first separated-pair mass with an arbitrary `ENNReal` weight on
fine labels. -/
noncomputable def actualGPrimeWeightedFineSeparatedPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal) : ENNReal :=
  ∑ r ∈ D.fineLabels,
    labelWeight r *
      ((actualGPrimeFineSeparatedPairsAt
        N D keep ballRadius r).card : ENNReal)

/-- Weight of the common retained fine labels of one ordered centre pair. -/
noncomputable def actualGPrimeWeightedCommonFineCenterMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (labelWeight : fineLabel -> ENNReal)
    (left right : iota) : ENNReal :=
  ∑ r ∈ actualGPrimeCommonFineCenterLabels N D keep left right,
    labelWeight r

/-- Centre-first form of the weighted separated-pair mass. -/
noncomputable def actualGPrimeWeightedFineSeparatedCenterPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal) : ENNReal :=
  richSeparatedPairENNRealWeightTotal N.family
    (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True)
    (actualGPrimeWeightedCommonFineCenterMass N D keep labelWeight)

/-- Multiplying the literal per-label separated-pair lower bound by a
nonnegative label weight and summing loses nothing. -/
theorem fineLabelWeightSum_mul_pairLower_le_weightedSeparatedPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal) (pairLower : Nat)
    (hlower : forall r, r ∈ D.fineLabels ->
      pairLower <=
        (actualGPrimeFineSeparatedPairsAt N D keep ballRadius r).card) :
    (∑ r ∈ D.fineLabels, labelWeight r) * (pairLower : ENNReal) <=
      actualGPrimeWeightedFineSeparatedPairMass
        N D keep ballRadius labelWeight := by
  rw [Finset.sum_mul]
  unfold actualGPrimeWeightedFineSeparatedPairMass
  apply Finset.sum_le_sum
  intro r hr
  gcongr
  exact_mod_cast hlower r hr

/-- Weighted Fubini: label-first and centre-first summation are exactly the
same, including infinite label weights. -/
theorem actualGPrimeWeightedFineSeparatedPairMass_eq_centerPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal) :
    actualGPrimeWeightedFineSeparatedPairMass
        N D keep ballRadius labelWeight =
      actualGPrimeWeightedFineSeparatedCenterPairMass
        N D keep ballRadius labelWeight := by
  classical
  symm
  unfold actualGPrimeWeightedFineSeparatedCenterPairMass
  unfold richSeparatedPairENNRealWeightTotal
  simp only [richSeparatedCenterPairs, and_true, Finset.sum_filter]
  calc
    (∑ pair ∈ N.family.product N.family,
        if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 then
          actualGPrimeWeightedCommonFineCenterMass
            N D keep labelWeight pair.1 pair.2 else 0) =
      ∑ pair ∈ N.family.product N.family,
        ∑ r ∈ D.fineLabels,
          if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
              pair.1 ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
              pair.2 ∈ actualGPrimeRetainedFineActiveFiber N D keep r
          then labelWeight r else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      by_cases hsep :
          canonicalTenRadiusSeparated N ballRadius pair.1 pair.2
      · simp only [hsep, if_true, true_and,
          actualGPrimeWeightedCommonFineCenterMass,
          actualGPrimeCommonFineCenterLabels, Finset.sum_filter]
      · simp [hsep]
    _ = ∑ r ∈ D.fineLabels,
        ∑ pair ∈ N.family.product N.family,
          if canonicalTenRadiusSeparated N ballRadius pair.1 pair.2 ∧
              pair.1 ∈ actualGPrimeRetainedFineActiveFiber N D keep r ∧
              pair.2 ∈ actualGPrimeRetainedFineActiveFiber N D keep r
          then labelWeight r else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ D.fineLabels,
        labelWeight r *
          ((actualGPrimeFineSeparatedPairsAt
            N D keep ballRadius r).card : ENNReal) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [actualGPrimeFineSeparatedPairsAt_eq_family_filter]
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ = actualGPrimeWeightedFineSeparatedPairMass
        N D keep ballRadius labelWeight := rfl

/-- A common fine label of the selected centres is a genuine bilateral label
for their radius balls. -/
theorem actualGPrimeCommonFineCenterLabels_subset_bilateral
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (hballRadiusLower : N.delta <= ballRadius) :
    actualGPrimeCommonFineCenterLabels N D keep left right ⊆
      actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius := by
  classical
  intro r hr
  have hrData := (mem_actualGPrimeCommonFineCenterLabels_iff
    N D keep left right r).mp hr
  have hleftData := (mem_actualGPrimeRetainedFineActiveFiber_iff
    N D keep r left).mp hrData.2.1
  have hrightData := (mem_actualGPrimeRetainedFineActiveFiber_iff
    N D keep r right).mp hrData.2.2
  let leftInFamily : N.family := ⟨left, hleftData.2⟩
  let rightInFamily : N.family := ⟨right, hrightData.2⟩
  have hleftMem : leftInFamily ∈
      actualGPrimeRetainedFineMetricNeighbors
        N D keep left ballRadius r := by
    apply (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep left ballRadius r leftInFamily).mpr
    exact ⟨hleftData.1,
      (N.self_le_delta left hleftData.2).trans hballRadiusLower⟩
  have hrightMem : rightInFamily ∈
      actualGPrimeRetainedFineMetricNeighbors
        N D keep right ballRadius r := by
    apply (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep right ballRadius r rightInFamily).mpr
    exact ⟨hrightData.1,
      (N.self_le_delta right hrightData.2).trans hballRadiusLower⟩
  exact (mem_actualGPrimeBilateralRetainedFineLabels_iff
    N D keep left right ballRadius r).mpr
      ⟨hrData.1, ⟨leftInFamily, hleftMem⟩,
        ⟨rightInFamily, hrightMem⟩⟩

/-- The common-centre weight is bounded by the genuine bilateral support
weight. -/
theorem weightedCommonFineCenterMass_le_bilateralWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (hballRadiusLower : N.delta <= ballRadius)
    (labelWeight : fineLabel -> ENNReal) :
    actualGPrimeWeightedCommonFineCenterMass
        N D keep labelWeight left right <=
      ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r := by
  unfold actualGPrimeWeightedCommonFineCenterMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (actualGPrimeCommonFineCenterLabels_subset_bilateral
      N D keep left right ballRadius hballRadiusLower)
    (fun _ _ _ => bot_le)

/-- Weight-aware G-prime centre pair.  The weighted averaging inequality is
with the actual bilateral label carrier that the random sampler consumes. -/
structure ActualGPrimeWeightedFineSeparatedBallPairOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) (labelWeight : fineLabel -> ENNReal) where
  left : iota
  right : iota
  left_mem : left ∈ N.family
  right_mem : right ∈ N.family
  centers_separated : canonicalTenRadiusSeparated N ballRadius left right
  weighted_average_common :
    (∑ r ∈ D.fineLabels, labelWeight r) *
        ((degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
            ENNReal) <=
      ((richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card : ENNReal) *
      actualGPrimeWeightedCommonFineCenterMass
        N D keep labelWeight left right
  common_weight_le_bilateral_weight :
    actualGPrimeWeightedCommonFineCenterMass
        N D keep labelWeight left right <=
      ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r
  weighted_average_bilateral :
    (∑ r ∈ D.fineLabels, labelWeight r) *
        ((degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
            ENNReal) <=
      ((richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card : ENNReal) *
      ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r
  bilateral :
    (actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).Nonempty
  cross_separated :
    FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
      (finiteFamilyMetricBall N.family N.distance ballRadius left)
      (finiteFamilyMetricBall N.family N.distance ballRadius right)
  left_ball_card :
    ((finiteFamilyMetricBall N.family N.distance
      ballRadius left).card : Real) <=
      (ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real)
  right_ball_card :
    ((finiteFamilyMetricBall N.family N.distance
      ballRadius right).card : Real) <=
      (ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real)

/-- Select the centre pair after inserting the label weight.  This is a new
selection, not a weighted property attached to the old cardinal maximizer. -/
theorem exists_actualGPrimeWeightedFineSeparatedBallPairOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) (labelWeight : fineLabel -> ENNReal)
    (hweight : 0 < ∑ r ∈ D.fineLabels, labelWeight r)
    (hdegree : forall r, r ∈ D.fineLabels ->
      degreeLower <=
        (actualGPrimeRetainedFineActiveFiber N D keep r).card)
    (hroom : automaticCanonicalNearCap N ballRadius < degreeLower)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    Nonempty (ActualGPrimeWeightedFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower labelWeight) := by
  let pairLower : Nat := degreeLower *
    (degreeLower - automaticCanonicalNearCap N ballRadius)
  have hpairLower : 0 < pairLower := by
    exact Nat.mul_pos (Nat.zero_lt_of_lt hroom) (Nat.sub_pos_of_lt hroom)
  let lowerBound : ENNReal :=
    (∑ r ∈ D.fineLabels, labelWeight r) * (pairLower : ENNReal)
  have hlowerBound : 0 < lowerBound := by
    exact ENNReal.mul_pos_iff.2
      ⟨hweight, by exact_mod_cast hpairLower⟩
  have hperLabel : forall r, r ∈ D.fineLabels ->
      pairLower <=
        (actualGPrimeFineSeparatedPairsAt N D keep ballRadius r).card := by
    intro r hr
    have hcap : forall left,
        left ∈ actualGPrimeRetainedFineActiveFiber N D keep r ->
        (actualGPrimeFineNearRightFiber
          N D keep ballRadius r left).card <=
          automaticCanonicalNearCap N ballRadius := by
      intro left hleft
      exact actualGPrimeFineNearRightFiber_card_le_automatic
        N D keep ballRadius r hsymm hnearRadiusLower hnearRadiusUpper
          left hleft
    exact (Nat.mul_le_mul (hdegree r hr)
      (Nat.sub_le_sub_right (hdegree r hr)
        (automaticCanonicalNearCap N ballRadius))).trans
      (actualGPrimeFineActive_card_mul_tsub_nearCap_le_separated_card
        N D keep ballRadius r
          (automaticCanonicalNearCap N ballRadius) hcap)
  have hlabelMass : lowerBound <=
      actualGPrimeWeightedFineSeparatedPairMass
        N D keep ballRadius labelWeight := by
    exact fineLabelWeightSum_mul_pairLower_le_weightedSeparatedPairMass
      N D keep ballRadius labelWeight pairLower hperLabel
  have hcenterMass : lowerBound <=
      actualGPrimeWeightedFineSeparatedCenterPairMass
        N D keep ballRadius labelWeight := by
    rw [← actualGPrimeWeightedFineSeparatedPairMass_eq_centerPairMass]
    exact hlabelMass
  obtain ⟨left, hleft, right, hright, hseparated, _htrue, havgCommon⟩ :=
    exists_richSeparated_pair_of_pos_totalENNRealWeight_lower
      N.family (canonicalTenRadiusSeparated N ballRadius)
      (fun _ _ => True)
      (actualGPrimeWeightedCommonFineCenterMass N D keep labelWeight)
      hlowerBound (by
        simpa only [actualGPrimeWeightedFineSeparatedCenterPairMass] using
          hcenterMass)
  have hcommonBilateral := weightedCommonFineCenterMass_le_bilateralWeight
    N D keep left right ballRadius hballRadiusLower labelWeight
  have havgBilateral : lowerBound <=
      ((richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card : ENNReal) *
      ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r :=
    havgCommon.trans (by
      gcongr)
  have hbilateralWeight : 0 <
      ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r := by
    by_contra hnot
    have hzero :
        (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius, labelWeight r) = 0 :=
      bot_unique (not_lt.mp hnot)
    rw [hzero, mul_zero] at havgBilateral
    exact (not_le_of_gt hlowerBound) havgBilateral
  have hbilateral :
      (actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius).Nonempty := by
    by_contra hnot
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty] at hbilateralWeight
    simp at hbilateralWeight
  have hballs := canonicalMetricBallPair_crossSeparated_and_card_bounds
    N hsymm htriangle hballRadiusLower hballRadiusUpper
      left right hleft hright hseparated
  exact ⟨{
    left := left
    right := right
    left_mem := hleft
    right_mem := hright
    centers_separated := hseparated
    weighted_average_common := by
      simpa only [lowerBound, pairLower] using havgCommon
    common_weight_le_bilateral_weight := hcommonBilateral
    weighted_average_bilateral := by
      simpa only [lowerBound, pairLower] using havgBilateral
    bilateral := hbilateral
    cross_separated := hballs.1
    left_ball_card := hballs.2.1
    right_ball_card := hballs.2.2
  }⟩

/-- Total version of the weighted selector.  If every label has zero weight,
the old unweighted selector supplies the geometric pair and both weighted
inequalities are trivial. -/
theorem exists_actualGPrimeWeightedFineSeparatedBallPairOutcome_total
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) (labelWeight : fineLabel -> ENNReal)
    (hfineLabels : D.fineLabels.Nonempty)
    (hdegree : forall r, r ∈ D.fineLabels ->
      degreeLower <=
        (actualGPrimeRetainedFineActiveFiber N D keep r).card)
    (hroom : automaticCanonicalNearCap N ballRadius < degreeLower)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    Nonempty (ActualGPrimeWeightedFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower labelWeight) := by
  by_cases hweight : 0 < ∑ r ∈ D.fineLabels, labelWeight r
  · exact exists_actualGPrimeWeightedFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower labelWeight hweight hdegree hroom
        hsymm htriangle hnearRadiusLower hnearRadiusUpper
          hballRadiusLower hballRadiusUpper
  · have hzero : (∑ r ∈ D.fineLabels, labelWeight r) = 0 :=
      bot_unique (not_lt.mp hweight)
    obtain ⟨G⟩ := exists_actualGPrimeFineSeparatedBallPairOutcome
      N D keep ballRadius degreeLower hfineLabels hdegree hroom
        hsymm htriangle hnearRadiusLower hnearRadiusUpper
          hballRadiusLower hballRadiusUpper
    have hcommon :=
      weightedCommonFineCenterMass_le_bilateralWeight
        N D keep G.left G.right ballRadius hballRadiusLower labelWeight
    exact ⟨{
      left := G.left
      right := G.right
      left_mem := G.left_mem
      right_mem := G.right_mem
      centers_separated := G.centers_separated
      weighted_average_common := by
        simp only [hzero, zero_mul]
        exact bot_le
      common_weight_le_bilateral_weight := hcommon
      weighted_average_bilateral := by
        simp only [hzero, zero_mul]
        exact bot_le
      bilateral := G.bilateral
      cross_separated := G.cross_separated
      left_ball_card := G.left_ball_card
      right_ball_card := G.right_ball_card
    }⟩

#print axioms fineLabelWeightSum_mul_pairLower_le_weightedSeparatedPairMass
#print axioms actualGPrimeWeightedFineSeparatedPairMass_eq_centerPairMass
#print axioms actualGPrimeCommonFineCenterLabels_subset_bilateral
#print axioms weightedCommonFineCenterMass_le_bilateralWeight
#print axioms exists_actualGPrimeWeightedFineSeparatedBallPairOutcome
#print axioms exists_actualGPrimeWeightedFineSeparatedBallPairOutcome_total

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
