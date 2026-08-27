import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSamplingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1

open scoped BigOperators ENNReal

open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSamplingV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

noncomputable section

universe u v

/-!
# Weighted G-prime centre selection and label-first sampling

The centre pair and the random sample are chosen in that order using the
same supplied label weight.  In the zero-weight branch the old cardinal
sampler is used, so the final survivor carrier remains nonempty without any
positive-volume hypothesis.
-/

/-- Total pulled-back label weight on the actual survivor type. -/
noncomputable def actualGPrimeLabelFirstSurvivorWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal) : ENNReal :=
  ∑ S : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega,
    labelWeight (actualGPrimeLabelFirstLabel
      N D keep left right ballRadius omega S)

/-- Package-free factor-eight composition used by the aggregate outcome. -/
theorem ennreal_weightedAverage_and_eighthSurvival
    (source degreeGap pairCount bilateral sampled : ENNReal)
    (haverage : source * degreeGap <= pairCount * bilateral)
    (hsurvival : bilateral / 8 <= sampled) :
    source * degreeGap <= 8 * pairCount * sampled := by
  have hbilateral : bilateral <= sampled * 8 :=
    (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp hsurvival
  calc
    source * degreeGap <= pairCount * bilateral := haverage
    _ <= pairCount * (sampled * 8) := by
      gcongr
    _ = 8 * pairCount * sampled := by ring

/-- One true weight-selected G-prime pair together with one sample of its
bilateral fine-label carrier. -/
structure ActualGPrimeWeightedFineSeparatedSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) (labelWeight : fineLabel -> ENNReal) where
  pair : ActualGPrimeWeightedFineSeparatedBallPairOutcome
    N D keep ballRadius degreeLower labelWeight
  omega : (N.family -> Fin 1) × (N.family -> Fin 1)
  sampled : ActualGPrimeLabelFirstWeightedSampledOutcome
    N D keep pair.left pair.right ballRadius labelWeight omega
  survivors_nonempty :
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep pair.left pair.right ballRadius omega)).Nonempty
  source_mul_gap_le_eight_pairCount_mul_survivorWeight :
    (∑ r ∈ D.fineLabels, labelWeight r) *
        ((degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
            ENNReal) <=
      8 *
        ((richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius)
          (fun _ _ => True)).card : ENNReal) *
        actualGPrimeLabelFirstSurvivorWeight N D keep pair.left pair.right
          ballRadius omega labelWeight

/-- The full weighted centre-plus-sample producer.  It has no positivity
assumption on the label weight. -/
theorem exists_actualGPrimeWeightedFineSeparatedSampledOutcome
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
    Nonempty (ActualGPrimeWeightedFineSeparatedSampledOutcome
      N D keep ballRadius degreeLower labelWeight) := by
  classical
  obtain ⟨G⟩ :=
    exists_actualGPrimeWeightedFineSeparatedBallPairOutcome_total
      N D keep ballRadius degreeLower labelWeight hfineLabels hdegree hroom
        hsymm htriangle hnearRadiusLower hnearRadiusUpper
          hballRadiusLower hballRadiusUpper
  by_cases hpositive : 0 <
      ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep G.left G.right ballRadius, labelWeight r
  · obtain ⟨omega, O⟩ :=
      exists_actualGPrimeLabelFirstWeightedSampledOutcome
        N D keep G.left G.right ballRadius labelWeight
    have hsampleWeight : 0 <
        actualGPrimeLabelFirstSurvivorWeight
          N D keep G.left G.right ballRadius omega labelWeight := by
      have hdiv : 0 <
          (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
            N D keep G.left G.right ballRadius, labelWeight r) / 8 :=
        ENNReal.div_pos hpositive.ne' (by norm_num)
      exact hdiv.trans_le O.weighted_survival
    have hsurvivors :
        (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
          N D keep G.left G.right ballRadius omega)).Nonempty := by
      by_contra hnot
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
      unfold actualGPrimeLabelFirstSurvivorWeight at hsampleWeight
      rw [hempty] at hsampleWeight
      simp at hsampleWeight
    refine ⟨{
      pair := G
      omega := omega
      sampled := O
      survivors_nonempty := hsurvivors
      source_mul_gap_le_eight_pairCount_mul_survivorWeight := ?_ }⟩
    exact ennreal_weightedAverage_and_eighthSurvival
      (∑ r ∈ D.fineLabels, labelWeight r)
      ((degreeLower *
        (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
          ENNReal)
      ((richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card : ENNReal)
      (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep G.left G.right ballRadius, labelWeight r)
      (actualGPrimeLabelFirstSurvivorWeight
        N D keep G.left G.right ballRadius omega labelWeight)
      G.weighted_average_bilateral O.weighted_survival
  · have hzero :
        (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
          N D keep G.left G.right ballRadius, labelWeight r) = 0 :=
      bot_unique (not_lt.mp hpositive)
    obtain ⟨omega, Ocard⟩ := exists_actualGPrimeLabelFirstSampledOutcome
      N D keep G.left G.right ballRadius
    let O : ActualGPrimeLabelFirstWeightedSampledOutcome
        N D keep G.left G.right ballRadius labelWeight omega := {
      weighted_survival := by
        rw [hzero, ENNReal.zero_div]
        exact bot_le
      load := Ocard.load
      retained_tube_card_le_load := Ocard.retained_tube_card_le_load }
    have hsurvivors := Ocard.survivors_nonempty
      N D keep G.left G.right ballRadius omega G.bilateral
    refine ⟨{
      pair := G
      omega := omega
      sampled := O
      survivors_nonempty := hsurvivors
      source_mul_gap_le_eight_pairCount_mul_survivorWeight := ?_ }⟩
    exact ennreal_weightedAverage_and_eighthSurvival
      (∑ r ∈ D.fineLabels, labelWeight r)
      ((degreeLower *
        (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
          ENNReal)
      ((richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius)
        (fun _ _ => True)).card : ENNReal)
      (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep G.left G.right ballRadius, labelWeight r)
      (actualGPrimeLabelFirstSurvivorWeight
        N D keep G.left G.right ballRadius omega labelWeight)
      G.weighted_average_bilateral O.weighted_survival

#print axioms actualGPrimeLabelFirstSurvivorWeight
#print axioms ennreal_weightedAverage_and_eighthSurvival
#print axioms ActualGPrimeWeightedFineSeparatedSampledOutcome
#print axioms exists_actualGPrimeWeightedFineSeparatedSampledOutcome

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
