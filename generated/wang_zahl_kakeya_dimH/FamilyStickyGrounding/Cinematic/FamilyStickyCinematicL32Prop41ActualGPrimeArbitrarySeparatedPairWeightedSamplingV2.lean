import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedSamplingV2

open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSamplingV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

noncomputable section

universe u v

/-!
# Weighted sampling for every actual separated pair

The maximising pair used by the usual weighted G-prime producer is needed
only for its global averaging inequality.  The later sampling and C-grid
geometry can be run for every literal separated pair.  We expose that fact
without adding a new geometric hypothesis: membership in
`actualGPrimeFineSeparatedPairsAt` supplies both active endpoints and their
separation, while the canonical metric-ball theorem supplies the cross-ball
geometry.

The output uses degree lower bound zero.  Thus its global-average field is
the true but deliberately vacuous inequality `0 <= ...`; no claim about
maximality of the chosen pair is made.  All bilateral-support, sampling,
survivor, load, and cross-separation fields remain the actual ones.
-/

/-- A literal separated active pair gives a weight-independent G-prime pair
package at degree zero.  This is the exact pair geometry needed downstream;
only the maximiser inequality has been intentionally trivialised. -/
noncomputable def actualGPrimeWeightedFineSeparatedBallPairOutcome_zero_of_mem
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal) (r : fineLabel)
    (pair : iota × iota)
    (hpair : pair ∈
      actualGPrimeFineSeparatedPairsAt N D keep ballRadius r)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    ActualGPrimeWeightedFineSeparatedBallPairOutcome
      N D keep ballRadius 0 labelWeight := by
  classical
  have hpairData := Finset.mem_filter.mp hpair
  have hactive := Finset.mem_product.mp hpairData.1
  have hleftData := (mem_actualGPrimeRetainedFineActiveFiber_iff
    N D keep r pair.1).mp hactive.1
  have hrightData := (mem_actualGPrimeRetainedFineActiveFiber_iff
    N D keep r pair.2).mp hactive.2
  have hleftMem : pair.1 ∈ N.family := hleftData.2
  have hrightMem : pair.2 ∈ N.family := hrightData.2
  have hcenters : canonicalTenRadiusSeparated N ballRadius
      pair.1 pair.2 := hpairData.2
  have hballs := canonicalMetricBallPair_crossSeparated_and_card_bounds
    N hsymm htriangle hballRadiusLower hballRadiusUpper pair.1 pair.2
      hleftMem hrightMem hcenters
  have hrFine : r ∈ D.fineLabels := by
    exact ((D.mem_retainedGoodPairs_iff keep).mp hleftData.1).1.2.1
  have hrCommon : r ∈
      actualGPrimeCommonFineCenterLabels N D keep pair.1 pair.2 := by
    exact Finset.mem_filter.mpr ⟨hrFine, hactive.1, hactive.2⟩
  have hrBilateral : r ∈ actualGPrimeBilateralRetainedFineLabels
      N D keep pair.1 pair.2 ballRadius :=
    actualGPrimeCommonFineCenterLabels_subset_bilateral
      N D keep pair.1 pair.2 ballRadius hballRadiusLower hrCommon
  refine {
    left := pair.1
    right := pair.2
    left_mem := hleftMem
    right_mem := hrightMem
    centers_separated := hcenters
    weighted_average_common := ?_
    common_weight_le_bilateral_weight :=
      weightedCommonFineCenterMass_le_bilateralWeight
        N D keep pair.1 pair.2 ballRadius hballRadiusLower labelWeight
    weighted_average_bilateral := ?_
    bilateral := ⟨r, hrBilateral⟩
    cross_separated := hballs.1
    left_ball_card := hballs.2.1
    right_ball_card := hballs.2.2 }
  · simp
  · simp

/-- Every literal separated active pair admits the same honest weighted
random sample used downstream.  Positive bilateral weight yields a survivor
from weighted retention; in the zero-weight branch the cardinal sampler uses
the already proved bilateral nonemptiness. -/
theorem exists_actualGPrimeArbitrarySeparatedPairWeightedSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal) (r : fineLabel)
    (pair : iota × iota)
    (hpair : pair ∈
      actualGPrimeFineSeparatedPairsAt N D keep ballRadius r)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    Nonempty (ActualGPrimeWeightedFineSeparatedSampledOutcome
      N D keep ballRadius 0 labelWeight) := by
  classical
  let G : ActualGPrimeWeightedFineSeparatedBallPairOutcome
      N D keep ballRadius 0 labelWeight :=
    actualGPrimeWeightedFineSeparatedBallPairOutcome_zero_of_mem
      N D keep ballRadius labelWeight r pair hpair hsymm htriangle
        hballRadiusLower hballRadiusUpper
  by_cases hpositive : 0 <
      ∑ r' ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep G.left G.right ballRadius, labelWeight r'
  · obtain ⟨omega, O⟩ :=
      exists_actualGPrimeLabelFirstWeightedSampledOutcome
        N D keep G.left G.right ballRadius labelWeight
    have hsampleWeight : 0 <
        actualGPrimeLabelFirstSurvivorWeight
          N D keep G.left G.right ballRadius omega labelWeight := by
      have hdiv : 0 <
          (∑ r' ∈ actualGPrimeBilateralRetainedFineLabels
            N D keep G.left G.right ballRadius, labelWeight r') / 8 :=
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
    simp
  · have hzero :
        (∑ r' ∈ actualGPrimeBilateralRetainedFineLabels
          N D keep G.left G.right ballRadius, labelWeight r') = 0 :=
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
    simp

#print axioms actualGPrimeWeightedFineSeparatedBallPairOutcome_zero_of_mem
#print axioms exists_actualGPrimeArbitrarySeparatedPairWeightedSampledOutcome

end

end FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedSamplingV2
