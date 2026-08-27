import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeMassBudgetNumericsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualGPrimeSharpPoorMassProducerV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassLowerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1

open scoped BigOperators

noncomputable section

universe u v w

/-!
# Sharp poor-rectangle mass arithmetic

A rectangle excluded by the threshold `richness` has strictly fewer than
`richness` curves.  Since the fibre cardinality is a natural number, its
actual upper bound is `richness - 1`, not `richness`.  Retaining this one
unit is exactly the degree block lost in the earlier coarse estimate.

For the canonical choice `richness = nearCap + 1`, the sharp subtraction is
therefore `nearCap * degreeUpper`.  This removes the spurious outer `+ 1`
from the E2 dominance condition.
-/

/-- The selected q-mass after the sharp predecessor-sized poor-rectangle
subtraction is retained on rectangles with threshold `richness`. -/
theorem automaticPredRichRetainedMassLower_le
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (richness degreeUpper : Nat)
    (hselection : D.goodPairs.card <= coarseDegreeBucketLoss D *
      (D.retainedGoodPairs keep).card)
    (hdegree : forall R i,
      i ∈ D.coarseCurveIndexFiber keep R ->
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card <= degreeUpper) :
    automaticRichRetainedMassLower D (richness - 1) degreeUpper <=
      (retainedGoodPairsOver D keep
        (richCoarseRectangleFamily D keep richness)).card := by
  classical
  let rich := richCoarseRectangleFamily D keep richness
  let poor := D.coarseRectangleFamily.filter fun R =>
    ¬ richness <= (D.coarseCurveIndexFiber keep R).card
  have hselectedLower : D.goodPairs.card / coarseDegreeBucketLoss D <=
      (D.retainedGoodPairs keep).card := by
    exact Nat.div_le_of_le_mul hselection
  have hsplit :
      (∑ R ∈ D.coarseRectangleFamily,
          (D.coarseIncidencePairs keep R).card) =
        (∑ R ∈ rich, (D.coarseIncidencePairs keep R).card) +
          ∑ R ∈ poor, (D.coarseIncidencePairs keep R).card := by
    simpa [rich, poor, richCoarseRectangleFamily] using
      (Finset.sum_filter_add_sum_filter_not
        (s := D.coarseRectangleFamily)
        (p := fun R => richness <=
          (D.coarseCurveIndexFiber keep R).card)
        (fun R => (D.coarseIncidencePairs keep R).card)).symm
  have hpoorPointwise : ∀ R ∈ poor,
      (D.coarseIncidencePairs keep R).card <=
        (richness - 1) * degreeUpper := by
    intro R hR
    have hnotRich : ¬ richness <=
        (D.coarseCurveIndexFiber keep R).card :=
      (Finset.mem_filter.mp hR).2
    have hfiberPred :
        (D.coarseCurveIndexFiber keep R).card <= richness - 1 := by
      omega
    have hincidence :=
      coarseIncidencePairs_card_le_curveFiber_card_mul_degreeUpper
        D keep R degreeUpper (fun i hi => hdegree R i hi)
    exact hincidence.trans
      (Nat.mul_le_mul_right degreeUpper hfiberPred)
  have hpoorSum :
      (∑ R ∈ poor, (D.coarseIncidencePairs keep R).card) <=
        D.coarseRectangleFamily.card *
          ((richness - 1) * degreeUpper) := by
    calc
      (∑ R ∈ poor, (D.coarseIncidencePairs keep R).card) <=
          ∑ _R ∈ poor, (richness - 1) * degreeUpper := by
        exact Finset.sum_le_sum fun R hR => hpoorPointwise R hR
      _ = poor.card * ((richness - 1) * degreeUpper) := by simp
      _ <= D.coarseRectangleFamily.card *
          ((richness - 1) * degreeUpper) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card
          (Finset.filter_subset _ _))
  have htotal : (D.retainedGoodPairs keep).card <=
      (retainedGoodPairsOver D keep rich).card +
        D.coarseRectangleFamily.card *
          ((richness - 1) * degreeUpper) := by
    rw [D.retainedGoodPairs_card_eq_sum_coarse keep, hsplit,
      retainedGoodPairsOver_card_eq_sum_coarseIncidencePairs]
    exact Nat.add_le_add_left hpoorSum _
  unfold automaticRichRetainedMassLower
  apply (Nat.sub_le_sub_right hselectedLower _).trans
  rw [Nat.sub_le_iff_le_add]
  simpa [rich, Nat.add_comm] using htotal

/-- The automatic G-prime lower bound with the exact poor threshold.  Its
mass term subtracts `nearCap`, while its selected rectangles still have
richness `nearCap + 1`, leaving strict room for separated pairs. -/
theorem automaticPred_bucket_separatedPairLower_le_total
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (hselection : D.goodPairs.card <= coarseDegreeBucketLoss D *
      (D.retainedGoodPairs (coarseDegreeBucketKeep D bucket)).card)
    (hfiberSubset : forall R,
      R ∈ richCoarseRectangleFamily D (coarseDegreeBucketKeep D bucket)
        (automaticCanonicalRichness N ballRadius) ->
      D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
        N.family)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling) :
    canonicalCoarseSeparatedPairProducedLower
        (automaticCanonicalRichness N ballRadius)
        (automaticCanonicalNearCap N ballRadius)
        (automaticRichRetainedMassLower D
          (automaticCanonicalNearCap N ballRadius)
          (2 * comparableBase bucket))
        (2 * comparableBase bucket) <=
      canonicalCoarseRichSeparatedPairCountTotal N D
        (coarseDegreeBucketKeep D bucket) ballRadius := by
  let keep := coarseDegreeBucketKeep D bucket
  let nearCap := automaticCanonicalNearCap N ballRadius
  let richness := automaticCanonicalRichness N ballRadius
  let degreeUpper := 2 * comparableBase bucket
  let rectangles := richCoarseRectangleFamily D keep richness
  have hrectangles : rectangles ⊆ D.coarseRectangleFamily :=
    Finset.filter_subset _ _
  have hdegreeAll : forall R i,
      i ∈ D.coarseCurveIndexFiber keep R ->
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card <= degreeUpper := by
    intro R i hi
    exact (coarseDegreeBucket_curve_degree_bounds D bucket R i hi).2
  have hmass : automaticRichRetainedMassLower D nearCap degreeUpper <=
      (retainedGoodPairsOver D keep rectangles).card := by
    have hpred := automaticPredRichRetainedMassLower_le D keep richness
      degreeUpper hselection hdegreeAll
    simpa only [rectangles, richness, nearCap,
      automaticCanonicalRichness, Nat.add_sub_cancel] using hpred
  have hdegree : forall R, R ∈ rectangles -> forall i,
      i ∈ D.coarseCurveIndexFiber keep R ->
        ((D.coarseIncidencePairs keep R).filter fun pair =>
          pair.1 = i).card <= degreeUpper := by
    intro R _hR i hi
    exact hdegreeAll R i hi
  have hrichness : forall R, R ∈ rectangles ->
      richness <= (D.coarseCurveIndexFiber keep R).card := by
    intro R hR
    exact (mem_richCoarseRectangleFamily_iff D keep richness).mp hR |>.2
  have hnumeric :
      ((10 * ballRadius) / N.criticalScale) ^ N.exponent *
          ((N.criticalBall.card : Nat) : Real) <= (nearCap : Real) :=
    Nat.le_ceil _
  apply canonicalCoarseSeparatedPairProducedLower_le_total
    N D keep ballRadius rectangles richness nearCap
      (automaticRichRetainedMassLower D nearCap degreeUpper) degreeUpper
  · exact hrectangles
  · intro R hR
    exact hfiberSubset R hR
  · exact hmass
  · exact hdegree
  · exact hrichness
  · exact hsymm
  · exact hnearRadiusLower
  · exact hnearRadiusUpper
  · exact hnumeric

/-- Positivity of the sharp automatic lower bound requires one degree block
after subtracting only the exact poor-fibre cap `nearCap`. -/
theorem automaticPred_bucket_separatedPairLower_pos
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (hbasePos : 0 < comparableBase bucket)
    (hmassBlock : 2 * comparableBase bucket <=
      automaticRichRetainedMassLower D
        (automaticCanonicalNearCap N ballRadius)
        (2 * comparableBase bucket)) :
    0 < canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalNearCap N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket) := by
  apply canonicalCoarseSeparatedPairProducedLower_pos
  · exact automaticCanonicalNearCap_lt_richness N ballRadius
  · exact Nat.mul_pos (by omega) hbasePos
  · exact hmassBlock

#print axioms automaticPredRichRetainedMassLower_le
#print axioms automaticPred_bucket_separatedPairLower_le_total
#print axioms automaticPred_bucket_separatedPairLower_pos

end

end FamilyStickyCinematicL32Prop41ActualGPrimeSharpPoorMassProducerV1
