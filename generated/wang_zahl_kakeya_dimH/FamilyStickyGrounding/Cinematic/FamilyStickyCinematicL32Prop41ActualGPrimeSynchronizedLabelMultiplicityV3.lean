import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteENNRealFiberFubiniV3
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedLabelMultiplicityV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteENNRealFiberFubiniV3
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# Exact label multiplicity after synchronizing actual pair packages

Every package-selected survivor still carries its literal global fine label.
This module regroups the total retained first-hit weight by that label. The
coefficient is the exact number of selected pair packages in which the label
survives; no ambient cardinality or pair-count bound is inserted. V1 and V2
were failed namespace/definitional-unfolding drafts and are not imported.
-/

/-- Exact cross-pair multiplicity of one fine label in a family of actual
pair packages. -/
noncomputable def actualGPrimeSynchronizedLabelMultiplicity
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (activePairs : Finset (iota × iota))
    (packageAt : forall pair : {p // p ∈ activePairs},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈ activePairs}) (r : fineLabel) : Nat :=
  ∑ pair ∈ selectedPairs,
    ((packageAt pair).package.selected.filter fun a =>
      actualGPrimeLabelFirstLabel N D keep pair.1.1 pair.1.2 ballRadius
        (packageAt pair).omega a = r).card

/-- The synchronized package weight is exactly the fine-label weight times
the true cross-pair label multiplicity. This is the lossless Fubini boundary
for the remaining owner/pair-degree geometry. -/
theorem finiteENNRealWeight_packageSelected_eq_sum_labelMultiplicity
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (activePairs : Finset (iota × iota))
    (packageAt : forall pair : {p // p ∈ activePairs},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈ activePairs}) :
    finiteENNRealWeight selectedPairs (fun pair =>
        actualGPrimePairPackageSelectedWeight fine N D keep pair.1
          ballRadius labelWeight f outerA outerB globalDelta tGlobal
            (packageAt pair)) =
      ∑ r ∈ D.fineLabels,
        (actualGPrimeSynchronizedLabelMultiplicity fine N D keep ballRadius
          labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt
            selectedPairs r : ENNReal) * labelWeight r := by
  classical
  unfold finiteENNRealWeight
  calc
    (∑ pair ∈ selectedPairs,
        actualGPrimePairPackageSelectedWeight fine N D keep pair.1
          ballRadius labelWeight f outerA outerB globalDelta tGlobal
            (packageAt pair)) =
      ∑ pair ∈ selectedPairs, ∑ r ∈ D.fineLabels,
        (((packageAt pair).package.selected.filter fun a =>
          actualGPrimeLabelFirstLabel N D keep pair.1.1 pair.1.2 ballRadius
            (packageAt pair).omega a = r).card : ENNReal) * labelWeight r := by
      apply Finset.sum_congr rfl
      intro pair hpair
      have hlabel : forall a, a ∈ (packageAt pair).package.selected ->
          actualGPrimeLabelFirstLabel N D keep pair.1.1 pair.1.2 ballRadius
            (packageAt pair).omega a ∈ D.fineLabels := by
        intro a ha
        exact ((D.mem_retainedGoodPairs_iff keep).mp
          ((packageAt pair).package.left_retained a ha)).1.2.1
      unfold actualGPrimePairPackageSelectedWeight
      unfold actualGPrimeLabelFirstSurvivorWeightAt
      exact finiteENNRealWeight_eq_sum_card_filter_mul
        (packageAt pair).package.selected D.fineLabels
          (actualGPrimeLabelFirstLabel N D keep pair.1.1 pair.1.2
            ballRadius (packageAt pair).omega) labelWeight hlabel
    _ = ∑ r ∈ D.fineLabels, ∑ pair ∈ selectedPairs,
        (((packageAt pair).package.selected.filter fun a =>
          actualGPrimeLabelFirstLabel N D keep pair.1.1 pair.1.2 ballRadius
            (packageAt pair).omega a = r).card : ENNReal) * labelWeight r := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ D.fineLabels,
        (actualGPrimeSynchronizedLabelMultiplicity fine N D keep ballRadius
          labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt
            selectedPairs r : ENNReal) * labelWeight r := by
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [actualGPrimeSynchronizedLabelMultiplicity, Nat.cast_sum,
        Finset.sum_mul]

#print axioms actualGPrimeSynchronizedLabelMultiplicity
#print axioms finiteENNRealWeight_packageSelected_eq_sum_labelMultiplicity

end

end FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedLabelMultiplicityV3
