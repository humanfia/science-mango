import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstBilateralSupportBoundaryV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairENNRealSelectionV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# Synchronizing the actual pair packages before owner packing

The package constructed for an arbitrary separated centre pair contains two
genuine finite choices: a three-shift C-grid label and a trace-shift label.
Choosing packages pair by pair and immediately replacing each by a scalar
owner envelope loses the identity needed for a cross-pair packing argument.

This module stops one step earlier. It chooses an actual package on every
separated pair with a nonempty common-label fibre, then uses two weighted
three-way pigeonholes to retain a single grid label and a single trace label.
The total centre-pair mass is charged to that synchronized carrier with the
honest factor 72 * 3 * 3 = 648.

No owner-degree or cross-pair packing bound is asserted here.
-/

/-- Rich separated pairs whose literal common fine-label fibre is nonempty. -/
noncomputable def actualGPrimeCommonActivePairs
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real) :
    Finset (iota × iota) := by
  classical
  exact
    (richSeparatedCenterPairs N.family
      (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True)).filter
        fun pair =>
          (actualGPrimeCommonFineCenterLabels
            N D keep pair.1 pair.2).Nonempty

/-- The retained first-hit weight of one actual pair package. -/
noncomputable def actualGPrimePairPackageSelectedWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (pair : iota × iota)
    (ballRadius : Real) (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (O : ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
      fine N D keep pair ballRadius labelWeight f outerA outerB globalDelta
        tGlobal) : ENNReal :=
  finiteENNRealWeight O.package.selected
    (actualGPrimeLabelFirstSurvivorWeightAt N D keep pair.1 pair.2
      ballRadius O.omega labelWeight)

/-- Actual pair packages can be synchronized to one C-grid label and one
trace-shift label before any owner identity is erased.

If there are no common-label separated pairs, the selected carrier is empty.
Otherwise it is nonempty. In both cases the displayed factor-648 estimate
is unconditional. -/
theorem exists_actualGPrime_synchronizedGridShift_pairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (hballRadiusLower : N.delta <= ballRadius)
    (hpackage : forall pair,
      pair ∈ richSeparatedCenterPairs N.family
        (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True) ->
      (actualGPrimeCommonFineCenterLabels
        N D keep pair.1 pair.2).Nonempty ->
      Nonempty (ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair ballRadius labelWeight f outerA outerB globalDelta
          tGlobal)) :
    let activePairs := actualGPrimeCommonActivePairs N D keep ballRadius
    exists packageAt : forall pair : {p // p ∈ activePairs},
        ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
          fine N D keep pair.1 ballRadius labelWeight f outerA outerB
            globalDelta tGlobal,
      exists selectedPairs : Finset {p // p ∈ activePairs},
        exists gridLabel shiftLabel : Fin 3,
          selectedPairs ⊆ Finset.univ ∧
          (forall pair, pair ∈ selectedPairs ->
            (packageAt pair).package.gridLabel = gridLabel ∧
            (packageAt pair).package.shiftLabel = shiftLabel) ∧
          actualGPrimeWeightedFineSeparatedCenterPairMass
              N D keep ballRadius labelWeight <=
            648 * finiteENNRealWeight selectedPairs (fun pair =>
              actualGPrimePairPackageSelectedWeight fine N D keep pair.1
                ballRadius labelWeight f outerA outerB globalDelta tGlobal
                  (packageAt pair)) ∧
          (activePairs.Nonempty -> selectedPairs.Nonempty) := by
  classical
  dsimp only
  let activePairs := actualGPrimeCommonActivePairs N D keep ballRadius
  let ActivePair := {p // p ∈ activePairs}
  have hpackageActive : forall pair : ActivePair,
      Nonempty (ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB globalDelta
          tGlobal) := by
    intro pair
    have hp := Finset.mem_filter.mp pair.2
    exact hpackage pair.1 hp.1 hp.2
  let packageAt : forall pair : ActivePair,
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal := fun pair => Classical.choice (hpackageActive pair)
  let weight : ActivePair -> ENNReal := fun pair =>
    actualGPrimePairPackageSelectedWeight fine N D keep pair.1 ballRadius
      labelWeight f outerA outerB globalDelta tGlobal (packageAt pair)
  have hactiveSubset :
      activePairs ⊆
        richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True) := by
    intro pair hp
    exact (Finset.mem_filter.mp hp).1
  have houtside : forall pair,
      pair ∈ richSeparatedCenterPairs N.family
          (canonicalTenRadiusSeparated N ballRadius) (fun _ _ => True) ->
      pair ∉ activePairs ->
      actualGPrimeWeightedCommonFineCenterMass
        N D keep labelWeight pair.1 pair.2 = 0 := by
    intro pair hpRich hpNot
    have hnotCommon :
        ¬(actualGPrimeCommonFineCenterLabels
          N D keep pair.1 pair.2).Nonempty := by
      intro hcommon
      exact hpNot (Finset.mem_filter.mpr ⟨hpRich, hcommon⟩)
    have hempty : actualGPrimeCommonFineCenterLabels
        N D keep pair.1 pair.2 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnotCommon
    unfold actualGPrimeWeightedCommonFineCenterMass
    rw [hempty]
    simp
  have hcenterEq :
      actualGPrimeWeightedFineSeparatedCenterPairMass
          N D keep ballRadius labelWeight =
        ∑ pair : ActivePair,
          actualGPrimeWeightedCommonFineCenterMass
            N D keep labelWeight pair.1.1 pair.1.2 := by
    unfold actualGPrimeWeightedFineSeparatedCenterPairMass
    unfold richSeparatedPairENNRealWeightTotal
    have hsum := Finset.sum_subset hactiveSubset houtside
    rw [← hsum]
    exact Finset.sum_subtype activePairs (fun _ => Iff.rfl)
      (fun pair => actualGPrimeWeightedCommonFineCenterMass
        N D keep labelWeight pair.1 pair.2)
  have hpair : forall pair : ActivePair,
      actualGPrimeWeightedCommonFineCenterMass
          N D keep labelWeight pair.1.1 pair.1.2 <= 72 * weight pair := by
    intro pair
    calc
      actualGPrimeWeightedCommonFineCenterMass
          N D keep labelWeight pair.1.1 pair.1.2 <=
        ∑ r ∈ actualGPrimeBilateralRetainedFineLabels
            N D keep pair.1.1 pair.1.2 ballRadius, labelWeight r :=
        weightedCommonFineCenterMass_le_bilateralWeight N D keep
          pair.1.1 pair.1.2 ballRadius hballRadiusLower labelWeight
      _ <= 72 * weight pair := by
        simpa only [weight, actualGPrimePairPackageSelectedWeight,
          finiteENNRealWeight,
          actualGPrimeLabelFirstSurvivorWeightAt] using
            (packageAt pair).package.seventyTwo_weight_retention
  have hcenter :
      actualGPrimeWeightedFineSeparatedCenterPairMass
          N D keep ballRadius labelWeight <=
        72 * finiteENNRealWeight (Finset.univ : Finset ActivePair) weight := by
    rw [hcenterEq]
    calc
      (∑ pair : ActivePair,
          actualGPrimeWeightedCommonFineCenterMass
            N D keep labelWeight pair.1.1 pair.1.2) <=
        ∑ pair : ActivePair, 72 * weight pair :=
          Finset.sum_le_sum fun pair _ => hpair pair
      _ = 72 * finiteENNRealWeight
          (Finset.univ : Finset ActivePair) weight := by
        unfold finiteENNRealWeight
        rw [Finset.mul_sum]
  by_cases hactive : activePairs.Nonempty
  · have huniv : (Finset.univ : Finset ActivePair).Nonempty := by
      obtain ⟨pair, hp⟩ := hactive
      exact ⟨⟨pair, hp⟩, Finset.mem_univ _⟩
    have hgridGood : forall pair : ActivePair,
        pair ∈ (Finset.univ : Finset ActivePair) ->
        exists k : Fin 3, (packageAt pair).package.gridLabel = k := by
      intro pair _hp
      exact ⟨(packageAt pair).package.gridLabel, rfl⟩
    obtain ⟨gridLabel, hgridNonempty, hgridSubset,
        hgridWeight, hgrid⟩ :=
      exists_uniform_threeShift_weighted_fiber
        (Finset.univ : Finset ActivePair)
        (fun pair k => (packageAt pair).package.gridLabel = k)
        weight huniv hgridGood
    let gridPairs := threeShiftFiber (Finset.univ : Finset ActivePair)
      (chosenThreeShiftLabel (Finset.univ : Finset ActivePair)
        (fun pair k => (packageAt pair).package.gridLabel = k) hgridGood)
      gridLabel
    have hshiftGood : forall pair : ActivePair, pair ∈ gridPairs ->
        exists k : Fin 3, (packageAt pair).package.shiftLabel = k := by
      intro pair _hp
      exact ⟨(packageAt pair).package.shiftLabel, rfl⟩
    obtain ⟨shiftLabel, hselectedNonempty, hselectedSubset,
        hshiftWeight, hshift⟩ :=
      exists_uniform_threeShift_weighted_fiber gridPairs
        (fun pair k => (packageAt pair).package.shiftLabel = k)
        weight hgridNonempty hshiftGood
    let selectedPairs := threeShiftFiber gridPairs
      (chosenThreeShiftLabel gridPairs
        (fun pair k => (packageAt pair).package.shiftLabel = k) hshiftGood)
      shiftLabel
    refine ⟨packageAt, selectedPairs, gridLabel, shiftLabel,
      hselectedSubset.trans hgridSubset, ?_, ?_, fun _ => hselectedNonempty⟩
    · intro pair hp
      exact ⟨hgrid pair (hselectedSubset hp), hshift pair hp⟩
    · calc
        actualGPrimeWeightedFineSeparatedCenterPairMass
            N D keep ballRadius labelWeight <=
          72 * finiteENNRealWeight
            (Finset.univ : Finset ActivePair) weight := hcenter
        _ <= 72 * (3 * finiteENNRealWeight gridPairs weight) := by
          gcongr
        _ <= 72 * (3 * (3 * finiteENNRealWeight selectedPairs weight)) := by
          gcongr
        _ = 648 * finiteENNRealWeight selectedPairs weight := by ring
  · have hempty : activePairs = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    have hunivEmpty : (Finset.univ : Finset ActivePair) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨pair, _hp⟩
      exact hactive ⟨pair.1, pair.2⟩
    have hmassZero :
        actualGPrimeWeightedFineSeparatedCenterPairMass
          N D keep ballRadius labelWeight = 0 := by
      rw [hcenterEq]
      rw [hunivEmpty]
      simp
    refine ⟨packageAt, ∅, 0, 0, by simp, ?_, ?_, ?_⟩
    · intro pair hp
      simp at hp
    · rw [hmassZero]
      exact bot_le
    · intro hne
      exact (hactive hne).elim

#print axioms actualGPrimeCommonActivePairs
#print axioms actualGPrimePairPackageSelectedWeight
#print axioms exists_actualGPrime_synchronizedGridShift_pairMass

end

end FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
