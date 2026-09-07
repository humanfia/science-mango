import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairSharingV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedLabelMultiplicityV3
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1

noncomputable section

universe u v

/-!
# True cross-centre sharing degree of an actual survivor pair

An endpoint pair can occur in several synchronized centre-pair packages.
This module exposes that repetition as a literal finite fibre.  Label
injectivity makes the centre-pair projection injective inside such a fibre,
and the sampling provenance places its two centres in the corresponding
radius-`R` metric balls.  Hence the exact sharing degree is bounded by the
product of those two genuine ball cardinalities.
-/

/-- Occurrences which represent one fixed pair of actual fine indices. -/
noncomputable def actualGPrimeSynchronizedOccurrenceFinePairFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (packageAt : forall pair : {p // p ∈
        actualGPrimeCommonActivePairs N D keep ballRadius},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈
      actualGPrimeCommonActivePairs N D keep ballRadius})
    (r : fineLabel) (q : iota × iota) :
    Finset (ActualGPrimeSynchronizedOccurrence fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal
        (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt) :=
  (actualGPrimeSynchronizedLabelOccurrences fine N D keep ballRadius
    labelWeight f outerA outerB globalDelta tGlobal
      (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt
        selectedPairs r).filter fun x =>
    actualGPrimeSynchronizedOccurrenceFinePair fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal
        (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt x = q

/-- The exact multiplicity partitions losslessly over its actual endpoint
pairs at the surviving separation radius. -/
theorem actualGPrimeSynchronizedLabelMultiplicity_eq_sum_finePairFiber
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (packageAt : forall pair : {p // p ∈
        actualGPrimeCommonActivePairs N D keep ballRadius},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈
      actualGPrimeCommonActivePairs N D keep ballRadius})
    (r : fineLabel)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j)) :
    actualGPrimeSynchronizedLabelMultiplicity fine N D keep ballRadius
        labelWeight f outerA outerB globalDelta tGlobal
          (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt
            selectedPairs r =
      ∑ q ∈ actualGPrimeFineSeparatedPairsAt N D keep
          (actualGPrimeSurvivorSeparationRadius ballRadius) r,
        (actualGPrimeSynchronizedOccurrenceFinePairFiber fine N D keep
          ballRadius labelWeight f outerA outerB globalDelta tGlobal
            packageAt selectedPairs r q).card := by
  classical
  rw [← actualGPrimeSynchronizedLabelOccurrences_card]
  exact Finset.card_eq_sum_card_fiberwise
    (s := actualGPrimeSynchronizedLabelOccurrences fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal
        (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt
          selectedPairs r)
    (t := actualGPrimeFineSeparatedPairsAt N D keep
      (actualGPrimeSurvivorSeparationRadius ballRadius) r)
    (f := actualGPrimeSynchronizedOccurrenceFinePair fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal
        (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt)
    (fun x hx => actualGPrimeSynchronizedOccurrenceFinePair_mem fine N D keep
      ballRadius labelWeight f outerA outerB globalDelta tGlobal
        (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt
          selectedPairs r hdistance x hx)

/-- The fibre over one actual endpoint pair injects into the product of the
two radius-`R` centre balls.  This is the true cross-centre sharing bound. -/
theorem actualGPrimeSynchronizedOccurrenceFinePairFiber_card_le_ballProduct
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (packageAt : forall pair : {p // p ∈
        actualGPrimeCommonActivePairs N D keep ballRadius},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈
      actualGPrimeCommonActivePairs N D keep ballRadius})
    (r : fineLabel) (q : iota × iota)
    (hsymm : forall x y, N.distance x y = N.distance y x) :
    (actualGPrimeSynchronizedOccurrenceFinePairFiber fine N D keep ballRadius
        labelWeight f outerA outerB globalDelta tGlobal packageAt selectedPairs
          r q).card <=
      (finiteFamilyMetricBall N.family N.distance ballRadius q.1).card *
        (finiteFamilyMetricBall N.family N.distance ballRadius q.2).card := by
  classical
  let source := actualGPrimeSynchronizedOccurrenceFinePairFiber fine N D keep
    ballRadius labelWeight f outerA outerB globalDelta tGlobal packageAt
      selectedPairs r q
  let target :=
    (finiteFamilyMetricBall N.family N.distance ballRadius q.1).product
      (finiteFamilyMetricBall N.family N.distance ballRadius q.2)
  let centerAt : ActualGPrimeSynchronizedOccurrence fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal
        (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt ->
      iota × iota := fun x => x.1.1
  have hcard : source.card <= target.card := by
    apply Finset.card_le_card_of_injOn centerAt
    · intro x hx
      have hxFiber := Finset.mem_filter.mp hx
      have hxOccurrence := Finset.mem_sigma.mp hxFiber.1
      rcases x with ⟨pair, a⟩
      have hpActive := pair.2
      have hpRich := (Finset.mem_filter.mp hpActive).1
      have hpData := (mem_richSeparatedCenterPairs_iff
        (left := pair.1.1) (right := pair.1.2)).mp hpRich
      have hpairEq := hxFiber.2
      change
        (actualGPrimeLabelFirstLeftIndex N D keep pair.1.1 pair.1.2 ballRadius
            (packageAt pair).omega a,
          actualGPrimeLabelFirstRightIndex N D keep pair.1.1 pair.1.2
            ballRadius (packageAt pair).omega a) = q at hpairEq
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨hpData.1, ?_⟩
        calc
          N.distance pair.1.1 q.1 =
              N.distance q.1 pair.1.1 := hsymm _ _
          _ = N.distance
              (actualGPrimeLabelFirstLeftIndex N D keep pair.1.1 pair.1.2
                ballRadius (packageAt pair).omega a) pair.1.1 := by
              rw [← congrArg Prod.fst hpairEq]
          _ <= ballRadius :=
            actualGPrimeLabelFirstLeftIndex_distance_center_le N D keep
              pair.1.1 pair.1.2 ballRadius (packageAt pair).omega a
      · apply Finset.mem_filter.mpr
        refine ⟨hpData.2.1, ?_⟩
        calc
          N.distance pair.1.2 q.2 =
              N.distance q.2 pair.1.2 := hsymm _ _
          _ = N.distance
              (actualGPrimeLabelFirstRightIndex N D keep pair.1.1 pair.1.2
                ballRadius (packageAt pair).omega a) pair.1.2 := by
              rw [← congrArg Prod.snd hpairEq]
          _ <= ballRadius :=
            actualGPrimeLabelFirstRightIndex_distance_center_le N D keep
              pair.1.1 pair.1.2 ballRadius (packageAt pair).omega a
    · intro x hx y hy hcenter
      have hxFiber := Finset.mem_filter.mp hx
      have hyFiber := Finset.mem_filter.mp hy
      have hxOccurrence := Finset.mem_sigma.mp hxFiber.1
      have hyOccurrence := Finset.mem_sigma.mp hyFiber.1
      rcases x with ⟨px, ax⟩
      rcases y with ⟨py, ay⟩
      change px.1 = py.1 at hcenter
      have hp : px = py := Subtype.ext hcenter
      subst py
      have haxData := Finset.mem_filter.mp hxOccurrence.2
      have hayData := Finset.mem_filter.mp hyOccurrence.2
      have ha : ax = ay := (packageAt px).package.label_injective
        (haxData.2.trans hayData.2.symm)
      subst ay
      rfl
  calc
    _ <= target.card := hcard
    _ = _ := Finset.card_product _ _

#print axioms actualGPrimeSynchronizedOccurrenceFinePairFiber
#print axioms actualGPrimeSynchronizedLabelMultiplicity_eq_sum_finePairFiber
#print axioms actualGPrimeSynchronizedOccurrenceFinePairFiber_card_le_ballProduct

end

end FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairSharingV3
