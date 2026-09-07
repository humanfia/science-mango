import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairSharingV3
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeCanonicalSharingCapV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Lemma57FiniteTwoEndsMaximizerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairSharingV3
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedLabelMultiplicityV3
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u v

/-!
# Canonical nonconcentration cap for synchronized cross-centre sharing

The previous module bounds a fixed endpoint-pair fibre by two literal metric
balls.  The canonical maximizer now bounds each radius-`R` ball, producing a
fully explicit finite sharing cap.  Summing first over actual endpoint pairs
and then over fine labels gives a callback-free weighted package bound.
-/

/-- The exact Nat ceiling of the canonical radius-`R` ball estimate. -/
def automaticCanonicalCenterSharingNatCap
    {iota : Type u} [DecidableEq iota]
    (N : CanonicalNormNonconcentrationData iota) (ballRadius : Real) : Nat :=
  Nat.ceil ((ballRadius / N.criticalScale) ^ N.exponent *
    ((N.criticalBall.card : Nat) : Real))

/-- Every literal canonical radius-`R` ball has the automatic ceiling cap. -/
theorem finiteFamilyMetricBall_card_le_automaticCenterSharingCap
    {iota : Type u} [DecidableEq iota]
    (N : CanonicalNormNonconcentrationData iota) (ballRadius : Real)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling)
    (center : iota) (hcenter : center ∈ N.family) :
    (finiteFamilyMetricBall N.family N.distance ballRadius center).card <=
      automaticCanonicalCenterSharingNatCap N ballRadius := by
  classical
  have hballReal :
      ((finiteFamilyMetricBall N.family N.distance
        ballRadius center).card : Real) <=
      (ballRadius / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real) := by
    simpa only [finiteBallCount, finiteFamilyMetricBall] using
      N.card_le_ratio_rpow hballRadiusLower hballRadiusUpper center hcenter
  have hcapReal :
      ((finiteFamilyMetricBall N.family N.distance
        ballRadius center).card : Real) <=
        (automaticCanonicalCenterSharingNatCap N ballRadius : Nat) := by
    exact hballReal.trans (Nat.le_ceil _)
  exact_mod_cast hcapReal

/-- One actual endpoint-pair fibre is bounded by the square of the automatic
canonical ball cap. -/
theorem actualGPrimeSynchronizedOccurrenceFinePairFiber_card_le_cap_sq
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
    (hq : q ∈ actualGPrimeFineSeparatedPairsAt N D keep
      (actualGPrimeSurvivorSeparationRadius ballRadius) r)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    (actualGPrimeSynchronizedOccurrenceFinePairFiber fine N D keep ballRadius
        labelWeight f outerA outerB globalDelta tGlobal packageAt selectedPairs
          r q).card <=
      automaticCanonicalCenterSharingNatCap N ballRadius *
        automaticCanonicalCenterSharingNatCap N ballRadius := by
  classical
  have hqData := Finset.mem_filter.mp hq
  have hqActive := Finset.mem_product.mp hqData.1
  have hleftN := (mem_actualGPrimeRetainedFineActiveFiber_iff
    N D keep r q.1).mp hqActive.1 |>.2
  have hrightN := (mem_actualGPrimeRetainedFineActiveFiber_iff
    N D keep r q.2).mp hqActive.2 |>.2
  exact (actualGPrimeSynchronizedOccurrenceFinePairFiber_card_le_ballProduct
    fine N D keep ballRadius labelWeight f outerA outerB globalDelta tGlobal
      packageAt selectedPairs r q hsymm).trans
        (Nat.mul_le_mul
          (finiteFamilyMetricBall_card_le_automaticCenterSharingCap N
            ballRadius hballRadiusLower hballRadiusUpper q.1 hleftN)
          (finiteFamilyMetricBall_card_le_automaticCenterSharingCap N
            ballRadius hballRadiusLower hballRadiusUpper q.2 hrightN))

/-- The true cross-centre multiplicity of one fine label is at most the
number of surviving actual endpoint pairs times the squared ball cap. -/
theorem actualGPrimeSynchronizedLabelMultiplicity_le_pairCard_mul_cap_sq
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
        (D.fine.tubes i) (D.fine.tubes j))
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    actualGPrimeSynchronizedLabelMultiplicity fine N D keep ballRadius
        labelWeight f outerA outerB globalDelta tGlobal
          (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt
            selectedPairs r <=
      (actualGPrimeFineSeparatedPairsAt N D keep
          (actualGPrimeSurvivorSeparationRadius ballRadius) r).card *
        (automaticCanonicalCenterSharingNatCap N ballRadius *
          automaticCanonicalCenterSharingNatCap N ballRadius) := by
  classical
  rw [actualGPrimeSynchronizedLabelMultiplicity_eq_sum_finePairFiber
    fine N D keep ballRadius labelWeight f outerA outerB globalDelta tGlobal
      packageAt selectedPairs r hdistance]
  calc
    (∑ q ∈ actualGPrimeFineSeparatedPairsAt N D keep
        (actualGPrimeSurvivorSeparationRadius ballRadius) r,
      (actualGPrimeSynchronizedOccurrenceFinePairFiber fine N D keep
        ballRadius labelWeight f outerA outerB globalDelta tGlobal packageAt
          selectedPairs r q).card) <=
      ∑ _q ∈ actualGPrimeFineSeparatedPairsAt N D keep
          (actualGPrimeSurvivorSeparationRadius ballRadius) r,
        automaticCanonicalCenterSharingNatCap N ballRadius *
          automaticCanonicalCenterSharingNatCap N ballRadius := by
      apply Finset.sum_le_sum
      intro q hq
      exact actualGPrimeSynchronizedOccurrenceFinePairFiber_card_le_cap_sq
        fine N D keep ballRadius labelWeight f outerA outerB globalDelta
          tGlobal packageAt selectedPairs r q hq hsymm hballRadiusLower
            hballRadiusUpper
    _ = _ := by simp

/-- Callback-free weighted endpoint: synchronized package mass is charged to
the genuine fine-separated endpoint-pair mass with precisely the squared
canonical centre-sharing cap. -/
theorem finiteENNRealWeight_packageSelected_le_cap_sq_mul_weightedPairMass
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
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling) :
    finiteENNRealWeight selectedPairs (fun pair =>
        actualGPrimePairPackageSelectedWeight fine N D keep pair.1 ballRadius
          labelWeight f outerA outerB globalDelta tGlobal (packageAt pair)) <=
      ((automaticCanonicalCenterSharingNatCap N ballRadius *
          automaticCanonicalCenterSharingNatCap N ballRadius : Nat) :
        ENNReal) *
        actualGPrimeWeightedFineSeparatedPairMass N D keep
          (actualGPrimeSurvivorSeparationRadius ballRadius) labelWeight := by
  classical
  rw [finiteENNRealWeight_packageSelected_eq_sum_labelMultiplicity]
  unfold actualGPrimeWeightedFineSeparatedPairMass
  calc
    (∑ r ∈ D.fineLabels,
        (actualGPrimeSynchronizedLabelMultiplicity fine N D keep ballRadius
          labelWeight f outerA outerB globalDelta tGlobal
            (actualGPrimeCommonActivePairs N D keep ballRadius) packageAt
              selectedPairs r : ENNReal) * labelWeight r) <=
      ∑ r ∈ D.fineLabels,
        (((actualGPrimeFineSeparatedPairsAt N D keep
            (actualGPrimeSurvivorSeparationRadius ballRadius) r).card *
          (automaticCanonicalCenterSharingNatCap N ballRadius *
            automaticCanonicalCenterSharingNatCap N ballRadius) : Nat) :
              ENNReal) * labelWeight r := by
      apply Finset.sum_le_sum
      intro r hr
      gcongr
      exact_mod_cast
        actualGPrimeSynchronizedLabelMultiplicity_le_pairCard_mul_cap_sq
          fine N D keep ballRadius labelWeight f outerA outerB globalDelta
            tGlobal packageAt selectedPairs r hdistance hsymm
              hballRadiusLower hballRadiusUpper
    _ = ((automaticCanonicalCenterSharingNatCap N ballRadius *
            automaticCanonicalCenterSharingNatCap N ballRadius : Nat) :
          ENNReal) *
        ∑ r ∈ D.fineLabels,
          labelWeight r *
            ((actualGPrimeFineSeparatedPairsAt N D keep
              (actualGPrimeSurvivorSeparationRadius ballRadius) r).card :
                ENNReal) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [Nat.cast_mul]
      ring

#print axioms automaticCanonicalCenterSharingNatCap
#print axioms finiteFamilyMetricBall_card_le_automaticCenterSharingCap
#print axioms actualGPrimeSynchronizedOccurrenceFinePairFiber_card_le_cap_sq
#print axioms actualGPrimeSynchronizedLabelMultiplicity_le_pairCard_mul_cap_sq
#print axioms finiteENNRealWeight_packageSelected_le_cap_sq_mul_weightedPairMass

end

end FamilyStickyCinematicL32Prop41ActualGPrimeCanonicalSharingCapV3
