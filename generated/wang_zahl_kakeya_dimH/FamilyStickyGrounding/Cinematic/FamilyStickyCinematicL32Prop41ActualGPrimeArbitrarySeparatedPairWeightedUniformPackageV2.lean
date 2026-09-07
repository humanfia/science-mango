import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedSamplingV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedCenteredHalfPointSourceV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedSamplingV2
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSamplingV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSeparatedSamplingOutcomeV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineCNormalizedThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1

noncomputable section

universe u v

/-!
# The weighted C-grid package for every actual separated pair

The global weighted selector constructs this package only for a maximising
centre pair.  The geometry itself does not use maximality.  Combining the
degree-zero arbitrary-pair sampler with the existing C-grid constructor gives
the identical weighted retention, trace shift, perturbation-ready lens data,
and cross-ball geometry for every literal member of
`actualGPrimeFineSeparatedPairsAt`.

This module does not assert a per-pair packing upper bound.  It removes the
selection mismatch which previously prevented the existing owner geometry
from even being instantiated for all terms of the label-first Fubini sum.
-/

/-- The dependent output keeps the actual random sample and the resulting
weighted geometric package on the original displayed pair. -/
structure ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (pair : iota × iota)
    (ballRadius : Real) (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real) where
  omega : (N.family -> Fin 1) × (N.family -> Fin 1)
  package :
    ActualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2
      fine N D keep pair.1 pair.2 ballRadius omega labelWeight f
        outerA outerB globalDelta tGlobal

/-- For a fixed literal separated pair, choose a weighted random sample with
nonempty survivor carrier.  No pair-averaging conclusion appears. -/
theorem exists_actualGPrimeArbitrarySeparatedPairWeightedRawSample
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
    exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
      ActualGPrimeLabelFirstWeightedSampledOutcome
          N D keep pair.1 pair.2 ballRadius labelWeight omega ∧
        (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
          N D keep pair.1 pair.2 ballRadius omega)).Nonempty := by
  classical
  let G := actualGPrimeWeightedFineSeparatedBallPairOutcome_zero_of_mem
    N D keep ballRadius labelWeight r pair hpair hsymm htriangle
      hballRadiusLower hballRadiusUpper
  by_cases hpositive : 0 <
      ∑ r' ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep pair.1 pair.2 ballRadius, labelWeight r'
  · obtain ⟨omega, O⟩ :=
      exists_actualGPrimeLabelFirstWeightedSampledOutcome
        N D keep pair.1 pair.2 ballRadius labelWeight
    have hsampleWeight : 0 <
        actualGPrimeLabelFirstSurvivorWeight
          N D keep pair.1 pair.2 ballRadius omega labelWeight := by
      have hdiv : 0 <
          (∑ r' ∈ actualGPrimeBilateralRetainedFineLabels
            N D keep pair.1 pair.2 ballRadius, labelWeight r') / 8 :=
        ENNReal.div_pos hpositive.ne' (by norm_num)
      exact hdiv.trans_le O.weighted_survival
    have hsurvivors :
        (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
          N D keep pair.1 pair.2 ballRadius omega)).Nonempty := by
      by_contra hnot
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
      unfold actualGPrimeLabelFirstSurvivorWeight at hsampleWeight
      rw [hempty] at hsampleWeight
      simp at hsampleWeight
    exact ⟨omega, O, hsurvivors⟩
  · have hzero :
        (∑ r' ∈ actualGPrimeBilateralRetainedFineLabels
          N D keep pair.1 pair.2 ballRadius, labelWeight r') = 0 :=
      bot_unique (not_lt.mp hpositive)
    obtain ⟨omega, Ocard⟩ := exists_actualGPrimeLabelFirstSampledOutcome
      N D keep pair.1 pair.2 ballRadius
    let O : ActualGPrimeLabelFirstWeightedSampledOutcome
        N D keep pair.1 pair.2 ballRadius labelWeight omega := {
      weighted_survival := by
        rw [hzero, ENNReal.zero_div]
        exact bot_le
      load := Ocard.load
      retained_tube_card_le_load := Ocard.retained_tube_card_le_load }
    have hsurvivors := Ocard.survivors_nonempty
      N D keep pair.1 pair.2 ballRadius omega G.bilateral
    exact ⟨omega, O, hsurvivors⟩

/-- Every actual separated pair supports the full existing weighted C-grid
and trace package.  All hypotheses below are the same analytic and numerical
inputs used by the canonical maximising-pair constructor. -/
theorem exists_actualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (centerTube : Tube radius) (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (pointSource : ActualCenteredHalfPointRectangleSource E centerTube tubeAt
      f outerA outerB tGlobal)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hft : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc outerA outerB))
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 (radius : Real)
      (prop41Y1PaperFineT (radius : Real) globalDelta tGlobal)
      globalDelta tGlobal)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal) (r : fineLabel)
    (pair : iota × iota)
    (hpair : pair ∈
      actualGPrimeFineSeparatedPairsAt N D keep ballRadius r)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (htriangle : forall x center y,
      N.distance x y <= N.distance x center + N.distance center y)
    (hballRadiusLower : N.delta <= ballRadius)
    (hballRadiusUpper : ballRadius <= N.ceiling)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hsmall : ActualY1PaperFineCNormalizedThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal (4 * ballRadius)) :
    Nonempty (ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
      fine N D keep pair ballRadius labelWeight f outerA outerB globalDelta
        tGlobal) := by
  classical
  obtain ⟨omega, O, hsurvivors⟩ :=
    exists_actualGPrimeArbitrarySeparatedPairWeightedRawSample
      N D keep ballRadius labelWeight r pair hpair hsymm htriangle
        hballRadiusLower hballRadiusUpper
  let G := actualGPrimeWeightedFineSeparatedBallPairOutcome_zero_of_mem
    N D keep ballRadius labelWeight r pair hpair hsymm htriangle
      hballRadiusLower hballRadiusUpper
  let Q : ActualGPrimeWeightedFineSeparatedSampledOutcome
      N D keep ballRadius 0 labelWeight := {
    pair := G
    omega := omega
    sampled := O
    survivors_nonempty := hsurvivors
    source_mul_gap_le_eight_pairCount_mul_survivorWeight := by simp }
  obtain ⟨P⟩ :=
    exists_actualGPrimeLabelFirstThreeShiftCGridPaperFineWeightedUniformPackageV2_of_sampledOutcome
      fine physical E Y1 fineLabels pointAt centerTube tubeAt f f1 f2
        outerA outerB hOuter hf hf1 tGlobal globalDelta facts pointSource
          hpointE sharp hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
            N D hD keep ballRadius 0 labelWeight hdistance Q hsmall
  refine ⟨{ omega := omega, package := ?_ }⟩
  simpa only [Q, G,
    actualGPrimeWeightedFineSeparatedBallPairOutcome_zero_of_mem] using P

#print axioms ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
#print axioms exists_actualGPrimeArbitrarySeparatedPairWeightedRawSample
#print axioms exists_actualGPrimeArbitrarySeparatedPairWeightedUniformOutcome

end

end FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
