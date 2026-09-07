import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterDatumV1
import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
import Mathlib.Tactic

/-!
# Small-`b` Equation (45) or the complementary large-`b` branch

This file is the minimal dichotomy wrapper around the stable Family 6
Frostman plank hypothesis on the exact normalized selected-occurrence outer
datum.  The density floor remains an explicit premise at the exponent
returned by that hypothesis.

If the normalized middle width is at most the returned analytic cutoff, the
Family 6 estimate and the existing fixed-normalization scalar comparison give
the displayed Equation (45) bound.  Otherwise the theorem returns exactly the
strict complementary inequality.  No large-`b` analytic estimate is asserted
here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceNormalizedOuterEq45OrLargeBV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedOccurrenceNormalizedOuterScaleBridgeV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- On the exact normalized selected outer datum, either the stable Family 6
hypothesis gives Equation (45) at its returned small-width cutoff, or the
normalized middle width is strictly larger than that cutoff.

The only density assumption is the literal normalized-outer density floor
required by `ConvexPlankFrostmanMultiplicityHypothesis.bound`. -/
theorem exists_selectedOccurrenceNormalizedOuter_eq45_or_largeB
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    {CF : ENNReal}
    (hF : IsFrostmanIn CF
      (selectedOccurrenceOuterFamily P Rside) ambient)
    (M : NNReal)
    (hcontrol :
      FrostmanThickenedPlankControl
        (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
          hlabel ambient ambientComparisonConstant ambient_is_unit_scale
          hF.family_subset)
        M)
    {epsilon beta : Real}
    (hepsilon : 0 < epsilon)
    (hbeta : 0 <= beta)
    (hdeltaA : delta / 576 <= bucketShortA labelOuter)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P Rside} beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hdensity :
          (bucketShortA labelOuter : ENNReal) ^ eta <=
            (selectedOccurrenceNormalizedOuterShading
              P Y labelOuter Rside).shadingDensity),
        (selectedOccurrenceNormalizedOuterShading
            P Y labelOuter Rside).averageMultiplicity <=
            (576 : ENNReal) ^ (epsilon / 2) *
              ((((M : ENNReal) *
                    ((bucketShortA labelOuter : ENNReal) /
                      (bucketShortB labelOuter : ENNReal))) ^
                  (beta / 2)) *
                proposition66AOuterFactor delta
                  (bucketShortA labelOuter) (bucketShortB labelOuter)
                  (Fintype.card
                    {q // q ∈ selectedOccurrenceIndices P Rside})
                  CF epsilon beta) ∨
          b0 < bucketShortB labelOuter := by
  let D := selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
    hlabel ambient ambientComparisonConstant ambient_is_unit_scale
      hF.family_subset
  have hhalfEpsilon : 0 < epsilon / 2 := by positivity
  obtain ⟨eta, b0, heta, hb0, hbound⟩ :=
    H.bound (epsilon / 2) hhalfEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hdensity
  by_cases hbSmall : bucketShortB labelOuter <= b0
  · left
    have ha : 0 < bucketShortA labelOuter :=
      bucketShortA_pos labelOuter
    have hab : bucketShortA labelOuter <= bucketShortB labelOuter :=
      bucketShortA_le_bucketShortB labelOuter
    have hFnorm : IsFrostmanIn CF D.family D.ambient := by
      dsimp only [D]
      exact selectedOccurrenceNormalizedOuterFamily_isFrostmanIn
        P labelOuter Rside ambient hF
    have hfamily6 :
        D.shading.averageMultiplicity <=
          convexPlankFrostmanFactor D (epsilon / 2) beta CF M :=
      hbound {q // q ∈ selectedOccurrenceIndices P Rside}
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        D CF M ha hab hbSmall hFnorm hdensity hcontrol
    calc
      (selectedOccurrenceNormalizedOuterShading
          P Y labelOuter Rside).averageMultiplicity =
          D.shading.averageMultiplicity := rfl
      _ <= convexPlankFrostmanFactor D (epsilon / 2) beta CF M :=
        hfamily6
      _ <= (576 : ENNReal) ^ (epsilon / 2) *
          ((((M : ENNReal) *
                ((bucketShortA labelOuter : ENNReal) /
                  (bucketShortB labelOuter : ENNReal))) ^
              (beta / 2)) *
            proposition66AOuterFactor delta
              (bucketShortA labelOuter) (bucketShortB labelOuter)
              (Fintype.card
                {q // q ∈ selectedOccurrenceIndices P Rside})
              CF epsilon beta) :=
        convexPlankFrostmanFactor_halfEpsilon_le_fixedScaleLoss_mul_coupledThickAspect_mul_outer
          D CF M hdelta hdeltaA hab hepsilon hbeta
  · right
    exact lt_of_not_ge hbSmall

#print axioms
  exists_selectedOccurrenceNormalizedOuter_eq45_or_largeB

end
end Family8SelectedOccurrenceNormalizedOuterEq45OrLargeBV1
