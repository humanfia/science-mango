import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickNEnvelopeV2
import Family8Grounding.Family8BufferedCanonicalOuterThickNEnvelopePowerAlgebraV1
import Family8Grounding.Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
import Mathlib.Tactic

/-!
# Delta-power bound for the explicit buffered selected outer/thick scalar

This combines the literal same-selected `N`-envelope with independent genuine
power bounds for its active-parent card and unrefined selected-source Frostman
constant.  The fixed refinement factor `16` and buffered comparison factor
`27 * 16^3` are both absorbed at explicit small-delta thresholds.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8BufferedCanonicalOuterThickNEnvelopePowerAlgebraV1
open Family8BufferedCommonScaleTubePlankV1
open Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickNEnvelopeV2
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (S : StickyScaleCover fine rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  (Y : Shading S.activeCoarseFamily)

theorem canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (cardExponent frostmanExponent refinementAbsorbExponent
      outerAbsorbExponent beta : Real)
    (hcardExponent : 0 ≤ cardExponent)
    (hfrostmanExponent : 0 ≤ frostmanExponent)
    (hrefinementAbsorbExponent : 0 < refinementAbsorbExponent)
    (houterAbsorbExponent : 0 < outerAbsorbExponent)
    (hbeta : 0 ≤ beta)
    (hrefinementSmall : delta ≤
      canonicalSelectedRefinementFixedThreshold refinementAbsorbExponent)
    (houterSmall : delta ≤
      bufferedCanonicalOuterThickFixedThreshold beta outerAbsorbExponent)
    (hN : (Fintype.card (ActiveParentIndex S) : ENNReal) ≤
      (delta : ENNReal) ^ (-cardExponent))
    (hSourceCF : CF ≤
      (delta : ENNReal) ^ (-frostmanExponent)) :
    (((((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal) *
        canonicalEq45ConflictLoss S U) *
      ((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal)) *
      (uniqueOwnerLocalDeltaThickM 16
        (Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
          (canonicalBufferedSelectedRefinedCF S CF)
          (canonicalBufferedSelectedFamily S U P Y)
          (canonicalBufferedSelectedAmbient (rho := rho)))
        (bufferedCommonWidth rho) (bufferedCommonWidth rho) : ENNReal) ^
          (beta / 2)) ≤
      (delta : ENNReal) ^
        (-(3 * cardExponent +
          (frostmanExponent + 2 * cardExponent +
            refinementAbsorbExponent) * (beta / 2) +
          outerAbsorbExponent)) := by
  have hbase :=
    canonicalBufferedSelected_explicitOuterThickLoss_le_NEnvelope
      S U P Y hrho hrhoHalf CF hCF source_frostman beta hbeta
  have hrefined : canonicalBufferedSelectedRefinedCF S CF ≤
      (delta : ENNReal) ^
        (-(frostmanExponent + cardExponent +
          refinementAbsorbExponent)) := by
    simpa only [canonicalBufferedSelectedRefinedCF,
      bufferedRefinedFrostmanConstant] using
      sourceCF_mul_sixteen_mul_card_le_delta_negativePower
        hdelta hrefinementAbsorbExponent hrefinementSmall hN hSourceCF
  have hrefinedExponent :
      0 ≤ frostmanExponent + cardExponent + refinementAbsorbExponent := by
    linarith
  have hpower :=
    bufferedCanonicalOuterThickNEnvelope_le_delta_negativePower
      hdelta hdeltaOne hcardExponent hrefinedExponent hbeta
      houterAbsorbExponent houterSmall hN hrefined
  have hexponent :
      3 * cardExponent +
          ((frostmanExponent + cardExponent + refinementAbsorbExponent) +
            cardExponent) * (beta / 2) + outerAbsorbExponent =
        3 * cardExponent +
          (frostmanExponent + 2 * cardExponent +
            refinementAbsorbExponent) * (beta / 2) +
          outerAbsorbExponent := by
    ring
  exact hbase.trans (by
    rw [← hexponent]
    exact hpower)

#print axioms
  canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower

end
end Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickPowerV1
