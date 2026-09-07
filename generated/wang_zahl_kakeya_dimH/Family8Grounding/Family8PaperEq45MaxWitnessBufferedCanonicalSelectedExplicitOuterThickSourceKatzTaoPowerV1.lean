import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickPowerV1
import Family8Grounding.Family8AllFrostmanStickyPopularParentPowerV4
import Mathlib.Tactic

/-!
# Source Katz--Tao production for the explicit buffered Equation (45) power

This discharges the active-parent-card premise of the literal buffered
outer/thick power estimate from the actual sticky scale-cover Katz--Tao
certificate.  The only remaining analytic scalar input is the power bound on
the unrefined selected-source Frostman constant.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickSourceKatzTaoPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8BufferedCanonicalOuterThickNEnvelopePowerAlgebraV1
open Family8BufferedCommonScaleTubePlankV1
open Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickPowerV1
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
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
  (S : StickyScaleCover D.family rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  (Y : Shading S.activeCoarseFamily)

include hD in
theorem canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower_of_sourceKT
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody)
    {A : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    (scaleExponent katzTaoExponent cardAbsorbExponent frostmanExponent
      refinementAbsorbExponent outerAbsorbExponent beta : Real)
    (hscaleExponent : 0 ≤ scaleExponent)
    (hkatzTaoExponent : 0 ≤ katzTaoExponent)
    (hcardAbsorbExponent : 0 < cardAbsorbExponent)
    (hfrostmanExponent : 0 ≤ frostmanExponent)
    (hrefinementAbsorbExponent : 0 < refinementAbsorbExponent)
    (houterAbsorbExponent : 0 < outerAbsorbExponent)
    (hbeta : 0 ≤ beta)
    (hcardSmall : delta ≤
      stickyPopularParentPowerThreshold cardAbsorbExponent)
    (hrefinementSmall : delta ≤
      canonicalSelectedRefinementFixedThreshold refinementAbsorbExponent)
    (houterSmall : delta ≤
      bufferedCanonicalOuterThickFixedThreshold beta outerAbsorbExponent)
    (hscale : (delta : ENNReal) ^ scaleExponent ≤ (rho : ENNReal))
    (hA : A ≤ (delta : ENNReal) ^ (-katzTaoExponent))
    (hSourceCF : CF ≤ (delta : ENNReal) ^ (-frostmanExponent)) :
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
        (-(3 * (katzTaoExponent + 2 * scaleExponent +
            cardAbsorbExponent) +
          (frostmanExponent +
            2 * (katzTaoExponent + 2 * scaleExponent +
              cardAbsorbExponent) + refinementAbsorbExponent) *
              (beta / 2) +
          outerAbsorbExponent)) := by
  have hcard :
      (Fintype.card (ActiveParentIndex S) : ENNReal) ≤
        (delta : ENNReal) ^
          (-(katzTaoExponent + 2 * scaleExponent +
            cardAbsorbExponent)) := by
    exact activeCoarse_card_le_delta_negativePower_of_katzTaoAtScale
      D hD S hrhoHalf hKT hcardAbsorbExponent hcardSmall hscale hA
  have hcardExponent :
      0 ≤ katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent := by
    linarith
  exact
    canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower
      S U P Y hrho hrhoHalf CF hCF source_frostman
      hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      (katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent)
      frostmanExponent refinementAbsorbExponent outerAbsorbExponent beta
      hcardExponent hfrostmanExponent hrefinementAbsorbExponent
      houterAbsorbExponent hbeta hrefinementSmall houterSmall hcard hSourceCF

#print axioms
  canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower_of_sourceKT

end
end Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickSourceKatzTaoPowerV1
