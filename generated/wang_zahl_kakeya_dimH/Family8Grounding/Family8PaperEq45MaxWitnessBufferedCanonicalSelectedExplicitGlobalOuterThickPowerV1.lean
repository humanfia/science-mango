import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickSourceKatzTaoPowerV1
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
import Mathlib.Tactic

/-!
# Global production of the explicit buffered Equation (45) power

Positive source shaded mass makes the actual exact-degree selection nonempty.
The global closed-ball Frostman certificate then restricts to precisely that
selected source, with the honest `16 * N` selection loss.  Together with the
actual source Katz--Tao certificate this produces the literal buffered
outer/thick delta-power estimate without a scalar callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitGlobalOuterThickPowerV1

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
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickSourceKatzTaoPowerV1
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
open Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

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
theorem canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower_of_globalFrostman_sourceKT
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {A C : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    (hglobal : IsFrostmanOn C S.activeCoarseFamily Finset.univ
      closedBallFourBody)
    (hsourceMass : Y.shadingMass ≠ 0)
    (scaleExponent katzTaoExponent cardAbsorbExponent
      globalFrostmanExponent selectionAbsorbExponent
      refinementAbsorbExponent outerAbsorbExponent beta : Real)
    (hscaleExponent : 0 ≤ scaleExponent)
    (hkatzTaoExponent : 0 ≤ katzTaoExponent)
    (hcardAbsorbExponent : 0 < cardAbsorbExponent)
    (hglobalFrostmanExponent : 0 ≤ globalFrostmanExponent)
    (hselectionAbsorbExponent : 0 < selectionAbsorbExponent)
    (hrefinementAbsorbExponent : 0 < refinementAbsorbExponent)
    (houterAbsorbExponent : 0 < outerAbsorbExponent)
    (hbeta : 0 ≤ beta)
    (hcardSmall : delta ≤
      stickyPopularParentPowerThreshold cardAbsorbExponent)
    (hselectionSmall : delta ≤
      canonicalSelectedRefinementFixedThreshold selectionAbsorbExponent)
    (hrefinementSmall : delta ≤
      canonicalSelectedRefinementFixedThreshold refinementAbsorbExponent)
    (houterSmall : delta ≤
      bufferedCanonicalOuterThickFixedThreshold beta outerAbsorbExponent)
    (hscale : (delta : ENNReal) ^ scaleExponent ≤ (rho : ENNReal))
    (hA : A ≤ (delta : ENNReal) ^ (-katzTaoExponent))
    (hC : C ≤ (delta : ENNReal) ^ (-globalFrostmanExponent)) :
    ∃ (_hCF : C *
        (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)) ≠ ∞)
      (_source_frostman : IsFrostmanOn
        (C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)))
        S.activeCoarseFamily
        (selectedOccurrenceFineIndices (actualUpperPartition S U P)
          (canonicalBufferedSelectedOccurrences S U P Y))
        closedBallFourBody),
      (((((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal) *
          canonicalEq45ConflictLoss S U) *
        ((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal)) *
        (uniqueOwnerLocalDeltaThickM 16
          (Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
            (canonicalBufferedSelectedRefinedCF S
              (C * (16 *
                (Fintype.card (ActiveParentIndex S) : ENNReal))))
            (canonicalBufferedSelectedFamily S U P Y)
            (canonicalBufferedSelectedAmbient (rho := rho)))
          (bufferedCommonWidth rho) (bufferedCommonWidth rho) : ENNReal) ^
            (beta / 2)) ≤
        (delta : ENNReal) ^
          (-(3 * (katzTaoExponent + 2 * scaleExponent +
              cardAbsorbExponent) +
            ((globalFrostmanExponent +
                (katzTaoExponent + 2 * scaleExponent +
                  cardAbsorbExponent) + selectionAbsorbExponent) +
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
  have hselected :=
    canonicalSelectedFine_nonempty_of_sourceShadingMass_ne_zero
      S U P Y hsourceMass
  have hsource : IsFrostmanOn
      (C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)))
      S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody := by
    exact canonicalSelected_source_frostman_of_nonempty
      S U P Y closedBallFourBody hglobal hselected hrhoHalf
  have hSourceCF :
      C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)) ≤
        (delta : ENNReal) ^
          (-(globalFrostmanExponent +
            (katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent) +
            selectionAbsorbExponent)) := by
    exact sourceCF_mul_sixteen_mul_card_le_delta_negativePower
      hD.delta_pos hselectionAbsorbExponent hselectionSmall hcard hC
  have hsourceExponent :
      0 ≤ globalFrostmanExponent +
        (katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent) +
        selectionAbsorbExponent := by
    linarith
  have hpowerTop :
      (delta : ENNReal) ^
          (-(globalFrostmanExponent +
            (katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent) +
            selectionAbsorbExponent)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  have hCF :
      C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)) ≠ ∞ :=
    ne_top_of_le_ne_top hpowerTop hSourceCF
  refine ⟨hCF, hsource, ?_⟩
  exact
    canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower_of_sourceKT
      D hD S U P Y hrho hrhoHalf
      (C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)))
      hCF hsource hKT scaleExponent katzTaoExponent cardAbsorbExponent
      (globalFrostmanExponent +
        (katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent) +
        selectionAbsorbExponent)
      refinementAbsorbExponent outerAbsorbExponent beta hscaleExponent
      hkatzTaoExponent hcardAbsorbExponent hsourceExponent
      hrefinementAbsorbExponent houterAbsorbExponent hbeta hcardSmall
      hrefinementSmall houterSmall hscale hA hSourceCF

#print axioms
  canonicalBufferedSelected_explicitOuterThickLoss_le_delta_negativePower_of_globalFrostman_sourceKT

end
end Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitGlobalOuterThickPowerV1
