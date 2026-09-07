import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickSourceKatzTaoPowerV2
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
import Mathlib.Tactic

/-!
# Global production of the canonical Equation (45) outer/thick power

Nonzero source shaded mass makes the literal exact-degree canonical selection
nonempty. Uniform tube volumes then restrict global Frostman control to that
same selected source with loss `16 * N`. Both this selection loss and the
subsequent common-witness refinement loss are absorbed using the actual
scale-cover Katz--Tao cardinality bound.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedGlobalOuterThickPowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8CanonicalOuterThickNEnvelopePowerAlgebraV4
open Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8PaperEq45MaxWitnessCanonicalSelectedGlobalFrostmanV3
open Family8PaperEq45MaxWitnessCanonicalSelectedInputV3
open Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV5
open Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickSourceKatzTaoPowerV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

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
  (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
  (h2rho : 2 * rho ≤ sigma)
  (sourceAmbient : ConvexBody Space)
  (ambientComparisonConstant : NNReal)
  (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
    (affineImageConvexBody (maxWitnessCommonScaleEquiv rho) sourceAmbient))

include hD in
theorem canonicalSelected_outerThickLoss_le_delta_negativePower_of_globalFrostman_sourceKT
    {A C : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    (hglobal : IsFrostmanOn C S.activeCoarseFamily Finset.univ sourceAmbient)
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
      canonicalOuterThickFixedThreshold beta outerAbsorbExponent)
    (hscale : (delta : ENNReal) ^ scaleExponent ≤ (rho : ENNReal))
    (hA : A ≤ (delta : ENNReal) ^ (-katzTaoExponent))
    (hC : C ≤ (delta : ENNReal) ^ (-globalFrostmanExponent)) :
    ∃ (hCF : C *
        (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)) ≠ ∞)
      (source_frostman : IsFrostmanOn
        (C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)))
        S.activeCoarseFamily
        (selectedOccurrenceFineIndices (actualUpperPartition S U P)
          (canonicalSelectedOccurrences S U P Y)) sourceAmbient),
      let I := canonicalSelectedInput S U P Y hrho hrhoHalf h2rho
        sourceAmbient ambientComparisonConstant ambient_is_unit_scale
        (C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)))
        hCF source_frostman
      (((((I.fibreCardCap : ENNReal) * canonicalEq45ConflictLoss S U) *
          (I.fibreCardCap : ENNReal)) *
        (thickM U I : ENNReal) ^ (beta / 2))) ≤
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
  have hcardExponent :
      0 ≤ katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent := by
    linarith
  have hselected :=
    canonicalSelectedFine_nonempty_of_sourceShadingMass_ne_zero
      S U P Y hsourceMass
  have hsource : IsFrostmanOn
      (C * (16 * (Fintype.card (ActiveParentIndex S) : ENNReal)))
      S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalSelectedOccurrences S U P Y)) sourceAmbient :=
    canonicalSelected_source_frostman_of_nonempty
      S U P Y sourceAmbient hglobal hselected hrhoHalf
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
    canonicalSelected_outerThickLoss_le_delta_negativePower_of_sourceKT
      D hD S U P Y hrho hrhoHalf h2rho sourceAmbient
      ambientComparisonConstant ambient_is_unit_scale
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
  canonicalSelected_outerThickLoss_le_delta_negativePower_of_globalFrostman_sourceKT

end
end Family8PaperEq45MaxWitnessCanonicalSelectedGlobalOuterThickPowerV3
