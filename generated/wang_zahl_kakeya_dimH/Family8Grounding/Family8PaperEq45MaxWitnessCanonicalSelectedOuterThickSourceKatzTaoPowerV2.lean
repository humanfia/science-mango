import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickPowerV4
import Family8Grounding.Family8AllFrostmanStickyPopularParentPowerV4
import Mathlib.Tactic

/-!
# Source-Katz--Tao production of the canonical Equation (45) card power

The active-parent cardinality premise of the actual canonical power envelope
is discharged from the literal scale-cover Katz--Tao certificate.  After this
module the sole analytic input on the Equation (45) side is the power bound
for the unrefined selected-source Frostman constant.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickSourceKatzTaoPowerV2

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
open Family8PaperEq45MaxWitnessCanonicalSelectedInputV3
open Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickPowerV4
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
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
  (CF : ENNReal) (hCF : CF ≠ ∞)
  (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
    (selectedOccurrenceFineIndices (actualUpperPartition S U P)
      (occurrencesMaxOwnedBy U (actualUpperPartition S U P) Y Finset.univ
        (canonicalEq45ConflictSelection S U P Y).selected))
    sourceAmbient)

include hD in
theorem canonicalSelected_outerThickLoss_le_delta_negativePower_of_sourceKT
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
      canonicalSelectedRefinementFixedThreshold
        refinementAbsorbExponent)
    (houterSmall : delta ≤
      canonicalOuterThickFixedThreshold beta outerAbsorbExponent)
    (hscale : (delta : ENNReal) ^ scaleExponent ≤ (rho : ENNReal))
    (hA : A ≤ (delta : ENNReal) ^ (-katzTaoExponent))
    (hSourceCF : CF ≤
      (delta : ENNReal) ^ (-frostmanExponent)) :
    let I := canonicalSelectedInput S U P Y hrho hrhoHalf h2rho
      sourceAmbient ambientComparisonConstant ambient_is_unit_scale
      CF hCF source_frostman
    (((((I.fibreCardCap : ENNReal) * canonicalEq45ConflictLoss S U) *
        (I.fibreCardCap : ENNReal)) *
      (thickM U I : ENNReal) ^ (beta / 2))) ≤
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
  exact canonicalSelected_outerThickLoss_le_delta_negativePower
    S U P Y hrho hrhoHalf h2rho sourceAmbient
    ambientComparisonConstant ambient_is_unit_scale CF hCF source_frostman
    hD.delta_pos (hD.delta_le_half.trans (by norm_num))
    (katzTaoExponent + 2 * scaleExponent + cardAbsorbExponent)
    frostmanExponent refinementAbsorbExponent outerAbsorbExponent beta
    hcardExponent hfrostmanExponent hrefinementAbsorbExponent
    houterAbsorbExponent hbeta hrefinementSmall houterSmall hcard hSourceCF

#print axioms
  canonicalSelected_outerThickLoss_le_delta_negativePower_of_sourceKT

end
end Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickSourceKatzTaoPowerV2
