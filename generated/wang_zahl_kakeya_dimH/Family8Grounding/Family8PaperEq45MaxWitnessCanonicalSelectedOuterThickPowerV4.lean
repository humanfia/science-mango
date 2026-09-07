import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickNEnvelopeV1
import Family8Grounding.Family8CanonicalOuterThickNEnvelopePowerAlgebraV4
import Family8Grounding.Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
import Mathlib.Tactic

/-!
# Actual canonical Equation (45) outer/thick power envelope

This composes the literal selected-object `N` envelope with the two scalar
power lemmas.  The only remaining inputs are honest power bounds for the
actual active-parent cardinality and the unrefined source Frostman constant.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickPowerV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CanonicalOuterThickNEnvelopePowerAlgebraV4
open Family8CanonicalSelectedRefinedFrostmanPowerAlgebraV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8PaperEq45MaxWitnessCanonicalSelectedInputV3
open Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickNEnvelopeV1
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
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
  {fine : UniformTubeFamily delta index}
  (S : StickyScaleCover fine rho)
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

theorem canonicalSelected_outerThickLoss_le_delta_negativePower
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (cardExponent frostmanExponent refinementAbsorbExponent
      outerAbsorbExponent beta : Real)
    (hcardExponent : 0 ≤ cardExponent)
    (hfrostmanExponent : 0 ≤ frostmanExponent)
    (hrefinementAbsorbExponent : 0 < refinementAbsorbExponent)
    (houterAbsorbExponent : 0 < outerAbsorbExponent)
    (hbeta : 0 ≤ beta)
    (hrefinementSmall : delta ≤
      canonicalSelectedRefinementFixedThreshold
        refinementAbsorbExponent)
    (houterSmall : delta ≤
      canonicalOuterThickFixedThreshold beta outerAbsorbExponent)
    (hN : (Fintype.card (ActiveParentIndex S) : ENNReal) ≤
      (delta : ENNReal) ^ (-cardExponent))
    (hSourceCF : CF ≤
      (delta : ENNReal) ^ (-frostmanExponent)) :
    let I := canonicalSelectedInput S U P Y hrho hrhoHalf h2rho
      sourceAmbient ambientComparisonConstant ambient_is_unit_scale
      CF hCF source_frostman
    (((((I.fibreCardCap : ENNReal) * canonicalEq45ConflictLoss S U) *
        (I.fibreCardCap : ENNReal)) *
      (thickM U I : ENNReal) ^ (beta / 2))) ≤
      (delta : ENNReal) ^
        (-(3 * cardExponent +
          (frostmanExponent + 2 * cardExponent +
            refinementAbsorbExponent) * (beta / 2) +
          outerAbsorbExponent)) := by
  dsimp only
  have hrefined : canonicalSelectedRefinedCF S CF ≤
      (delta : ENNReal) ^
        (-(frostmanExponent + cardExponent +
          refinementAbsorbExponent)) := by
    exact sourceCF_mul_sixteen_mul_card_le_delta_negativePower
      hdelta hrefinementAbsorbExponent hrefinementSmall hN hSourceCF
  have hrefinedExponent :
      0 ≤ frostmanExponent + cardExponent + refinementAbsorbExponent := by
    linarith
  have hpower := canonicalOuterThickNEnvelope_le_delta_negativePower
    hdelta hdeltaOne hcardExponent hrefinedExponent hbeta
    houterAbsorbExponent houterSmall hN hrefined
  have houter := canonicalSelected_outerThickLoss_le_NEnvelope
    S U P Y hrho hrhoHalf h2rho sourceAmbient
    ambientComparisonConstant ambient_is_unit_scale
    CF hCF source_frostman beta hbeta
  exact houter.trans (by
    convert hpower using 1
    · rfl
    · congr 1
      ring)

#print axioms canonicalSelected_outerThickLoss_le_delta_negativePower

end
end Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickPowerV4
