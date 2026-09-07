import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalOuterThickLossUpperV1
import Mathlib.Tactic

/-!
# Actual canonical selected input for Equation (45)

The common-scale constructor was previously never instantiated.  This module
builds its literal upper-cover input: the doubled-parent selection uses the
exact finite conflict degree, and the fibre cap is the actual active-parent
index cardinality.  Consequently the conflict loss, selected witness count,
and fibre cap all have the same automatic finite envelope.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickEnvelopeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictExactDegreeBudgetV1.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family6AffineConvexVolumeCoreV1
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8PaperEq45MaxWitnessCanonicalSelectedInputV3
open Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalOuterThickLossUpperV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

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

theorem canonicalSelected_outerThickLoss_le_explicitCardEnvelope
    (beta : Real) (hbeta : 0 ≤ beta) :
    let I := canonicalSelectedInput S U P Y hrho hrhoHalf h2rho
      sourceAmbient ambientComparisonConstant ambient_is_unit_scale
      CF hCF source_frostman
    (((((I.fibreCardCap : ENNReal) * canonicalEq45ConflictLoss S U) *
        (I.fibreCardCap : ENNReal)) *
      (thickM U I : ENNReal) ^ (beta / 2))) ≤
      (((((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal) *
          canonicalEq45ConflictLoss S U) *
        ((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal)) *
      (max 1 ((216 : ENNReal) * canonicalSelectedRefinedCF S CF *
        (Fintype.card {q // q ∈ selectedOccurrenceIndices
          (actualUpperPartition S U P)
          (canonicalSelectedOccurrences S U P Y)} : ENNReal))) ^
        (beta / 2)) := by
  dsimp only
  have hrefinedTop : canonicalSelectedRefinedCF S CF ≠ ∞ :=
    maxWitnessRefinedFrostmanConstant_ne_top CF
      (Fintype.card (ActiveParentIndex S)) hCF
  have hcontained : ∀ q,
      (canonicalSelectedFamily S U P Y q : Set Space) ⊆
        (canonicalSelectedAmbient (rho := rho) sourceAmbient : Set Space) := by
    intro q
    exact Set.image_mono
      (selectedOccurrenceMaxWitness_subset_ambient U Y
        (canonicalSelectedOccurrences S U P Y) sourceAmbient
        source_frostman q)
  have hraw :=
    canonicalMaxWitness_outerThickLoss_le_explicitCardEnvelope
      (canonicalSelectedRefinedCF S CF)
      (canonicalSelectedFamily S U P Y)
      (canonicalSelectedAmbient (rho := rho) sourceAmbient)
      hrefinedTop hcontained (ne_of_gt ambient_is_unit_scale.volume_pos)
      (Fintype.card (ActiveParentIndex S))
      (canonicalEq45ConflictLoss S U)
      (maxWitnessCommonWidth rho) (maxWitnessCommonWidth_pos hrho)
      beta hbeta
  simp only [canonicalEq45CommonScaleInput_fibreCardCap,
    canonicalSelectedInput_thickM]
  convert hraw using 1
  all_goals rfl

#print axioms canonicalSelected_outerThickLoss_le_explicitCardEnvelope

end
end Family8PaperEq45MaxWitnessCanonicalSelectedOuterThickEnvelopeV1
