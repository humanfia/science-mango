import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFiniteBoundsV1
import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalOuterThickLossUpperV1
import Mathlib.Tactic

/-!
# Explicit same-selected buffered outer/thick envelope

This is the elaboration-safe successor to the monolithic dependent-input
statement.  Its scalar is nevertheless literal: the exact-degree conflict
loss, active-parent card, selected buffered family, buffered ambient body,
canonical Delta, and comparison constant `16` all occur in the conclusion.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickNEnvelopeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8BufferedCommonScaleTubePlankV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1
open Family8PaperEq45MaxWitnessBufferedCanonicalOuterThickLossUpperV1
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFiniteBoundsV1
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

theorem canonicalBufferedSelected_explicitOuterThickLoss_le_NEnvelope
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody)
    (beta : Real) (hbeta : 0 ≤ beta) :
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
      (((((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal) *
          ((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal)) *
        ((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal)) *
      (max 1 ((110592 : ENNReal) *
        canonicalBufferedSelectedRefinedCF S CF *
        ((Fintype.card (ActiveParentIndex S) : Nat) : ENNReal))) ^
          (beta / 2)) := by
  exact bufferedCanonicalMaxWitness_outerThickLoss_le_NEnvelope
    (canonicalBufferedSelectedRefinedCF S CF)
    (canonicalBufferedSelectedFamily S U P Y)
    (canonicalBufferedSelectedAmbient (rho := rho))
    (canonicalBufferedSelectedRefinedCF_ne_top S CF hCF)
    (canonicalBufferedSelectedFamily_contained S U P Y CF source_frostman)
    (canonicalBufferedSelectedAmbient_volume_ne_zero (rho := rho) hrhoHalf)
    (Fintype.card (ActiveParentIndex S) : ENNReal)
    (canonicalEq45ConflictLoss S U)
    (Fintype.card (ActiveParentIndex S) : ENNReal)
    le_rfl (canonicalEq45ConflictLoss_le_activeParentCard S U)
    (canonicalBufferedSelected_card_le_activeParentCard_ennreal S U P Y)
    (bufferedCommonWidth rho) (bufferedCommonWidth_pos hrho) beta hbeta

#print axioms
  canonicalBufferedSelected_explicitOuterThickLoss_le_NEnvelope

end
end Family8PaperEq45MaxWitnessBufferedCanonicalSelectedExplicitOuterThickNEnvelopeV2
