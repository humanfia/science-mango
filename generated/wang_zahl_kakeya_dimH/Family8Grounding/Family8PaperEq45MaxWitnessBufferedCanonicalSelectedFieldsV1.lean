import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedInputV1
import Mathlib.Tactic

/-!
# Definitional fields of the actual buffered selected Equation (45) input

This module freezes the literal family, ambient body, Frostman constant,
canonical Delta, thickening loss, and selected cardinality of the exact-degree
buffered input.  The equalities are definitional and introduce no numerical
assumption.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFieldsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8BufferedCommonScaleTubePlankV1
open Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1.PaperEq45MaxWitnessBufferedInput
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedInputV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleDatumV1
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
  {fine : UniformTubeFamily delta index}
  (S : StickyScaleCover fine rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  (Y : Shading S.activeCoarseFamily)

noncomputable abbrev canonicalBufferedSelectedOccurrences :=
  occurrencesMaxOwnedBy U (actualUpperPartition S U P) Y Finset.univ
    (canonicalEq45ConflictSelection S U P Y).selected

noncomputable abbrev canonicalBufferedSelectedFamily :=
  selectedOccurrenceMaxWitnessBufferedFamily U Y
    (canonicalBufferedSelectedOccurrences S U P Y)

noncomputable abbrev canonicalBufferedSelectedAmbient :=
  affineImageConvexBody (bufferedCommonScaleEquiv rho) closedBallFourBody

def canonicalBufferedSelectedRefinedCF (CF : ENNReal) : ENNReal :=
  bufferedRefinedFrostmanConstant CF
    (Fintype.card (ActiveParentIndex S))

noncomputable abbrev canonicalBufferedSelectedInput
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody) :=
  canonicalEq45BufferedInput S U P Y hrho hrhoHalf h2rho
    CF hCF source_frostman

@[simp] theorem canonicalBufferedSelectedInput_frostmanConstant
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody) :
    (canonicalBufferedSelectedInput S U P Y hrho hrhoHalf h2rho
      CF hCF source_frostman).frostmanConstant =
        canonicalBufferedSelectedRefinedCF S CF := by
  rfl

@[simp] theorem canonicalBufferedSelectedInput_Delta
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody) :
    (canonicalBufferedSelectedInput S U P Y hrho hrhoHalf h2rho
      CF hCF source_frostman).Delta =
      Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
        (canonicalBufferedSelectedRefinedCF S CF)
        (canonicalBufferedSelectedFamily S U P Y)
        (canonicalBufferedSelectedAmbient (rho := rho)) := by
  rfl

@[simp] theorem canonicalBufferedSelectedInput_thickM
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody) :
    thickM U (canonicalBufferedSelectedInput S U P Y hrho hrhoHalf h2rho
      CF hCF source_frostman) =
      uniqueOwnerLocalDeltaThickM 16
        (Family8PaperEq45MaxWitnessBufferedCanonicalV1.canonicalMaxWitnessDelta
          (canonicalBufferedSelectedRefinedCF S CF)
          (canonicalBufferedSelectedFamily S U P Y)
          (canonicalBufferedSelectedAmbient (rho := rho)))
        (bufferedCommonWidth rho) (bufferedCommonWidth rho) := by
  rfl

@[simp] theorem canonicalBufferedSelectedInput_plankCount
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody) :
    plankCount U (canonicalBufferedSelectedInput S U P Y hrho hrhoHalf h2rho
      CF hCF source_frostman) =
      Fintype.card {q // q ∈ selectedOccurrenceIndices
        (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y)} := by
  rfl

#print axioms canonicalBufferedSelectedInput_frostmanConstant
#print axioms canonicalBufferedSelectedInput_Delta
#print axioms canonicalBufferedSelectedInput_thickM
#print axioms canonicalBufferedSelectedInput_plankCount

end
end Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFieldsV1
