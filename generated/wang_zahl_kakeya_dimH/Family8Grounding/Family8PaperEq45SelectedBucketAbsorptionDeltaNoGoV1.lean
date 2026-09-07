import Family8Grounding.Family8PaperEq45MaxWitnessSelectedBucketUpperV1
import Mathlib.Tactic

/-!
# Delta underdetermination in selected-bucket Equation (45) absorption

The current max-witness input records only a lower bound on `Delta`.  Hence
`Delta` can be inflated without changing the actual datum, shading, Frostman
constant, selected occurrences, or cardinal cap.  The honest Family 6 factor
does change, through `thickM = max 1 (216 * Delta)` at the isotropic common
witness.

This module formalizes that obstruction.  It is an audit theorem, not a new
hypothesis wrapper: a uniform selected-bucket absorption theorem needs an
actual upper control on `Delta`, or must retain the resulting thickening loss.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PaperEq45SelectedBucketAbsorptionDeltaNoGoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8UniqueOwnerLocalDeltaMaxThickControlV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}
  {Y : Shading fine.bodyFamily}
  {R0 : Finset (Fin (blocks fine.bodyFamily P).length)}
  {conflictLoss : ENNReal}
  {W : DoubledParentConflictWeightedSelection C
    (occurrenceMaxOwnerMass C P Y R0) conflictLoss}

/-- Inflate only the underconstrained `Delta` field.  Every field describing
the actual max-witness object remains definitionally unchanged. -/
def inflateMaxWitnessDelta
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W :=
  { I with
    Delta := max I.Delta level
    Delta_dominates := I.Delta_dominates.trans
      (ENNReal.coe_le_coe.mpr (le_max_left I.Delta level)) }

@[simp] theorem inflateMaxWitnessDelta_Delta
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    (inflateMaxWitnessDelta C I level).Delta = max I.Delta level := rfl

@[simp] theorem inflateMaxWitnessDelta_frostmanConstant
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    (inflateMaxWitnessDelta C I level).frostmanConstant =
      I.frostmanConstant := rfl

@[simp] theorem inflateMaxWitnessDelta_fibreCardCap
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    (inflateMaxWitnessDelta C I level).fibreCardCap = I.fibreCardCap := rfl

@[simp] theorem inflateMaxWitnessDelta_datum
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    datum C (inflateMaxWitnessDelta C I level) = datum C I := rfl

@[simp] theorem inflateMaxWitnessDelta_selected
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    selected C (inflateMaxWitnessDelta C I level) = selected C I := rfl

/-- The honest thickening count is monotone under the admissible inflation. -/
theorem thickM_le_thickM_inflateMaxWitnessDelta
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    thickM C I <= thickM C (inflateMaxWitnessDelta C I level) := by
  unfold thickM uniqueOwnerLocalDeltaThickM
  gcongr
  exact le_max_left I.Delta level

/-- More strongly, the same unchanged actual object supports inputs whose
recorded thickening count dominates any prescribed finite level. -/
theorem level_le_thickM_inflateMaxWitnessDelta
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    level <= thickM C (inflateMaxWitnessDelta C I level) := by
  have hw : maxWitnessCommonWidth delta ≠ 0 :=
    (maxWitnessCommonWidth_pos I.delta_pos).ne'
  simp only [thickM, uniqueOwnerLocalDeltaThickM,
    inflateMaxWitnessDelta_Delta, div_self hw]
  calc
    level <= max I.Delta level := le_max_right I.Delta level
    _ <= 27 * 2 ^ 3 * max I.Delta level * 1 := by
      nlinarith [show 0 <= max I.Delta level from bot_le]
    _ <= max 1 (27 * 2 ^ 3 * max I.Delta level * 1) :=
      le_max_right _ _

/-- For nonnegative `beta`, the genuine Family 6 factor is monotone in this
otherwise invisible input inflation. -/
theorem family6Factor_le_inflateMaxWitnessDelta
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) {epsilon beta : Real} (hbeta : 0 <= beta) :
    family6Factor C I epsilon beta <=
      family6Factor C (inflateMaxWitnessDelta C I level) epsilon beta := by
  unfold family6Factor convexPlankFrostmanFactor
  simp only [inflateMaxWitnessDelta_frostmanConstant,
    inflateMaxWitnessDelta_selected]
  gcongr
  exact thickM_le_thickM_inflateMaxWitnessDelta C I level

/-- Precise audit endpoint: all target-visible object/cardinal data are fixed,
while the hidden thickening count has no upper bound in the current input
type. -/
theorem exists_sameObjectInput_with_level_le_thickM
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (level : NNReal) :
    exists I' : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W,
      datum C I' = datum C I /\
      I'.frostmanConstant = I.frostmanConstant /\
      I'.fibreCardCap = I.fibreCardCap /\
      level <= thickM C I' := by
  refine ⟨inflateMaxWitnessDelta C I level, rfl, rfl, rfl, ?_⟩
  exact level_le_thickM_inflateMaxWitnessDelta C I level

#print axioms inflateMaxWitnessDelta
#print axioms thickM_le_thickM_inflateMaxWitnessDelta
#print axioms level_le_thickM_inflateMaxWitnessDelta
#print axioms family6Factor_le_inflateMaxWitnessDelta
#print axioms exists_sameObjectInput_with_level_le_thickM

end
end Family8PaperEq45SelectedBucketAbsorptionDeltaNoGoV1
