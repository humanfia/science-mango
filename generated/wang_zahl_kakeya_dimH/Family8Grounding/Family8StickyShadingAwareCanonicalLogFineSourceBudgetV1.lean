import Family8Grounding.Family8StickyShadingAwareCanonicalLogPartitionV1
import Family8Grounding.Family8WithinFactorFineCardSourceBudgetV3
import Mathlib.Tactic

/-!
# Fine-card source budget for the shading-aware logarithmic partition

Actual selected shading retention implies selected tube-body retention by a
literal termwise carrier inclusion.  This avoids any dependent cast between
the original and refinement-retagged body-family types.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyShadingAwareCanonicalLogFineSourceBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareCanonicalLogRestrictedFamiliesV1
open Family8WithinFactorFineCardSourceBudgetV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem shadingAwareLogPartition_fine_sourceBudget
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (sourceA fineTarget : NNReal) (hsourceA : 0 < sourceA)
    (hrho : 0 < rho) (hscale : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hFineAbsorb :
      (131072 : ENNReal) *
          (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) *
          (2 : ENNReal) ^ 2 * (sourceA : ENNReal) ≤
        (fineTarget : ENNReal) * shadingMassOn Y S.activeFine) :
    8192 * ((shadingAwareLogPartition
        S Y (sourceA : ENNReal)
          (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
          hrho hscale hactive hmass).branchingLoss : NNReal) ^ 2 * sourceA ≤
      fineTarget *
        ((shadingAwareLogPartition
          S Y (sourceA : ENNReal)
            (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
            hrho hscale hactive hmass).fineIndices.card : NNReal) *
        (delta ^ 2 / 2) := by
  let Ppart := shadingAwareLogPartition
    S Y (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      hrho hscale hactive hmass
  let Fsel := shadingAwareSelectedFineFamily
    S Y (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      hrho hactive hmass
  have hretainShading := shadingAwareLogPartition_shadingMass_withinFactor
    S Y (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      hrho hscale hactive hmass
  have hmassLe :
      shadingMassOn Y Ppart.fineIndices ≤
        bodyMassOn Fsel.bodyFamily Ppart.fineIndices := by
    unfold shadingMassOn bodyMassOn
    apply Finset.sum_le_sum
    intro i hi
    change volume (Y.carrier i) ≤ volume (fine.tubes i).carrier
    exact measure_mono (Y.carrier_subset i)
  have hretainBody : WithinFactor
      (2 * (Nat.log 2 (Fintype.card index) + 1))
      (shadingMassOn Y S.activeFine)
      (bodyMassOn Fsel.bodyFamily Ppart.fineIndices) := by
    unfold WithinFactor at hretainShading ⊢
    calc
      shadingMassOn Y S.activeFine ≤
          (2 * (Nat.log 2 (Fintype.card index) + 1)) •
            shadingMassOn Y Ppart.fineIndices := by
        simpa only [Ppart] using hretainShading
      _ ≤ (2 * (Nat.log 2 (Fintype.card index) + 1)) •
          bodyMassOn Fsel.bodyFamily Ppart.fineIndices :=
        nsmul_le_nsmul_right hmassLe _
  have hbudget := fineCard_source_budget_of_withinFactor
    Fsel Ppart.fineIndices hdeltaHalf
    (shadingMassOn Y S.activeFine)
    (2 * (Nat.log 2 (Fintype.card index) + 1)) 2
    sourceA fineTarget (by omega) hretainBody hFineAbsorb
  simpa only [Ppart, shadingAwareLogPartition_branchingLoss] using hbudget

#print axioms shadingAwareLogPartition_fine_sourceBudget

end
end Family8StickyShadingAwareCanonicalLogFineSourceBudgetV1
