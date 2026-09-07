import Family8Grounding.Family8AllFrostmanStickyPopularFiberPowerV3
import Family8Grounding.Family8ShadingAwareLogPartitionKatzTaoBranchingCapV2
import Family8Grounding.Family8ShadingAwareSelectionBranchLossPowerV1
import Mathlib.Tactic

/-!
# Canonical power envelope for the full shading-aware source cap

For the canonical source Katz--Tao constant `delta ^ (-etaKT)`, the actual
shading-aware source cap is the product of two independently produced terms:
the logarithmic selection plus fixed branching loss, and the selected
branching itself.  The former costs an arbitrary small power; the latter is
bounded by the genuine doubled-fibre Katz--Tao ceiling and its established
ordinary-fibre power envelope.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ShadingAwareCanonicalSourceCapPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyPopularFiberPowerV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8ShadingAwareLogPartitionKatzTaoBranchingCapV2
open Family8ShadingAwareSelectionBranchLossPowerV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The complete actual source cap of the same shading-aware partition is
bounded by the sum of its small logarithmic exponent and the established
ordinary-fibre exponent. -/
theorem shadingAwareCanonicalSourceCap_le_delta_negativePower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (Y : Shading D.family.bodyFamily)
    (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    {etaKT selectionEta scaleLoss fiberAbsorbExponent : Real}
    (hEtaKT : 0 < etaKT) (hselectionEta : 0 < selectionEta)
    (hKT : KatzTaoHypotheses D etaKT)
    (hscaleRatio :
      (rho : ENNReal) ^ 2 / ((delta : ENNReal) ^ 2 / 2) <=
        2 * (delta : ENNReal) ^ (-2 * scaleLoss))
    (hfiberAbsorb : 0 < fiberAbsorbExponent)
    (hdeltaFiber :
      delta <= ordinaryFiberNatCapSmallDeltaThreshold fiberAbsorbExponent)
    (hdeltaSelection :
      delta <= shadingAwareSelectionBranchLossPowerThreshold selectionEta) :
    let sourceA : ENNReal := (delta : ENNReal) ^ (-etaKT)
    let Ppart := shadingAwareLogPartition S Y sourceA
      (by
        dsimp only [sourceA]
        exact ne_of_gt
          (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
            ENNReal.coe_ne_top))
      (by
        dsimp only [sourceA]
        exact ENNReal.rpow_ne_top_of_ne_zero
          (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top)
      (hD.delta_pos.trans_le hdeltaRho) hdeltaRho hactive hmass
    (((2 * (Nat.log 2 (Fintype.card index) + 1)) *
        (Ppart.branchingLoss * Ppart.branching) : Nat) : ENNReal) <=
      (delta : ENNReal) ^
        (-(selectionEta +
          ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent)) := by
  dsimp only
  let sourceA : ENNReal := (delta : ENNReal) ^ (-etaKT)
  let Ppart := shadingAwareLogPartition S Y sourceA
    (by
      dsimp only [sourceA]
      exact ne_of_gt
        (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
          ENNReal.coe_ne_top))
    (by
      dsimp only [sourceA]
      exact ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top)
    (hD.delta_pos.trans_le hdeltaRho) hdeltaRho hactive hmass
  have hsourceA0 : sourceA ≠ 0 := by
    dsimp only [sourceA]
    exact ne_of_gt
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top)
  have hsourceAtop : sourceA ≠ ∞ := by
    dsimp only [sourceA]
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  have hsourceKT : IsKatzTao sourceA D.family.bodyFamily := by
    dsimp only [sourceA]
    exact ((katzTaoHypotheses_iff_density_and_isKatzTao D etaKT).mp hKT).2
  have hbranchNat : Ppart.branching <=
      katzTaoDoubledFiberNatCap delta rho sourceA := by
    dsimp only [Ppart]
    exact shadingAwareLogPartition_branching_le_katzTaoDoubledFiberNatCap
      S Y sourceA hsourceA0 hsourceAtop
      (hD.delta_pos.trans_le hdeltaRho) hdeltaRho hactive hmass
      hD.delta_pos hD.delta_le_half hrhoOne hsourceKT
  have hbranch : (Ppart.branching : ENNReal) <=
      (katzTaoDoubledFiberNatCap delta rho sourceA : ENNReal) := by
    exact_mod_cast hbranchNat
  have hfiber :=
    (activeIndexFiber_card_and_power_le_of_katzTaoHypotheses
      D hD S hdeltaRho hrhoOne hEtaKT hKT hscaleRatio
      hfiberAbsorb hdeltaFiber).2
  have hselection :=
    shadingAwareSelectionBranchLoss_le_delta_negativePower
      D hD hselectionEta hdeltaSelection
  have hsourceCapIdentity :
      (((2 * (Nat.log 2 (Fintype.card index) + 1)) *
          (Ppart.branchingLoss * Ppart.branching) : Nat) : ENNReal) =
        ((2 * (2 * (Nat.log 2 (Fintype.card index) + 1)) : Nat) : ENNReal) *
          (Ppart.branching : ENNReal) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    simp only [Ppart, shadingAwareLogPartition_branchingLoss]
    norm_num
    ring
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  rw [hsourceCapIdentity]
  calc
    ((2 * (2 * (Nat.log 2 (Fintype.card index) + 1)) : Nat) : ENNReal) *
        (Ppart.branching : ENNReal) <=
      (delta : ENNReal) ^ (-selectionEta) *
        (delta : ENNReal) ^
          (-ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent) :=
      mul_le_mul' hselection (hbranch.trans hfiber)
    _ = (delta : ENNReal) ^
        (-(selectionEta +
          ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent)) := by
      rw [show -(selectionEta +
          ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent) =
        -selectionEta +
          -ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent by
        ring,
        ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]

#print axioms shadingAwareCanonicalSourceCap_le_delta_negativePower

end
end Family8ShadingAwareCanonicalSourceCapPowerV1
