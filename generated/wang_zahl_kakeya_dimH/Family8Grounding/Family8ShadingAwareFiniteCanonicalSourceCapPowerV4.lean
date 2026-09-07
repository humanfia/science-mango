import Family8Grounding.Family8ShadingAwareCanonicalSourceCapPowerV1
import Family8Grounding.Family8ShadingAwareLogPartitionCoefficientCongruenceV3
import Mathlib.Tactic

/-!
# Finite-source scalar adapter for the canonical shading-aware source cap, V4

The selected family types depend on the source coefficient.  Consequently,
rewriting the coefficient inside the whole partition elaborates a large
dependent term.  This successor transports only the natural-number cap used
by the analytic estimate, through the scalar congruence theorem of V3.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ShadingAwareFiniteCanonicalSourceCapPowerV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalOrdinaryFiberCapNumericsV1
open Family8ShadingAwareCanonicalSourceCapPowerV1
open Family8ShadingAwareLogPartitionCoefficientCongruenceV3
open Family8ShadingAwareSelectionBranchLossPowerV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The canonical power bound for the literal finite source coefficient.
Only the scalar natural cap is transported; no dependent partition equality
is asserted. -/
theorem shadingAwareFiniteCanonicalSourceCap_le_delta_negativePower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (Y : Shading D.family.bodyFamily)
    (sourceA : NNReal) (hsourceA : 0 < sourceA)
    {etaKT selectionEta scaleLoss fiberAbsorbExponent : Real}
    (hsourceACoe : (sourceA : ENNReal) =
      (delta : ENNReal) ^ (-etaKT))
    (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hetaKT : 0 < etaKT) (hselectionEta : 0 < selectionEta)
    (hKT : KatzTaoHypotheses D etaKT)
    (hscaleRatio :
      (rho : ENNReal) ^ 2 / ((delta : ENNReal) ^ 2 / 2) <=
        2 * (delta : ENNReal) ^ (-2 * scaleLoss))
    (hfiberAbsorbExponent : 0 < fiberAbsorbExponent)
    (hdeltaFiber : delta <=
      ordinaryFiberNatCapSmallDeltaThreshold fiberAbsorbExponent)
    (hdeltaSelection : delta <=
      shadingAwareSelectionBranchLossPowerThreshold selectionEta) :
    let P0 := shadingAwareLogPartition S Y (sourceA : ENNReal)
      (ENNReal.coe_ne_zero.mpr hsourceA.ne') ENNReal.coe_ne_top
      (hD.delta_pos.trans_le hdeltaRho) hdeltaRho hactive hmass
    (((2 * (Nat.log 2 (Fintype.card index) + 1)) *
        (P0.branchingLoss * P0.branching) : Nat) : ENNReal) <=
      (delta : ENNReal) ^
        (-(selectionEta +
          ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent)) := by
  dsimp only
  let powerA : ENNReal := (delta : ENNReal) ^ (-etaKT)
  have hsourceA0 : (sourceA : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hsourceA.ne'
  have hsourceAtop : (sourceA : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hpowerA0 : powerA ≠ 0 := by
    dsimp only [powerA]
    exact ne_of_gt
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top)
  have hpowerAtop : powerA ≠ ∞ := by
    dsimp only [powerA]
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  let Psource := shadingAwareLogPartition S Y (sourceA : ENNReal)
    hsourceA0 hsourceAtop (hD.delta_pos.trans_le hdeltaRho)
    hdeltaRho hactive hmass
  let Ppower := shadingAwareLogPartition S Y powerA
    hpowerA0 hpowerAtop (hD.delta_pos.trans_le hdeltaRho)
    hdeltaRho hactive hmass
  have hpower :
      (((2 * (Nat.log 2 (Fintype.card index) + 1)) *
          (Ppower.branchingLoss * Ppower.branching) : Nat) : ENNReal) <=
        (delta : ENNReal) ^
          (-(selectionEta +
            ordinaryFiberPowerEnvelope scaleLoss etaKT
              fiberAbsorbExponent)) := by
    simpa only [powerA, Ppower] using
      (shadingAwareCanonicalSourceCap_le_delta_negativePower
        D hD S Y hdeltaRho hrhoOne hactive hmass hetaKT hselectionEta
        hKT hscaleRatio hfiberAbsorbExponent hdeltaFiber hdeltaSelection)
  have hcapEq :
      (2 * (Nat.log 2 (Fintype.card index) + 1)) *
          (Psource.branchingLoss * Psource.branching) =
        (2 * (Nat.log 2 (Fintype.card index) + 1)) *
          (Ppower.branchingLoss * Ppower.branching) := by
    dsimp only [Psource, Ppower]
    exact shadingAwareLogPartition_sourceCap_congr_coefficient
      S Y (hsourceACoe.trans (by rfl)) hsourceA0 hsourceAtop
      hpowerA0 hpowerAtop (hD.delta_pos.trans_le hdeltaRho)
      hdeltaRho hactive hmass
  have hcapCoe := congrArg (fun n : Nat => (n : ENNReal)) hcapEq
  change
    (((2 * (Nat.log 2 (Fintype.card index) + 1)) *
        (Psource.branchingLoss * Psource.branching) : Nat) : ENNReal) <=
      (delta : ENNReal) ^
        (-(selectionEta +
          ordinaryFiberPowerEnvelope scaleLoss etaKT fiberAbsorbExponent))
  exact hcapCoe.le.trans hpower

#print axioms
  shadingAwareFiniteCanonicalSourceCap_le_delta_negativePower

end
end Family8ShadingAwareFiniteCanonicalSourceCapPowerV4
