import Family8Grounding.Family8StickyShadingAwareSelectedBaseRatioGlobalPowerV1
import Family8Grounding.Family8StickyShadingAwareSelectedFiberDensityFloorV1
import Family8Grounding.Family8ShadingAwareDensityFloorGlobalPowerV1
import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Mathlib.Tactic

/-!
# Same-parent source power budgets with a separate global parameter, V2

V1 omitted the scale-order binder required by the log partition and is not imported.  One genuine shading-aware mass-popular parent supplies both the normalized
contracted-John base comparison and the retained source-density comparison.
The fine radius controls geometry, while `globalDelta` controls all small
power absorptions.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyShadingAwareSelectedSourcePowerBudgetsGlobalV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ShadingAwareDensityFloorGlobalPowerV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open Family8StickyShadingAwareCanonicalLogPartitionV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareSelectedBaseRatioGlobalPowerV1
open Family8StickyShadingAwareSelectedFiberDensityFloorV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {globalDelta delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The same mass-popular active parent satisfies both literal source power
premises of the fresh low-CF long-middle producer. -/
theorem exists_shadingAwareSelected_sourceDensity_and_basePower
    {eta p a etaF lossExp xExp baseAbsorbExp baseScaleExp : Real}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hdeltaRho : delta ≤ rho)
    (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0)
    (hloss :
      (2 * (Nat.log 2 (Fintype.card index) + 1) : Nat) ≤
        (globalDelta : ENNReal) ^ (-lossExp))
    (hX : (activeCoarseCardScaleMass S : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-xExp))
    (hbaseConstant : massPopularBaseFixedConstant eta p a ≤
      (globalDelta : ENNReal) ^ (-baseAbsorbExp))
    (hqBase : ((delta : ENNReal) / (rho : ENNReal)) ≤
      (globalDelta : ENNReal) ^ baseScaleExp)
    (hbaseGain : 0 ≤ eta - (2 * p + a))
    (hbaseBudget : 2 * etaF + lossExp + xExp + baseAbsorbExp ≤
      baseScaleExp * (eta - (2 * p + a)))
    (hsourceMass : (globalDelta : ENNReal) ^ (2 * etaF) ≤
      shadingMassOn Y S.activeFine)
    {densityEtaF coverExp branchExp densityAbsorbExp densityScaleExp : Real}
    (hcover : 2 * stickyShadingAwareCoverLoss S Y A ≤
      (globalDelta : ENNReal) ^ (-coverExp))
    (hbranch : 2 *
        ((shadingAwareLogPartition S Y A hA0 hAtop hrho hdeltaRho hactive hmass).branching :
          ENNReal) ≤
      (globalDelta : ENNReal) ^ (-branchExp))
    (hdensityConstant : (2 * 8 * 93312 * 128 : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-densityAbsorbExp))
    (hqDensity : ((delta : ENNReal) / (rho : ENNReal)) ≤
      (globalDelta : ENNReal) ^ densityScaleExp)
    (hdensityGain : 0 ≤ eta - (p + a) + 2)
    (hdensityBudget :
      2 * densityEtaF + coverExp + branchExp + densityAbsorbExp ≤
        densityScaleExp * (eta - (p + a) + 2))
    (hsourceAPower : (globalDelta : ENNReal) ^ (2 * densityEtaF) ≤ A)
    (hproxyGap : 0 ≤ eta - (p + a)) :
    ∃ q : {q // q ∈ S.activeCoarse},
      q.1 ∈ shadingAwareSelectedParents
        S Y A hA0 hAtop hrho hactive hmass ∧
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ eta) ≤
        ((stickyFiberSourceShading S Y q.1).shadingDensity / 93312 / 128) /
          (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-(p + a))) ∧
      (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
          (-(2 * p + a))) ≤
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
            (-eta)) *
          ((Fintype.card {i // i ∈ S.fiber q.1} : ENNReal) *
            (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^
              2 / 2)) := by
  let selectedParents := shadingAwareSelectedParents
    S Y A hA0 hAtop hrho hactive hmass
  let Ppart := shadingAwareLogPartition S Y A hA0 hAtop hrho hdeltaRho hactive hmass
  let ratio : ENNReal := (delta : ENNReal) / (rho : ENNReal)
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  obtain ⟨k, hkSelected, _hstrong, hbaseRatio⟩ :=
    exists_shadingAwareSelected_massPopular_baseRatio_and_mass_of_globalPowerCaps
      S Y A hA0 hAtop hglobal hglobalOne hdelta hdeltaHalf hrho
        hactive hmass hloss hX hbaseConstant hqBase hbaseGain
        hbaseBudget hsourceMass
  have hkActive : k ∈ S.activeCoarse :=
    shadingAwareSelectedParents_subset_activeCoarse
      S Y A hA0 hAtop hrho hactive hmass hkSelected
  let q : {q // q ∈ S.activeCoarse} := ⟨k, hkActive⟩
  have hcover0 : stickyShadingAwareCoverLoss S Y A ≠ 0 :=
    stickyShadingAwareCoverLoss_ne_zero S Y hA0 hrho hactive
  have hcoverTop : stickyShadingAwareCoverLoss S Y A ≠ ∞ :=
    stickyShadingAwareCoverLoss_ne_top S Y hAtop hmass
  have hbranch0 : (Ppart.branching : ENNReal) ≠ 0 := by
    exact_mod_cast Ppart.branching_pos.ne'
  have hbranchTop : (Ppart.branching : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  have hfloorRaw := shadingAwareSelectedParent_density_floor
    S Y A hA0 hAtop hrho hrhoHalf hactive hmass hdeltaHalf k hkSelected
  have hfloor :
      (A * ((rho : ENNReal) ^ 2 / 2)) /
          ((2 * stickyShadingAwareCoverLoss S Y A) *
            ((2 * (Ppart.branching : ENNReal)) *
              (8 * (delta : ENNReal) ^ 2))) ≤
        (stickyFiberSourceShading S Y k).shadingDensity := by
    simpa only [Ppart, shadingAwareLogPartition_branching,
      Nat.cast_mul, Nat.cast_ofNat] using hfloorRaw
  have hdensityRatio := densityRatio_of_densityFloor_and_globalPowerCaps
    hglobal hglobalOne hdelta hrho hcover0 hcoverTop hbranch0 hbranchTop
      hfloor hcover hbranch hdensityConstant hqDensity hdensityGain
        hdensityBudget hsourceAPower
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact div_pos (contractedJohnProxyRadius_pos hdelta hrho) (by norm_num)
  have hscale0 : (scale : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hscalePos.ne'
  have hscaleTop : (scale : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdensity : (scale : ENNReal) ^ eta ≤
      ((stickyFiberSourceShading S Y k).shadingDensity / 93312 / 128) /
        (scale : ENNReal) ^ (-(p + a)) := by
    have hdenPos : 0 < (scale : ENNReal) ^ (-(p + a)) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hscalePos) ENNReal.coe_ne_top
    have hdenTop : (scale : ENNReal) ^ (-(p + a)) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_ne_zero hscale0 hscaleTop
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hdenPos.ne') (Or.inl hdenTop)).2
    calc
      (scale : ENNReal) ^ eta * (scale : ENNReal) ^ (-(p + a)) =
          (scale : ENNReal) ^ (eta - (p + a)) := by
        rw [← ENNReal.rpow_add _ _ hscale0 hscaleTop]
        congr 1
      _ ≤ ratio ^ (eta - (p + a)) := by
        simpa only [scale, ratio] using
          contractedJohnProxyRadius_div_eight_rpow_le_ratio_rpow
            (delta := delta) hrho hproxyGap
      _ ≤ (stickyFiberSourceShading S Y k).shadingDensity / 93312 / 128 := by
        simpa only [ratio] using hdensityRatio
  have hbase : (scale : ENNReal) ^ (-(2 * p + a)) ≤
      (scale : ENNReal) ^ (-eta) *
        ((Fintype.card {i // i ∈ S.fiber k} : ENNReal) *
          ((scale : ENNReal) ^ 2 / 2)) := by
    rw [show (scale : ENNReal) ^ (-(2 * p + a)) =
        (3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          ratio ^ (-(2 * p + a)) by
      simpa only [scale, ratio] using
        contractedJohnProxyRadius_div_eight_rpow_eq
          (delta := delta) hrho (-(2 * p + a))]
    rw [show (scale : ENNReal) ^ (-eta) =
        (3 / 64 : ENNReal) ^ (-eta) * ratio ^ (-eta) by
      simpa only [scale, ratio] using
        contractedJohnProxyRadius_div_eight_rpow_eq
          (delta := delta) hrho (-eta)]
    rw [show (scale : ENNReal) ^ 2 =
        (3 / 64 : ENNReal) ^ 2 * ratio ^ 2 by
      rw [show (scale : ENNReal) = (3 / 64 : ENNReal) * ratio by
        simpa only [scale, ratio] using
          coe_contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
            (delta := delta) hrho]
      ring]
    simpa only [ratio] using hbaseRatio
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa only [q, selectedParents] using hkSelected
  · simpa only [q, scale] using hdensity
  · simpa only [q, scale] using hbase

#print axioms exists_shadingAwareSelected_sourceDensity_and_basePower

end
end Family8StickyShadingAwareSelectedSourcePowerBudgetsGlobalV2
