import Family8Grounding.Family8ActiveFrozenComparableLogLossAbsorptionV4
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FrozenComparableLogLossSourceCardTransferV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8CommonPointTubePackingV1
open Family8StickySourceCardFallbackV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-!
# Transfer active frozen logarithmic loss through an ambient source-card bound

The lower family of a canonical `tau`-to-buffered cover is reindexed by the
active `tau` parents and therefore has a different index type from the
original datum.  Its cardinality is nevertheless at most the original tube
cardinality.  This file shows that this one comparison suffices to reuse the
uniform arbitrary-small-power logarithmic absorption at the original scale.
-/

theorem sourceIndexCard_real_le_sourcePower
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (D : ActualTubeDatum delta sourceIndex) (hD : D.IsAdmissible)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (Fintype.card sourceIndex : Real) ≤
      (2 * commonPointFamilyVolumeConstant).toReal *
        (delta : Real) ^ (-4 : Real) := by
  have hsource :=
    actualTubeDatum_indexCard_le_two_mul_commonPointConstant_rpow_neg_four
      D hD hdeltaSmall
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hboundFinite :
      (2 * commonPointFamilyVolumeConstant) *
          (delta : ENNReal) ^ (-4 : Real) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp)
        commonPointFamilyVolumeConstant_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono hboundFinite hsource
  have hpowToReal :
      ((delta : ENNReal) ^ (-4 : Real)).toReal =
        (delta : Real) ^ (-4 : Real) := by
    rw [← ENNReal.toReal_rpow]
    rfl
  simpa only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal, hpowToReal] using hreal

variable {lowerDelta rho : NNReal} {lowerIndex : Type}
  [Fintype lowerIndex] [DecidableEq lowerIndex]
  {fine : UniformTubeFamily lowerDelta lowerIndex}

theorem coverActiveCards_real_le_ambientSourcePower
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (D : ActualTubeDatum delta sourceIndex) (hD : D.IsAdmissible)
    (S : StickyScaleCover fine rho)
    (hindex : Fintype.card lowerIndex ≤ Fintype.card sourceIndex)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (S.activeFine.card : Real) ≤
        (2 * commonPointFamilyVolumeConstant).toReal *
          (delta : Real) ^ (-4 : Real) ∧
      (S.activeCoarse.card : Real) ≤
        (2 * commonPointFamilyVolumeConstant).toReal *
          (delta : Real) ^ (-4 : Real) := by
  have hsource := sourceIndexCard_real_le_sourcePower D hD hdeltaSmall
  have hfineLower : S.activeFine.card ≤ Fintype.card lowerIndex := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ S.activeFine)
  have hcoarseFine : S.activeCoarse.card ≤ S.activeFine.card :=
    activeCoarse_card_le_activeFine_card S
  have hfineSource : (S.activeFine.card : Real) ≤
      Fintype.card sourceIndex := by
    exact_mod_cast hfineLower.trans hindex
  have hcoarseSource : (S.activeCoarse.card : Real) ≤
      Fintype.card sourceIndex := by
    exact_mod_cast hcoarseFine.trans (hfineLower.trans hindex)
  exact ⟨hfineSource.trans hsource, hcoarseSource.trans hsource⟩

theorem activeFrozenComparableLoss_real_le_of_indexCard_le_source
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (D : ActualTubeDatum delta sourceIndex) (hD : D.IsAdmissible)
    (S : StickyScaleCover fine rho)
    (hindex : Fintype.card lowerIndex ≤ Fintype.card sourceIndex)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) : Real) ≤
      activeFrozenLogProductConstant lossEta *
        (delta : Real) ^ (-(lossEta / 2)) := by
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans (div_le_one_of_le₀ (by norm_num) (by positivity))
  obtain ⟨hfineCard, hcoarseCard⟩ :=
    coverActiveCards_real_le_ambientSourcePower
      D hD S hindex hdeltaSmall
  have hfine :=
    natLogFactor_real_le hD.delta_pos hdeltaOne hlossEta hfineCard
  have hcoarse :=
    natLogFactor_real_le hD.delta_pos hdeltaOne hlossEta hcoarseCard
  have hfactorNonneg :
      0 ≤ activeFrozenLogFactorConstant lossEta *
        (delta : Real) ^ (-(lossEta / 4)) :=
    mul_nonneg (activeFrozenLogFactorConstant_pos hlossEta).le
      (Real.rpow_nonneg (by positivity) _)
  have hscale :
      ((delta : Real) ^ (-(lossEta / 4))) ^ 2 =
        (delta : Real) ^ (-(lossEta / 2)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show 0 ≤ (delta : Real) by positivity)]
    congr 1
    ring
  unfold frozenComparableLoss activeFrozenLogProductConstant
  simp only [Fintype.card_coe, Fintype.card_fin]
  rw [Nat.cast_mul]
  calc
    ((Nat.log 2 S.activeFine.card + 2 : Nat) : Real) *
        ((Nat.log 2 S.activeCoarse.card + 2 : Nat) : Real) ≤
      (activeFrozenLogFactorConstant lossEta *
          (delta : Real) ^ (-(lossEta / 4))) ^ 2 := by
        rw [pow_two]
        exact mul_le_mul hfine hcoarse (by positivity) hfactorNonneg
    _ = (activeFrozenLogFactorConstant lossEta) ^ 2 *
        ((delta : Real) ^ (-(lossEta / 4))) ^ 2 := by rw [mul_pow]
    _ = (activeFrozenLogFactorConstant lossEta) ^ 2 *
        (delta : Real) ^ (-(lossEta / 2)) := by rw [hscale]

theorem activeFrozenComparableLoss_le_rpow_of_indexCard_le_source
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (D : ActualTubeDatum delta sourceIndex) (hD : D.IsAdmissible)
    (S : StickyScaleCover fine rho)
    (hindex : Fintype.card lowerIndex ≤ Fintype.card sourceIndex)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta ≤
      activeFrozenComparableLossAbsorptionThreshold lossEta) :
    (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) : ENNReal) ≤
      (delta : ENNReal) ^ (-lossEta) := by
  have hdeltaSmall : delta ≤ (1 / 100 : NNReal) :=
    hdelta.trans (min_le_left _ _)
  have hreal :=
    activeFrozenComparableLoss_real_le_of_indexCard_le_source
      D hD S hindex hlossEta hdeltaSmall
  have hconstantNonneg :
      0 ≤ activeFrozenLogProductConstant lossEta := by
    unfold activeFrozenLogProductConstant
    positivity
  have hdeltaReal : 0 < (delta : Real) := by exact_mod_cast hD.delta_pos
  have hlossENN :
      (frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin S.activeCoarse.card) : ENNReal) ≤
        ENNReal.ofReal (activeFrozenLogProductConstant lossEta) *
          (delta : ENNReal) ^ (-(lossEta / 2)) := by
    rw [← ENNReal.ofReal_natCast
      (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card))]
    rw [show (delta : ENNReal) ^ (-(lossEta / 2)) =
        ENNReal.ofReal ((delta : Real) ^ (-(lossEta / 2))) by
      simpa using ENNReal.ofReal_rpow_of_pos hdeltaReal]
    rw [← ENNReal.ofReal_mul hconstantNonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  let K : ENNReal :=
    ENNReal.ofReal (activeFrozenLogProductConstant lossEta)
  have hhalf : 0 < lossEta / 2 := by positivity
  have hKFinite : K ≠ ∞ := by
    dsimp only [K]
    simp
  have hK : K ≤ (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact finiteConstant_le_delta_negativePower hKFinite hhalf hD.delta_pos
      (hdelta.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) : ENNReal) ≤
      K * (delta : ENNReal) ^ (-(lossEta / 2)) := by
        simpa only [K] using hlossENN
    _ ≤ (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) := by gcongr
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms sourceIndexCard_real_le_sourcePower
#print axioms coverActiveCards_real_le_ambientSourcePower
#print axioms activeFrozenComparableLoss_real_le_of_indexCard_le_source
#print axioms activeFrozenComparableLoss_le_rpow_of_indexCard_le_source

end
end Family8FrozenComparableLogLossSourceCardTransferV2
