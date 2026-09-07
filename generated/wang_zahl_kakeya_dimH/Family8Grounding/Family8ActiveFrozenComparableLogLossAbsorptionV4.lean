import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickySourceCardFallbackV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActiveFrozenComparableLogLossAbsorptionV4

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
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Absorbing the genuine active-index frozen logarithmic loss

The coarse global source-card estimate costs `delta ^ (-4)` if used
directly.  Here it is used only inside the two `Nat.log 2` factors of the
frozen comparable assembly.  Real logarithm-to-power bounds therefore make
the complete active-index loss smaller than an arbitrary prescribed positive
power at a uniform small scale.
-/

/-- The real coefficient left after converting one active-index logarithm
to the `lossEta / 4` power of `delta`. -/
def activeFrozenLogFactorConstant (lossEta : Real) : Real :=
  ((2 * commonPointFamilyVolumeConstant).toReal ^ (lossEta / 16) /
      (lossEta / 16) / Real.log 2) + 2

/-- The coefficient for the product of the active-fine and active-coarse
logarithmic factors. -/
def activeFrozenLogProductConstant (lossEta : Real) : Real :=
  (activeFrozenLogFactorConstant lossEta) ^ 2

theorem activeFrozenLogFactorConstant_pos
    {lossEta : Real} (hlossEta : 0 < lossEta) :
    0 < activeFrozenLogFactorConstant lossEta := by
  unfold activeFrozenLogFactorConstant
  have hq : 0 < lossEta / 16 := by positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconstant : 0 <= (2 * commonPointFamilyVolumeConstant).toReal :=
    ENNReal.toReal_nonneg
  have hpow : 0 <=
      (2 * commonPointFamilyVolumeConstant).toReal ^ (lossEta / 16) :=
    Real.rpow_nonneg hconstant _
  positivity

/-- A single literal `Nat.log 2 n + 2` factor is bounded by a small power,
provided `n` obeys the proved source-card power bound. -/
theorem natLogFactor_real_le
    {delta : NNReal} {n : Nat} {lossEta : Real}
    (hdeltaPos : 0 < delta) (hdeltaOne : delta <= 1)
    (hlossEta : 0 < lossEta)
    (hn : (n : Real) <=
      (2 * commonPointFamilyVolumeConstant).toReal *
        (delta : Real) ^ (-4 : Real)) :
    ((Nat.log 2 n + 2 : Nat) : Real) <=
      activeFrozenLogFactorConstant lossEta *
        (delta : Real) ^ (-(lossEta / 4)) := by
  let q : Real := lossEta / 16
  let C : Real := (2 * commonPointFamilyVolumeConstant).toReal
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdeltaReal : 0 < (delta : Real) := by exact_mod_cast hdeltaPos
  have hdeltaRealOne : (delta : Real) <= 1 := by exact_mod_cast hdeltaOne
  have hC : 0 <= C := by
    dsimp only [C]
    exact ENNReal.toReal_nonneg
  have hnNonneg : 0 <= (n : Real) := by positivity
  have hlog := Real.log_le_rpow_div hnNonneg hq
  have hpowMono :
      (n : Real) ^ q <=
        (C * (delta : Real) ^ (-4 : Real)) ^ q := by
    apply Real.rpow_le_rpow hnNonneg
    · simpa only [C] using hn
    · exact hq.le
  have hdeltaPowNonneg :
      0 <= (delta : Real) ^ (-4 : Real) :=
    Real.rpow_nonneg hdeltaReal.le _
  have hscalePower :
      ((delta : Real) ^ (-4 : Real)) ^ q =
        (delta : Real) ^ (-(lossEta / 4)) := by
    rw [<- Real.rpow_mul hdeltaReal.le]
    dsimp only [q]
    congr 1
    ring
  have hlogbPower :
      Real.logb 2 n <=
        (C ^ q / q / Real.log 2) *
          (delta : Real) ^ (-(lossEta / 4)) := by
    unfold Real.logb
    calc
      Real.log (n : Real) / Real.log 2 <=
          ((n : Real) ^ q / q) / Real.log 2 :=
        (div_le_div_iff_of_pos_right hlogTwo).2 hlog
      _ <= ((C * (delta : Real) ^ (-4 : Real)) ^ q / q) /
          Real.log 2 := by gcongr
      _ = ((C ^ q * ((delta : Real) ^ (-4 : Real)) ^ q) / q) /
          Real.log 2 := by
        rw [Real.mul_rpow hC hdeltaPowNonneg]
      _ = (C ^ q / q / Real.log 2) *
          (delta : Real) ^ (-(lossEta / 4)) := by
        rw [hscalePower]
        ring
  have hnatLog :
      (Nat.log 2 n : Real) <= Real.logb 2 n := by
    simpa using Real.natLog_le_logb n 2
  have hscaleOne :
      1 <= (delta : Real) ^ (-(lossEta / 4)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdeltaReal hdeltaRealOne
      (by linarith)
  calc
    ((Nat.log 2 n + 2 : Nat) : Real) =
        (Nat.log 2 n : Real) + 2 := by norm_num
    _ <= Real.logb 2 n + 2 := by gcongr
    _ <= (C ^ q / q / Real.log 2) *
          (delta : Real) ^ (-(lossEta / 4)) + 2 := by gcongr
    _ <= (C ^ q / q / Real.log 2) *
          (delta : Real) ^ (-(lossEta / 4)) +
        2 * (delta : Real) ^ (-(lossEta / 4)) := by
      have htwo : (2 : Real) <=
          2 * (delta : Real) ^ (-(lossEta / 4)) := by
        calc
          (2 : Real) = 2 * 1 := by ring
          _ <= 2 * (delta : Real) ^ (-(lossEta / 4)) :=
            mul_le_mul_of_nonneg_left hscaleOne (by norm_num)
      exact add_le_add_right htwo _
    _ = activeFrozenLogFactorConstant lossEta *
          (delta : Real) ^ (-(lossEta / 4)) := by
      unfold activeFrozenLogFactorConstant
      dsimp only [C, q]
      ring

/-- Both genuine active cardinalities inherit the uniform source-card power
bound from admissibility. -/
theorem activeFine_and_coarse_card_real_le_sourcePower
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    (S.activeFine.card : Real) <=
        (2 * commonPointFamilyVolumeConstant).toReal *
          (delta : Real) ^ (-4 : Real) /\
      (S.activeCoarse.card : Real) <=
        (2 * commonPointFamilyVolumeConstant).toReal *
          (delta : Real) ^ (-4 : Real) := by
  have hsource :=
    actualTubeDatum_indexCard_le_two_mul_commonPointConstant_rpow_neg_four
      D hD hdeltaSmall
  have hfineNat : S.activeFine.card <= Fintype.card iota := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ S.activeFine)
  have hcoarseNat : S.activeCoarse.card <= S.activeFine.card :=
    activeCoarse_card_le_activeFine_card S
  have hfineENN : (S.activeFine.card : ENNReal) <=
      (2 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real) := by
    calc
      (S.activeFine.card : ENNReal) <= (Fintype.card iota : ENNReal) := by
        exact_mod_cast hfineNat
      _ <= _ := hsource
  have hcoarseENN : (S.activeCoarse.card : ENNReal) <=
      (2 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real) := by
    calc
      (S.activeCoarse.card : ENNReal) <=
          (S.activeFine.card : ENNReal) := by exact_mod_cast hcoarseNat
      _ <= _ := hfineENN
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hboundFinite :
      (2 * commonPointFamilyVolumeConstant) *
          (delta : ENNReal) ^ (-4 : Real) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by simp)
        commonPointFamilyVolumeConstant_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top
  have hfineReal := ENNReal.toReal_mono hboundFinite hfineENN
  have hcoarseReal := ENNReal.toReal_mono hboundFinite hcoarseENN
  have hpowToReal :
      ((delta : ENNReal) ^ (-4 : Real)).toReal =
        (delta : Real) ^ (-4 : Real) := by
    rw [← ENNReal.toReal_rpow]
    rfl
  constructor
  · simpa only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.coe_toReal, hpowToReal] using hfineReal
  · simpa only [ENNReal.toReal_natCast, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.coe_toReal, hpowToReal] using hcoarseReal

/-- Before absorbing the remaining finite coefficient, the literal frozen
loss spends only half of the requested exponent. -/
theorem activeFrozenComparableLoss_real_le
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdeltaSmall : delta <= (1 / 100 : NNReal)) :
    (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) : Real) <=
      activeFrozenLogProductConstant lossEta *
        (delta : Real) ^ (-(lossEta / 2)) := by
  have hdeltaOne : delta <= 1 :=
    hdeltaSmall.trans (div_le_one_of_le₀ (by norm_num) (by positivity))
  obtain ⟨hfineCard, hcoarseCard⟩ :=
    activeFine_and_coarse_card_real_le_sourcePower D hD S hdeltaSmall
  have hfine := natLogFactor_real_le hD.delta_pos hdeltaOne hlossEta hfineCard
  have hcoarse := natLogFactor_real_le hD.delta_pos hdeltaOne hlossEta hcoarseCard
  have hfineNonneg :
      0 <= ((Nat.log 2 S.activeFine.card + 2 : Nat) : Real) := by positivity
  have hfactorNonneg :
      0 <= activeFrozenLogFactorConstant lossEta *
        (delta : Real) ^ (-(lossEta / 4)) :=
    mul_nonneg (activeFrozenLogFactorConstant_pos hlossEta).le
      (Real.rpow_nonneg (by positivity) _)
  have hscale :
      ((delta : Real) ^ (-(lossEta / 4))) ^ 2 =
        (delta : Real) ^ (-(lossEta / 2)) := by
    rw [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul (show 0 <= (delta : Real) by positivity)]
    congr 1
    ring
  unfold frozenComparableLoss activeFrozenLogProductConstant
  simp only [Fintype.card_coe, Fintype.card_fin]
  rw [Nat.cast_mul]
  calc
    ((Nat.log 2 S.activeFine.card + 2 : Nat) : Real) *
        ((Nat.log 2 S.activeCoarse.card + 2 : Nat) : Real) <=
      (activeFrozenLogFactorConstant lossEta *
          (delta : Real) ^ (-(lossEta / 4))) ^ 2 := by
        rw [pow_two]
        exact mul_le_mul hfine hcoarse (by positivity) hfactorNonneg
    _ = (activeFrozenLogFactorConstant lossEta) ^ 2 *
        ((delta : Real) ^ (-(lossEta / 4))) ^ 2 := by rw [mul_pow]
    _ = (activeFrozenLogFactorConstant lossEta) ^ 2 *
        (delta : Real) ^ (-(lossEta / 2)) := by rw [hscale]

/-- Explicit uniform scale threshold which absorbs the remaining finite
coefficient. -/
def activeFrozenComparableLossAbsorptionThreshold (lossEta : Real) : NNReal :=
  min (1 / 100 : NNReal)
    (finiteConstantSmallDeltaThreshold
      (ENNReal.ofReal (activeFrozenLogProductConstant lossEta))
      (lossEta / 2))

theorem activeFrozenComparableLossAbsorptionThreshold_pos
    (lossEta : Real) :
    0 < activeFrozenComparableLossAbsorptionThreshold lossEta := by
  unfold activeFrozenComparableLossAbsorptionThreshold
  exact lt_min (by norm_num) (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The genuine two-level frozen loss is uniformly absorbed into an
arbitrarily small prescribed positive power of the original scale. -/
theorem activeFrozenComparableLoss_le_rpow
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hdelta : delta <=
      activeFrozenComparableLossAbsorptionThreshold lossEta) :
    (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) : ENNReal) <=
      (delta : ENNReal) ^ (-lossEta) := by
  have hdeltaSmall : delta <= (1 / 100 : NNReal) :=
    hdelta.trans (min_le_left _ _)
  have hreal := activeFrozenComparableLoss_real_le
    D hD S hlossEta hdeltaSmall
  have hconstantNonneg :
      0 <= activeFrozenLogProductConstant lossEta := by
    unfold activeFrozenLogProductConstant
    positivity
  have hdeltaReal : 0 < (delta : Real) := by exact_mod_cast hD.delta_pos
  have hlossENN :
      (frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin S.activeCoarse.card) : ENNReal) <=
        ENNReal.ofReal (activeFrozenLogProductConstant lossEta) *
          (delta : ENNReal) ^ (-(lossEta / 2)) := by
    rw [<- ENNReal.ofReal_natCast
      (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card))]
    rw [show (delta : ENNReal) ^ (-(lossEta / 2)) =
        ENNReal.ofReal ((delta : Real) ^ (-(lossEta / 2))) by
      simpa using ENNReal.ofReal_rpow_of_pos hdeltaReal]
    rw [<- ENNReal.ofReal_mul hconstantNonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  let K : ENNReal :=
    ENNReal.ofReal (activeFrozenLogProductConstant lossEta)
  have hhalf : 0 < lossEta / 2 := by positivity
  have hKFinite : K ≠ ∞ := by
    dsimp only [K]
    simp
  have hK : K <= (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact finiteConstant_le_delta_negativePower hKFinite hhalf hD.delta_pos
      (hdelta.trans (min_le_right _ _))
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) : ENNReal) <=
      K * (delta : ENNReal) ^ (-(lossEta / 2)) := by
        simpa only [K] using hlossENN
    _ <= (delta : ENNReal) ^ (-(lossEta / 2)) *
        (delta : ENNReal) ^ (-(lossEta / 2)) := by gcongr
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms activeFine_and_coarse_card_real_le_sourcePower
#print axioms activeFrozenComparableLoss_real_le
#print axioms activeFrozenComparableLoss_le_rpow

end
end Family8ActiveFrozenComparableLogLossAbsorptionV4
