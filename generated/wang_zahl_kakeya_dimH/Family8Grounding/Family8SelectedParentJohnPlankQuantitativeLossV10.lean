import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8SelectedParentJohnPlankQuantitativeLossV10

open Family8SelectedParentJohnPlankQuantitativeLossV9
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Absorbing the selected-parent cubic logarithmic bucket loss

V9 leaves the literal loss

`((ceil (logb 2 (5971968 / rho)) + 1).toNat) ^ 3`.

Here `Real.log_le_rpow_div` bounds the logarithm by the `lossEta / 6`
power of its argument.  Cubing spends `lossEta / 2`; the remaining half is
used by the explicit finite-constant small-scale threshold.  In particular,
the theorem below handles the actual `Int.ceil`, `Int.toNat`, and cube rather
than replacing the bucket loss by an assumed real-log estimate.
-/

/-- The finite real coefficient left after the log-to-power bound and the
three-coordinate cube. -/
def selectedParentLogarithmicSidePowerConstant (lossEta : Real) : Real :=
  (((5971968 : Real) ^ (lossEta / 6) / (lossEta / 6) /
      Real.log 2) + 2) ^ 3

theorem selectedParentLogarithmicSidePowerConstant_pos
    {lossEta : Real} (hlossEta : 0 < lossEta) :
    0 < selectedParentLogarithmicSidePowerConstant lossEta := by
  unfold selectedParentLogarithmicSidePowerConstant
  have hq : 0 < lossEta / 6 := by positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : 0 < (5971968 : Real) ^ (lossEta / 6) :=
    Real.rpow_pos_of_pos (by norm_num) _
  positivity

/-- The literal ceil/toNat bucket base is bounded by a finite coefficient
times `rho ^ (-lossEta/6)`. -/
theorem selectedParentLogarithmicSideBucketBase_real_le
    {rho : NNReal} {lossEta : Real}
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) (hlossEta : 0 < lossEta) :
    (((dyadicCeilBucket (5971968 / (rho : Real)) + 1).toNat : Nat) : Real) ≤
      (((5971968 : Real) ^ (lossEta / 6) / (lossEta / 6) /
          Real.log 2) + 2) *
        (rho : Real) ^ (-(lossEta / 6)) := by
  let q : Real := lossEta / 6
  let x : Real := 5971968 / (rho : Real)
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hrhoReal : 0 < (rho : Real) := by exact_mod_cast hrho
  have hrhoRealOne : (rho : Real) ≤ 1 := by exact_mod_cast hrhoOne
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hxOne : 1 ≤ x := by
    dsimp only [x]
    rw [le_div_iff₀ hrhoReal]
    calc
      (1 : Real) * (rho : Real) = (rho : Real) := one_mul _
      _ ≤ 1 := hrhoRealOne
      _ ≤ 5971968 := by norm_num
  have hlogbNonneg : 0 ≤ Real.logb 2 x :=
    Real.logb_nonneg (by norm_num) hxOne
  have hceilNonneg : 0 ≤ dyadicCeilBucket x := by
    unfold dyadicCeilBucket
    exact Int.ceil_nonneg hlogbNonneg
  have hsumNonneg : 0 ≤ dyadicCeilBucket x + 1 := by omega
  have htoNatInt :
      ((((dyadicCeilBucket x + 1).toNat : Nat) : Int)) =
        dyadicCeilBucket x + 1 :=
    Int.toNat_of_nonneg hsumNonneg
  have htoNatReal :
      ((((dyadicCeilBucket x + 1).toNat : Nat) : Real)) =
        ((dyadicCeilBucket x + 1 : Int) : Real) := by
    exact_mod_cast htoNatInt
  have hceilReal :
      ((dyadicCeilBucket x : Int) : Real) ≤ Real.logb 2 x + 1 := by
    unfold dyadicCeilBucket
    exact (Int.ceil_lt_add_one _).le
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_rpow_div hx.le hq
  have hlogbPower :
      Real.logb 2 x ≤
        ((5971968 : Real) ^ q / q / Real.log 2) *
          (rho : Real) ^ (-q) := by
    unfold Real.logb
    calc
      Real.log x / Real.log 2 ≤ (x ^ q / q) / Real.log 2 :=
        (div_le_div_iff_of_pos_right hlogTwo).2 hlog
      _ = ((5971968 : Real) ^ q / q / Real.log 2) *
          (rho : Real) ^ (-q) := by
        dsimp only [x]
        rw [Real.div_rpow (by norm_num) hrhoReal.le]
        rw [Real.rpow_neg hrhoReal.le]
        ring
  have hrhoPowerOne : 1 ≤ (rho : Real) ^ (-q) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hrhoReal hrhoRealOne (by linarith)
  calc
    (((dyadicCeilBucket (5971968 / (rho : Real)) + 1).toNat : Nat) : Real) =
        (((dyadicCeilBucket x + 1).toNat : Nat) : Real) := by rfl
    _ = ((dyadicCeilBucket x + 1 : Int) : Real) := htoNatReal
    _ = (dyadicCeilBucket x : Real) + 1 := by norm_num
    _ ≤ (Real.logb 2 x + 1) + 1 := by gcongr
    _ = Real.logb 2 x + 2 := by ring
    _ ≤ (((5971968 : Real) ^ q / q / Real.log 2) *
          (rho : Real) ^ (-q)) + 2 := by gcongr
    _ ≤ (((5971968 : Real) ^ q / q / Real.log 2) *
          (rho : Real) ^ (-q)) + 2 * (rho : Real) ^ (-q) := by
      have htwo : (2 : Real) ≤ 2 * (rho : Real) ^ (-q) := by
        calc
          (2 : Real) = 2 * 1 := by ring
          _ ≤ 2 * (rho : Real) ^ (-q) :=
            mul_le_mul_of_nonneg_left hrhoPowerOne (by norm_num)
      linarith
    _ = (((5971968 : Real) ^ q / q / Real.log 2) + 2) *
          (rho : Real) ^ (-q) := by ring
    _ = (((5971968 : Real) ^ (lossEta / 6) / (lossEta / 6) /
          Real.log 2) + 2) *
        (rho : Real) ^ (-(lossEta / 6)) := by rfl

/-- Real form of the full cubic loss bound.  Half of `lossEta` remains for
absorbing its finite coefficient. -/
theorem selectedParentLogarithmicSideBucketLoss_real_le
    {rho : NNReal} {lossEta : Real}
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) (hlossEta : 0 < lossEta) :
    (selectedParentLogarithmicSideBucketLoss rho : Real) ≤
      selectedParentLogarithmicSidePowerConstant lossEta *
        (rho : Real) ^ (-(lossEta / 2)) := by
  let q : Real := lossEta / 6
  let base : Real :=
    ((5971968 : Real) ^ q / q / Real.log 2) + 2
  have hbase := selectedParentLogarithmicSideBucketBase_real_le
    hrho hrhoOne hlossEta
  change
    (((((dyadicCeilBucket (5971968 / (rho : Real)) + 1).toNat) ^ 3 : Nat) : Real)) ≤
      selectedParentLogarithmicSidePowerConstant lossEta *
        (rho : Real) ^ (-(lossEta / 2))
  rw [Nat.cast_pow]
  change
    ((((dyadicCeilBucket (5971968 / (rho : Real)) + 1).toNat : Nat) : Real) ^ 3) ≤
      base ^ 3 * (rho : Real) ^ (-(lossEta / 2))
  have hbaseNonneg : 0 ≤
      (((dyadicCeilBucket (5971968 / (rho : Real)) + 1).toNat : Nat) : Real) :=
    by positivity
  have hrhoPowerCube :
      ((rho : Real) ^ (-q)) ^ 3 =
        (rho : Real) ^ (-(lossEta / 2)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show (0 : Real) ≤ (rho : Real) by positivity)]
    congr 1
    dsimp only [q]
    ring
  calc
    ((((dyadicCeilBucket (5971968 / (rho : Real)) + 1).toNat : Nat) : Real) ^ 3) ≤
        (base * (rho : Real) ^ (-q)) ^ 3 :=
      pow_le_pow_left₀ hbaseNonneg hbase 3
    _ = base ^ 3 * ((rho : Real) ^ (-q)) ^ 3 := by rw [mul_pow]
    _ = base ^ 3 * (rho : Real) ^ (-(lossEta / 2)) := by rw [hrhoPowerCube]

/-- Explicit threshold which absorbs both an arbitrary fixed finite constant
and the literal selected-parent bucket loss. -/
def selectedParentLogarithmicSideBucketAbsorptionThreshold
    (fixedConstant : ENNReal) (lossEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (fixedConstant *
      ENNReal.ofReal (selectedParentLogarithmicSidePowerConstant lossEta))
    (lossEta / 2)

theorem selectedParentLogarithmicSideBucketAbsorptionThreshold_pos
    (fixedConstant : ENNReal) (lossEta : Real) :
    0 < selectedParentLogarithmicSideBucketAbsorptionThreshold
      fixedConstant lossEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem selectedParentLogarithmicSideBucketAbsorptionThreshold_le_one
    (fixedConstant : ENNReal) {lossEta : Real} (hlossEta : 0 < lossEta) :
    selectedParentLogarithmicSideBucketAbsorptionThreshold
      fixedConstant lossEta ≤ 1 := by
  exact finiteConstantSmallDeltaThreshold_le_one _ (by positivity)

/-- Any fixed finite coefficient times the actual cubic dyadic bucket count
is absorbed by an arbitrary positive small power below the explicit
threshold. -/
theorem fixedConstant_mul_selectedParentLogarithmicSideBucketLoss_le_rpow
    {rho : NNReal} {fixedConstant : ENNReal} {lossEta : Real}
    (hfixedFinite : fixedConstant ≠ ∞) (hlossEta : 0 < lossEta)
    (hrho : 0 < rho)
    (hrhoThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        fixedConstant lossEta) :
    fixedConstant * (selectedParentLogarithmicSideBucketLoss rho : ENNReal) ≤
      (rho : ENNReal) ^ (-lossEta) := by
  let K : ENNReal := fixedConstant *
    ENNReal.ofReal (selectedParentLogarithmicSidePowerConstant lossEta)
  have hhalf : 0 < lossEta / 2 := by positivity
  have hrhoOne : rho ≤ 1 :=
    hrhoThreshold.trans
      (selectedParentLogarithmicSideBucketAbsorptionThreshold_le_one
        fixedConstant hlossEta)
  have hreal := selectedParentLogarithmicSideBucketLoss_real_le
    hrho hrhoOne hlossEta
  have hconstantNonneg :
      0 ≤ selectedParentLogarithmicSidePowerConstant lossEta :=
    (selectedParentLogarithmicSidePowerConstant_pos hlossEta).le
  have hrhoReal : 0 < (rho : Real) := by exact_mod_cast hrho
  have hlossENN :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) ≤
        ENNReal.ofReal (selectedParentLogarithmicSidePowerConstant lossEta) *
          (rho : ENNReal) ^ (-(lossEta / 2)) := by
    rw [← ENNReal.ofReal_natCast
      (selectedParentLogarithmicSideBucketLoss rho)]
    rw [show (rho : ENNReal) ^ (-(lossEta / 2)) =
        ENNReal.ofReal ((rho : Real) ^ (-(lossEta / 2))) by
      simpa using ENNReal.ofReal_rpow_of_pos hrhoReal]
    rw [← ENNReal.ofReal_mul hconstantNonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  have hKFinite : K ≠ ∞ := by
    dsimp only [K]
    exact ENNReal.mul_ne_top hfixedFinite (by simp)
  have hK : K ≤ (rho : ENNReal) ^ (-(lossEta / 2)) := by
    exact finiteConstant_le_delta_negativePower hKFinite hhalf hrho
      (by simpa [selectedParentLogarithmicSideBucketAbsorptionThreshold, K]
        using hrhoThreshold)
  calc
    fixedConstant * (selectedParentLogarithmicSideBucketLoss rho : ENNReal) ≤
        fixedConstant *
          (ENNReal.ofReal
            (selectedParentLogarithmicSidePowerConstant lossEta) *
              (rho : ENNReal) ^ (-(lossEta / 2))) := by gcongr
    _ = K * (rho : ENNReal) ^ (-(lossEta / 2)) := by
      dsimp only [K]
      ac_rfl
    _ ≤ (rho : ENNReal) ^ (-(lossEta / 2)) *
        (rho : ENNReal) ^ (-(lossEta / 2)) := by gcongr
    _ = (rho : ENNReal) ^ (-lossEta) := by
      rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hrho.ne') (by simp)]
      congr 1
      ring

/-- Coefficient-one form used when V9's bucket loss is the only loss to
absorb. -/
theorem selectedParentLogarithmicSideBucketLoss_le_rpow
    {rho : NNReal} {lossEta : Real} (hlossEta : 0 < lossEta)
    (hrho : 0 < rho)
    (hrhoThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold 1 lossEta) :
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) ≤
      (rho : ENNReal) ^ (-lossEta) := by
  simpa using
    (fixedConstant_mul_selectedParentLogarithmicSideBucketLoss_le_rpow
      (rho := rho) (fixedConstant := 1) (lossEta := lossEta)
      (by simp) hlossEta hrho hrhoThreshold)

#print axioms selectedParentLogarithmicSideBucketLoss_real_le
#print axioms fixedConstant_mul_selectedParentLogarithmicSideBucketLoss_le_rpow
#print axioms selectedParentLogarithmicSideBucketLoss_le_rpow

end
end Family8SelectedParentJohnPlankQuantitativeLossV10
