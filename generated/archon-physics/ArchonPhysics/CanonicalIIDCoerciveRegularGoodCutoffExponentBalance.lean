import ArchonPhysics.CanonicalIIDCoerciveRegularGoodOscillatoryBudget
import ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion

/-!
# General cutoff exponents for regular-good FPUT histories

The square-cutoff closure uses deliberately generous microscopic coupling
powers.  This module instead records the exact exponent balance for a
general cutoff

`gamma(g) = |g|^alpha`.

If a regular history carries `power` coupling powers and loses
`denominatorLoss` inverse gaps, while the kinetic prefactor costs
`deficit` powers of `|g|`, its remaining exponent is

`power - alpha * denominatorLoss - deficit`.

A linear small-ball probability has remaining exponent `alpha - deficit`.
Thus one cutoff exponent works for both pieces exactly when these two
exponents are positive.  For positive denominator loss, such an exponent
exists if and only if

`deficit * (denominatorLoss + 1) < power`.

For the actual Picard counting, a quadratic vertex contributes one power of
`|g|`, a quartic vertex contributes two, and the direct ordered resolvent
loses one denominator per vertex.  Consequently:

* the quadratic fixed-order balance is impossible (`power = loss = order`,
  `deficit = 1`), and increasing the order alone does not repair it;
* the quartic balance is possible precisely for `0 < alpha < 2`;
* a quadratic growing-order garden can work at this absolute-value level
  only if its effective denominator loss is strictly below `order - 1`, or
  if cancellation supplies more than one extra coupling power.

The last section feeds the proved power-cutoff limits into the existing
linear-small-ball good/bad criterion.  It does not assert the model-specific
cancellation needed to reduce the quadratic denominator loss.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance

open Filter Topology
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualGardenHistoryDecomposition
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodOscillatoryBudget
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion
open ArchonPhysics.PhyslibFPUTHigherOrderKineticRPACriterion

noncomputable section

/-! ## Algebraic exponent balance -/

/-- General power-law small-denominator cutoff.  The real exponent permits
the strict interval between the regular and exceptional constraints. -/
def powerCouplingCutoff (alpha g : Real) : Real :=
  |g| ^ alpha

/-- Power remaining in a regular-good term after inverse denominators and
the kinetic-time channel prefactor. -/
def regularKineticExponent
    (power denominatorLoss deficit alpha : Real) : Real :=
  power - alpha * denominatorLoss - deficit

/-- Power remaining in a linear small-ball term after the same channel
prefactor. -/
def badKineticExponent (deficit alpha : Real) : Real :=
  alpha - deficit

/-- A cutoff exponent is admissible when both the regular-good resolvent
bound and the bad-small-denominator bound have a strictly positive power. -/
def CutoffExponentAdmissible
    (power denominatorLoss deficit alpha : Real) : Prop :=
  0 < badKineticExponent deficit alpha /\
    0 < regularKineticExponent power denominatorLoss deficit alpha

theorem cutoffExponentAdmissible_iff
    (power denominatorLoss deficit alpha : Real) :
    CutoffExponentAdmissible power denominatorLoss deficit alpha <->
      deficit < alpha /\
        alpha * denominatorLoss < power - deficit := by
  unfold CutoffExponentAdmissible badKineticExponent regularKineticExponent
  constructor <;> rintro ⟨hbad, hregular⟩ <;> constructor <;> linarith

/-- Explicit midpoint of the nonempty admissible cutoff interval. -/
def midpointCutoffExponent
    (power denominatorLoss deficit : Real) : Real :=
  deficit +
    (power - deficit * (denominatorLoss + 1)) /
      (2 * denominatorLoss)

/-- If the coupling-power margin is positive, the explicit midpoint is
admissible. -/
theorem midpointCutoffExponent_admissible
    {power denominatorLoss deficit : Real}
    (hloss : 0 < denominatorLoss)
    (hmargin : deficit * (denominatorLoss + 1) < power) :
    CutoffExponentAdmissible power denominatorLoss deficit
      (midpointCutoffExponent power denominatorLoss deficit) := by
  rw [cutoffExponentAdmissible_iff]
  let margin : Real := power - deficit * (denominatorLoss + 1)
  have hmargin0 : 0 < margin := by
    dsimp [margin]
    exact sub_pos.mpr hmargin
  have hdenom : 0 < 2 * denominatorLoss := mul_pos (by norm_num) hloss
  have hquotient : 0 < margin / (2 * denominatorLoss) :=
    div_pos hmargin0 hdenom
  have hloss0 : denominatorLoss ≠ 0 := ne_of_gt hloss
  constructor
  · unfold midpointCutoffExponent
    change deficit < deficit + margin / (2 * denominatorLoss)
    linarith
  · have heq :
        midpointCutoffExponent power denominatorLoss deficit *
            denominatorLoss =
          deficit * denominatorLoss + margin / 2 := by
      unfold midpointCutoffExponent
      dsimp only [margin]
      field_simp [hloss0]
    rw [heq]
    dsimp only [margin] at hmargin0 ⊢
    linarith

/-- Exact feasibility criterion for a positive number of denominator
losses. -/
theorem exists_cutoffExponentAdmissible_iff
    {power denominatorLoss deficit : Real}
    (hloss : 0 < denominatorLoss) :
    (exists alpha,
      CutoffExponentAdmissible power denominatorLoss deficit alpha) <->
      deficit * (denominatorLoss + 1) < power := by
  constructor
  · rintro ⟨alpha, halpha⟩
    rw [cutoffExponentAdmissible_iff] at halpha
    have hmul := mul_lt_mul_of_pos_right halpha.1 hloss
    linarith
  · intro hmargin
    exact ⟨midpointCutoffExponent power denominatorLoss deficit,
      midpointCutoffExponent_admissible hloss hmargin⟩

/-- If the feasibility margin is nonpositive, no cutoff exponent can close
both the good and bad estimates. -/
theorem no_cutoffExponentAdmissible_of_power_le
    {power denominatorLoss deficit : Real}
    (hloss : 0 < denominatorLoss)
    (hpower : power <= deficit * (denominatorLoss + 1)) :
    ¬ (exists alpha,
      CutoffExponentAdmissible power denominatorLoss deficit alpha) := by
  rw [exists_cutoffExponentAdmissible_iff hloss]
  exact not_lt_of_ge hpower

/-! ## Actual quadratic and quartic Picard counts -/

/-- At order `r`, direct quadratic Picard counting supplies `r` powers. -/
def actualQuadraticPicardPower (order : Nat) : Real := order

/-- At order `r`, direct quartic Picard counting supplies `2r` powers. -/
def actualQuarticPicardPower (order : Nat) : Real := 2 * order

/-- Direct ordered integration by parts loses one gap per vertex. -/
def fullOrderedResolventLoss (order : Nat) : Real := order

/-- Quadratic channels have one negative kinetic power because their outer
coupling is `|g|` while kinetic time is `|g|^-2`. -/
def quadraticKineticDeficit : Real := 1

/-- Quartic outer coupling `|g|^2` exactly cancels kinetic time. -/
def quarticKineticDeficit : Real := 0

theorem actualQuadraticRegularKineticExponent_eq
    (order : Nat) (alpha : Real) :
    regularKineticExponent (actualQuadraticPicardPower order)
        (fullOrderedResolventLoss order) quadraticKineticDeficit alpha =
      (order : Real) * (1 - alpha) - 1 := by
  unfold regularKineticExponent actualQuadraticPicardPower
    fullOrderedResolventLoss quadraticKineticDeficit
  ring

theorem actualQuadraticBadKineticExponent_eq (alpha : Real) :
    badKineticExponent quadraticKineticDeficit alpha = alpha - 1 := rfl

theorem actualQuarticRegularKineticExponent_eq
    (order : Nat) (alpha : Real) :
    regularKineticExponent (actualQuarticPicardPower order)
        (fullOrderedResolventLoss order) quarticKineticDeficit alpha =
      (order : Real) * (2 - alpha) := by
  unfold regularKineticExponent actualQuarticPicardPower
    fullOrderedResolventLoss quarticKineticDeficit
  ring

theorem actualQuarticBadKineticExponent_eq (alpha : Real) :
    badKineticExponent quarticKineticDeficit alpha = alpha := by
  simp [badKineticExponent, quarticKineticDeficit]

/-- Fixed-order quadratic no-go with the true one-power-per-vertex Picard
count and a full one-denominator-per-vertex resolvent loss. -/
theorem actualQuadraticFullResolvent_no_cutoff
    (order : Nat) :
    ¬ (exists alpha,
      CutoffExponentAdmissible
        (actualQuadraticPicardPower order)
        (fullOrderedResolventLoss order)
        quadraticKineticDeficit alpha) := by
  rintro ⟨alpha, hbad, hregular⟩
  rw [actualQuadraticBadKineticExponent_eq] at hbad
  rw [actualQuadraticRegularKineticExponent_eq] at hregular
  have horder0 : 0 <= (order : Real) := Nat.cast_nonneg order
  have hmul : (order : Real) <= (order : Real) * alpha := by
    calc
      (order : Real) = (order : Real) * 1 := by ring
      _ <= (order : Real) * alpha :=
        mul_le_mul_of_nonneg_left (by linarith) horder0
  nlinarith

/-- Merely allowing the perturbative order to grow cannot fix the preceding
pointwise incompatibility while every vertex still loses a denominator. -/
theorem actualQuadraticFullResolvent_no_growingOrder_schedule
    (order : Nat -> Nat) :
    ¬ (exists alpha : Nat -> Real, forall n,
      CutoffExponentAdmissible
        (actualQuadraticPicardPower (order n))
        (fullOrderedResolventLoss (order n))
        quadraticKineticDeficit (alpha n)) := by
  rintro ⟨alpha, halpha⟩
  exact actualQuadraticFullResolvent_no_cutoff (order 0)
    ⟨alpha 0, halpha 0⟩

/-- For a positive quartic order, the exact feasible cutoff interval is
`0 < alpha < 2`. -/
theorem actualQuarticFullResolvent_admissible_iff
    {order : Nat} (horder : 0 < order) (alpha : Real) :
    CutoffExponentAdmissible
        (actualQuarticPicardPower order)
        (fullOrderedResolventLoss order)
        quarticKineticDeficit alpha <->
      0 < alpha /\ alpha < 2 := by
  have horderReal : 0 < (order : Real) := by exact_mod_cast horder
  unfold CutoffExponentAdmissible
  rw [actualQuarticBadKineticExponent_eq,
    actualQuarticRegularKineticExponent_eq]
  constructor
  · rintro ⟨halpha0, hregular⟩
    refine ⟨halpha0, ?_⟩
    have hfactor : 0 < (order : Real) * (2 - alpha) := hregular
    have := (mul_pos_iff.mp hfactor)
    rcases this with hpositive | hnegative
    · linarith [hpositive.2]
    · linarith [hnegative.1, horderReal]
  · rintro ⟨halpha0, halpha2⟩
    exact ⟨halpha0,
      mul_pos horderReal (sub_pos.mpr halpha2)⟩

/-- In particular `alpha = 1` closes the direct quartic fixed-order balance. -/
theorem actualQuarticFullResolvent_one_admissible
    {order : Nat} (horder : 0 < order) :
    CutoffExponentAdmissible
      (actualQuarticPicardPower order)
      (fullOrderedResolventLoss order)
      quarticKineticDeficit 1 := by
  rw [actualQuarticFullResolvent_admissible_iff horder]
  norm_num

/-- With true quadratic Picard power, an effective loss count admits some
cutoff exactly when it is strictly smaller than `order - 1`.  This is the
precise target for a growing-order cancellation/garden argument. -/
theorem actualQuadratic_exists_cutoff_iff_effectiveLoss
    {order denominatorLoss : Nat} (hloss : 0 < denominatorLoss) :
    (exists alpha,
      CutoffExponentAdmissible (order : Real) (denominatorLoss : Real)
        quadraticKineticDeficit alpha) <->
      denominatorLoss + 1 < order := by
  have hlossReal : 0 < (denominatorLoss : Real) := by
    exact_mod_cast hloss
  rw [exists_cutoffExponentAdmissible_iff hlossReal]
  unfold quadraticKineticDeficit
  norm_num
  exact_mod_cast (Iff.rfl : denominatorLoss + 1 < order <->
    denominatorLoss + 1 < order)

/-- If direct full resolvent loss is retained, extra coupling power
`surplus` makes the quadratic interval nonempty exactly when `surplus > 1`. -/
theorem quadraticFullResolvent_exists_cutoff_iff_surplus
    {order surplus : Real} (horder : 0 < order) :
    (exists alpha,
      CutoffExponentAdmissible (order + surplus) order
        quadraticKineticDeficit alpha) <->
      1 < surplus := by
  rw [exists_cutoffExponentAdmissible_iff horder]
  unfold quadraticKineticDeficit
  constructor <;> intro h <;> linarith

/-! ## Exact power envelopes and limits -/

/-- Regular-good absolute-value envelope before the kinetic channel
normalization. -/
def regularGoodPowerEnvelope
    (power denominatorLoss alpha coefficient g : Real) : Real :=
  coefficient *
    (|g| ^ power / (powerCouplingCutoff alpha g) ^ denominatorLoss)

/-- Nat-order form obtained directly from the arbitrary-order oscillatory
realization certificate. -/
def fixedOrderRegularGoodPowerEnvelope
    (order couplingPower capacity : Nat)
    (coefficient alpha g : Real) : Real :=
  ((capacity : Real) * coefficient * (2 : Real) ^ order) *
    (|g| ^ couplingPower / (powerCouplingCutoff alpha g) ^ order)

/-- The previous actual-history realization theorem works for every positive
power cutoff, without assuming the square-cutoff surplus powers. -/
theorem RegularGoodOscillatoryRealization.sectorNormBudget_le_powerEnvelope
    {History I : Type*} [DecidableEq History] [DecidableEq I]
    {left right : Finset I} {leftDefect rightDefect : I -> Complex}
    {order couplingPower capacity : Nat}
    {coefficient alpha g time : Real}
    {expansion : ClusterUnitSlotHistoryExpansion History I
      left right leftDefect rightDefect}
    (realization : RegularGoodOscillatoryRealization expansion
      order couplingPower capacity coefficient g
        (powerCouplingCutoff alpha g) time) :
    expansion.sectorNormBudget .regularGoodGarden <=
      fixedOrderRegularGoodPowerEnvelope
        order couplingPower capacity coefficient alpha g := by
  apply realization.sectorNormBudget_le_coupling_resolvent.trans_eq
  unfold fixedOrderRegularGoodPowerEnvelope
  rw [div_pow]
  ring

/-- The Nat-order and real-exponent envelopes coincide. -/
theorem fixedOrderRegularGoodPowerEnvelope_eq
    (order couplingPower capacity : Nat)
    (coefficient alpha g : Real) :
    fixedOrderRegularGoodPowerEnvelope
        order couplingPower capacity coefficient alpha g =
      regularGoodPowerEnvelope (couplingPower : Real) (order : Real) alpha
        ((capacity : Real) * coefficient * (2 : Real) ^ order) g := by
  unfold fixedOrderRegularGoodPowerEnvelope regularGoodPowerEnvelope
  rw [Real.rpow_natCast, Real.rpow_natCast]

/-- Exact exponent arithmetic for a nonzero coupling. -/
theorem regularGoodPowerEnvelope_div_rpow_eq
    (power denominatorLoss deficit alpha coefficient : Real)
    {g : Real} (hg : g ≠ 0) :
    regularGoodPowerEnvelope power denominatorLoss alpha coefficient g /
        |g| ^ deficit =
      coefficient *
        |g| ^ regularKineticExponent
          power denominatorLoss deficit alpha := by
  have habs : 0 < |g| := abs_pos.mpr hg
  unfold regularGoodPowerEnvelope powerCouplingCutoff
    regularKineticExponent
  calc
    coefficient * (|g| ^ power / (|g| ^ alpha) ^ denominatorLoss) /
          |g| ^ deficit =
        coefficient *
          ((|g| ^ power / (|g| ^ alpha) ^ denominatorLoss) /
            |g| ^ deficit) := by ring
    _ = coefficient * |g| ^ (power - alpha * denominatorLoss - deficit) := by
      congr 1
      rw [← Real.rpow_mul (abs_nonneg g) alpha denominatorLoss,
        ← Real.rpow_sub habs power (alpha * denominatorLoss),
        ← Real.rpow_sub habs (power - alpha * denominatorLoss) deficit]

/-- Exact normalized exponent of the power cutoff itself. -/
theorem powerCouplingCutoff_div_rpow_eq
    (deficit alpha : Real) {g : Real} (hg : g ≠ 0) :
    powerCouplingCutoff alpha g / |g| ^ deficit =
      |g| ^ badKineticExponent deficit alpha := by
  have habs : 0 < |g| := abs_pos.mpr hg
  unfold powerCouplingCutoff badKineticExponent
  exact (Real.rpow_sub habs alpha deficit).symm

/-- Positive real powers of a coupling sequence tending to zero also tend
to zero. -/
theorem abs_rpow_tendsto_zero
    {exponent : Real} (hexponent : 0 < exponent)
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n => |g n| ^ exponent) atTop (nhds 0) := by
  have hraw := hg.abs.rpow_const (Or.inr hexponent.le)
  simpa only [abs_zero, Real.zero_rpow hexponent.ne'] using hraw

theorem powerCouplingCutoff_tendsto_zero
    {alpha : Real} (halpha : 0 < alpha)
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n => powerCouplingCutoff alpha (g n))
      atTop (nhds 0) := by
  exact abs_rpow_tendsto_zero halpha g hg

/-- A positive bad exponent is exactly the normalized cutoff limit consumed
by a linear small-ball bound. -/
theorem powerCouplingCutoff_div_rpow_tendsto_zero
    {deficit alpha : Real}
    (hbad : 0 < badKineticExponent deficit alpha)
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n =>
      powerCouplingCutoff alpha (g n) / |g n| ^ deficit)
        atTop (nhds 0) := by
  have hpow := abs_rpow_tendsto_zero hbad g hg
  exact hpow.congr' (Filter.Eventually.of_forall (fun n =>
    (powerCouplingCutoff_div_rpow_eq deficit alpha (hg0 n)).symm))

/-- A positive regular exponent gives decay of the normalized
regular-resolvent envelope. -/
theorem regularGoodPowerEnvelope_div_rpow_tendsto_zero
    {power denominatorLoss deficit alpha coefficient : Real}
    (hregular : 0 < regularKineticExponent
      power denominatorLoss deficit alpha)
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n =>
      regularGoodPowerEnvelope power denominatorLoss alpha coefficient
          (g n) / |g n| ^ deficit) atTop (nhds 0) := by
  have hpow := abs_rpow_tendsto_zero hregular g hg
  have hscaled : Tendsto (fun n =>
      coefficient * |g n| ^ regularKineticExponent
        power denominatorLoss deficit alpha) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hpow : Tendsto (fun n =>
        coefficient * |g n| ^ regularKineticExponent
          power denominatorLoss deficit alpha) atTop
            (nhds (coefficient * 0)))
  exact hscaled.congr' (Filter.Eventually.of_forall (fun n =>
    (regularGoodPowerEnvelope_div_rpow_eq
      power denominatorLoss deficit alpha coefficient (hg0 n)).symm))

/-! ## Reuse of the existing linear-small-ball channel criterion -/

/-- General-cutoff version of the existing good/bad channel criterion.  The
displayed exponent balances discharge all four asymptotic premises; the
budget decomposition and linear small-ball inequalities remain explicit. -/
theorem higherOrder_channel_criteria_of_powerCutoff
    (g quadraticBudget quarticBudget quadraticBad quarticBad : Nat -> Real)
    (quadraticPower quadraticLoss quarticPower quarticLoss alpha : Real)
    (quadraticCoefficient quarticCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (quadraticSmallBallCoefficient quarticSmallBallCoefficient : Real)
    (hquadraticBalance : CutoffExponentAdmissible
      quadraticPower quadraticLoss quadraticKineticDeficit alpha)
    (hquarticBalance : CutoffExponentAdmissible
      quarticPower quarticLoss quarticKineticDeficit alpha)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0)
    (hquadraticBudget0 : forall n, 0 <= quadraticBudget n)
    (hquarticBudget0 : forall n, 0 <= quarticBudget n)
    (hquadraticBad0 : forall n, 0 <= quadraticBad n)
    (hquarticBad0 : forall n, 0 <= quarticBad n)
    (hquadraticBudget : forall n,
      quadraticBudget n <=
        regularGoodPowerEnvelope quadraticPower quadraticLoss alpha
            quadraticCoefficient (g n) +
          quadraticGlobal * quadraticBad n)
    (hquarticBudget : forall n,
      quarticBudget n <=
        regularGoodPowerEnvelope quarticPower quarticLoss alpha
            quarticCoefficient (g n) +
          quarticGlobal * quarticBad n)
    (hquadraticSmallBall : forall n,
      quadraticBad n <= quadraticSmallBallCoefficient *
        powerCouplingCutoff alpha (g n))
    (hquarticSmallBall : forall n,
      quarticBad n <= quarticSmallBallCoefficient *
        powerCouplingCutoff alpha (g n)) :
    Tendsto (fun n => quadraticBudget n / |g n|)
        atTop (nhds 0) /\
      Tendsto quarticBudget atTop (nhds 0) := by
  have hquadraticGood : Tendsto (fun n =>
      regularGoodPowerEnvelope quadraticPower quadraticLoss alpha
        quadraticCoefficient (g n) / |g n|) atTop (nhds 0) := by
    simpa only [quadraticKineticDeficit, Real.rpow_one] using
      regularGoodPowerEnvelope_div_rpow_tendsto_zero
        hquadraticBalance.2 g hg hg0
  have hquarticGoodRaw : Tendsto (fun n =>
      regularGoodPowerEnvelope quarticPower quarticLoss alpha
        quarticCoefficient (g n) / |g n| ^ (0 : Real))
        atTop (nhds 0) :=
    regularGoodPowerEnvelope_div_rpow_tendsto_zero
      hquarticBalance.2 g hg hg0
  have hquarticGood : Tendsto (fun n =>
      regularGoodPowerEnvelope quarticPower quarticLoss alpha
        quarticCoefficient (g n)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, div_one] using hquarticGoodRaw
  have hquadraticCutoff : Tendsto (fun n =>
      powerCouplingCutoff alpha (g n) / |g n|) atTop (nhds 0) := by
    simpa only [quadraticKineticDeficit, Real.rpow_one] using
      powerCouplingCutoff_div_rpow_tendsto_zero
        hquadraticBalance.1 g hg hg0
  have hquarticCutoffRaw : Tendsto (fun n =>
      powerCouplingCutoff alpha (g n) / |g n| ^ (0 : Real))
        atTop (nhds 0) :=
    powerCouplingCutoff_div_rpow_tendsto_zero
      hquarticBalance.1 g hg hg0
  have hquarticCutoff : Tendsto (fun n =>
      powerCouplingCutoff alpha (g n)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, div_one] using hquarticCutoffRaw
  exact higherOrder_channel_criteria_of_linearSmallBall
    g quadraticBudget quarticBudget
    (fun n => regularGoodPowerEnvelope quadraticPower quadraticLoss alpha
      quadraticCoefficient (g n))
    (fun n => regularGoodPowerEnvelope quarticPower quarticLoss alpha
      quarticCoefficient (g n))
    quadraticBad quarticBad
    (fun n => powerCouplingCutoff alpha (g n))
    (fun n => powerCouplingCutoff alpha (g n))
    quadraticGlobal quarticGlobal
    quadraticSmallBallCoefficient quarticSmallBallCoefficient
    hquadraticBudget0 hquarticBudget0 hquadraticBad0 hquarticBad0
    hquadraticBudget hquarticBudget hquadraticSmallBall hquarticSmallBall
    hquadraticGood hquarticGood hquadraticCutoff hquarticCutoff

/-- End-to-end kinetic-time consequence of the feasible general-cutoff
balance. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime_powerCutoff
    (g quadraticBudget quarticBudget quadraticBad quarticBad : Nat -> Real)
    (quadraticPower quadraticLoss quarticPower quarticLoss alpha : Real)
    (kappa beta tau : Real)
    (quadraticCoefficient quarticCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (quadraticSmallBallCoefficient quarticSmallBallCoefficient : Real)
    (hquadraticBalance : CutoffExponentAdmissible
      quadraticPower quadraticLoss quadraticKineticDeficit alpha)
    (hquarticBalance : CutoffExponentAdmissible
      quarticPower quarticLoss quarticKineticDeficit alpha)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0)
    (hquadraticBudget0 : forall n, 0 <= quadraticBudget n)
    (hquarticBudget0 : forall n, 0 <= quarticBudget n)
    (hquadraticBad0 : forall n, 0 <= quadraticBad n)
    (hquarticBad0 : forall n, 0 <= quarticBad n)
    (hquadraticBudget : forall n,
      quadraticBudget n <=
        regularGoodPowerEnvelope quadraticPower quadraticLoss alpha
            quadraticCoefficient (g n) +
          quadraticGlobal * quadraticBad n)
    (hquarticBudget : forall n,
      quarticBudget n <=
        regularGoodPowerEnvelope quarticPower quarticLoss alpha
            quarticCoefficient (g n) +
          quarticGlobal * quarticBad n)
    (hquadraticSmallBall : forall n,
      quadraticBad n <= quadraticSmallBallCoefficient *
        powerCouplingCutoff alpha (g n))
    (hquarticSmallBall : forall n,
      quarticBad n <= quarticSmallBallCoefficient *
        powerCouplingCutoff alpha (g n)) :
    Tendsto (fun n =>
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) := by
  obtain ⟨hquadratic, hquartic⟩ :=
    higherOrder_channel_criteria_of_powerCutoff
      g quadraticBudget quarticBudget quadraticBad quarticBad
      quadraticPower quadraticLoss quarticPower quarticLoss alpha
      quadraticCoefficient quarticCoefficient quadraticGlobal quarticGlobal
      quadraticSmallBallCoefficient quarticSmallBallCoefficient
      hquadraticBalance hquarticBalance hg hg0
      hquadraticBudget0 hquarticBudget0 hquadraticBad0 hquarticBad0
      hquadraticBudget hquarticBudget hquadraticSmallBall hquarticSmallBall
  exact coupling_channel_budget_tendsto_zero_at_kineticTime
    g quadraticBudget quarticBudget kappa beta tau hg0
      hquadratic hquartic

end

end ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
