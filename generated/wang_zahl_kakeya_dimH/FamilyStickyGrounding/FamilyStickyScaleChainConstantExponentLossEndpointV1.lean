import FamilyStickyGrounding.FamilyStickyScaleChainConstantBearingStoppingEndpointV1
import FamilyStickyGrounding.FamilyStickyScaleChainParentNormalizerReverseProducerV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainConstantExponentLossEndpointV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainRootedRefinementTreeV1.IntervalRootedRefinementScaleTree
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Absorbing a finite stopping constant by an explicit exponent loss

The actual Family7 stopping theorem produces

`(theta / rho) ^ eta(stage) <= K * middleValue rho`.

This file never erases `K`.  Instead, it records the exact pointwise budget
`K <= (theta / rho) ^ loss` and cancels that power to obtain the honest
weakened exponent `eta(stage) - loss`.  A second adapter will derive the
pointwise budget from the buffered endpoint and an explicit scale-gap bound.
-/

variable {delta : NNReal} {N : Nat} {epsilon : Real}
  {eta : Nat -> Real} {K : ENNReal}

/-- The weakest transparent power budget used to absorb the constant on the
actual buffered interval. -/
structure BufferedExponentLossBudget
    (W : KatzTaoConstantDividingWitness delta N epsilon eta K)
    (loss : Real) : Prop where
  loss_nonneg : 0 <= loss
  constant_le_power : forall rho : NNReal,
    (W.tau : ENNReal) *
          (((W.theta / W.tau : NNReal) : ENNReal) ^ epsilon) <= rho ->
      (rho : ENNReal) <=
          (W.theta : ENNReal) *
            (((W.tau / W.theta : NNReal) : ENNReal) ^ epsilon) ->
      K <= (((W.theta / rho : NNReal) : ENNReal) ^ loss)

/-- A single endpoint scale-gap check.  This is stronger than the pointwise
budget only by monotonicity over the buffered interval. -/
structure EndpointScaleGapExponentLossBudget
    (W : KatzTaoConstantDividingWitness delta N epsilon eta K)
    (loss : Real) : Prop where
  loss_nonneg : 0 <= loss
  constant_le_gap_power :
    K <= (((W.theta / W.tau : NNReal) : ENNReal) ^ (epsilon * loss))

namespace EndpointScaleGapExponentLossBudget

/-- The buffered upper endpoint makes `theta / rho` at least
`(theta / tau)^epsilon`, so the one scale-gap check generates every
pointwise absorption inequality. -/
theorem toBufferedExponentLossBudget
    {W : KatzTaoConstantDividingWitness delta N epsilon eta K}
    {loss : Real}
    (B : EndpointScaleGapExponentLossBudget W loss)
    (tau_pos : 0 < W.tau) :
    BufferedExponentLossBudget W loss where
  loss_nonneg := B.loss_nonneg
  constant_le_power := by
    intro rho hlower hupper
    let a : ENNReal := ((W.theta / W.tau : NNReal) : ENNReal)
    let b : ENNReal := ((W.tau / W.theta : NNReal) : ENNReal)
    let x : ENNReal := ((W.theta / rho : NNReal) : ENNReal)
    have hthetaPos : 0 < W.theta := tau_pos.trans_le W.tau_le_theta
    have hthetaTauPos : 0 < W.theta / W.tau := div_pos hthetaPos tau_pos
    have hbufferPos : 0 <
        (W.tau : ENNReal) * a ^ epsilon := by
      exact ENNReal.mul_pos (ENNReal.coe_pos.mpr tau_pos).ne'
        (ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hthetaTauPos) ENNReal.coe_ne_top).ne'
    have hrhoPos : 0 < rho := by
      exact_mod_cast hbufferPos.trans_le hlower
    have hab : a * b = 1 := by
      change ((W.theta / W.tau : NNReal) : ENNReal) *
          ((W.tau / W.theta : NNReal) : ENNReal) = 1
      rw [<- ENNReal.coe_mul, div_mul_div_cancel₀ tau_pos.ne',
        div_self hthetaPos.ne']
      rfl
    have hscaled : a ^ epsilon * (rho : ENNReal) <= W.theta := by
      calc
        a ^ epsilon * (rho : ENNReal) <=
            a ^ epsilon * ((W.theta : ENNReal) * b ^ epsilon) :=
          mul_le_mul' le_rfl hupper
        _ = (W.theta : ENNReal) * (a ^ epsilon * b ^ epsilon) := by
          ac_rfl
        _ = (W.theta : ENNReal) * (a * b) ^ epsilon := by
          rw [ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top
            ENNReal.coe_ne_top epsilon]
        _ = W.theta := by rw [hab]; simp
    have hgap_le_ratio : a ^ epsilon <= x := by
      change a ^ epsilon <= ((W.theta / rho : NNReal) : ENNReal)
      rw [ENNReal.coe_div hrhoPos.ne']
      exact (ENNReal.le_div_iff_mul_le
        (Or.inl (ENNReal.coe_ne_zero.mpr hrhoPos.ne'))
        (Or.inl ENNReal.coe_ne_top)).2 hscaled
    calc
      K <= a ^ (epsilon * loss) := by
        simpa [a] using B.constant_le_gap_power
      _ = (a ^ epsilon) ^ loss := ENNReal.rpow_mul a epsilon loss
      _ <= x ^ loss := ENNReal.rpow_le_rpow hgap_le_ratio B.loss_nonneg
      _ = (((W.theta / rho : NNReal) : ENNReal) ^ loss) := by rfl

end EndpointScaleGapExponentLossBudget

/-- A scale-independent small-delta condition which pays for the same loss
for every witness at the fixed base scale `delta`. -/
structure SmallDeltaExponentLossBudget
    (delta : NNReal) (epsilon : Real) (K : ENNReal) (loss : Real) : Prop where
  epsilon_nonneg : 0 <= epsilon
  loss_nonneg : 0 <= loss
  constant_le_delta_power :
    K <= (delta : ENNReal) ^ (-(epsilon ^ 2 * loss))

namespace SmallDeltaExponentLossBudget

/-- The witness longness inequality converts the small-delta power into the
endpoint scale-gap power. -/
theorem toEndpointScaleGapExponentLossBudget
    {W : KatzTaoConstantDividingWitness delta N epsilon eta K}
    {loss : Real}
    (B : SmallDeltaExponentLossBudget delta epsilon K loss)
    (delta_pos : 0 < delta) :
    EndpointScaleGapExponentLossBudget W loss where
  loss_nonneg := B.loss_nonneg
  constant_le_gap_power := by
    let d : ENNReal := (delta : ENNReal)
    let a : ENNReal := ((W.theta / W.tau : NNReal) : ENNReal)
    have tau_pos : 0 < W.tau := delta_pos.trans_le W.delta_le_tau
    have hthetaPos : 0 < W.theta := tau_pos.trans_le W.tau_le_theta
    have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr delta_pos.ne'
    have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
    have hscaled : d ^ (-epsilon) * (W.tau : ENNReal) <= W.theta := by
      calc
        d ^ (-epsilon) * (W.tau : ENNReal) <=
            d ^ (-epsilon) *
              (d ^ epsilon * (W.theta : ENNReal)) :=
          mul_le_mul' le_rfl W.long
        _ = (d ^ (-epsilon) * d ^ epsilon) * W.theta := by
          ac_rfl
        _ = d ^ ((-epsilon) + epsilon) * W.theta := by
          rw [ENNReal.rpow_add (-epsilon) epsilon hd0 hdTop]
        _ = W.theta := by simp
    have hdeltaGap : d ^ (-epsilon) <= a := by
      change d ^ (-epsilon) <=
        ((W.theta / W.tau : NNReal) : ENNReal)
      rw [ENNReal.coe_div tau_pos.ne']
      exact (ENNReal.le_div_iff_mul_le
        (Or.inl (ENNReal.coe_ne_zero.mpr tau_pos.ne'))
        (Or.inl ENNReal.coe_ne_top)).2 hscaled
    have hexponentNonneg : 0 <= epsilon * loss :=
      mul_nonneg B.epsilon_nonneg B.loss_nonneg
    calc
      K <= d ^ (-(epsilon ^ 2 * loss)) := by
        simpa [d] using B.constant_le_delta_power
      _ = d ^ ((-epsilon) * (epsilon * loss)) := by
        congr 1
        ring
      _ = (d ^ (-epsilon)) ^ (epsilon * loss) :=
        ENNReal.rpow_mul d (-epsilon) (epsilon * loss)
      _ <= a ^ (epsilon * loss) :=
        ENNReal.rpow_le_rpow hdeltaGap hexponentNonneg
      _ = (((W.theta / W.tau : NNReal) : ENNReal) ^
          (epsilon * loss)) := by rfl

end SmallDeltaExponentLossBudget

/-- Output which retains both the original constant-bearing witness and the
new exponent loss. -/
structure KatzTaoExponentLossDividingWitness
    (delta : NNReal) (N : Nat) (epsilon : Real)
    (eta : Nat -> Real) (K : ENNReal) (loss : Real) where
  original : KatzTaoConstantDividingWitness delta N epsilon eta K
  budget : BufferedExponentLossBudget original loss
  middle_lower_after_loss : forall rho : NNReal,
    (original.tau : ENNReal) *
          (((original.theta / original.tau : NNReal) : ENNReal) ^ epsilon) <= rho ->
      (rho : ENNReal) <=
          (original.theta : ENNReal) *
            (((original.tau / original.theta : NNReal) : ENNReal) ^ epsilon) ->
      (((original.theta / rho : NNReal) : ENNReal) ^
        (eta original.stage - loss)) <= original.middleValue rho

namespace KatzTaoConstantDividingWitness

/-- Pointwise exponent loss absorbs `K` by cancellative `ENNReal` power
algebra.  The original `K`-bearing inequality remains packaged in the output. -/
def toExponentLossWitness
    (W : KatzTaoConstantDividingWitness delta N epsilon eta K)
    (tau_pos : 0 < W.tau) (loss : Real)
    (B : BufferedExponentLossBudget W loss) :
    KatzTaoExponentLossDividingWitness delta N epsilon eta K loss where
  original := W
  budget := B
  middle_lower_after_loss := by
    intro rho hlower hupper
    let x : ENNReal := ((W.theta / rho : NNReal) : ENNReal)
    let q : ENNReal := x ^ loss
    have hthetaPos : 0 < W.theta := tau_pos.trans_le W.tau_le_theta
    have hthetaTauPos : 0 < W.theta / W.tau := div_pos hthetaPos tau_pos
    have hbufferPos : 0 <
        (W.tau : ENNReal) *
          (((W.theta / W.tau : NNReal) : ENNReal) ^ epsilon) := by
      exact ENNReal.mul_pos (ENNReal.coe_pos.mpr tau_pos).ne'
        (ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hthetaTauPos) ENNReal.coe_ne_top).ne'
    have hrhoPos : 0 < rho := by
      exact_mod_cast hbufferPos.trans_le hlower
    have hxPos : 0 < W.theta / rho := div_pos hthetaPos hrhoPos
    have hx0 : x ≠ 0 := ENNReal.coe_ne_zero.mpr hxPos.ne'
    have hxTop : x ≠ ∞ := ENNReal.coe_ne_top
    have hq0 : q ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hxPos) hxTop).ne'
    have hqTop : q ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg B.loss_nonneg hxTop
    have hpow : q * x ^ (eta W.stage - loss) = x ^ eta W.stage := by
      calc
        q * x ^ (eta W.stage - loss) =
            x ^ (loss + (eta W.stage - loss)) := by
          rw [ENNReal.rpow_add loss (eta W.stage - loss) hx0 hxTop]
        _ = x ^ eta W.stage := by congr 1; ring
    have hmul : q * x ^ (eta W.stage - loss) <=
        q * W.middleValue rho := by
      rw [hpow]
      calc
        x ^ eta W.stage <= K * W.middleValue rho := by
          simpa [x] using W.middle_lower_with_constant rho hlower hupper
        _ <= q * W.middleValue rho :=
          mul_le_mul' (B.constant_le_power rho hlower hupper) le_rfl
    exact (ENNReal.mul_le_mul_iff_right hq0 hqTop).1 hmul

end KatzTaoConstantDividingWitness

/-! ## Literal compatibility with an honest lowered exponent -/

/-- Change only the selected stopping exponent.  The predecessor exponent
used by the global and adjacent bounds is left unchanged. -/
def lowerStoppingExponent (eta : Nat -> Real) (stage : Nat) (loss : Real) :
    Nat -> Real := fun j => if j = stage then eta j - loss else eta j

@[simp] theorem lowerStoppingExponent_at
    (eta : Nat -> Real) (stage : Nat) (loss : Real) :
    lowerStoppingExponent eta stage loss stage = eta stage - loss := by
  simp [lowerStoppingExponent]

theorem lowerStoppingExponent_pred
    (eta : Nat -> Real) {stage : Nat} (stage_pos : 1 <= stage)
    (loss : Real) :
    lowerStoppingExponent eta stage loss (stage - 1) = eta (stage - 1) := by
  have hne : stage - 1 ≠ stage := by omega
  simp [lowerStoppingExponent, hne]

/-- The lowered profile remains monotone exactly when the original adjacent
exponent gap can pay for `loss`. -/
theorem lowerStoppingExponent_monotone
    (eta : Nat -> Real) {stage : Nat} (stage_pos : 1 <= stage)
    {loss : Real} (loss_nonneg : 0 <= loss)
    (eta_monotone : Monotone eta)
    (loss_le_gap : eta (stage - 1) + loss <= eta stage) :
    Monotone (lowerStoppingExponent eta stage loss) := by
  intro a b hab
  by_cases ha : a = stage
  · subst a
    have heta := eta_monotone hab
    by_cases hb : b = stage
    · subst b
      exact le_rfl
    · rw [lowerStoppingExponent_at]
      simp only [lowerStoppingExponent, if_neg hb]
      linarith
  · by_cases hb : b = stage
    · subst b
      have ha_le_pred : a <= stage - 1 := by omega
      have heta := eta_monotone ha_le_pred
      rw [lowerStoppingExponent_at]
      simp only [lowerStoppingExponent, if_neg ha]
      linarith
    · simpa only [lowerStoppingExponent, if_neg ha, if_neg hb] using
        eta_monotone hab

namespace KatzTaoExponentLossDividingWitness

/-- The old literal witness API is recovered at the explicitly lowered
stopping exponent, while the richer wrapper still retains the original
constant-bearing proof. -/
def toLiteralDividingWitness
    {loss : Real}
    (W : KatzTaoExponentLossDividingWitness
      delta N epsilon eta K loss) :
    KatzTaoDividingWitness delta N epsilon
      (lowerStoppingExponent eta W.original.stage loss) where
  tau := W.original.tau
  theta := W.original.theta
  stage := W.original.stage
  stage_pos := W.original.stage_pos
  stage_le := W.original.stage_le
  delta_le_tau := W.original.delta_le_tau
  tau_le_theta := W.original.tau_le_theta
  theta_le_one := W.original.theta_le_one
  long := W.original.long
  globalValue := W.original.globalValue
  adjacentValue := W.original.adjacentValue
  middleValue := W.original.middleValue
  global_upper := by
    simpa [lowerStoppingExponent_pred eta W.original.stage_pos loss] using
      W.original.global_upper
  adjacent_upper := by
    simpa [lowerStoppingExponent_pred eta W.original.stage_pos loss] using
      W.original.adjacent_upper
  middle_lower := by
    intro rho hlower hupper
    simpa using W.middle_lower_after_loss rho hlower hupper

end KatzTaoExponentLossDividingWitness

#print axioms EndpointScaleGapExponentLossBudget.toBufferedExponentLossBudget
#print axioms SmallDeltaExponentLossBudget.toEndpointScaleGapExponentLossBudget
#print axioms KatzTaoConstantDividingWitness.toExponentLossWitness
#print axioms lowerStoppingExponent_at
#print axioms lowerStoppingExponent_pred
#print axioms lowerStoppingExponent_monotone
#print axioms KatzTaoExponentLossDividingWitness.toLiteralDividingWitness

end
end FamilyStickyScaleChainConstantExponentLossEndpointV1
