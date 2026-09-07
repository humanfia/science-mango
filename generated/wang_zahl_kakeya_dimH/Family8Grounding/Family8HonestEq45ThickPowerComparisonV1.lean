import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# Honest Family 6 / Equation (45) scalar comparison

The Family 6 convex-plank Frostman factor retains the literal thickening
count `M`.  At half the Equation (45) epsilon, its remaining scalar is bounded
by the Proposition 6.6(A) outer factor.  Thus the comparison below keeps the
exact loss `M^(beta/2)`; it neither absorbs that loss nor replaces it by a
conclusion-valued callback.

Only two monotonicities enter the proof:

* `a^(-epsilon/2) <= delta^(-epsilon/2)` when `0 < delta <= a`;
* `a / b <= (a / b)^(1-beta/2)` when `0 < a <= b` and `0 <= beta <= 1`.
-/

open scoped ENNReal NNReal

namespace Family8HonestEq45ThickPowerComparisonV1

open Family6AffinePlankAnalyticHypothesesStableV1
open Family8Prop66AOuterInnerProductAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

universe u

/-- The epsilon loss at plank width `a` is no larger than the same half-loss
at the finer scale `delta`. -/
theorem halfEpsilon_widthLoss_le_deltaLoss
    {delta a : NNReal} {epsilon : Real}
    (hdelta : 0 < delta) (hdeltaA : delta <= a)
    (hepsilon : 0 < epsilon) :
    (a : ENNReal) ^ (-(epsilon / 2)) <=
      (delta : ENNReal) ^ (-epsilon / 2) := by
  have ha : 0 < a := hdelta.trans_le hdeltaA
  have hNN : a ^ (-(epsilon / 2)) <= delta ^ (-(epsilon / 2)) :=
    NNReal.rpow_le_rpow_of_nonpos hdelta hdeltaA (by linarith)
  rw [show -epsilon / 2 = -(epsilon / 2) by ring]
  rw [<- ENNReal.coe_rpow_of_ne_zero ha.ne' (-(epsilon / 2)),
    <- ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-(epsilon / 2))]
  exact ENNReal.coe_le_coe.mpr hNN

/-- On an aspect ratio in `(0,1]`, lowering the exponent from `1` to
`1-beta/2` can only increase the real power. -/
theorem aspectRatio_le_oneSubHalfBetaPower
    {a b : NNReal} {beta : Real}
    (ha : 0 < a) (hab : a <= b)
    (hbeta0 : 0 <= beta) (_hbeta1 : beta <= 1) :
    (a : ENNReal) / (b : ENNReal) <=
      ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) := by
  have hb : 0 < b := ha.trans_le hab
  have hratioNN : a / b <= 1 := (div_le_one hb).2 hab
  have hratio : (a : ENNReal) / (b : ENNReal) <= 1 := by
    rw [<- ENNReal.coe_div hb.ne']
    exact ENNReal.coe_le_coe.mpr hratioNN
  calc
    (a : ENNReal) / (b : ENNReal) =
        ((a : ENNReal) / (b : ENNReal)) ^ (1 : Real) := by
      rw [ENNReal.rpow_one]
    _ <= ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hratio (by linarith)

/-- Exact coupling of the Family 6 thickening power with one copy of the
plank aspect ratio.  This is the algebra which allows a later bound on
`M * (a / b)` to cancel a reciprocal-aspect contribution inside `M`.

No cancellation by `M` is used, so the identity remains valid when `M = 0`.
Positivity and finiteness are required only for the aspect ratio, in order to
combine its two arbitrary real powers. -/
theorem coupledThickAspectPower_mul_outerAspect_eq
    {a b : NNReal} (M : NNReal) {beta : Real}
    (ha : 0 < a) (hab : a <= b) (hbeta0 : 0 <= beta) :
    (((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^ (beta / 2)) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) =
      (M : ENNReal) ^ (beta / 2) *
        ((a : ENNReal) / (b : ENNReal)) := by
  have hb : 0 < b := ha.trans_le hab
  let x : ENNReal := (a : ENNReal) / (b : ENNReal)
  let p : Real := beta / 2
  have hp : 0 <= p := by
    dsimp only [p]
    linarith
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr ha.ne', ENNReal.coe_ne_top⟩
  have hxTop : x ≠ ∞ := by
    dsimp only [x]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hb.ne')
  have hexponent : p + (1 - p) = 1 := by ring
  change (((M : ENNReal) * x) ^ p) * x ^ (1 - p) =
    (M : ENNReal) ^ p * x
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
  calc
    ((M : ENNReal) ^ p * x ^ p) * x ^ (1 - p) =
        (M : ENNReal) ^ p * (x ^ p * x ^ (1 - p)) := by
      ac_rfl
    _ = (M : ENNReal) ^ p * x ^ (p + (1 - p)) := by
      rw [ENNReal.rpow_add p (1 - p) hx0 hxTop]
    _ = (M : ENNReal) ^ p * x := by
      rw [hexponent, ENNReal.rpow_one]

/-- Honest scalar bridge from the literal Family 6 Equation (45) output to
the Proposition 6.6(A) outer factor.

The thickening factor is retained exactly as `(M : ENNReal)^(beta/2)`.  In
particular this theorem does not use a bound on `M`, does not absorb it into a
power of `delta`, and does not assume a callback with the desired conclusion.
-/
theorem convexPlankFrostmanFactor_halfEpsilon_le_thickPower_mul_proposition66AOuterFactor
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {delta a b : NNReal}
    (D : ShadedConvexPlankFamily iota a b)
    (CF : ENNReal) (M : NNReal) {epsilon beta : Real}
    (hdelta : 0 < delta) (hdeltaA : delta <= a) (hab : a <= b)
    (hepsilon : 0 < epsilon)
    (hbeta0 : 0 <= beta) (hbeta1 : beta <= 1) :
    convexPlankFrostmanFactor D (epsilon / 2) beta CF M <=
      (M : ENNReal) ^ (beta / 2) *
        proposition66AOuterFactor delta a b
          (Fintype.card iota) CF epsilon beta := by
  have ha : 0 < a := hdelta.trans_le hdeltaA
  have hscale :
      (a : ENNReal) ^ (-(epsilon / 2)) <=
        (delta : ENNReal) ^ (-epsilon / 2) :=
    halfEpsilon_widthLoss_le_deltaLoss hdelta hdeltaA hepsilon
  have haspect :
      (a : ENNReal) / (b : ENNReal) <=
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) :=
    aspectRatio_le_oneSubHalfBetaPower ha hab hbeta0 hbeta1
  unfold convexPlankFrostmanFactor proposition66AOuterFactor
  calc
    (a : ENNReal) ^ (-(epsilon / 2)) *
          CF ^ (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (Fintype.card iota : ENNReal)) ^ (1 - beta / 2) <=
        (delta : ENNReal) ^ (-epsilon / 2) *
          CF ^ (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          (((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2)) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (Fintype.card iota : ENNReal)) ^ (1 - beta / 2) := by
      gcongr
    _ = (M : ENNReal) ^ (beta / 2) *
        ((delta : ENNReal) ^ (-epsilon / 2) *
          CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (Fintype.card iota : ENNReal)) ^ (1 - beta / 2)) := by
      ac_rfl

/-- Stronger honest bridge which couples the thickening loss to the plank
aspect ratio before comparing with Equation (45).

Unlike the preceding theorem, this result does not weaken the Family 6
aspect factor `a / b` to `(a / b)^(1-beta/2)`.  It uses the exact identity

`M^(beta/2) * (a/b) = (M*(a/b))^(beta/2) * (a/b)^(1-beta/2)`.

Consequently an upstream estimate of the form `M <= C * (b/a)` becomes an
estimate on the coupled loss `M * (a/b)` and does not leave a spurious
reciprocal-aspect power. -/
theorem convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspectPower_mul_proposition66AOuterFactor
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {rho a b : NNReal}
    (D : ShadedConvexPlankFamily iota a b)
    (CF : ENNReal) (M : NNReal) {epsilon beta : Real}
    (hrho : 0 < rho) (hrhoA : rho <= a) (hab : a <= b)
    (hepsilon : 0 < epsilon)
    (hbeta0 : 0 <= beta) :
    convexPlankFrostmanFactor D (epsilon / 2) beta CF M <=
      (((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^ (beta / 2)) *
        proposition66AOuterFactor rho a b
          (Fintype.card iota) CF epsilon beta := by
  have ha : 0 < a := hrho.trans_le hrhoA
  have hscale :
      (a : ENNReal) ^ (-(epsilon / 2)) <=
        (rho : ENNReal) ^ (-epsilon / 2) :=
    halfEpsilon_widthLoss_le_deltaLoss hrho hrhoA hepsilon
  unfold convexPlankFrostmanFactor proposition66AOuterFactor
  calc
    (a : ENNReal) ^ (-(epsilon / 2)) *
          CF ^ (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (Fintype.card iota : ENNReal)) ^ (1 - beta / 2) <=
        (rho : ENNReal) ^ (-epsilon / 2) *
          CF ^ (1 - beta / 2) *
          (M : ENNReal) ^ (beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (Fintype.card iota : ENNReal)) ^ (1 - beta / 2) := by
      gcongr
    _ = ((((M : ENNReal) *
            ((a : ENNReal) / (b : ENNReal))) ^ (beta / 2)) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2)) *
        ((rho : ENNReal) ^ (-epsilon / 2) *
          CF ^ (1 - beta / 2) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (Fintype.card iota : ENNReal)) ^ (1 - beta / 2)) := by
      rw [coupledThickAspectPower_mul_outerAspect_eq M ha hab hbeta0]
      ac_rfl
    _ = (((M : ENNReal) *
            ((a : ENNReal) / (b : ENNReal))) ^ (beta / 2)) *
        ((rho : ENNReal) ^ (-epsilon / 2) *
          CF ^ (1 - beta / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) *
          (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (Fintype.card iota : ENNReal)) ^ (1 - beta / 2)) := by
      ac_rfl

#print axioms halfEpsilon_widthLoss_le_deltaLoss
#print axioms aspectRatio_le_oneSubHalfBetaPower
#print axioms coupledThickAspectPower_mul_outerAspect_eq
#print axioms
  convexPlankFrostmanFactor_halfEpsilon_le_thickPower_mul_proposition66AOuterFactor
#print axioms
  convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspectPower_mul_proposition66AOuterFactor

end
end Family8HonestEq45ThickPowerComparisonV1
