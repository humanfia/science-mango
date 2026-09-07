import Family8Grounding.Family8HonestEq45ThickPowerComparisonV1
import Mathlib.Tactic

/-!
# Honest Equation (45) comparison with coupled thick/aspect loss

The Family 6 Frostman factor contains both the honest thickening power
`M^(beta/2)` and one full aspect ratio `a / b`.  Equation (45) already
contains `(a / b)^(1-beta/2)`.  Keeping these two facts coupled gives the
strictly sharper external loss

`(M * (a / b))^(beta/2)`.

This matters for the normalized selected-occurrence datum: its canonical
thick parameter contains `b / a`, which cancels inside this coupled loss.
No bound for `M`, cardinality envelope, or scalar absorption callback is
used here.
-/

open scoped ENNReal NNReal

namespace Family8HonestEq45CoupledThickAspectComparisonV1

open Family6AffinePlankAnalyticHypothesesStableV1
open Family8HonestEq45ThickPowerComparisonV1
open Family8Prop66AOuterInnerProductAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

universe u

/-- Honest Family 6 to Equation (45) comparison with the thickening power
coupled to the aspect-ratio power that is absent from the outer factor.

The scale hypothesis is only `rho <= a`.  In particular, this theorem does
not assert that the original fine scale is below the normalized winner
width; a caller using a fixed normalization constant must supply that scale
bridge separately. -/
theorem convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspect_mul_proposition66AOuterFactor
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {rho a b : NNReal}
    (D : ShadedConvexPlankFamily iota a b)
    (CF : ENNReal) (M : NNReal) {epsilon beta : Real}
    (hrho : 0 < rho) (hrhoA : rho <= a) (hab : a <= b)
    (hepsilon : 0 < epsilon) (hbeta : 0 <= beta) :
    convexPlankFrostmanFactor D (epsilon / 2) beta CF M <=
      (((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^
          (beta / 2)) *
        proposition66AOuterFactor rho a b
          (Fintype.card iota) CF epsilon beta := by
  exact
    convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspectPower_mul_proposition66AOuterFactor
      D CF M hrho hrhoA hab hepsilon hbeta
/-
  have ha : 0 < a := hrho.trans_le hrhoA
  have hb : 0 < b := ha.trans_le hab
  have hscale :
      (a : ENNReal) ^ (-(epsilon / 2)) <=
        (rho : ENNReal) ^ (-epsilon / 2) :=
    halfEpsilon_widthLoss_le_deltaLoss hrho hrhoA hepsilon
  have hhalf : 0 <= beta / 2 := by linarith
  have hratio0 :
      (a : ENNReal) / (b : ENNReal) ≠ 0 :=
    ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr ha.ne', ENNReal.coe_ne_top⟩
  have hratioTop :
      (a : ENNReal) / (b : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hb.ne')
  have hratioSplit :
      (((a : ENNReal) / (b : ENNReal)) ^ (beta / 2)) *
          (((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2)) =
        (a : ENNReal) / (b : ENNReal) := by
    calc
      (((a : ENNReal) / (b : ENNReal)) ^ (beta / 2)) *
          (((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2)) =
        ((a : ENNReal) / (b : ENNReal)) ^
          ((beta / 2) + (1 - beta / 2)) := by
            rw [ENNReal.rpow_add (beta / 2) (1 - beta / 2)
              hratio0 hratioTop]
      _ = (a : ENNReal) / (b : ENNReal) := by
        rw [show (beta / 2) + (1 - beta / 2) = (1 : Real) by ring,
          ENNReal.rpow_one]
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
    _ =
        (((M : ENNReal) ^ (beta / 2)) *
          (((a : ENNReal) / (b : ENNReal)) ^ (beta / 2))) *
          ((rho : ENNReal) ^ (-epsilon / 2) *
            CF ^ (1 - beta / 2) *
            (((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2)) *
            (b : ENNReal) ^ (-2 * beta) *
            (((b : ENNReal) ^ (2 : Nat)) *
              (Fintype.card iota : ENNReal)) ^ (1 - beta / 2)) := by
      rw [← hratioSplit]
      ac_rfl
    _ =
        (((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^
          (beta / 2)) *
          ((rho : ENNReal) ^ (-epsilon / 2) *
            CF ^ (1 - beta / 2) *
            (((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2)) *
            (b : ENNReal) ^ (-2 * beta) *
            (((b : ENNReal) ^ (2 : Nat)) *
              (Fintype.card iota : ENNReal)) ^ (1 - beta / 2)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf]
-/

/-- Reparameterized form exposing the weakest normalized-width bridge.
Supplying `delta / 576 <= a` is enough to apply the coupled theorem at the
source scale `delta / 576`.  Moving the displayed outer factor back from
`delta / 576` to `delta` costs only the fixed scalar
`576^(epsilon/2)`; no thickening or cardinality loss is involved in that
last scalar rewrite. -/
theorem convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspect_mul_proposition66AOuterFactor_div_576
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {delta a b : NNReal}
    (D : ShadedConvexPlankFamily iota a b)
    (CF : ENNReal) (M : NNReal) {epsilon beta : Real}
    (hdelta : 0 < delta) (hdeltaA : delta / 576 <= a) (hab : a <= b)
    (hepsilon : 0 < epsilon) (hbeta : 0 <= beta) :
    convexPlankFrostmanFactor D (epsilon / 2) beta CF M <=
      (((M : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^
          (beta / 2)) *
        proposition66AOuterFactor (delta / 576) a b
          (Fintype.card iota) CF epsilon beta := by
  exact
    convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspect_mul_proposition66AOuterFactor
      D CF M (div_pos hdelta (by norm_num)) hdeltaA hab hepsilon hbeta

#print axioms
  convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspect_mul_proposition66AOuterFactor
#print axioms
  convexPlankFrostmanFactor_halfEpsilon_le_coupledThickAspect_mul_proposition66AOuterFactor_div_576

end

end Family8HonestEq45CoupledThickAspectComparisonV1
