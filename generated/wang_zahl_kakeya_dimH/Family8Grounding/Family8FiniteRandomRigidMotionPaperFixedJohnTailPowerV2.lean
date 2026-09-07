import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPolynomialV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnTailPowerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxCardPowerV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4

noncomputable section

/-!
# Small-power bound for the fixed-John logarithmic tail

The fixed-John test catalogue has degree-fifteen cardinality.  Its Chernoff
tail is only the logarithm of that cardinality, so it costs an arbitrary
positive power of the normalized radius, not the full degree fifteen.  The
constant and every exponent are explicit below.
-/

/-- Uniform constant in the polynomial upper bound for the logarithm
argument. -/
def fixedJohnTailCostConstant : Real :=
  (46082 : Real) ^ 15 * Real.exp (Real.exp 1 - 1) + 1

theorem fixedJohnTailCostConstant_nonneg :
    0 ≤ fixedJohnTailCostConstant := by
  unfold fixedJohnTailCostConstant
  positivity

/-- Constant after spending `tailEta` of scale exponent on the logarithm. -/
def fixedJohnTailPowerConstant (tailEta : Real) : Real :=
  max 1
    (fixedJohnTailCostConstant ^ (tailEta / 15) / (tailEta / 15))

theorem one_le_fixedJohnTailPowerConstant (tailEta : Real) :
    1 ≤ fixedJohnTailPowerConstant tailEta :=
  le_max_left _ _

theorem fixedJohnTailPowerConstant_nonneg (tailEta : Real) :
    0 ≤ fixedJohnTailPowerConstant tailEta :=
  zero_le_one.trans (one_le_fixedJohnTailPowerConstant tailEta)

/-- The literal logarithm argument is bounded by a fixed constant times the
negative fifteenth power of the normalized radius. -/
theorem fixedJohnTailArgument_le_polynomial
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (Fintype.card (FixedJohnTest D hD) : Real) *
          Real.exp (Real.exp 1 - 1) + 1 ≤
      fixedJohnTailCostConstant *
        (((delta / 8 : NNReal) : Real) ^ (-15 : Real)) := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hrhoOne : rho ≤ 1 := by
    dsimp only [rho]
    exact_mod_cast
      ((div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8)).trans
          (hD.delta_le_half.trans (by norm_num : (2 : NNReal)⁻¹ ≤ 1)))
  have hrhoNegFifteen : 1 ≤ rho ^ (-15 : Real) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hrho hrhoOne (by norm_num)
  have hrhoHalf : delta / 8 ≤ (1 / 2 : NNReal) := by
    simpa only [one_div] using
      (div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8)).trans hD.delta_le_half
  have hcard :
      (Fintype.card (FixedJohnTest D hD) : Real) ≤
        (46082 / rho) ^ 15 := by
    simpa only [FixedJohnTest, Fintype.card_fin, rho] using
      card_catalogueIndex_real_le_div_pow
        (delta / 8) (admissibleNormalizedRadiusPos hD) hrhoHalf
  have hdiv :
      ((46082 : Real) / rho) ^ 15 =
        (46082 : Real) ^ 15 * rho ^ (-15 : Real) := by
    rw [Real.rpow_neg hrho.le, div_pow, div_eq_mul_inv]
    exact congrArg (fun x : Real => (46082 : Real) ^ 15 * x)
      (congrArg (fun x : Real => x⁻¹)
        (Real.rpow_natCast rho 15).symm)
  have hexp : 0 ≤ Real.exp (Real.exp 1 - 1) := (Real.exp_pos _).le
  calc
    (Fintype.card (FixedJohnTest D hD) : Real) *
          Real.exp (Real.exp 1 - 1) + 1 ≤
        ((46082 : Real) / rho) ^ 15 *
          Real.exp (Real.exp 1 - 1) + 1 := by
      gcongr
    _ = ((46082 : Real) ^ 15 *
          Real.exp (Real.exp 1 - 1)) * rho ^ (-15 : Real) + 1 := by
      rw [hdiv]
      ring
    _ ≤ ((46082 : Real) ^ 15 *
          Real.exp (Real.exp 1 - 1)) * rho ^ (-15 : Real) +
        1 * rho ^ (-15 : Real) := by
      gcongr
      simpa using hrhoNegFifteen
    _ = fixedJohnTailCostConstant * rho ^ (-15 : Real) := by
      unfold fixedJohnTailCostConstant
      ring

/-- The logarithmic simultaneous-tail parameter costs any prescribed
positive exponent `tailEta`. -/
theorem fixedJohnTailParameter_le_power
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {tailEta : Real} (htailEta : 0 < tailEta) :
    fixedJohnTailParameter D hD ≤
      fixedJohnTailPowerConstant tailEta *
        (((delta / 8 : NNReal) : Real) ^ (-tailEta)) := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let x : Real :=
    (Fintype.card (FixedJohnTest D hD) : Real) *
      Real.exp (Real.exp 1 - 1) + 1
  let q : Real := tailEta / 15
  have hq : 0 < q := div_pos htailEta (by norm_num)
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hrhoOne : rho ≤ 1 := by
    dsimp only [rho]
    exact_mod_cast
      ((div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8)).trans
          (hD.delta_le_half.trans (by norm_num : (2 : NNReal)⁻¹ ≤ 1)))
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hcost : x ≤ fixedJohnTailCostConstant * rho ^ (-15 : Real) := by
    simpa only [x, rho] using fixedJohnTailArgument_le_polynomial D hD
  have hlog : Real.log x ≤ x ^ q / q :=
    Real.log_le_rpow_div hx hq
  have hpower :
      x ^ q ≤ fixedJohnTailCostConstant ^ q * rho ^ (-tailEta) := by
    calc
      x ^ q ≤
          (fixedJohnTailCostConstant * rho ^ (-15 : Real)) ^ q :=
        Real.rpow_le_rpow hx hcost hq.le
      _ = fixedJohnTailCostConstant ^ q *
          (rho ^ (-15 : Real)) ^ q := by
        rw [Real.mul_rpow fixedJohnTailCostConstant_nonneg
          (Real.rpow_nonneg hrho.le _)]
      _ = fixedJohnTailCostConstant ^ q *
          rho ^ ((-15 : Real) * q) := by
        rw [Real.rpow_mul hrho.le]
      _ = fixedJohnTailCostConstant ^ q * rho ^ (-tailEta) := by
        congr 2
        dsimp only [q]
        ring
  have hlogPower :
      Real.log x ≤
        (fixedJohnTailCostConstant ^ q / q) * rho ^ (-tailEta) := by
    calc
      Real.log x ≤ x ^ q / q := hlog
      _ ≤ (fixedJohnTailCostConstant ^ q * rho ^ (-tailEta)) / q :=
        (div_le_div_iff_of_pos_right hq).2 hpower
      _ = (fixedJohnTailCostConstant ^ q / q) * rho ^ (-tailEta) := by ring
  have hrhoPowerOne : 1 ≤ rho ^ (-tailEta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hrho hrhoOne (neg_nonpos.mpr htailEta.le)
  unfold fixedJohnTailParameter
  apply max_le
  · calc
      1 ≤ 1 * rho ^ (-tailEta) := by simpa using hrhoPowerOne
      _ ≤ fixedJohnTailPowerConstant tailEta * rho ^ (-tailEta) := by
        gcongr
        exact one_le_fixedJohnTailPowerConstant tailEta
  · dsimp only [x] at hlogPower
    exact hlogPower.trans (by
      apply mul_le_mul_of_nonneg_right
      · simpa only [q, fixedJohnTailPowerConstant] using
          (le_max_right 1
            (fixedJohnTailCostConstant ^ (tailEta / 15) /
              (tailEta / 15)))
      · positivity)

#print axioms fixedJohnTailArgument_le_polynomial
#print axioms fixedJohnTailParameter_le_power

end
end Family8FiniteRandomRigidMotionPaperFixedJohnTailPowerV2
