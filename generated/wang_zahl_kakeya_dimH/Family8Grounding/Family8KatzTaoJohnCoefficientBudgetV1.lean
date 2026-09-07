import Family8Grounding.Family8ZeroColorPolynomialJohnKatzTaoV1
import Family8Grounding.Family8KatzTaoSamplingMultiplicityV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8KatzTaoJohnCoefficientBudgetV1

open Family8ZeroColorPolynomialJohnKatzTaoV1
open Family8PolynomialJohnFrameBoxVolumeV2
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# Absorbing the polynomial John catalogue coefficient

The catalogue has polynomial size, but its simultaneous Chernoff cost is the
logarithm of that size.  The lemma below uses `Real.log_le_rpow_div` with an
arbitrary positive exponent.  Consequently the logarithm costs an arbitrary
small power of `delta`, not the degree of the catalogue polynomial.
-/

/-- Constant left after bounding `log(A delta^(-p))` by the
`tailEta / p` power of its argument. -/
def johnLogTailConstant (A p tailEta : Real) : Real :=
  max 1 (A ^ (tailEta / p) / (tailEta / p))

theorem one_le_johnLogTailConstant (A p tailEta : Real) :
    1 ≤ johnLogTailConstant A p tailEta :=
  le_max_left _ _

theorem johnLogTailConstant_nonneg (A p tailEta : Real) :
    0 ≤ johnLogTailConstant A p tailEta :=
  zero_le_one.trans (one_le_johnLogTailConstant A p tailEta)

/-- A polynomial upper bound for the argument of the logarithm gives an
arbitrarily small power upper bound for the actual John tail parameter. -/
theorem polynomialJohnTailParameter_le_constant_mul_rpow
    {delta : NNReal} {k : Nat} {A p tailEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hA : 0 ≤ A) (hp : 0 < p) (htailEta : 0 < tailEta)
    (hcost :
      polynomialJohnCatalogueUpperCost delta k + 1 ≤
        A * (delta : Real) ^ (-p)) :
    polynomialJohnTailParameter delta k ≤
      johnLogTailConstant A p tailEta *
        (delta : Real) ^ (-tailEta) := by
  let q : Real := tailEta / p
  have hq : 0 < q := div_pos htailEta hp
  have hdeltaReal : 0 < (delta : Real) := by exact_mod_cast hdelta
  have hdeltaRealOne : (delta : Real) ≤ 1 := by exact_mod_cast hdeltaOne
  have hcostNonneg : 0 ≤ polynomialJohnCatalogueUpperCost delta k + 1 := by
    unfold polynomialJohnCatalogueUpperCost
    positivity
  have hlog :
      Real.log (polynomialJohnCatalogueUpperCost delta k + 1) ≤
        (polynomialJohnCatalogueUpperCost delta k + 1) ^ q / q :=
    Real.log_le_rpow_div hcostNonneg hq
  have hpower :
      (polynomialJohnCatalogueUpperCost delta k + 1) ^ q ≤
        A ^ q * (delta : Real) ^ (-tailEta) := by
    calc
      (polynomialJohnCatalogueUpperCost delta k + 1) ^ q ≤
          (A * (delta : Real) ^ (-p)) ^ q :=
        Real.rpow_le_rpow hcostNonneg hcost hq.le
      _ = A ^ q * ((delta : Real) ^ (-p)) ^ q := by
        rw [Real.mul_rpow hA (Real.rpow_nonneg hdeltaReal.le _)]
      _ = A ^ q * (delta : Real) ^ ((-p) * q) := by
        rw [Real.rpow_mul hdeltaReal.le]
      _ = A ^ q * (delta : Real) ^ (-tailEta) := by
        congr 2
        dsimp only [q]
        field_simp [ne_of_gt hp]
  have hlogPower :
      Real.log (polynomialJohnCatalogueUpperCost delta k + 1) ≤
        (A ^ q / q) * (delta : Real) ^ (-tailEta) := by
    calc
      Real.log (polynomialJohnCatalogueUpperCost delta k + 1) ≤
          (polynomialJohnCatalogueUpperCost delta k + 1) ^ q / q := hlog
      _ ≤ (A ^ q * (delta : Real) ^ (-tailEta)) / q := by
        exact (div_le_div_iff_of_pos_right hq).2 hpower
      _ = (A ^ q / q) * (delta : Real) ^ (-tailEta) := by ring
  have hdeltaPowerOne :
      1 ≤ (delta : Real) ^ (-tailEta) := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdeltaReal hdeltaRealOne (by linarith)
  apply max_le
  · calc
      1 ≤ 1 * (delta : Real) ^ (-tailEta) := by simpa using hdeltaPowerOne
      _ ≤ johnLogTailConstant A p tailEta *
          (delta : Real) ^ (-tailEta) := by
        gcongr
        exact one_le_johnLogTailConstant A p tailEta
  · exact hlogPower.trans (by
      apply mul_le_mul_of_nonneg_right
      · exact le_max_right _ _
      · positivity)

/-- Explicit threshold for absorbing the finite logarithmic coefficient and
the fixed John volume enlargement. -/
def johnCoefficientThreshold
    (A p tailEta constantEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (ENNReal.ofReal (johnLogTailConstant A p tailEta) *
      johnCatalogueVolumeConstant) constantEta

theorem johnCoefficientThreshold_pos
    (A p tailEta constantEta : Real) :
    0 < johnCoefficientThreshold A p tailEta constantEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- The real logarithmic bound and one finite-constant threshold produce the
exact coefficient premise consumed by the sampled Katz--Tao application. -/
theorem polynomialJohn_coefficient_le_rpow
    {delta : NNReal} {k : Nat} {A p tailEta constantEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hA : 0 ≤ A) (hp : 0 < p) (htailEta : 0 < tailEta)
    (hconstantEta : 0 < constantEta)
    (hcost :
      polynomialJohnCatalogueUpperCost delta k + 1 ≤
        A * (delta : Real) ^ (-p))
    (hdeltaThreshold :
      delta ≤ johnCoefficientThreshold A p tailEta constantEta) :
    ENNReal.ofReal (polynomialJohnTailParameter delta k) *
        johnCatalogueVolumeConstant ≤
      (delta : ENNReal) ^ (-(tailEta + constantEta)) := by
  let K : ENNReal :=
    ENNReal.ofReal (johnLogTailConstant A p tailEta) *
      johnCatalogueVolumeConstant
  have hKtop : K ≠ ∞ := by
    dsimp only [K]
    apply ENNReal.mul_ne_top
    · simp
    · norm_num [johnCatalogueVolumeConstant]
  have hK : K ≤ (delta : ENNReal) ^ (-constantEta) := by
    exact finiteConstant_le_delta_negativePower hKtop hconstantEta hdelta
      (by simpa [johnCoefficientThreshold, K] using hdeltaThreshold)
  have htail := polynomialJohnTailParameter_le_constant_mul_rpow
    hdelta hdeltaOne hA hp htailEta hcost
  have htailNonneg : 0 ≤ polynomialJohnTailParameter delta k :=
    zero_le_one.trans (one_le_polynomialJohnTailParameter delta k)
  have htailENN :
      ENNReal.ofReal (polynomialJohnTailParameter delta k) ≤
        ENNReal.ofReal (johnLogTailConstant A p tailEta) *
          (delta : ENNReal) ^ (-tailEta) := by
    rw [show (delta : ENNReal) ^ (-tailEta) =
      ENNReal.ofReal ((delta : Real) ^ (-tailEta)) by
        simpa using (ENNReal.ofReal_rpow_of_pos
          (show 0 < (delta : Real) by exact_mod_cast hdelta))]
    rw [← ENNReal.ofReal_mul
      (johnLogTailConstant_nonneg A p tailEta)]
    exact ENNReal.ofReal_le_ofReal htail
  calc
    ENNReal.ofReal (polynomialJohnTailParameter delta k) *
        johnCatalogueVolumeConstant ≤
      (ENNReal.ofReal (johnLogTailConstant A p tailEta) *
        (delta : ENNReal) ^ (-tailEta)) *
          johnCatalogueVolumeConstant := by gcongr
    _ = K * (delta : ENNReal) ^ (-tailEta) := by
      dsimp only [K]
      ac_rfl
    _ ≤ (delta : ENNReal) ^ (-constantEta) *
        (delta : ENNReal) ^ (-tailEta) := by gcongr
    _ = (delta : ENNReal) ^ (-(tailEta + constantEta)) := by
      rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hdelta.ne') (by simp)]
      congr 1
      ring

def johnCataloguePolynomialCostConstant : Real :=
  4 * ((((46082 : Real) ^ 15 + 1) *
    Real.exp (Real.exp 1 - 1))) + 1

theorem johnCataloguePolynomialCostConstant_pos :
    0 < johnCataloguePolynomialCostConstant := by
  unfold johnCataloguePolynomialCostConstant
  positivity

/-- The automatic sampling multiplicity and the degree-fifteen catalogue give
one honest polynomial upper bound for the logarithm argument. -/
theorem polynomialJohnCatalogueUpperCost_add_one_le
    {delta : NNReal} {k : Nat} {sourceEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceEta : 0 ≤ sourceEta)
    (hk :
      (k : Real) ≤ 2 * (delta : Real) ^ (-sourceEta)) :
    polynomialJohnCatalogueUpperCost delta k + 1 ≤
      johnCataloguePolynomialCostConstant *
        (delta : Real) ^ (-(15 + sourceEta)) := by
  have hd : 0 < (delta : Real) := by exact_mod_cast hdelta
  have hdOne : (delta : Real) ≤ 1 := by exact_mod_cast hdeltaOne
  have hdNegFifteen : 1 ≤ (delta : Real) ^ (-15 : Real) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hdOne (by norm_num)
  have hdNegSource : 0 ≤ (delta : Real) ^ (-sourceEta) :=
    Real.rpow_nonneg hd.le _
  have hcatalogue :
      ((46082 : Real) / (delta : Real)) ^ 15 + 1 ≤
        ((46082 : Real) ^ 15 + 1) *
          (delta : Real) ^ (-15 : Real) := by
    have hdiv :
        ((46082 : Real) / (delta : Real)) ^ 15 =
          (46082 : Real) ^ 15 * (delta : Real) ^ (-15 : Real) := by
      rw [Real.rpow_neg hd.le, div_pow, div_eq_mul_inv]
      exact congrArg (fun x : Real => (46082 : Real) ^ 15 * x)
        (congrArg (fun x : Real => x⁻¹)
          (Real.rpow_natCast (delta : Real) 15).symm)
    rw [hdiv]
    calc
      (46082 : Real) ^ 15 * (delta : Real) ^ (-15 : Real) + 1 ≤
          (46082 : Real) ^ 15 * (delta : Real) ^ (-15 : Real) +
            1 * (delta : Real) ^ (-15 : Real) := by
        simpa [add_comm] using
          (add_le_add_right (by simpa using hdNegFifteen)
            ((46082 : Real) ^ 15 * (delta : Real) ^ (-15 : Real)))
      _ = ((46082 : Real) ^ 15 + 1) *
          (delta : Real) ^ (-15 : Real) := by ring
  have hcombined :
      (delta : Real) ^ (-sourceEta) *
          (delta : Real) ^ (-15 : Real) =
        (delta : Real) ^ (-(15 + sourceEta)) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hdCombinedOne :
      1 ≤ (delta : Real) ^ (-(15 + sourceEta)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hdOne (by linarith)
  unfold polynomialJohnCatalogueUpperCost
  calc
    (2 * (k : Real)) *
          ((((46082 : Real) / (delta : Real)) ^ 15 + 1) *
            Real.exp (Real.exp 1 - 1)) + 1 ≤
        (2 * (2 * (delta : Real) ^ (-sourceEta))) *
          ((((46082 : Real) ^ 15 + 1) *
              (delta : Real) ^ (-15 : Real)) *
            Real.exp (Real.exp 1 - 1)) + 1 := by
      gcongr
    _ = (4 * (((46082 : Real) ^ 15 + 1) *
          Real.exp (Real.exp 1 - 1))) *
        ((delta : Real) ^ (-sourceEta) *
          (delta : Real) ^ (-15 : Real)) + 1 := by ring
    _ = (4 * (((46082 : Real) ^ 15 + 1) *
          Real.exp (Real.exp 1 - 1))) *
        (delta : Real) ^ (-(15 + sourceEta)) + 1 := by rw [hcombined]
    _ ≤ (4 * (((46082 : Real) ^ 15 + 1) *
          Real.exp (Real.exp 1 - 1))) *
        (delta : Real) ^ (-(15 + sourceEta)) +
          1 * (delta : Real) ^ (-(15 + sourceEta)) := by
      gcongr
      simpa using hdCombinedOne
    _ = johnCataloguePolynomialCostConstant *
        (delta : Real) ^ (-(15 + sourceEta)) := by
      unfold johnCataloguePolynomialCostConstant
      ring

/-- Specialize the polynomial cost bound to
`k = ceil(C.toReal)` and an ENNReal concentration power bound. -/
theorem automaticPolynomialJohnCatalogueUpperCost_add_one_le
    {delta : NNReal} {C : ENNReal} {sourceEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceEta : 0 ≤ sourceEta)
    (hCfinite : C ≠ ∞) (hCone : 1 ≤ C)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta)) :
    polynomialJohnCatalogueUpperCost delta
        (Family8KatzTaoSamplingMultiplicityV1.katzTaoSamplingMultiplicity C) + 1 ≤
      johnCataloguePolynomialCostConstant *
        (delta : Real) ^ (-(15 + sourceEta)) := by
  have hrpowTop : (delta : ENNReal) ^ (-sourceEta) ≠ ∞ := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-sourceEta)]
    exact ENNReal.coe_ne_top
  have hCReal : C.toReal ≤ (delta : Real) ^ (-sourceEta) := by
    have hto := (ENNReal.toReal_le_toReal hCfinite hrpowTop).2 hC
    rw [← ENNReal.toReal_rpow] at hto
    simpa using hto
  have hk :
      (Family8KatzTaoSamplingMultiplicityV1.katzTaoSamplingMultiplicity C : Real) ≤
        2 * (delta : Real) ^ (-sourceEta) := by
    exact
      (Family8KatzTaoSamplingMultiplicityV1.katzTaoSamplingMultiplicity_cast_le_two_mul_toReal
        hCone hCfinite).trans (mul_le_mul_of_nonneg_left hCReal (by norm_num))
  exact polynomialJohnCatalogueUpperCost_add_one_le hdelta hdeltaOne
    hsourceEta hk

/-- Fully automatic John coefficient bound for the ceiling sampling
multiplicity.  The two positive exponents separately pay the logarithmic
power and the remaining finite constant. -/
theorem automaticPolynomialJohn_coefficient_le_rpow
    {delta : NNReal} {C : ENNReal}
    {sourceEta tailEta constantEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceEta : 0 ≤ sourceEta)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (hCfinite : C ≠ ∞) (hCone : 1 ≤ C)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta))
    (hdeltaThreshold :
      delta ≤ johnCoefficientThreshold johnCataloguePolynomialCostConstant
        (15 + sourceEta) tailEta constantEta) :
    ENNReal.ofReal (polynomialJohnTailParameter delta
        (Family8KatzTaoSamplingMultiplicityV1.katzTaoSamplingMultiplicity C)) *
        johnCatalogueVolumeConstant ≤
      (delta : ENNReal) ^ (-(tailEta + constantEta)) := by
  apply polynomialJohn_coefficient_le_rpow
    (A := johnCataloguePolynomialCostConstant)
    (p := 15 + sourceEta) (tailEta := tailEta)
    (constantEta := constantEta) hdelta hdeltaOne
      johnCataloguePolynomialCostConstant_pos.le (by linarith)
      htailEta hconstantEta
  · exact automaticPolynomialJohnCatalogueUpperCost_add_one_le
      hdelta hdeltaOne hsourceEta hCfinite hCone hC
  · exact hdeltaThreshold

#print axioms polynomialJohnCatalogueUpperCost_add_one_le
#print axioms automaticPolynomialJohnCatalogueUpperCost_add_one_le
#print axioms automaticPolynomialJohn_coefficient_le_rpow

#print axioms polynomialJohnTailParameter_le_constant_mul_rpow
#print axioms polynomialJohn_coefficient_le_rpow

end
end Family8KatzTaoJohnCoefficientBudgetV1
