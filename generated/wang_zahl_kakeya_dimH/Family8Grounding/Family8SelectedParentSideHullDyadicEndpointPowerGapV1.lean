import Family8Grounding.Family8SelectedParentSideHullDyadicActualCountGateV1
import Family8Grounding.Family8SelectedParentSideHullEnvelopeExponentV1
import Mathlib.Tactic

/-!
# Endpoint power ledger for the selected-side dyadic count-one gate

This file expands the two terms in the last scalar premise of the
selected-side route.  It is intentionally a scalar file: no occurrence,
partition, or side label is selected here.

The exact expansion records a structural cost which is easy to miss.  Even
after using the high-density base
`delta ^ (-(etaKT / 8))`, the quotient of the side-hull residual by the
count-one Proposition 6.6(A) inner factor has a scale cost between one and
two powers of `delta` (before the favourable `epsilon` and density-bucket
gains).  Thus this route cannot be closed by declaring all remaining losses
to be an arbitrarily small negative power.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8SelectedParentSideHullDyadicEndpointPowerGapV1

open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentSideHullDyadicActualCountGateV1
open Family8SelectedParentSideHullEnvelopeExponentV1
open Family8SelectedParentSideHullReserveProducerV1

noncomputable section

/-- Exact count-one simplification of the Proposition 6.6(A) inner factor. -/
theorem proposition66AInnerFactor_countOne_eq
    {delta a b : NNReal} (hdelta : 0 < delta) (ha : 0 < a)
    (epsilon gamma : Real) :
    proposition66AInnerFactor delta a b 1 epsilon gamma =
      (delta : ENNReal) ^ (-epsilon / 2) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - gamma) *
          ((delta : ENNReal) / (a : ENNReal)) ^ (2 - 3 * gamma) := by
  let x : ENNReal := (delta : ENNReal) / (a : ENNReal)
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    exact ENNReal.div_ne_zero.mpr
      <| And.intro (ENNReal.coe_ne_zero.mpr hdelta.ne') ENNReal.coe_ne_top
  have hxTop : x ≠ ∞ := by
    dsimp only [x]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr ha.ne')
  have hsquare :
      ((x ^ (2 : Nat)) * (1 : ENNReal)) ^ (1 - gamma / 2) =
        x ^ (2 - gamma) := by
    rw [mul_one, <- ENNReal.rpow_natCast, <- ENNReal.rpow_mul]
    congr 1
    ring
  unfold proposition66AInnerFactor
  simp only [Nat.cast_one, mul_one]
  change
    (delta : ENNReal) ^ (-epsilon / 2) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - gamma) *
      x ^ (-2 * gamma) *
        (x ^ (2 : Nat)) ^ (1 - gamma / 2) = _
  rw [show (x ^ (2 : Nat)) ^ (1 - gamma / 2) = x ^ (2 - gamma) by
    simpa only [mul_one] using hsquare]
  calc
    (delta : ENNReal) ^ (-epsilon / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - gamma) *
        x ^ (-2 * gamma) * x ^ (2 - gamma) =
      (delta : ENNReal) ^ (-epsilon / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - gamma) *
        (x ^ (-2 * gamma) * x ^ (2 - gamma)) := by ac_rfl
    _ = (delta : ENNReal) ^ (-epsilon / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - gamma) *
        x ^ (2 - 3 * gamma) := by
      rw [<- ENNReal.rpow_add _ _ hx0 hxTop]
      congr 2
      ring

/-- The exact coefficient left after dividing the side-hull/density-base
residual by the count-one inner factor.  This is a definition, not an upper
envelope: the powers of both side lengths are still visible. -/
def sideHullDyadicCountOneExactCoefficient
    (delta a b : NNReal) (etaKT epsilon gamma : Real) : ENNReal :=
  (2 : ENNReal) ^ (gamma / 2) *
    (selectedParentSideHullEnvelopeConstant : ENNReal) ^ (gamma / 2) *
      (delta : ENNReal) ^
        (epsilon / 2 + 5 * gamma / 2 - 2 +
          etaKT * (1 - gamma) / 8) *
        (a : ENNReal) ^ (1 - 5 * gamma / 2) *
          (b : ENNReal) ^ (1 - gamma)

/-- Exact expansion of the selected-side count-one gate at
`base = delta^(-(etaKT/8))`.  In particular no power of the actual block
cardinality remains here. -/
theorem sideHullDyadic_countOne_residual_eq_exactCoefficient_mul_inner
    {delta a b : NNReal}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (etaKT epsilon gamma : Real) (hgamma0 : 0 ≤ gamma) :
    ((2 : ENNReal) ^ (gamma / 2) *
          (selectedParentSideHullEnvelope delta a) ^ (gamma / 2)) *
        (((delta : ENNReal) ^ (-(etaKT / 8))) ^ (gamma - 1)) =
      sideHullDyadicCountOneExactCoefficient
          delta a b etaKT epsilon gamma *
        proposition66AInnerFactor delta a b 1 epsilon gamma := by
  let D : ENNReal := delta
  let A : ENNReal := a
  let B : ENNReal := b
  let C : ENNReal := selectedParentSideHullEnvelopeConstant
  have hD0 : D ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hA0 : A ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr ha.ne'
  have hB0 : B ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hb.ne'
  have hDTop : D ≠ ∞ := ENNReal.coe_ne_top
  have hATop : A ≠ ∞ := ENNReal.coe_ne_top
  have hBTop : B ≠ ∞ := ENNReal.coe_ne_top
  have hmulRpow (x y : ENNReal) (hxTop : x ≠ ∞) (hyTop : y ≠ ∞)
      (p : Real) : (x * y) ^ p = x ^ p * y ^ p := by
    exact ENNReal.mul_rpow_of_ne_top hxTop hyTop p
  have hdivRpow (x y : ENNReal) (hxTop : x ≠ ∞)
      (hy0 : y ≠ 0) (p : Real) :
      (x / y) ^ p = x ^ p * y ^ (-p) := by
    rw [div_eq_mul_inv,
      ENNReal.mul_rpow_of_ne_top hxTop (ENNReal.inv_ne_top.mpr hy0),
      ENNReal.inv_rpow, <- ENNReal.rpow_neg]
  have hcombine2 (x : ENNReal) (hx0 : x ≠ 0) (hxTop : x ≠ ∞)
      (p q : Real) : x ^ p * x ^ q = x ^ (p + q) := by
    exact (ENNReal.rpow_add p q hx0 hxTop).symm
  have hcombine3 (x : ENNReal) (hx0 : x ≠ 0) (hxTop : x ≠ ∞)
      (p q r : Real) : x ^ p * x ^ q * x ^ r = x ^ (p + q + r) := by
    rw [hcombine2 x hx0 hxTop p q,
      hcombine2 x hx0 hxTop (p + q) r]
  have hEnvelope :
      (selectedParentSideHullEnvelope delta a) ^ (gamma / 2) =
        C ^ (gamma / 2) * (D * A) ^ (-(gamma / 2)) := by
    simpa only [C, D, A, ENNReal.coe_mul] using
      (selectedParentSideHullEnvelope_rpow_eq
        (rho := delta) (a := a) hdelta ha (beta := gamma) hgamma0)
  have hBase :
      (D ^ (-(etaKT / 8))) ^ (gamma - 1) =
        D ^ (etaKT * (1 - gamma) / 8) := by
    rw [<- ENNReal.rpow_mul]
    congr 1
    ring
  have hInner :
      proposition66AInnerFactor delta a b 1 epsilon gamma =
        D ^ (-epsilon / 2) *
          (A ^ (1 - gamma) * B ^ (-(1 - gamma))) *
            (D ^ (2 - 3 * gamma) * A ^ (-(2 - 3 * gamma))) := by
    rw [proposition66AInnerFactor_countOne_eq hdelta ha epsilon gamma]
    change
      D ^ (-epsilon / 2) * (A / B) ^ (1 - gamma) *
          (D / A) ^ (2 - 3 * gamma) = _
    rw [hdivRpow A B hATop hB0,
      hdivRpow D A hDTop hA0]
  have hLeft :
      ((2 : ENNReal) ^ (gamma / 2) *
            (selectedParentSideHullEnvelope delta a) ^ (gamma / 2)) *
          ((D ^ (-(etaKT / 8))) ^ (gamma - 1)) =
        (2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
          D ^ (-(gamma / 2) + etaKT * (1 - gamma) / 8) *
            A ^ (-(gamma / 2)) := by
    rw [hEnvelope, hBase, hmulRpow D A hDTop hATop]
    calc
      (2 : ENNReal) ^ (gamma / 2) *
            (C ^ (gamma / 2) *
              (D ^ (-(gamma / 2)) * A ^ (-(gamma / 2)))) *
          D ^ (etaKT * (1 - gamma) / 8) =
        (2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
          (D ^ (-(gamma / 2)) *
            D ^ (etaKT * (1 - gamma) / 8)) *
          A ^ (-(gamma / 2)) := by ac_rfl
      _ = (2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
          D ^ (-(gamma / 2) + etaKT * (1 - gamma) / 8) *
            A ^ (-(gamma / 2)) := by
        rw [hcombine2 D hD0 hDTop]
  rw [hLeft, hInner]
  unfold sideHullDyadicCountOneExactCoefficient
  change
    (2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
          D ^ (-(gamma / 2) + etaKT * (1 - gamma) / 8) *
        A ^ (-(gamma / 2)) =
      ((2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
              D ^ (epsilon / 2 + 5 * gamma / 2 - 2 +
                etaKT * (1 - gamma) / 8) *
            A ^ (1 - 5 * gamma / 2) * B ^ (1 - gamma)) *
        (D ^ (-epsilon / 2) *
          (A ^ (1 - gamma) * B ^ (-(1 - gamma))) *
            (D ^ (2 - 3 * gamma) * A ^ (-(2 - 3 * gamma))))
  have hDExponent :
      (epsilon / 2 + 5 * gamma / 2 - 2 +
          etaKT * (1 - gamma) / 8) + (-epsilon / 2) +
          (2 - 3 * gamma) =
        -(gamma / 2) + etaKT * (1 - gamma) / 8 := by ring
  have hAExponent :
      (1 - 5 * gamma / 2) + (1 - gamma) +
          (-(2 - 3 * gamma)) = -(gamma / 2) := by ring
  have hBExponent :
      (1 - gamma) + (-(1 - gamma)) = 0 := by ring
  calc
    (2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
          D ^ (-(gamma / 2) + etaKT * (1 - gamma) / 8) *
        A ^ (-(gamma / 2)) =
      (2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
        D ^ ((epsilon / 2 + 5 * gamma / 2 - 2 +
            etaKT * (1 - gamma) / 8) + (-epsilon / 2) +
              (2 - 3 * gamma)) *
        A ^ ((1 - 5 * gamma / 2) + (1 - gamma) +
              (-(2 - 3 * gamma))) *
        B ^ ((1 - gamma) + (-(1 - gamma))) := by
      rw [hDExponent, hAExponent, hBExponent, ENNReal.rpow_zero, mul_one]
    _ = ((2 : ENNReal) ^ (gamma / 2) * C ^ (gamma / 2) *
              D ^ (epsilon / 2 + 5 * gamma / 2 - 2 +
                etaKT * (1 - gamma) / 8) *
            A ^ (1 - 5 * gamma / 2) * B ^ (1 - gamma)) *
        (D ^ (-epsilon / 2) *
          (A ^ (1 - gamma) * B ^ (-(1 - gamma))) *
            (D ^ (2 - 3 * gamma) * A ^ (-(2 - 3 * gamma)))) := by
      rw [<- hcombine3 D hD0 hDTop,
        <- hcombine3 A hA0 hATop,
        <- hcombine2 B hB0 hBTop]
      ac_rfl

/-- Fixed coefficient in the low-`gamma` (`gamma <= 2/5`) side regime. -/
def sideHullDyadicCountOneLowFixedCoefficient (gamma : Real) : ENNReal :=
  (2 : ENNReal) ^ (gamma / 2) *
    (selectedParentSideHullEnvelopeConstant : ENNReal) ^ (gamma / 2)

/-- Fixed coefficient in the high-`gamma` (`2/5 <= gamma`) side regime.
The last factor is the literal selected-parent short-side floor loss. -/
def sideHullDyadicCountOneHighFixedCoefficient (gamma : Real) : ENNReal :=
  sideHullDyadicCountOneLowFixedCoefficient gamma *
    (11943936 : ENNReal) ^ (5 * gamma / 2 - 1)

/-- On the low-`gamma` side of the sign change, both residual side powers
are bounded by one.  This is the sharp scale exponent obtained from the
literal count-one expansion. -/
theorem sideHullDyadicCountOneExactCoefficient_le_lowGammaPower
    {delta a b : NNReal}
    (hab : a <= b) (hbOne : b <= 1)
    (etaKT epsilon gamma : Real)
    (hgammaLow : gamma <= 2 / 5) :
    sideHullDyadicCountOneExactCoefficient
        delta a b etaKT epsilon gamma <=
      sideHullDyadicCountOneLowFixedCoefficient gamma *
        (delta : ENNReal) ^
          (epsilon / 2 + 5 * gamma / 2 - 2 +
            etaKT * (1 - gamma) / 8) := by
  have haOne : a <= 1 := hab.trans hbOne
  have hApow : (a : ENNReal) ^ (1 - 5 * gamma / 2) <= 1 := by
    apply ENNReal.rpow_le_one
    · exact_mod_cast haOne
    · linarith
  have hBpow : (b : ENNReal) ^ (1 - gamma) <= 1 := by
    apply ENNReal.rpow_le_one
    · exact_mod_cast hbOne
    · linarith
  unfold sideHullDyadicCountOneExactCoefficient
  unfold sideHullDyadicCountOneLowFixedCoefficient
  calc
    (2 : ENNReal) ^ (gamma / 2) *
          (selectedParentSideHullEnvelopeConstant : ENNReal) ^ (gamma / 2) *
        (delta : ENNReal) ^
          (epsilon / 2 + 5 * gamma / 2 - 2 +
            etaKT * (1 - gamma) / 8) *
      (a : ENNReal) ^ (1 - 5 * gamma / 2) *
        (b : ENNReal) ^ (1 - gamma) <=
      (2 : ENNReal) ^ (gamma / 2) *
          (selectedParentSideHullEnvelopeConstant : ENNReal) ^ (gamma / 2) *
        (delta : ENNReal) ^
          (epsilon / 2 + 5 * gamma / 2 - 2 +
            etaKT * (1 - gamma) / 8) * 1 * 1 := by
      exact mul_le_mul' (mul_le_mul' le_rfl hApow) hBpow
    _ = ((2 : ENNReal) ^ (gamma / 2) *
          (selectedParentSideHullEnvelopeConstant : ENNReal) ^ (gamma / 2)) *
        (delta : ENNReal) ^
          (epsilon / 2 + 5 * gamma / 2 - 2 +
            etaKT * (1 - gamma) / 8) := by simp [mul_assoc]

/-- On the high-`gamma` side of the sign change, the negative power of the
short side costs exactly the floor factor `11943936^(5*gamma/2-1)` and one
full inverse power of `delta`. -/
theorem sideHullDyadicCountOneExactCoefficient_le_highGammaPower
    {delta a b : NNReal}
    (hdelta : 0 < delta)
    (haFloor : delta / 11943936 <= a)
    (hbOne : b <= 1)
    (etaKT epsilon gamma : Real) (hgammaHigh : 2 / 5 <= gamma)
    (hgammaOne : gamma <= 1) :
    sideHullDyadicCountOneExactCoefficient
        delta a b etaKT epsilon gamma <=
      sideHullDyadicCountOneHighFixedCoefficient gamma *
        (delta : ENNReal) ^
          (epsilon / 2 - 1 + etaKT * (1 - gamma) / 8) := by
  let D : ENNReal := delta
  let A : ENNReal := a
  let B : ENNReal := b
  let K : ENNReal := sideHullDyadicCountOneLowFixedCoefficient gamma
  let c : NNReal := 11943936
  let p : Real := 1 - 5 * gamma / 2
  let q : Real := 1 - gamma
  let e : Real := epsilon / 2 + 5 * gamma / 2 - 2 +
    etaKT * (1 - gamma) / 8
  have hc : 0 < c := by norm_num [c]
  have hfloorPos : 0 < delta / c := div_pos hdelta hc
  have ha : 0 < a := hfloorPos.trans_le (by simpa only [c] using haFloor)
  have hp : p <= 0 := by dsimp only [p]; linarith
  have hq : 0 <= q := by dsimp only [q]; linarith
  have hApowNN : a ^ p <= (delta / c) ^ p :=
    NNReal.rpow_le_rpow_of_nonpos hfloorPos
      (by simpa only [c] using haFloor) hp
  have hApow : A ^ p <= (((delta / c : NNReal) : ENNReal)) ^ p := by
    dsimp only [A]
    rw [<- ENNReal.coe_rpow_of_ne_zero ha.ne' p,
      <- ENNReal.coe_rpow_of_ne_zero hfloorPos.ne' p]
    exact ENNReal.coe_le_coe.mpr hApowNN
  have hBpow : B ^ q <= 1 := by
    apply ENNReal.rpow_le_one
    · dsimp only [B]
      exact ENNReal.coe_le_coe.mpr hbOne
    · exact hq
  have hD0 : D ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hDTop : D ≠ ∞ := ENNReal.coe_ne_top
  have hc0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc.ne'
  have hDdivC :
      (((delta / c : NNReal) : ENNReal)) ^ p =
        D ^ p * (c : ENNReal) ^ (-p) := by
    rw [ENNReal.coe_div hc.ne', div_eq_mul_inv,
      ENNReal.mul_rpow_of_ne_top hDTop (ENNReal.inv_ne_top.mpr hc0),
      ENNReal.inv_rpow, <- ENNReal.rpow_neg]
  have hcombine : D ^ e * D ^ p = D ^ (e + p) := by
    exact (ENNReal.rpow_add e p hD0 hDTop).symm
  have hexponent : e + p =
      epsilon / 2 - 1 + etaKT * (1 - gamma) / 8 := by
    dsimp only [e, p]
    ring
  have hminusP : -p = 5 * gamma / 2 - 1 := by
    dsimp only [p]
    ring
  unfold sideHullDyadicCountOneExactCoefficient
  change K * D ^ e * A ^ p * B ^ q <= _
  calc
    K * D ^ e * A ^ p * B ^ q <=
        K * D ^ e * (((delta / c : NNReal) : ENNReal) ^ p) * 1 := by
      exact mul_le_mul' (mul_le_mul' le_rfl hApow) hBpow
    _ = K * (c : ENNReal) ^ (-p) * D ^ (e + p) := by
      rw [hDdivC]
      calc
        K * D ^ e * (D ^ p * (c : ENNReal) ^ (-p)) * 1 =
            K * (D ^ e * D ^ p) * (c : ENNReal) ^ (-p) := by ac_rfl
        _ = K * D ^ (e + p) * (c : ENNReal) ^ (-p) := by rw [hcombine]
        _ = K * (c : ENNReal) ^ (-p) * D ^ (e + p) := by ac_rfl
    _ = sideHullDyadicCountOneHighFixedCoefficient gamma *
        D ^ (epsilon / 2 - 1 + etaKT * (1 - gamma) / 8) := by
      rw [hexponent, hminusP]
      rfl

/-- The endpoint share inequality pays exactly this part of the dyadic-base
gain.  The factor `1-gamma` is essential: at `gamma = 1` the density base
supplies no gain at all. -/
theorem two_outputEta_mul_one_sub_gamma_le_densityBaseGain
    {etaKT outputEta gamma : Real}
    (houtputShare : 16 * outputEta <= etaKT)
    (hgammaOne : gamma <= 1) :
    2 * outputEta * (1 - gamma) <=
      etaKT * (1 - gamma) / 8 := by
  have hnonneg : 0 <= 1 - gamma := by linarith
  have hmul := mul_le_mul_of_nonneg_right houtputShare hnonneg
  nlinarith

/-- Thin conversion of the expanded coefficient payment into the literal
count-one gate used by the selected-side route.  The premise is not the
desired gate in disguise: it contains neither the side-hull envelope nor a
Proposition 6.6(A) factor. -/
theorem sideHullDyadic_countOne_jointScale_of_exactCoefficient
    {delta a b : NNReal} {bucketKey : Nat}
    {johnLoss sourceDensity geometryLoss : ENNReal}
    {etaKT epsilon gamma : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hgamma0 : 0 <= gamma) (hgammaOne : gamma <= 1)
    (hcoefficient :
      johnLoss * sideHullDyadicCountOneExactCoefficient
        delta a b etaKT epsilon gamma <= sourceDensity * geometryLoss) :
    johnLoss *
        (((2 : ENNReal) ^ (gamma / 2) *
            (selectedParentSideHullEnvelope delta a) ^ (gamma / 2)) *
          ((2 : ENNReal) ^ bucketKey *
            (delta : ENNReal) ^ (-(etaKT / 8))) ^ (gamma - 1)) <=
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor delta a b 1 epsilon gamma := by
  let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
  let d0 : ENNReal := (2 : ENNReal) ^ bucketKey * A
  have hA_le_d0 : A <= d0 := by
    dsimp only [d0]
    calc
      A = 1 * A := by simp
      _ <= (2 : ENNReal) ^ bucketKey * A :=
        mul_le_mul' (one_le_pow₀ (by norm_num)) le_rfl
  have hq : 0 <= 1 - gamma := by linarith
  have hpositivePower : A ^ (1 - gamma) <= d0 ^ (1 - gamma) :=
    ENNReal.rpow_le_rpow hA_le_d0 hq
  have hnegativePower : d0 ^ (gamma - 1) <= A ^ (gamma - 1) := by
    have hinv := ENNReal.inv_le_inv' hpositivePower
    simpa only [show gamma - 1 = -(1 - gamma) by ring,
      ENNReal.rpow_neg] using hinv
  have hexact :=
    sideHullDyadic_countOne_residual_eq_exactCoefficient_mul_inner
      hdelta ha hb etaKT epsilon gamma hgamma0
  calc
    johnLoss *
        (((2 : ENNReal) ^ (gamma / 2) *
            (selectedParentSideHullEnvelope delta a) ^ (gamma / 2)) *
          ((2 : ENNReal) ^ bucketKey *
            (delta : ENNReal) ^ (-(etaKT / 8))) ^ (gamma - 1)) <=
      johnLoss *
        (((2 : ENNReal) ^ (gamma / 2) *
            (selectedParentSideHullEnvelope delta a) ^ (gamma / 2)) *
          ((delta : ENNReal) ^ (-(etaKT / 8))) ^ (gamma - 1)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (by
        simpa only [A, d0] using hnegativePower))
    _ = (johnLoss * sideHullDyadicCountOneExactCoefficient
          delta a b etaKT epsilon gamma) *
        proposition66AInnerFactor delta a b 1 epsilon gamma := by
      rw [hexact]
      ac_rfl
    _ <= (sourceDensity * geometryLoss) *
        proposition66AInnerFactor delta a b 1 epsilon gamma :=
      mul_le_mul' hcoefficient le_rfl

/-- The same thin coefficient payment produces the actual-count
`hjointScale`; the count is inserted only by the exact count factorization
already proved in `Family8SelectedParentSideHullDyadicActualCountGateV1`. -/
theorem sideHullDyadic_actualCount_jointScale_of_exactCoefficient
    {delta a b : NNReal} {bucketKey m : Nat}
    {johnLoss sourceDensity geometryLoss : ENNReal}
    {etaKT epsilon gamma : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hgamma0 : 0 <= gamma) (hgammaOne : gamma <= 1)
    (hcoefficient :
      johnLoss * sideHullDyadicCountOneExactCoefficient
        delta a b etaKT epsilon gamma <= sourceDensity * geometryLoss) :
    johnLoss *
        ((((2 : ENNReal) ^ (gamma / 2) *
              (selectedParentSideHullEnvelope delta a) ^ (gamma / 2)) *
            ((2 : ENNReal) ^ bucketKey *
              (delta : ENNReal) ^ (-(etaKT / 8))) ^ (gamma - 1)) *
          (m : ENNReal) ^ (1 - gamma / 2)) <=
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor delta a b m epsilon gamma := by
  apply jointScale_actualCount_of_countOne hgammaOne
  exact sideHullDyadic_countOne_jointScale_of_exactCoefficient
    hdelta ha hb hgamma0 hgammaOne hcoefficient

#print axioms proposition66AInnerFactor_countOne_eq
#print axioms
  sideHullDyadic_countOne_residual_eq_exactCoefficient_mul_inner
#print axioms sideHullDyadicCountOneExactCoefficient_le_lowGammaPower
#print axioms sideHullDyadicCountOneExactCoefficient_le_highGammaPower
#print axioms two_outputEta_mul_one_sub_gamma_le_densityBaseGain
#print axioms sideHullDyadic_countOne_jointScale_of_exactCoefficient
#print axioms sideHullDyadic_actualCount_jointScale_of_exactCoefficient

end
end Family8SelectedParentSideHullDyadicEndpointPowerGapV1
