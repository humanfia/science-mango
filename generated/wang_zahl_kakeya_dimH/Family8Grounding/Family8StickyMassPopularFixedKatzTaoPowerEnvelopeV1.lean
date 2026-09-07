import Family8Grounding.Family8StickyMassPopularFixedKatzTaoCoefficientV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped ENNReal NNReal

namespace Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1

open Family8LongIntervalOrdinaryFiberCapNumericsV1

noncomputable section

/-!
# Pure power producers for the fixed-Katz--Tao first factor

After the exact local fibre-cap cancellation, both scalar budgets consume
the same relative-scale gain `eta - (2*p+a)`.  This module keeps the three
global costs as independent `delta`-power caps, so the parameter ladder can
instantiate them without changing the geometric construction.
-/

def massPopularDensityFixedConstant : ENNReal :=
  8 * ordinaryFiberNatCapFixedConstant * 93312 * 128

def massPopularBaseFixedConstant (eta p a : Real) : ENNReal :=
  16 * (3 / 64 : ENNReal) ^ (eta - (2 * p + a) - 2)

theorem fixedPowerCore_le_source
    {delta : NNReal} {lossBound XUpper q source K : ENNReal}
    {lossExp xExp absorbExp scaleExp gain etaF : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hloss : lossBound <= (delta : ENNReal) ^ (-lossExp))
    (hX : XUpper <= (delta : ENNReal) ^ (-xExp))
    (hK : K <= (delta : ENNReal) ^ (-absorbExp))
    (hq : q <= (delta : ENNReal) ^ scaleExp)
    (hgain : 0 <= gain)
    (hbudget : 2 * etaF + lossExp + xExp + absorbExp <=
      scaleExp * gain)
    (hsource : (delta : ENNReal) ^ (2 * etaF) <= source) :
    K * (lossBound * XUpper * q ^ gain) <= source := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : (delta : ENNReal) <= 1 := by exact_mod_cast hdeltaOne
  have hqPower : q ^ gain <=
      (delta : ENNReal) ^ (scaleExp * gain) := by
    calc
      q ^ gain <= ((delta : ENNReal) ^ scaleExp) ^ gain :=
        ENNReal.rpow_le_rpow hq hgain
      _ = (delta : ENNReal) ^ (scaleExp * gain) := by
        rw [ENNReal.rpow_mul]
  have hproduct :
      K * (lossBound * XUpper * q ^ gain) <=
        (delta : ENNReal) ^
          (-absorbExp + (-lossExp) + (-xExp) + scaleExp * gain) := by
    calc
      K * (lossBound * XUpper * q ^ gain) <=
          (delta : ENNReal) ^ (-absorbExp) *
            ((delta : ENNReal) ^ (-lossExp) *
              (delta : ENNReal) ^ (-xExp) *
                (delta : ENNReal) ^ (scaleExp * gain)) := by
        exact mul_le_mul' hK
          (mul_le_mul' (mul_le_mul' hloss hX) hqPower)
      _ = (delta : ENNReal) ^
          (-absorbExp + (-lossExp) + (-xExp) + scaleExp * gain) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop,
          ENNReal.rpow_add _ _ hd0 hdTop,
          ENNReal.rpow_add _ _ hd0 hdTop]
        ring
  have hpower :
      (delta : ENNReal) ^
          (-absorbExp + (-lossExp) + (-xExp) + scaleExp * gain) <=
        (delta : ENNReal) ^ (2 * etaF) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hdOne
    linarith
  exact hproduct.trans (hpower.trans hsource)

theorem densityEnvelope_of_powerCaps
    {delta : NNReal} {lossBound XUpper C q source : ENNReal}
    {eta p a etaF lossExp xExp absorbExp scaleExp : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    (hC : C <= q ^ (-p))
    (hloss : lossBound <= (delta : ENNReal) ^ (-lossExp))
    (hX : XUpper <= (delta : ENNReal) ^ (-xExp))
    (hconstant : massPopularDensityFixedConstant <=
      (delta : ENNReal) ^ (-absorbExp))
    (hq : q <= (delta : ENNReal) ^ scaleExp)
    (hgain : 0 <= eta - (2 * p + a))
    (hbudget : 2 * etaF + lossExp + xExp + absorbExp <=
      scaleExp * (eta - (2 * p + a)))
    (hsource : (delta : ENNReal) ^ (2 * etaF) <= source) :
    (lossBound *
        (8 * (XUpper * (ordinaryFiberNatCapFixedConstant * C)))) *
      ((q ^ (eta - (p + a)) * 93312) * 128) <= source := by
  have hCgain : C * q ^ (eta - (p + a)) <=
      q ^ (eta - (2 * p + a)) := by
    calc
      C * q ^ (eta - (p + a)) <=
          q ^ (-p) * q ^ (eta - (p + a)) :=
        mul_le_mul' hC le_rfl
      _ = q ^ (eta - (2 * p + a)) := by
        rw [<- ENNReal.rpow_add _ _ hq0 hqTop]
        congr 1
        ring
  have hcore := fixedPowerCore_le_source
    hdelta hdeltaOne hloss hX hconstant hq hgain hbudget hsource
  calc
    (lossBound *
        (8 * (XUpper * (ordinaryFiberNatCapFixedConstant * C)))) *
      ((q ^ (eta - (p + a)) * 93312) * 128) =
        massPopularDensityFixedConstant *
          (lossBound * XUpper *
            (C * q ^ (eta - (p + a)))) := by
      unfold massPopularDensityFixedConstant
      ring
    _ <= massPopularDensityFixedConstant *
          (lossBound * XUpper * q ^ (eta - (2 * p + a))) := by
      exact mul_le_mul' le_rfl
        (mul_le_mul' le_rfl hCgain)
    _ <= source := hcore

theorem baseEnvelope_of_powerCaps
    {delta : NNReal} {lossBound XUpper q source : ENNReal}
    {eta p a etaF lossExp xExp absorbExp scaleExp : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    (hloss : lossBound <= (delta : ENNReal) ^ (-lossExp))
    (hX : XUpper <= (delta : ENNReal) ^ (-xExp))
    (hconstant : massPopularBaseFixedConstant eta p a <=
      (delta : ENNReal) ^ (-absorbExp))
    (hq : q <= (delta : ENNReal) ^ scaleExp)
    (hgain : 0 <= eta - (2 * p + a))
    (hbudget : 2 * etaF + lossExp + xExp + absorbExp <=
      scaleExp * (eta - (2 * p + a)))
    (hsource : (delta : ENNReal) ^ (2 * etaF) <= source) :
    (lossBound * (8 * (XUpper * q ^ (2 : Nat)))) *
        ((3 / 64 : ENNReal) ^ (-(2 * p + a)) *
          q ^ (-(2 * p + a))) <=
      (((3 / 64 : ENNReal) ^ (-eta) * q ^ (-eta) *
        ((3 / 64 : ENNReal) ^ (2 : Nat) * q ^ (2 : Nat) / 2)) *
        source) := by
  let c : ENNReal := 3 / 64
  let gain : Real := eta - (2 * p + a)
  have hbaseConstant : massPopularBaseFixedConstant eta p a =
      16 * c ^ (eta - (2 * p + a) - 2) := by rfl
  have hc0 : c ≠ 0 := by norm_num [c]
  have hcTop : c ≠ ∞ := by
    dsimp only [c]
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hcPower :
      c ^ (-eta) * c ^ (2 : Nat) *
          c ^ (eta - (2 * p + a) - 2) =
        c ^ (-(2 * p + a)) := by
    rw [<- ENNReal.rpow_natCast]
    rw [<- ENNReal.rpow_add _ _ hc0 hcTop,
      <- ENNReal.rpow_add _ _ hc0 hcTop]
    congr 1
    ring
  have hqPower :
      q ^ (-eta) * q ^ (2 : Nat) * q ^ gain =
        q ^ (-(2 * p + a)) * q ^ (2 : Nat) := by
    rw [<- ENNReal.rpow_natCast]
    rw [<- ENNReal.rpow_add _ _ hq0 hqTop,
      <- ENNReal.rpow_add _ _ hq0 hqTop,
      <- ENNReal.rpow_add _ _ hq0 hqTop]
    dsimp only [gain]
    congr 1
    ring
  have hhalfSixteen (x : ENNReal) : (x / 2) * 16 = x * 8 := by
    calc
      (x / 2) * 16 = ((x / 2) * 2) * 8 := by ring
      _ = x * 8 := by
        rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  have hcore := fixedPowerCore_le_source
    hdelta hdeltaOne hloss hX hconstant hq hgain hbudget hsource
  have hcoreGain : massPopularBaseFixedConstant eta p a *
      (lossBound * XUpper * q ^ gain) <= source := by
    simpa only [gain] using hcore
  have hscaled := mul_le_mul' le_rfl hcoreGain
    (a := (((c ^ (-eta) * q ^ (-eta)) *
      (c ^ (2 : Nat) * q ^ (2 : Nat) / 2))))
  calc
    (lossBound * (8 * (XUpper * q ^ (2 : Nat)))) *
        (c ^ (-(2 * p + a)) * q ^ (-(2 * p + a))) =
      8 * lossBound * XUpper *
        ((c ^ (-eta) * c ^ (2 : Nat) *
            c ^ (eta - (2 * p + a) - 2)) *
          (q ^ (-eta) * q ^ (2 : Nat) * q ^ gain)) := by
      rw [hcPower, hqPower]
      ring
    _ = (((c ^ (-eta) * q ^ (-eta)) *
          (c ^ (2 : Nat) * q ^ (2 : Nat) / 2))) *
        (massPopularBaseFixedConstant eta p a *
          (lossBound * XUpper * q ^ gain)) := by
      rw [hbaseConstant]
      calc
        8 * lossBound * XUpper *
            ((c ^ (-eta) * c ^ (2 : Nat) *
                c ^ (eta - (2 * p + a) - 2)) *
              (q ^ (-eta) * q ^ (2 : Nat) * q ^ gain)) =
          (lossBound * XUpper * c ^ (-eta) *
              c ^ (eta - (2 * p + a) - 2) *
              q ^ (-eta) * q ^ gain) *
            ((c ^ (2 : Nat) * q ^ (2 : Nat)) * 8) := by ring
        _ = (lossBound * XUpper * c ^ (-eta) *
              c ^ (eta - (2 * p + a) - 2) *
              q ^ (-eta) * q ^ gain) *
            (((c ^ (2 : Nat) * q ^ (2 : Nat)) / 2) * 16) := by
          rw [hhalfSixteen]
        _ = (((c ^ (-eta) * q ^ (-eta)) *
              (c ^ (2 : Nat) * q ^ (2 : Nat) / 2))) *
            (16 * c ^ (eta - (2 * p + a) - 2) *
              (lossBound * XUpper * q ^ gain)) := by ring
    _ <= (((c ^ (-eta) * q ^ (-eta)) *
          (c ^ (2 : Nat) * q ^ (2 : Nat) / 2))) * source := hscaled
    _ = (((3 / 64 : ENNReal) ^ (-eta) * q ^ (-eta) *
        ((3 / 64 : ENNReal) ^ (2 : Nat) * q ^ (2 : Nat) / 2)) *
        source) := by
      dsimp only [c]

#print axioms fixedPowerCore_le_source
#print axioms densityEnvelope_of_powerCaps
#print axioms baseEnvelope_of_powerCaps

end
end Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
