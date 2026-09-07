import Family8Grounding.Family8Prop66AFrostmanAspectGainAlgebraV1
import Mathlib.Tactic

/-!
# Proposition 6.6(A): outer/inner scalar multiplication

This file formalizes only the scalar simplification in Section 6.5 of the
Guth--Wang--Zahl paper.  The factors below are the right-hand sides of
Equations (45) and (46), without any assertion that a multiplicity is bounded
by them.  Under exact uniform counting, their product is exactly Equation
(32), including the aspect gain `(a / b)^(3 * beta / 2)`.
-/

open scoped ENNReal NNReal

namespace Family8Prop66AOuterInnerProductAlgebraV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Equation (45): the outer family of `a x b x 1` planks. -/
def proposition66AOuterFactor
    (delta a b : NNReal) (plankCount : Nat)
    (CF : ENNReal) (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon / 2) *
    CF ^ (1 - beta / 2) *
      ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta / 2) *
        (b : ENNReal) ^ (-2 * beta) *
          (((b : ENNReal) ^ (2 : Nat)) *
            (plankCount : ENNReal)) ^ (1 - beta / 2)

/-- Equation (46): the affine-rescaled tube fiber inside one plank. -/
def proposition66AInnerFactor
    (delta a b : NNReal) (tubesPerPlank : Nat)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon / 2) *
    ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta) *
      ((delta : ENNReal) / (a : ENNReal)) ^ (-2 * beta) *
        (((((delta : ENNReal) / (a : ENNReal)) ^ (2 : Nat))) *
          (tubesPerPlank : ENNReal)) ^ (1 - beta / 2)

/-- Equations (44), (45), and (46) have no residual scalar loss: multiplying
the outer and one uniform inner factor and using
`totalCount = plankCount * tubesPerPlank` gives exactly Equation (32).

No multiplicity estimate is an input or output of this theorem. -/
theorem proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
    {delta a b : NNReal} {plankCount tubesPerPlank totalCount : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (_hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hcount : totalCount = plankCount * tubesPerPlank) :
    proposition66AOuterFactor delta a b plankCount CF epsilon beta *
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta =
      proposition66AFrostmanFactor delta a b totalCount CF epsilon beta := by
  subst totalCount
  let d : ENNReal := (delta : ENNReal)
  let A : ENNReal := (a : ENNReal)
  let B : ENNReal := (b : ENNReal)
  let x : ENNReal := A / B
  let y : ENNReal := d / A
  let N : ENNReal := (plankCount : ENNReal)
  let M : ENNReal := (tubesPerPlank : ENNReal)
  let p : Real := 1 - beta / 2
  let r : Real := -2 * beta + 2 * p
  have hp : 0 ≤ p := by
    dsimp only [p]
    linarith
  have hd0 : d ≠ 0 := by
    dsimp only [d]
    exact ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hA0 : A ≠ 0 := by
    dsimp only [A]
    exact ENNReal.coe_ne_zero.mpr ha.ne'
  have hB0 : B ≠ 0 := by
    dsimp only [B]
    exact ENNReal.coe_ne_zero.mpr hb.ne'
  have hdTop : d ≠ ∞ := by simp [d]
  have hATop : A ≠ ∞ := by simp [A]
  have hBTop : B ≠ ∞ := by simp [B]
  have hx0 : x ≠ 0 := by
    dsimp only [x]
    exact ENNReal.div_ne_zero.mpr ⟨hA0, hBTop⟩
  have hxTop : x ≠ ∞ := by
    dsimp only [x]
    exact ENNReal.div_ne_top hATop hB0
  have hy0 : y ≠ 0 := by
    dsimp only [y]
    exact ENNReal.div_ne_zero.mpr ⟨hd0, hATop⟩
  have hyTop : y ≠ ∞ := by
    dsimp only [y]
    exact ENNReal.div_ne_top hdTop hA0
  have hrexp : (-2 * beta) + 2 * p = r := by
    rfl
  have hsquareCount (z : ENNReal) (n : Nat) :
      ((z ^ (2 : Nat)) * (n : ENNReal)) ^ p =
        z ^ (2 * p) * (n : ENNReal) ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have houter :
      proposition66AOuterFactor delta a b plankCount CF epsilon beta =
        d ^ (-epsilon / 2) * CF ^ p * x ^ p * B ^ r * N ^ p := by
    change
      d ^ (-epsilon / 2) * CF ^ p * x ^ p * B ^ (-2 * beta) *
          ((B ^ (2 : Nat)) * N) ^ p =
        d ^ (-epsilon / 2) * CF ^ p * x ^ p * B ^ r * N ^ p
    rw [hsquareCount B plankCount]
    calc
      d ^ (-epsilon / 2) * CF ^ p * x ^ p * B ^ (-2 * beta) *
          (B ^ (2 * p) * N ^ p) =
        d ^ (-epsilon / 2) * CF ^ p * x ^ p *
          (B ^ (-2 * beta) * B ^ (2 * p)) * N ^ p := by
        ac_rfl
      _ = d ^ (-epsilon / 2) * CF ^ p * x ^ p * B ^ r * N ^ p := by
        rw [← ENNReal.rpow_add (-2 * beta) (2 * p) hB0 hBTop, hrexp]
  have hinner :
      proposition66AInnerFactor delta a b tubesPerPlank epsilon beta =
        d ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ r * M ^ p := by
    change
      d ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ (-2 * beta) *
          ((y ^ (2 : Nat)) * M) ^ p =
        d ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ r * M ^ p
    rw [hsquareCount y tubesPerPlank]
    calc
      d ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ (-2 * beta) *
          (y ^ (2 * p) * M ^ p) =
        d ^ (-epsilon / 2) * x ^ (1 - beta) *
          (y ^ (-2 * beta) * y ^ (2 * p)) * M ^ p := by
        ac_rfl
      _ = d ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ r * M ^ p := by
        rw [← ENNReal.rpow_add (-2 * beta) (2 * p) hy0 hyTop, hrexp]
  have hepsilon :
      d ^ (-epsilon / 2) * d ^ (-epsilon / 2) = d ^ (-epsilon) := by
    rw [← ENNReal.rpow_add (-epsilon / 2) (-epsilon / 2) hd0 hdTop]
    congr 1
    ring
  have hbase : B * y = d / x := by
    dsimp only [x, y]
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hATop), inv_inv]
    ac_rfl
  have hdivRpow :
      (d / x) ^ r = d ^ r * x ^ (-r) := by
    rw [div_eq_mul_inv,
      ENNReal.mul_rpow_of_ne_top hdTop (ENNReal.inv_ne_top.mpr hx0),
      ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  have hscale : B ^ r * y ^ r = d ^ r * x ^ (-r) := by
    calc
      B ^ r * y ^ r = (B * y) ^ r :=
        (ENNReal.mul_rpow_of_ne_top hBTop hyTop r).symm
      _ = (d / x) ^ r := by rw [hbase]
      _ = d ^ r * x ^ (-r) := hdivRpow
  have hxcombine :
      (x ^ p * x ^ (1 - beta)) * x ^ (-r) =
        x ^ (3 * beta / 2) := by
    calc
      (x ^ p * x ^ (1 - beta)) * x ^ (-r) =
          x ^ (p + (1 - beta)) * x ^ (-r) := by
        rw [ENNReal.rpow_add p (1 - beta) hx0 hxTop]
      _ = x ^ ((p + (1 - beta)) + (-r)) := by
        rw [ENNReal.rpow_add (p + (1 - beta)) (-r) hx0 hxTop]
      _ = x ^ (3 * beta / 2) := by
        congr 1
        dsimp only [p, r]
        ring
  have hcounts : N ^ p * M ^ p = (N * M) ^ p :=
    (ENNReal.mul_rpow_of_nonneg N M hp).symm
  have hproduct :
      proposition66AOuterFactor delta a b plankCount CF epsilon beta *
          proposition66AInnerFactor delta a b tubesPerPlank epsilon beta =
        d ^ (-epsilon) * CF ^ p * x ^ (3 * beta / 2) *
          d ^ r * (N * M) ^ p := by
    rw [houter, hinner]
    calc
      (d ^ (-epsilon / 2) * CF ^ p * x ^ p * B ^ r * N ^ p) *
          (d ^ (-epsilon / 2) * x ^ (1 - beta) * y ^ r * M ^ p) =
        (d ^ (-epsilon / 2) * d ^ (-epsilon / 2)) * CF ^ p *
          ((x ^ p * x ^ (1 - beta)) * (B ^ r * y ^ r)) *
            (N ^ p * M ^ p) := by
        ac_rfl
      _ = d ^ (-epsilon) * CF ^ p *
          ((x ^ p * x ^ (1 - beta)) * (d ^ r * x ^ (-r))) *
            (N * M) ^ p := by
        rw [hepsilon, hscale, hcounts]
      _ = d ^ (-epsilon) * CF ^ p *
          ((x ^ p * x ^ (1 - beta)) * x ^ (-r)) *
            d ^ r * (N * M) ^ p := by
        ac_rfl
      _ = d ^ (-epsilon) * CF ^ p * x ^ (3 * beta / 2) *
          d ^ r * (N * M) ^ p := by
        rw [hxcombine]
  rw [hproduct]
  unfold proposition66AFrostmanFactor proposition66ACardScaleVolume
  rw [Nat.cast_mul]
  change
    d ^ (-epsilon) * CF ^ p * x ^ (3 * beta / 2) *
        d ^ r * (N * M) ^ p =
      d ^ (-epsilon) * CF ^ p * x ^ (3 * beta / 2) *
        d ^ (-2 * beta) * ((d ^ (2 : Nat)) * (N * M)) ^ p
  have hcardPower :
      ((d ^ (2 : Nat)) * (N * M)) ^ p =
        d ^ (2 * p) * (N * M) ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hcardPower]
  calc
    d ^ (-epsilon) * CF ^ p * x ^ (3 * beta / 2) *
        d ^ r * (N * M) ^ p =
      d ^ (-epsilon) * CF ^ p * x ^ (3 * beta / 2) *
        (d ^ (-2 * beta) * d ^ (2 * p)) * (N * M) ^ p := by
      rw [← ENNReal.rpow_add (-2 * beta) (2 * p) hd0 hdTop, hrexp]
    _ = d ^ (-epsilon) * CF ^ p * x ^ (3 * beta / 2) *
        d ^ (-2 * beta) * (d ^ (2 * p) * (N * M) ^ p) := by
      ac_rfl

#print axioms proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor

end

end Family8Prop66AOuterInnerProductAlgebraV1
