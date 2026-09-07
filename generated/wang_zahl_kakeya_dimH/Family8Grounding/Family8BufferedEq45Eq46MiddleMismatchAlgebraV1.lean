import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Exact mismatch scalar for buffered Equation (45) and Equation (46)

The buffered max-witness outer family is isotropic at width `w`, while the
actual Equation (46) fibre uses the selected sides `a,b`.  This module
isolates the exact coefficient left after multiplying the two factors and
normalizing by the Section 8 scale-count factor.  It introduces no
multiplicity assertion or numerical callback.
-/

open scoped ENNReal NNReal

namespace Family8BufferedEq45Eq46MiddleMismatchAlgebraV1

open Family8Prop66AOuterInnerProductAlgebraV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-- Equation (45) after removing only the genuine thickening power. -/
def bufferedIsotropicEq45Remainder
    (w : NNReal) (plankCount : Nat) (CF : ENNReal)
    (lemmaEpsilon beta : Real) : ENNReal :=
  (w : ENNReal) ^ (-lemmaEpsilon) *
    CF ^ (1 - beta / 2) *
    (w : ENNReal) ^ (-2 * beta) *
    (((w : ENNReal) ^ (2 : Nat)) *
      (plankCount : ENNReal)) ^ (1 - beta / 2)

/-- The exact scalar mismatch between the isotropic buffered outer datum and
the actual selected `(a,b)` inner datum. -/
def bufferedEq45Eq46MiddleMismatch
    (rho w a b : NNReal) (CF : ENNReal)
    (lemmaEpsilon epsilon beta : Real) : ENNReal :=
  (w : ENNReal) ^ (-lemmaEpsilon) *
    (rho : ENNReal) ^ (-epsilon / 2) *
    CF ^ (1 - beta / 2) *
    ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta) *
    ((w : ENNReal) / (a : ENNReal)) ^ (2 - 3 * beta)

theorem bufferedIsotropicEq45Remainder_mul_inner_eq_mismatch_mul_sectionEight
    {rho w a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF : ENNReal} {lemmaEpsilon epsilon beta : Real}
    (hrho : 0 < rho) (hw : 0 < w) (ha : 0 < a)
    (hbetaTwo : beta <= 2) :
    bufferedIsotropicEq45Remainder w plankCount CF lemmaEpsilon beta *
        proposition66AInnerFactor rho a b tubesPerPlank epsilon beta =
      bufferedEq45Eq46MiddleMismatch rho w a b CF
          lemmaEpsilon epsilon beta *
        sectionEightScaleCountFrostmanFactor rho 1
          (plankCount * tubesPerPlank) beta := by
  let R : ENNReal := rho
  let W : ENNReal := w
  let A : ENNReal := a
  let B : ENNReal := b
  let N : ENNReal := plankCount
  let M : ENNReal := tubesPerPlank
  let p : Real := 1 - beta / 2
  let q : Real := 2 - 3 * beta
  have hp : 0 <= p := by dsimp only [p]; linarith
  have hR0 : R ≠ 0 := ENNReal.coe_ne_zero.mpr hrho.ne'
  have hW0 : W ≠ 0 := ENNReal.coe_ne_zero.mpr hw.ne'
  have hA0 : A ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  have hRTop : R ≠ ⊤ := ENNReal.coe_ne_top
  have hWTop : W ≠ ⊤ := ENNReal.coe_ne_top
  have hATop : A ≠ ⊤ := ENNReal.coe_ne_top
  have hsquareCount (z : ENNReal) (n : Nat) :
      ((z ^ (2 : Nat)) * (n : ENNReal)) ^ p =
        z ^ (2 * p) * (n : ENNReal) ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
      <- ENNReal.rpow_natCast, <- ENNReal.rpow_mul]
    norm_num
  have hscaleW : W ^ (-2 * beta) * W ^ (2 * p) = W ^ q := by
    rw [<- ENNReal.rpow_add (-2 * beta) (2 * p) hW0 hWTop]
    congr 1
    dsimp only [p, q]
    ring
  have hscaleRA : (R / A) ^ (-2 * beta) *
      (R / A) ^ (2 * p) = (R / A) ^ q := by
    have hRA0 : R / A ≠ 0 :=
      ENNReal.div_ne_zero.mpr (And.intro hR0 hATop)
    have hRATop : R / A ≠ ⊤ :=
      ENNReal.div_ne_top hRTop hA0
    rw [<- ENNReal.rpow_add (-2 * beta) (2 * p) hRA0 hRATop]
    congr 1
    dsimp only [p, q]
    ring
  have hscaleR : R ^ (-2 * beta) * R ^ (2 * p) = R ^ q := by
    rw [← ENNReal.rpow_add (-2 * beta) (2 * p) hR0 hRTop]
    congr 1
    dsimp only [p, q]
    ring
  have hratio : W ^ q * (R / A) ^ q =
      (W / A) ^ q * R ^ q := by
    calc
      W ^ q * (R / A) ^ q = (W * (R / A)) ^ q :=
        (ENNReal.mul_rpow_of_ne_top hWTop
          (ENNReal.div_ne_top hRTop hA0) q).symm
      _ = ((W / A) * R) ^ q := by
        congr 1
        simp only [div_eq_mul_inv]
        ac_rfl
      _ = (W / A) ^ q * R ^ q :=
        ENNReal.mul_rpow_of_ne_top
          (ENNReal.div_ne_top hWTop hA0) hRTop q
  have hleft :
      bufferedIsotropicEq45Remainder w plankCount CF lemmaEpsilon beta *
          proposition66AInnerFactor rho a b tubesPerPlank epsilon beta =
        (W ^ (-lemmaEpsilon) * R ^ (-epsilon / 2) * CF ^ p *
            (A / B) ^ (1 - beta)) *
          ((W / A) ^ q * R ^ q) * (N ^ p * M ^ p) := by
    unfold bufferedIsotropicEq45Remainder proposition66AInnerFactor
    change
      W ^ (-lemmaEpsilon) * CF ^ p * W ^ (-2 * beta) *
            ((W ^ (2 : Nat)) * N) ^ p *
          (R ^ (-epsilon / 2) * (A / B) ^ (1 - beta) *
            (R / A) ^ (-2 * beta) *
            (((R / A) ^ (2 : Nat)) * M) ^ p) = _
    rw [hsquareCount W plankCount,
      hsquareCount (R / A) tubesPerPlank]
    calc
      W ^ (-lemmaEpsilon) * CF ^ p * W ^ (-2 * beta) *
            (W ^ (2 * p) * N ^ p) *
          (R ^ (-epsilon / 2) * (A / B) ^ (1 - beta) *
            (R / A) ^ (-2 * beta) *
            ((R / A) ^ (2 * p) * M ^ p)) =
          (W ^ (-lemmaEpsilon) * R ^ (-epsilon / 2) * CF ^ p *
              (A / B) ^ (1 - beta)) *
            ((W ^ (-2 * beta) * W ^ (2 * p)) *
              ((R / A) ^ (-2 * beta) * (R / A) ^ (2 * p))) *
            (N ^ p * M ^ p) := by ac_rfl
      _ = (W ^ (-lemmaEpsilon) * R ^ (-epsilon / 2) * CF ^ p *
              (A / B) ^ (1 - beta)) *
            (W ^ q * (R / A) ^ q) * (N ^ p * M ^ p) := by
        rw [hscaleW, hscaleRA]
      _ = _ := by rw [hratio]
  rw [hleft]
  unfold bufferedEq45Eq46MiddleMismatch
    sectionEightScaleCountFrostmanFactor
  simp only [ENNReal.coe_one, div_one]
  change
    (W ^ (-lemmaEpsilon) * R ^ (-epsilon / 2) * CF ^ p *
        (A / B) ^ (1 - beta)) *
      ((W / A) ^ q * R ^ q) * (N ^ p * M ^ p) =
    (W ^ (-lemmaEpsilon) * R ^ (-epsilon / 2) * CF ^ p *
        (A / B) ^ (1 - beta) * (W / A) ^ q) *
      (R ^ (-2 * beta) *
        ((R ^ (2 : Nat)) *
          ((plankCount * tubesPerPlank : Nat) : ENNReal)) ^ p)
  rw [hsquareCount R (plankCount * tubesPerPlank)]
  rw [show ((plankCount * tubesPerPlank : Nat) : ENNReal) = N * M by
    norm_num [N, M], ENNReal.mul_rpow_of_nonneg N M hp]
  rw [← hscaleR]
  ac_rfl

#print axioms bufferedIsotropicEq45Remainder
#print axioms bufferedEq45Eq46MiddleMismatch
#print axioms
  bufferedIsotropicEq45Remainder_mul_inner_eq_mismatch_mul_sectionEight

end
end Family8BufferedEq45Eq46MiddleMismatchAlgebraV1
