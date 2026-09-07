import Family8Grounding.Family8ThinPlankFivePackingNatCapLowerV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
import Mathlib.Tactic

/-!
# Proxy-and-aspect lower reserve in the adaptive full-fibre cap

For a finite transformed Katz--Tao constant, the literal ceiling retains the
constant from below.  Together with the wide-grid lower bound, the actual
adaptive natural cap therefore contains `Cproxy * (b/a)^2`.
-/

open scoped ENNReal NNReal

namespace Family8AdaptiveFullFiberCapProxyAspectLowerV1

open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
open Family8ThinPlankFivePackingNatCapLowerV1
open Family8ThinPlankFiveParameterPackingV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- The finite ENNReal input to a natural ceiling is retained from below. -/
theorem le_natCeil_toReal (A : ENNReal) (hAfinite : A ≠ ∞) :
    A <= (Nat.ceil A.toReal : Nat) := by
  apply (ENNReal.toReal_le_toReal hAfinite ENNReal.coe_ne_top).mp
  simpa using (Nat.le_ceil A.toReal)

/-- The exact adaptive full-fibre cap retains both the proxy Katz--Tao
constant and the square of the same bucket aspect. -/
theorem proxy_mul_bucketAspect_sq_le_adaptiveThinCountFullFiberNatCap
    (Cproxy : ENNReal) (hCfinite : Cproxy ≠ ∞)
    (label : Fin 3 -> Int) :
    Cproxy *
        (((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) ^ (2 : Nat)) <=
      (adaptiveThinCountFullFiberNatCap Cproxy label : ENNReal) := by
  let a := bucketShortA label
  let b := bucketShortB label
  let scaled : ENNReal := 480000 * (128 * Cproxy)
  have hscaledFinite : scaled ≠ ∞ := by
    dsimp only [scaled]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) hCfinite)
  have hCscaled : Cproxy <= scaled := by
    dsimp only [scaled]
    calc
      Cproxy = 1 * Cproxy := by simp
      _ <= (480000 * 128 : ENNReal) * Cproxy := by gcongr; norm_num
      _ = 480000 * (128 * Cproxy) := by ring
  have hfactor : Cproxy <=
      ((Nat.ceil scaled.toReal + 1 : Nat) : ENNReal) := by
    calc
      Cproxy <= scaled := hCscaled
      _ <= (Nat.ceil scaled.toReal : Nat) :=
        le_natCeil_toReal scaled hscaledFinite
      _ <= ((Nat.ceil scaled.toReal + 1 : Nat) : ENNReal) := by
        norm_num
  have ha : 0 < a := bucketShortA_pos label
  have hpackScaled := aspect_sq_le_thinPlankFivePackingNatCap
    a ((3 : NNReal) * b) ha
  have haspectNonneg :
      0 <= (b : ENNReal) / (a : ENNReal) := bot_le
  have haspectScale :
      ((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat) <=
        ((((3 : NNReal) * b : NNReal) : ENNReal) /
          (a : ENNReal)) ^ (2 : Nat) := by
    apply pow_le_pow_left₀ haspectNonneg
    rw [ENNReal.coe_mul]
    calc
      (b : ENNReal) / (a : ENNReal) =
          1 * ((b : ENNReal) / (a : ENNReal)) := by simp
      _ <= 3 * ((b : ENNReal) / (a : ENNReal)) := by gcongr; norm_num
      _ = (3 * (b : ENNReal)) / (a : ENNReal) := by
        rw [mul_div_assoc]
  have hpack :
      ((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat) <=
        (thinPlankFivePackingNatCap
          (3 * selectedPlankFineCanonicalAspect label) : ENNReal) := by
    exact haspectScale.trans (by
      simpa only [a, b, selectedPlankFineCanonicalAspect, NNReal.coe_mul,
        NNReal.coe_ofNat, mul_div_assoc] using hpackScaled)
  unfold adaptiveThinCountFullFiberNatCap
  rw [Nat.cast_mul]
  exact mul_le_mul' (by simpa only [scaled] using hfactor)
    (by simpa only [a, b] using hpack)

#print axioms le_natCeil_toReal
#print axioms
  proxy_mul_bucketAspect_sq_le_adaptiveThinCountFullFiberNatCap

end
end Family8AdaptiveFullFiberCapProxyAspectLowerV1
