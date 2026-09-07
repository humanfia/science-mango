import Family8Grounding.Family8SectionEightBetaGammaCardScaleBridgeV3
import Mathlib.Tactic

/-!
# Lossless beta-to-gamma transport for a one-scale Section-8 factor, V2

V1 is a failed draft and is not imported.  The exact normalization gap is a
nonnegative power of the same-object quantity `b^4 * (b^2 * n)`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open scoped ENNReal NNReal

namespace Family8SectionEightBetaGammaLosslessBridgeV2

open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8SectionEightBetaGammaCardScaleBridgeV3

noncomputable section

/-- The stronger same-object card-scale bound `b^4 (b^2 n) <= 1` absorbs
the entire beta-to-gamma normalization gap without a delta-power loss. -/
theorem sectionEight_to_one_beta_le_gamma_of_fourth_cardScale
    {b : NNReal} {n : Nat} {beta gamma : Real}
    (hb : 0 < b) (hn : 0 < n) (hbetaGamma : beta <= gamma)
    (hfourth :
      ((b : ENNReal) ^ (4 : Nat)) *
          (((b : ENNReal) ^ (2 : Nat)) * (n : ENNReal)) <= 1) :
    sectionEightScaleCountFrostmanFactor b 1 n beta <=
      sectionEightScaleCountFrostmanFactor b 1 n gamma := by
  let gapHalf : Real := (gamma - beta) / 2
  let X : ENNReal :=
    ((b : ENNReal) ^ (2 : Nat)) * (n : ENNReal)
  have hgapHalf : 0 <= gapHalf := by
    dsimp only [gapHalf]
    linarith
  have hpow :
      (((b : ENNReal) ^ (4 : Nat)) ^ gapHalf) =
        (b : ENNReal) ^ (2 * (gamma - beta)) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    dsimp only [gapHalf]
    ring
  have hfactorEq :
      ((b : ENNReal) ^ (2 * (gamma - beta))) * (X ^ gapHalf) =
        ((((b : ENNReal) ^ (4 : Nat)) * X) ^ gapHalf) := by
    calc
      ((b : ENNReal) ^ (2 * (gamma - beta))) * (X ^ gapHalf) =
          (((b : ENNReal) ^ (4 : Nat)) ^ gapHalf) * (X ^ gapHalf) := by
            rw [hpow]
      _ = ((((b : ENNReal) ^ (4 : Nat)) * X) ^ gapHalf) :=
        (ENNReal.mul_rpow_of_nonneg _ _ hgapHalf).symm
  have hfactor :
      ((b : ENNReal) ^ (2 * (gamma - beta))) * (X ^ gapHalf) <= 1 := by
    rw [hfactorEq, ← ENNReal.one_rpow gapHalf]
    exact ENNReal.rpow_le_rpow hfourth hgapHalf
  rw [sectionEight_to_one_beta_eq_gap_mul_gamma hb hn]
  exact mul_le_of_le_one_left' hfactor

#print axioms sectionEight_to_one_beta_le_gamma_of_fourth_cardScale

end
end Family8SectionEightBetaGammaLosslessBridgeV2
