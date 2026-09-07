import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV7
import Family8Grounding.Family8CanonicalLowerBufferedScaleV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV11

open Family8CanonicalLowerBufferedScaleV4
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV7

noncomputable section

/-!
# Canonical buffered-radius instance of the exact-degree power bound

The already-proved canonical lower buffered scale supplies the sharp ratio
`b / tau <= globalDelta^(-epsilon)`.  The two lemmas below perform only the
square/tube-floor algebra and then instantiate the V7 exact-degree bound.
-/

theorem canonicalLowerBufferedScale_squared_div_halfSq_le
    {globalDelta tau theta : NNReal} {epsilon : Real}
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (hthetaOne : theta <= 1) (hepsilon : 0 <= epsilon) :
    ((canonicalLowerBufferedScale tau theta epsilon : NNReal) : ENNReal) ^ 2 /
          ((tau : ENNReal) ^ 2 / 2) <=
      2 * (globalDelta : ENNReal) ^ (-2 * epsilon) := by
  let b : NNReal := canonicalLowerBufferedScale tau theta epsilon
  have htau : 0 < tau := hglobal.trans_le hglobalTau
  have hratio : b / tau <= globalDelta ^ (-epsilon) := by
    simpa only [b] using
      canonicalLowerBufferedScale_div_tau_le_delta_rpow_neg
        hglobal hglobalTau hthetaOne hepsilon
  have hratioSq : (b / tau) ^ 2 <=
      (globalDelta ^ (-epsilon)) ^ 2 := by
    gcongr
  have hnormalize :
      b ^ 2 / (tau ^ 2 / 2) = 2 * (b / tau) ^ 2 := by
    rw [div_pow]
    field_simp [htau.ne']
  have hglobalPower :
      (globalDelta ^ (-epsilon)) ^ 2 =
        globalDelta ^ (-2 * epsilon) := by
    rw [← NNReal.rpow_natCast (globalDelta ^ (-epsilon)) 2]
    rw [← NNReal.rpow_mul]
    congr 1
    norm_num
    ring
  have hnn : b ^ 2 / (tau ^ 2 / 2) <=
      2 * globalDelta ^ (-2 * epsilon) := by
    rw [hnormalize, ← hglobalPower]
    gcongr
  have hden : tau ^ 2 / 2 ≠ 0 := by positivity
  have hcast :
      ((b ^ 2 / (tau ^ 2 / 2) : NNReal) : ENNReal) <=
        ((2 * globalDelta ^ (-2 * epsilon) : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr hnn
  simpa only [b, ENNReal.coe_div hden,
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_pow, ENNReal.coe_mul, ENNReal.coe_ofNat,
    ENNReal.coe_rpow_of_ne_zero hglobal.ne'] using hcast

/-- Fully canonical long-interval numerical degree cap.  No radius or
ceiling estimate remains as a premise. -/
theorem canonicalLowerBufferedScale_exactConflictDegree_le_power
    {globalDelta tau theta : NNReal} {A : ENNReal}
    {epsilon eta : Real}
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (hthetaOne : theta <= 1) (hepsilon : 0 <= epsilon)
    (hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio tau
        (canonicalLowerBufferedScale tau theta epsilon) A)
    (hratioFinite :
      activeOwnerKatzTaoIncidenceRatio tau
        (canonicalLowerBufferedScale tau theta epsilon) A ≠ ∞)
    (hA : A <= (globalDelta : ENNReal) ^ (-eta)) :
    ((1 +
        katzTaoDoubledFiberNatCap tau
            (canonicalLowerBufferedScale tau theta epsilon) A *
          katzTaoDoubledParentsNatCap tau
            (canonicalLowerBufferedScale tau theta epsilon) A : Nat) :
        ENNReal) <=
      8 *
        (480000 *
          (globalDelta : ENNReal) ^ (-(eta + 2 * epsilon))) ^ 2 := by
  apply exactConflictDegree_coe_le_longIntervalPower
    hglobal hratioOne hratioFinite hA
  exact canonicalLowerBufferedScale_squared_div_halfSq_le
    hglobal hglobalTau hthetaOne hepsilon

#print axioms canonicalLowerBufferedScale_squared_div_halfSq_le
#print axioms canonicalLowerBufferedScale_exactConflictDegree_le_power

end
end Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV11
