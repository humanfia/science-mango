import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV11
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14

open Family8CanonicalLowerBufferedScaleV4
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV11
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Fixed-constant absorption for the exact active-owner degree

The V11 bound has the sole fixed coefficient `8 * 480000^2`.  Below an
explicit positive small-delta threshold this file absorbs that coefficient
into a reserved exponent `absorbEta`, leaving the exact envelope
`2 * eta + 4 * epsilon + absorbEta`.
-/

def activeOwnerExactDegreeFixedConstant : ENNReal :=
  8 * 480000 ^ 2

def activeOwnerExactDegreeSmallDeltaThreshold
    (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    activeOwnerExactDegreeFixedConstant absorbEta

def activeOwnerExactDegreePowerEnvelope
    (epsilon eta absorbEta : Real) : Real :=
  2 * eta + 4 * epsilon + absorbEta

theorem activeOwnerExactDegreeSmallDeltaThreshold_pos
    (absorbEta : Real) :
    0 < activeOwnerExactDegreeSmallDeltaThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem activeOwnerExactDegreeSmallDeltaThreshold_le_one
    {absorbEta : Real} (habsorbEta : 0 < absorbEta) :
    activeOwnerExactDegreeSmallDeltaThreshold absorbEta <= 1 :=
  finiteConstantSmallDeltaThreshold_le_one _ habsorbEta

theorem activeOwnerExactDegreeFixedConstant_ne_top :
    activeOwnerExactDegreeFixedConstant ≠ ∞ := by
  norm_num [activeOwnerExactDegreeFixedConstant]

theorem activeOwnerExactDegreeFixedConstant_le_negativePower
    {globalDelta : NNReal} {absorbEta : Real}
    (hglobal : 0 < globalDelta) (habsorbEta : 0 < absorbEta)
    (hglobalThreshold :
      globalDelta <=
        activeOwnerExactDegreeSmallDeltaThreshold absorbEta) :
    activeOwnerExactDegreeFixedConstant <=
      (globalDelta : ENNReal) ^ (-absorbEta) := by
  exact finiteConstant_le_delta_negativePower
    activeOwnerExactDegreeFixedConstant_ne_top habsorbEta hglobal
      hglobalThreshold

/-- Pure scalar absorption; no geometric hypothesis occurs here. -/
theorem exactDegreeScalar_le_absorbedPower
    {globalDelta : NNReal} {p absorbEta : Real}
    (hglobal : 0 < globalDelta) (habsorbEta : 0 < absorbEta)
    (hglobalThreshold :
      globalDelta <=
        activeOwnerExactDegreeSmallDeltaThreshold absorbEta) :
    8 *
        (480000 * (globalDelta : ENNReal) ^ (-p)) ^ 2 <=
      (globalDelta : ENNReal) ^ (-(2 * p + absorbEta)) := by
  let d : ENNReal := (globalDelta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hglobal.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hconstant : activeOwnerExactDegreeFixedConstant <=
      d ^ (-absorbEta) := by
    simpa only [d] using
      activeOwnerExactDegreeFixedConstant_le_negativePower
        hglobal habsorbEta hglobalThreshold
  have hsquare :
      (d ^ (-p)) ^ 2 = d ^ ((-p) * 2) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    8 * (480000 * d ^ (-p)) ^ 2 =
        activeOwnerExactDegreeFixedConstant * (d ^ (-p)) ^ 2 := by
      unfold activeOwnerExactDegreeFixedConstant
      ring
    _ = activeOwnerExactDegreeFixedConstant * d ^ ((-p) * 2) := by
      rw [hsquare]
    _ <= d ^ (-absorbEta) * d ^ ((-p) * 2) :=
      mul_le_mul' hconstant le_rfl
    _ = d ^ ((-absorbEta) + ((-p) * 2)) := by
      rw [ENNReal.rpow_add (-absorbEta) ((-p) * 2) hd0 hdTop]
    _ = d ^ (-(2 * p + absorbEta)) := by
      congr 1
      ring

/-- Canonical buffered-scale exact conflict degree, now bounded by one
explicit small power `delta^(-B)`. -/
theorem canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope
    {globalDelta tau theta : NNReal} {A : ENNReal}
    {epsilon eta absorbEta : Real}
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (hthetaOne : theta <= 1) (hepsilon : 0 <= epsilon)
    (habsorbEta : 0 < absorbEta)
    (hglobalThreshold :
      globalDelta <=
        activeOwnerExactDegreeSmallDeltaThreshold absorbEta)
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
      (globalDelta : ENNReal) ^
        (-activeOwnerExactDegreePowerEnvelope epsilon eta absorbEta) := by
  calc
    ((1 +
        katzTaoDoubledFiberNatCap tau
            (canonicalLowerBufferedScale tau theta epsilon) A *
          katzTaoDoubledParentsNatCap tau
            (canonicalLowerBufferedScale tau theta epsilon) A : Nat) :
        ENNReal) <=
        8 *
          (480000 *
            (globalDelta : ENNReal) ^ (-(eta + 2 * epsilon))) ^ 2 :=
      canonicalLowerBufferedScale_exactConflictDegree_le_power
        hglobal hglobalTau hthetaOne hepsilon hratioOne hratioFinite hA
    _ <= (globalDelta : ENNReal) ^
          (-(2 * (eta + 2 * epsilon) + absorbEta)) :=
      exactDegreeScalar_le_absorbedPower
        hglobal habsorbEta hglobalThreshold
    _ = (globalDelta : ENNReal) ^
          (-activeOwnerExactDegreePowerEnvelope epsilon eta absorbEta) := by
      congr 1
      unfold activeOwnerExactDegreePowerEnvelope
      ring

#print axioms activeOwnerExactDegreeFixedConstant_le_negativePower
#print axioms exactDegreeScalar_le_absorbedPower
#print axioms canonicalLowerBufferedScale_exactConflictDegree_le_powerEnvelope

end
end Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
