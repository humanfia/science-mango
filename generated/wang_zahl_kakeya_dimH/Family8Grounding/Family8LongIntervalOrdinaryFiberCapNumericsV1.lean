import Family8Grounding.Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
import Family8Grounding.Family8KatzTaoSamplingMultiplicityV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8LongIntervalOrdinaryFiberCapNumericsV1

open Family8CanonicalLowerBufferedScaleV4
open Family8KatzTaoSamplingMultiplicityV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV7
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV11
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV17
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Small-power envelope for one ordinary parent fibre

The exact natural cap is one ceiling of the Katz--Tao incidence ratio, not
the square of two caps used by the conflict graph degree.  Consequently its
scale exponent is `etaKT + 2 * epsilon`.  This file removes the ceiling and
absorbs the remaining finite coefficient below an explicit positive scale.
-/

/-- The fixed coefficient after removing the single natural ceiling. -/
def ordinaryFiberNatCapFixedConstant : ENNReal := 960000

/-- The coefficient appearing after the outer factor eight in the
active-fine-to-parent mass comparison. -/
def ordinaryFiberMassLossFixedConstant : ENNReal :=
  8 * ordinaryFiberNatCapFixedConstant

def ordinaryFiberNatCapSmallDeltaThreshold
    (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold ordinaryFiberNatCapFixedConstant absorbEta

def ordinaryFiberMassLossSmallDeltaThreshold
    (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold ordinaryFiberMassLossFixedConstant absorbEta

def ordinaryFiberPowerEnvelope
    (epsilon etaKT absorbEta : Real) : Real :=
  etaKT + 2 * epsilon + absorbEta

theorem ordinaryFiberNatCapFixedConstant_ne_top :
    ordinaryFiberNatCapFixedConstant ≠ ∞ := by
  norm_num [ordinaryFiberNatCapFixedConstant]

theorem ordinaryFiberMassLossFixedConstant_ne_top :
    ordinaryFiberMassLossFixedConstant ≠ ∞ := by
  norm_num [ordinaryFiberMassLossFixedConstant,
    ordinaryFiberNatCapFixedConstant]

theorem ordinaryFiberNatCapSmallDeltaThreshold_pos
    (absorbEta : Real) :
    0 < ordinaryFiberNatCapSmallDeltaThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem ordinaryFiberMassLossSmallDeltaThreshold_pos
    (absorbEta : Real) :
    0 < ordinaryFiberMassLossSmallDeltaThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- Before fixed-constant absorption, one ceiling costs exactly the displayed
coefficient and one copy of the incidence-ratio power. -/
theorem canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_fixedPower
    {globalDelta tau theta : NNReal} {A : ENNReal}
    {epsilon etaKT : Real}
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (htauTheta : tau <= theta) (hthetaOne : theta <= 1)
    (hepsilon : 0 <= epsilon) (hAone : 1 <= A)
    (hA : A <= (globalDelta : ENNReal) ^ (-etaKT)) :
    (katzTaoDoubledFiberNatCap tau
        (canonicalLowerBufferedScale tau theta epsilon) A : ENNReal) <=
      ordinaryFiberNatCapFixedConstant *
        (globalDelta : ENNReal) ^ (-(etaKT + 2 * epsilon)) := by
  have htau : 0 < tau := hglobal.trans_le hglobalTau
  have hradius : tau <=
      canonicalLowerBufferedScale tau theta epsilon :=
    canonicalLowerBufferedScale_ge_tau htau htauTheta hepsilon
  have hAfinite : A ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hA
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hglobal.ne') ENNReal.coe_ne_top
  have hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio tau
        (canonicalLowerBufferedScale tau theta epsilon) A :=
    one_le_activeOwnerKatzTaoIncidenceRatio htau hradius hAone
  have hratioFinite :
      activeOwnerKatzTaoIncidenceRatio tau
        (canonicalLowerBufferedScale tau theta epsilon) A ≠ ∞ :=
    activeOwnerKatzTaoIncidenceRatio_ne_top htau hAfinite
  have hcap :
      (katzTaoDoubledFiberNatCap tau
          (canonicalLowerBufferedScale tau theta epsilon) A : ENNReal) <=
        2 * activeOwnerKatzTaoIncidenceRatio tau
          (canonicalLowerBufferedScale tau theta epsilon) A := by
    rw [katzTaoDoubledFiberNatCap_eq_samplingMultiplicity]
    exact katzTaoSamplingMultiplicity_coe_le_two_mul
      hratioOne hratioFinite
  have hratioPower :
      activeOwnerKatzTaoIncidenceRatio tau
          (canonicalLowerBufferedScale tau theta epsilon) A <=
        480000 *
          (globalDelta : ENNReal) ^ (-(etaKT + 2 * epsilon)) :=
    activeOwnerKatzTaoIncidenceRatio_le_longIntervalPower
      hglobal hA
      (canonicalLowerBufferedScale_squared_div_halfSq_le
        hglobal hglobalTau hthetaOne hepsilon)
  calc
    (katzTaoDoubledFiberNatCap tau
        (canonicalLowerBufferedScale tau theta epsilon) A : ENNReal) <=
        2 * activeOwnerKatzTaoIncidenceRatio tau
          (canonicalLowerBufferedScale tau theta epsilon) A := hcap
    _ <= 2 *
        (480000 *
          (globalDelta : ENNReal) ^ (-(etaKT + 2 * epsilon))) :=
      mul_le_mul' le_rfl hratioPower
    _ = ordinaryFiberNatCapFixedConstant *
        (globalDelta : ENNReal) ^ (-(etaKT + 2 * epsilon)) := by
      unfold ordinaryFiberNatCapFixedConstant
      ring

/-- Pure absorption of the single-cap fixed coefficient. -/
theorem ordinaryFiberNatCapFixedPower_le_absorbedPower
    {globalDelta : NNReal} {p absorbEta : Real}
    (hglobal : 0 < globalDelta) (habsorbEta : 0 < absorbEta)
    (hglobalThreshold : globalDelta <=
      ordinaryFiberNatCapSmallDeltaThreshold absorbEta) :
    ordinaryFiberNatCapFixedConstant *
        (globalDelta : ENNReal) ^ (-p) <=
      (globalDelta : ENNReal) ^ (-(p + absorbEta)) := by
  have hd0 : (globalDelta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hglobal.ne'
  have hdTop : (globalDelta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hconstant : ordinaryFiberNatCapFixedConstant <=
      (globalDelta : ENNReal) ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      ordinaryFiberNatCapFixedConstant_ne_top habsorbEta hglobal
        hglobalThreshold
  calc
    ordinaryFiberNatCapFixedConstant *
        (globalDelta : ENNReal) ^ (-p) <=
      (globalDelta : ENNReal) ^ (-absorbEta) *
        (globalDelta : ENNReal) ^ (-p) :=
      mul_le_mul' hconstant le_rfl
    _ = (globalDelta : ENNReal) ^ ((-absorbEta) + (-p)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (globalDelta : ENNReal) ^ (-(p + absorbEta)) := by
      congr 1
      ring

/-- Canonical ordinary-fibre cap with all ceiling and constant losses
absorbed into one explicit small exponent. -/
theorem canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_powerEnvelope
    {globalDelta tau theta : NNReal} {A : ENNReal}
    {epsilon etaKT absorbEta : Real}
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (htauTheta : tau <= theta) (hthetaOne : theta <= 1)
    (hepsilon : 0 <= epsilon) (habsorbEta : 0 < absorbEta)
    (hglobalThreshold : globalDelta <=
      ordinaryFiberNatCapSmallDeltaThreshold absorbEta)
    (hAone : 1 <= A)
    (hA : A <= (globalDelta : ENNReal) ^ (-etaKT)) :
    (katzTaoDoubledFiberNatCap tau
        (canonicalLowerBufferedScale tau theta epsilon) A : ENNReal) <=
      (globalDelta : ENNReal) ^
        (-ordinaryFiberPowerEnvelope epsilon etaKT absorbEta) := by
  have hfixed :=
    canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_fixedPower
      hglobal hglobalTau htauTheta hthetaOne hepsilon hAone hA
  have habsorb := ordinaryFiberNatCapFixedPower_le_absorbedPower
    (p := etaKT + 2 * epsilon) hglobal habsorbEta hglobalThreshold
  exact hfixed.trans (by
    simpa only [ordinaryFiberPowerEnvelope] using habsorb)

/-- Pure absorption with the additional outer factor eight used by the
active-fine mass comparison. -/
theorem ordinaryFiberMassLossFixedPower_le_absorbedPower
    {globalDelta : NNReal} {p absorbEta : Real}
    (hglobal : 0 < globalDelta) (habsorbEta : 0 < absorbEta)
    (hglobalThreshold : globalDelta <=
      ordinaryFiberMassLossSmallDeltaThreshold absorbEta) :
    8 * (ordinaryFiberNatCapFixedConstant *
        (globalDelta : ENNReal) ^ (-p)) <=
      (globalDelta : ENNReal) ^ (-(p + absorbEta)) := by
  have hd0 : (globalDelta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hglobal.ne'
  have hdTop : (globalDelta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hconstant : ordinaryFiberMassLossFixedConstant <=
      (globalDelta : ENNReal) ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      ordinaryFiberMassLossFixedConstant_ne_top habsorbEta hglobal
        hglobalThreshold
  calc
    8 * (ordinaryFiberNatCapFixedConstant *
        (globalDelta : ENNReal) ^ (-p)) =
      ordinaryFiberMassLossFixedConstant *
        (globalDelta : ENNReal) ^ (-p) := by
      unfold ordinaryFiberMassLossFixedConstant
      ring
    _ <= (globalDelta : ENNReal) ^ (-absorbEta) *
        (globalDelta : ENNReal) ^ (-p) :=
      mul_le_mul' hconstant le_rfl
    _ = (globalDelta : ENNReal) ^ ((-absorbEta) + (-p)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (globalDelta : ENNReal) ^ (-(p + absorbEta)) := by
      congr 1
      ring

/-- The exact scalar used in the mass-to-`X` chain: the outer eight times
the ordinary natural fibre cap has only exponent
`etaKT + 2 epsilon + absorbEta`. -/
theorem eight_mul_canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_powerEnvelope
    {globalDelta tau theta : NNReal} {A : ENNReal}
    {epsilon etaKT absorbEta : Real}
    (hglobal : 0 < globalDelta) (hglobalTau : globalDelta <= tau)
    (htauTheta : tau <= theta) (hthetaOne : theta <= 1)
    (hepsilon : 0 <= epsilon) (habsorbEta : 0 < absorbEta)
    (hglobalThreshold : globalDelta <=
      ordinaryFiberMassLossSmallDeltaThreshold absorbEta)
    (hAone : 1 <= A)
    (hA : A <= (globalDelta : ENNReal) ^ (-etaKT)) :
    8 * (katzTaoDoubledFiberNatCap tau
        (canonicalLowerBufferedScale tau theta epsilon) A : ENNReal) <=
      (globalDelta : ENNReal) ^
        (-ordinaryFiberPowerEnvelope epsilon etaKT absorbEta) := by
  have hfixed :=
    canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_fixedPower
      hglobal hglobalTau htauTheta hthetaOne hepsilon hAone hA
  have hmul :
      8 * (katzTaoDoubledFiberNatCap tau
          (canonicalLowerBufferedScale tau theta epsilon) A : ENNReal) <=
        8 * (ordinaryFiberNatCapFixedConstant *
          (globalDelta : ENNReal) ^ (-(etaKT + 2 * epsilon))) :=
    mul_le_mul' le_rfl hfixed
  exact hmul.trans (by
    simpa only [ordinaryFiberPowerEnvelope] using
      (ordinaryFiberMassLossFixedPower_le_absorbedPower
        (p := etaKT + 2 * epsilon) hglobal habsorbEta hglobalThreshold))

#print axioms
  canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_fixedPower
#print axioms ordinaryFiberNatCapFixedPower_le_absorbedPower
#print axioms
  canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_powerEnvelope
#print axioms ordinaryFiberMassLossFixedPower_le_absorbedPower
#print axioms
  eight_mul_canonicalLowerBufferedScale_doubledFiberNatCap_coe_le_powerEnvelope

end
end Family8LongIntervalOrdinaryFiberCapNumericsV1
