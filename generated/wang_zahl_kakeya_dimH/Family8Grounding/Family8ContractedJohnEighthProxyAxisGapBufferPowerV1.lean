import Family8Grounding.Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Small-delta absorption of the contracted-John/eighth proxy axis gap

The geometric producer gives the explicit normalized-axis gap

`(15561 * tau) / (64 * rho)`.

This file turns the usual relative-scale gain

`tau / rho <= delta ^ (epsilon ^ 2)`

into an honest fixed parent buffer.  Below the explicit finite-constant
threshold for `15561`, the positive and negative powers cancel and in fact
give the stronger bound `axisGap <= 1 / 64`.  Hence the actual buffer `1 / 8`
is available without assuming any form of the desired axis-gap conclusion.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set
open scoped ENNReal NNReal

namespace Family8ContractedJohnEighthProxyAxisGapBufferPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyCarrierMonoV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8ContractedJohnEighthProxySelectedAncestorAxisGapV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-- The concrete containing-tube buffer used by the scalar absorption. -/
def contractedJohnEighthSelectedAncestorOneEighthBuffer : NNReal := 1 / 8

/-- Explicit small-scale threshold that absorbs the full numerator `15561`.
This deliberately proves a `1 / 64` bound before weakening to the advertised
`1 / 8` containing-tube buffer. -/
def contractedJohnEighthSelectedAncestorAxisGapThreshold
    (epsilon : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold (15561 : ENNReal) (epsilon ^ 2)

theorem contractedJohnEighthSelectedAncestorAxisGapThreshold_pos
    (epsilon : Real) :
    0 < contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon :=
  finiteConstantSmallDeltaThreshold_pos (15561 : ENNReal) (epsilon ^ 2)

theorem contractedJohnEighthSelectedAncestorAxisGapThreshold_le_one
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon <= 1 := by
  exact finiteConstantSmallDeltaThreshold_le_one
    (15561 : ENNReal) (by positivity : 0 < epsilon ^ 2)

/-- The ratio-power gain and the explicit small-delta threshold produce the
strong scalar estimate `15561 * (tau / rho) <= 1`. -/
theorem numerator_mul_ratio_le_one_of_ratioPower
    {delta tau rho : NNReal} {epsilon : Real}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hratio : tau / rho <= delta ^ (epsilon ^ 2))
    (hsmall : delta <=
      contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon) :
    (15561 : NNReal) * (tau / rho) <= 1 := by
  have hexponent : 0 < epsilon ^ 2 := by positivity
  have hconstant : (15561 : ENNReal) <=
      (delta : ENNReal) ^ (-(epsilon ^ 2)) := by
    exact finiteConstant_le_delta_negativePower
      (by norm_num) hexponent hdelta hsmall
  have hratioENN :
      ((tau / rho : NNReal) : ENNReal) <=
        (delta : ENNReal) ^ (epsilon ^ 2) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (epsilon ^ 2)]
    exact ENNReal.coe_le_coe.mpr hratio
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hscaledENN :
      (15561 : ENNReal) * ((tau / rho : NNReal) : ENNReal) <= 1 := by
    calc
      (15561 : ENNReal) * ((tau / rho : NNReal) : ENNReal) <=
          (delta : ENNReal) ^ (-(epsilon ^ 2)) *
            (delta : ENNReal) ^ (epsilon ^ 2) :=
        mul_le_mul' hconstant hratioENN
      _ = (delta : ENNReal) ^
          (-(epsilon ^ 2) + epsilon ^ 2) := by
        rw [← ENNReal.rpow_add (-(epsilon ^ 2)) (epsilon ^ 2)
          hdelta0 ENNReal.coe_ne_top]
      _ = 1 := by ring_nf; simp
  rw [← ENNReal.coe_le_coe]
  simpa only [ENNReal.coe_mul, ENNReal.coe_div, ENNReal.coe_ofNat,
    ENNReal.coe_one] using hscaledENN

/-- Honest scalar absorption for the exact selected-ancestor axis gap.  The
proof uses the ratio-power theorem as an input and derives the buffer bound;
it does not assume an axis-gap comparison in disguised form. -/
theorem contractedJohnEighthSelectedAncestorAxisGap_le_oneEighthBuffer
    {delta tau rho : NNReal} {epsilon : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hepsilon : 0 < epsilon)
    (hratio : tau / rho <= delta ^ (epsilon ^ 2))
    (hsmall : delta <=
      contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon) :
    contractedJohnEighthSelectedAncestorAxisGap tau rho <=
      contractedJohnEighthSelectedAncestorOneEighthBuffer := by
  have hscaled : (15561 : NNReal) * (tau / rho) <= 1 :=
    numerator_mul_ratio_le_one_of_ratioPower
      hdelta hepsilon hratio hsmall
  calc
    contractedJohnEighthSelectedAncestorAxisGap tau rho =
        ((15561 : NNReal) * (tau / rho)) / 64 := by
      unfold contractedJohnEighthSelectedAncestorAxisGap
      field_simp [hrho.ne']
    _ <= 1 / 64 := by gcongr
    _ <= contractedJohnEighthSelectedAncestorOneEighthBuffer := by
      unfold contractedJohnEighthSelectedAncestorOneEighthBuffer
      rw [← NNReal.coe_le_coe]
      norm_num

/-- End-to-end consumer: source carrier nesting plus the scalar ratio-power
gain gives containment in the genuine parent proxy with buffer `1 / 8`. -/
theorem contractedJohnEighthProxyTube_subset_selectedAncestorOneEighthContainingTube
    {delta tau rho : NNReal} (P : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (w : JohnAxisWitness P.body)
    (T : Tube delta) (U : Tube tau) (hdelta : 0 < delta)
    (hdeltaTau : delta <= tau)
    (hTU : T.carrier ⊆ U.carrier) {epsilon : Real}
    (hepsilon : 0 < epsilon)
    (hratio : tau / rho <= delta ^ (epsilon ^ 2))
    (hsmall : delta <=
      contractedJohnEighthSelectedAncestorAxisGapThreshold epsilon) :
    (contractedJohnEighthProxyTube P hrho w T).carrier ⊆
      (contractedJohnEighthProxyContainingTube P hrho w U
        contractedJohnEighthSelectedAncestorOneEighthBuffer).carrier := by
  apply contractedJohnEighthProxyTube_subset_selectedAncestorContainingTube
    P hrho hrhoOne w T U hdeltaTau hTU
  exact contractedJohnEighthSelectedAncestorAxisGap_le_oneEighthBuffer
    hdelta hrho hepsilon hratio hsmall

#print axioms contractedJohnEighthSelectedAncestorOneEighthBuffer
#print axioms contractedJohnEighthSelectedAncestorAxisGapThreshold
#print axioms contractedJohnEighthSelectedAncestorAxisGapThreshold_pos
#print axioms contractedJohnEighthSelectedAncestorAxisGapThreshold_le_one
#print axioms numerator_mul_ratio_le_one_of_ratioPower
#print axioms contractedJohnEighthSelectedAncestorAxisGap_le_oneEighthBuffer
#print axioms
  contractedJohnEighthProxyTube_subset_selectedAncestorOneEighthContainingTube

end
end Family8ContractedJohnEighthProxyAxisGapBufferPowerV1
