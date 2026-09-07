import FamilyStickyGrounding.FamilyStickyDividingScalesFiniteStoppingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalLowerBufferedScaleV4

open FamilyStickyDividingScalesFiniteStoppingV1

noncomputable section

/-!
# A canonical scale in the buffered core

For an interval `tau <= theta`, the lower endpoint of the paper's buffered
core is

`b = tau^(1-epsilon) * theta^epsilon
   = tau * (theta / tau)^epsilon`.

When `0 <= epsilon <= 1/2`, this endpoint really lies in the buffered core.
The choice also retains the sharp scale information needed by the incidence
degree estimate: `b <= tau^(1-epsilon)`, and, in a finite scale sequence,
`b / tau <= delta^(-epsilon)`.
-/

/-- The lower endpoint of the multiplicatively buffered interval. -/
def canonicalLowerBufferedScale
    (tau theta : NNReal) (epsilon : Real) : NNReal :=
  tau ^ (1 - epsilon) * theta ^ epsilon

theorem canonicalLowerBufferedScale_eq_lowerEndpoint
    {tau theta : NNReal} (htau : 0 < tau) (epsilon : Real) :
    canonicalLowerBufferedScale tau theta epsilon =
      tau * (theta / tau) ^ epsilon := by
  have htauPow : 0 < tau ^ epsilon := NNReal.rpow_pos htau
  have hsplit : tau ^ (1 - epsilon) * tau ^ epsilon = tau := by
    rw [← NNReal.rpow_add htau.ne']
    convert NNReal.rpow_one tau using 1
    ring
  rw [canonicalLowerBufferedScale, NNReal.div_rpow, ← mul_div_assoc]
  apply (eq_div_iff htauPow.ne').2
  calc
    (tau ^ (1 - epsilon) * theta ^ epsilon) * tau ^ epsilon =
        (tau ^ (1 - epsilon) * tau ^ epsilon) * theta ^ epsilon := by ring
    _ = tau * theta ^ epsilon := by rw [hsplit]

theorem canonicalLowerBufferedScale_le_upperEndpoint
    {tau theta : NNReal} (htau : 0 < tau) (htheta : 0 < theta)
    (htauTheta : tau ≤ theta) {epsilon : Real}
    (_hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2) :
    canonicalLowerBufferedScale tau theta epsilon ≤
      theta * (tau / theta) ^ epsilon := by
  have hq : 0 ≤ 1 - 2 * epsilon := by linarith
  have hpow : tau ^ (1 - 2 * epsilon) ≤
      theta ^ (1 - 2 * epsilon) :=
    NNReal.rpow_le_rpow htauTheta hq
  have htauSplit : tau ^ (1 - epsilon) =
      tau ^ (1 - 2 * epsilon) * tau ^ epsilon := by
    rw [← NNReal.rpow_add htau.ne']
    congr 1
    ring
  have hthetaSplit : theta ^ (1 - epsilon) =
      theta ^ (1 - 2 * epsilon) * theta ^ epsilon := by
    rw [← NNReal.rpow_add htheta.ne']
    congr 1
    ring
  have hupper : theta * (tau / theta) ^ epsilon =
      theta ^ (1 - epsilon) * tau ^ epsilon := by
    have hthetaPow : 0 < theta ^ epsilon := NNReal.rpow_pos htheta
    have hsplit : theta ^ (1 - epsilon) * theta ^ epsilon = theta := by
      rw [← NNReal.rpow_add htheta.ne']
      convert NNReal.rpow_one theta using 1
      ring
    rw [NNReal.div_rpow, ← mul_div_assoc]
    apply (div_eq_iff hthetaPow.ne').2
    calc
      theta * tau ^ epsilon =
          (theta ^ (1 - epsilon) * theta ^ epsilon) * tau ^ epsilon := by
        rw [hsplit]
      _ = (theta ^ (1 - epsilon) * tau ^ epsilon) *
          theta ^ epsilon := by ring
  rw [canonicalLowerBufferedScale, htauSplit, hupper, hthetaSplit]
  calc
    (tau ^ (1 - 2 * epsilon) * tau ^ epsilon) * theta ^ epsilon =
        tau ^ (1 - 2 * epsilon) *
          (tau ^ epsilon * theta ^ epsilon) := by ring
    _ ≤ theta ^ (1 - 2 * epsilon) *
          (tau ^ epsilon * theta ^ epsilon) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (theta ^ (1 - 2 * epsilon) * theta ^ epsilon) *
          tau ^ epsilon := by ring

/-- The canonical lower endpoint is an honest buffered scale. -/
theorem canonicalLowerBufferedScale_isBuffered
    {delta : NNReal} {depth : Nat}
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (delta_pos : 0 < delta) {epsilon : Real}
    (hepsilon : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2) :
    S.IsBuffered epsilon m
      (canonicalLowerBufferedScale (S.tau m) (S.theta m) epsilon) := by
  have htau : 0 < S.tau m := delta_pos.trans_le (S.delta_le_tau m)
  have htheta : 0 < S.theta m := htau.trans_le (S.tau_le_theta m)
  constructor
  · rw [← ENNReal.coe_rpow_of_ne_zero
        (div_pos htheta htau).ne' epsilon,
      ← ENNReal.coe_mul,
      ← canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
  · have hupper := canonicalLowerBufferedScale_le_upperEndpoint
      htau htheta (S.tau_le_theta m) hepsilon hepsilonHalf
    exact_mod_cast hupper

/-- The lower buffered endpoint has the scale upper bound used in the long
interval numerical bootstrap. -/
theorem canonicalLowerBufferedScale_le_tau_rpow_one_sub
    {tau theta : NNReal} (hthetaOne : theta ≤ 1)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    canonicalLowerBufferedScale tau theta epsilon ≤
      tau ^ (1 - epsilon) := by
  have hthetaPow : theta ^ epsilon ≤ (1 : NNReal) ^ epsilon :=
    NNReal.rpow_le_rpow hthetaOne hepsilon
  simpa only [canonicalLowerBufferedScale, NNReal.one_rpow, mul_one] using
    mul_le_mul_of_nonneg_left hthetaPow (by positivity)

/-- Relative to the fine radius, the canonical coarse radius costs only the
small global power `delta^(-epsilon)`. -/
theorem canonicalLowerBufferedScale_div_tau_le_delta_rpow_neg
    {delta tau theta : NNReal} (hdelta : 0 < delta)
    (hdeltaTau : delta ≤ tau) (hthetaOne : theta ≤ 1)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    canonicalLowerBufferedScale tau theta epsilon / tau ≤
      delta ^ (-epsilon) := by
  have htau : 0 < tau := hdelta.trans_le hdeltaTau
  have htheta : theta / tau ≤ 1 / delta := by
    calc
      theta / tau ≤ 1 / tau :=
        (div_le_div_iff_of_pos_right htau).2 hthetaOne
      _ = tau⁻¹ := one_div tau
      _ ≤ delta⁻¹ := inv_anti₀ hdelta hdeltaTau
      _ = 1 / delta := (one_div delta).symm
  have hratioPow : (theta / tau) ^ epsilon ≤
      (1 / delta) ^ epsilon :=
    NNReal.rpow_le_rpow htheta hepsilon
  rw [canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon,
    mul_div_cancel_left₀ _ htau.ne']
  calc
    (theta / tau) ^ epsilon ≤ (1 / delta) ^ epsilon := hratioPow
    _ = delta ^ (-epsilon) := by
      rw [one_div, NNReal.inv_rpow, NNReal.rpow_neg]

#print axioms canonicalLowerBufferedScale_eq_lowerEndpoint
#print axioms canonicalLowerBufferedScale_isBuffered
#print axioms canonicalLowerBufferedScale_le_tau_rpow_one_sub
#print axioms canonicalLowerBufferedScale_div_tau_le_delta_rpow_neg

end

end Family8CanonicalLowerBufferedScaleV4
