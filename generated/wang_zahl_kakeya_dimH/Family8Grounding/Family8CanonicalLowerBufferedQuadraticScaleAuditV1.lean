import Family8Grounding.Family8CanonicalLowerBufferedScaleV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped NNReal

namespace Family8CanonicalLowerBufferedQuadraticScaleAuditV1

open Family8CanonicalLowerBufferedScaleV4

/-!
# Quadratic-scale audit for the canonical lower buffered endpoint

For the paper range `0 <= epsilon ≤ 1/2`, the lower buffered endpoint is at
most the square root of its lower adjacent scale.  Consequently it cannot
serve as a quadratic enlargement of that lower scale by any constant bigger
than one.  Separately, the order data `delta <= tau <= 1` stored by a finite
scale sequence do not imply `648 * delta ≤ tau^2`.
-/

theorem canonicalLowerBufferedScale_sq_le_tau
    {tau theta : NNReal} (htau : 0 < tau) (htauTheta : tau ≤ theta) (hthetaOne : theta ≤ 1)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    canonicalLowerBufferedScale tau theta epsilon ^ 2 ≤ tau := by
  have hb : canonicalLowerBufferedScale tau theta epsilon ≤
      tau ^ (1 - epsilon) :=
    canonicalLowerBufferedScale_le_tau_rpow_one_sub hthetaOne hepsilon
  calc
    canonicalLowerBufferedScale tau theta epsilon ^ 2 =
        canonicalLowerBufferedScale tau theta epsilon *
          canonicalLowerBufferedScale tau theta epsilon := by ring
    _ ≤ tau ^ (1 - epsilon) * tau ^ (1 - epsilon) :=
      mul_le_mul' hb hb
    _ = tau ^ ((1 - epsilon) + (1 - epsilon)) := by
      rw [NNReal.rpow_add htau.ne']
    _ ≤ tau ^ (1 : Real) := by
      exact NNReal.rpow_le_rpow_of_exponent_ge htau
        (htauTheta.trans hthetaOne) (by linarith)
    _ = tau := NNReal.rpow_one tau

theorem not_648_mul_tau_le_canonicalLowerBufferedScale_sq
    {tau theta : NNReal} (htau : 0 < tau) (htauTheta : tau ≤ theta) (hthetaOne : theta ≤ 1)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2) :
    ¬ (648 * tau ≤ canonicalLowerBufferedScale tau theta epsilon ^ 2) := by
  intro h
  have hbad : 648 * tau ≤ tau :=
    h.trans (canonicalLowerBufferedScale_sq_le_tau
      htau htauTheta hthetaOne hepsilon hepsilonHalf)
  nlinarith

theorem scale_order_alone_does_not_imply_648_mul_delta_le_tau_sq :
    ∃ delta tau : NNReal,
      0 < delta ∧ delta ≤ tau ∧ tau ≤ 1 ∧
        ¬ (648 * delta ≤ tau ^ 2) := by
  refine ⟨(1 / 2 : NNReal), (1 / 2 : NNReal), ?_⟩
  norm_num

#print axioms canonicalLowerBufferedScale_sq_le_tau
#print axioms not_648_mul_tau_le_canonicalLowerBufferedScale_sq
#print axioms scale_order_alone_does_not_imply_648_mul_delta_le_tau_sq

end Family8CanonicalLowerBufferedQuadraticScaleAuditV1
