import Family8Grounding.Family8CanonicalLowerBufferedScaleV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalUpperBufferedScaleV3

open Family8CanonicalLowerBufferedScaleV4
open FamilyStickyDividingScalesFiniteStoppingV1

noncomputable section

/-!
# The upper canonical scale in the buffered core, V3

V1--V2 were failed drafts and are not imported.  The upper endpoint

`b₊ = theta^(1-epsilon) * tau^epsilon
    = theta * (tau / theta)^epsilon`

is an honest buffered scale.  Its relative separation from `tau` retains
the exponent `epsilon * (1-epsilon)` of a long interval, while the endpoint
itself is bounded by `delta^(epsilon^2)`.
-/

def canonicalUpperBufferedScale
    (tau theta : NNReal) (epsilon : Real) : NNReal :=
  theta ^ (1 - epsilon) * tau ^ epsilon

theorem canonicalUpperBufferedScale_eq_upperEndpoint
    {tau theta : NNReal} (htheta : 0 < theta) (epsilon : Real) :
    canonicalUpperBufferedScale tau theta epsilon =
      theta * (tau / theta) ^ epsilon := by
  have hthetaPow : 0 < theta ^ epsilon := NNReal.rpow_pos htheta
  have hsplit : theta ^ (1 - epsilon) * theta ^ epsilon = theta := by
    rw [← NNReal.rpow_add htheta.ne']
    convert NNReal.rpow_one theta using 1
    ring
  rw [canonicalUpperBufferedScale, NNReal.div_rpow, ← mul_div_assoc]
  apply (eq_div_iff hthetaPow.ne').2
  calc
    (theta ^ (1 - epsilon) * tau ^ epsilon) * theta ^ epsilon =
        (theta ^ (1 - epsilon) * theta ^ epsilon) * tau ^ epsilon := by
      ring
    _ = theta * tau ^ epsilon := by rw [hsplit]

theorem canonicalUpperBufferedScale_pos
    {tau theta : NNReal} (htau : 0 < tau) (htheta : 0 < theta)
    (epsilon : Real) :
    0 < canonicalUpperBufferedScale tau theta epsilon := by
  unfold canonicalUpperBufferedScale
  exact mul_pos (NNReal.rpow_pos htheta) (NNReal.rpow_pos htau)

theorem canonicalUpperBufferedScale_isBuffered
    {delta : NNReal} {depth : Nat}
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (hdelta : 0 < delta) {epsilon : Real}
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2) :
    S.IsBuffered epsilon m
      (canonicalUpperBufferedScale (S.tau m) (S.theta m) epsilon) := by
  have htau : 0 < S.tau m := hdelta.trans_le (S.delta_le_tau m)
  have htheta : 0 < S.theta m := htau.trans_le (S.tau_le_theta m)
  constructor
  · have hlower :=
      canonicalLowerBufferedScale_le_upperEndpoint
        htau htheta (S.tau_le_theta m) hepsilon hepsilonHalf
    rw [← canonicalUpperBufferedScale_eq_upperEndpoint htheta epsilon] at hlower
    rw [← ENNReal.coe_rpow_of_ne_zero
          (div_pos htheta htau).ne' epsilon,
        ← ENNReal.coe_mul,
        ← canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
    exact_mod_cast hlower
  · rw [← ENNReal.coe_rpow_of_ne_zero
        (div_pos htau htheta).ne' epsilon,
      ← ENNReal.coe_mul,
      ← canonicalUpperBufferedScale_eq_upperEndpoint htheta epsilon]

theorem tau_div_canonicalUpperBufferedScale
    {tau theta : NNReal} (htau : 0 < tau) (_htheta : 0 < theta)
    (epsilon : Real) :
    tau / canonicalUpperBufferedScale tau theta epsilon =
      (tau / theta) ^ (1 - epsilon) := by
  have htauPow : 0 < tau ^ epsilon := NNReal.rpow_pos htau
  have hsplit : tau ^ (1 - epsilon) * tau ^ epsilon = tau := by
    rw [← NNReal.rpow_add htau.ne']
    convert NNReal.rpow_one tau using 1
    ring
  unfold canonicalUpperBufferedScale
  calc
    tau / (theta ^ (1 - epsilon) * tau ^ epsilon) =
        (tau ^ (1 - epsilon) * tau ^ epsilon) /
          (theta ^ (1 - epsilon) * tau ^ epsilon) := by
      rw [hsplit]
    _ = tau ^ (1 - epsilon) / theta ^ (1 - epsilon) := by
      exact mul_div_mul_right _ _ htauPow.ne'
    _ = (tau / theta) ^ (1 - epsilon) := by
      rw [NNReal.div_rpow]

theorem tau_div_canonicalUpperBufferedScale_le_long_power
    {delta : NNReal} {depth : Nat}
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (hdelta : 0 < delta) {epsilon : Real}
    (_hepsilon : 0 <= epsilon) (hepsilonOne : epsilon <= 1)
    (hlong : S.IsLong epsilon m) :
    S.tau m /
        canonicalUpperBufferedScale (S.tau m) (S.theta m) epsilon <=
      delta ^ (epsilon * (1 - epsilon)) := by
  have htau : 0 < S.tau m := hdelta.trans_le (S.delta_le_tau m)
  have htheta : 0 < S.theta m := htau.trans_le (S.tau_le_theta m)
  have hlongENN :
      (S.tau m : ENNReal) <=
        (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal) := by
    simpa only [FiniteScaleSequence.IsLong] using hlong
  have hlongNN :
      S.tau m <= delta ^ epsilon * S.theta m := by
    rw [← ENNReal.coe_le_coe]
    simpa only [ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hlongENN
  have hratio :
      S.tau m / S.theta m <= delta ^ epsilon := by
    apply (div_le_iff₀ htheta).2
    simpa only [mul_comm] using hlongNN
  rw [tau_div_canonicalUpperBufferedScale htau htheta epsilon]
  calc
    (S.tau m / S.theta m) ^ (1 - epsilon) <=
        (delta ^ epsilon) ^ (1 - epsilon) :=
      NNReal.rpow_le_rpow hratio (sub_nonneg.mpr hepsilonOne)
    _ = delta ^ (epsilon * (1 - epsilon)) := by
      rw [NNReal.rpow_mul]

theorem canonicalUpperBufferedScale_le_long_power
    {delta : NNReal} {depth : Nat}
    (S : FiniteScaleSequence delta depth) (m : Fin depth)
    (hdelta : 0 < delta) {epsilon : Real}
    (hepsilon : 0 <= epsilon) (_hepsilonOne : epsilon <= 1)
    (hlong : S.IsLong epsilon m) :
    canonicalUpperBufferedScale (S.tau m) (S.theta m) epsilon <=
      delta ^ (epsilon ^ 2) := by
  have htau : 0 < S.tau m := hdelta.trans_le (S.delta_le_tau m)
  have htheta : 0 < S.theta m := htau.trans_le (S.tau_le_theta m)
  have hlongENN :
      (S.tau m : ENNReal) <=
        (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal) := by
    simpa only [FiniteScaleSequence.IsLong] using hlong
  have hlongNN :
      S.tau m <= delta ^ epsilon * S.theta m := by
    rw [← ENNReal.coe_le_coe]
    simpa only [ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hlongENN
  have htauPower :
      (S.tau m) ^ epsilon <=
        (delta ^ epsilon * S.theta m) ^ epsilon :=
    NNReal.rpow_le_rpow hlongNN hepsilon
  have hthetaPower :
      (S.theta m) ^ (1 - epsilon) * (S.theta m) ^ epsilon =
        S.theta m := by
    rw [← NNReal.rpow_add htheta.ne']
    convert NNReal.rpow_one (S.theta m) using 1
    ring
  calc
    canonicalUpperBufferedScale (S.tau m) (S.theta m) epsilon =
        (S.theta m) ^ (1 - epsilon) * (S.tau m) ^ epsilon := rfl
    _ <= (S.theta m) ^ (1 - epsilon) *
        (delta ^ epsilon * S.theta m) ^ epsilon :=
      mul_le_mul_of_nonneg_left htauPower (by positivity)
    _ = (S.theta m) ^ (1 - epsilon) *
        (delta ^ (epsilon * epsilon) * (S.theta m) ^ epsilon) := by
      rw [NNReal.mul_rpow, NNReal.rpow_mul]
    _ = delta ^ (epsilon * epsilon) *
        ((S.theta m) ^ (1 - epsilon) * (S.theta m) ^ epsilon) := by
      ring
    _ = delta ^ (epsilon * epsilon) * S.theta m := by
      rw [hthetaPower]
    _ = delta ^ (epsilon ^ 2) * S.theta m := by
      congr 2
      ring
    _ <= delta ^ (epsilon ^ 2) * 1 := by
      gcongr
      exact S.theta_le_one m
    _ = delta ^ (epsilon ^ 2) := mul_one _

#print axioms canonicalUpperBufferedScale
#print axioms canonicalUpperBufferedScale_eq_upperEndpoint
#print axioms canonicalUpperBufferedScale_isBuffered
#print axioms tau_div_canonicalUpperBufferedScale
#print axioms tau_div_canonicalUpperBufferedScale_le_long_power
#print axioms canonicalUpperBufferedScale_le_long_power

end

end Family8CanonicalUpperBufferedScaleV3
