import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace Family8FrozenOuterThirdBaseExponentChoiceV1

open Family8ParameterLadderV1

noncomputable section

/-!
# Explicit Frostman exponent for the frozen outer base budget

The canonical choice below is the smallest algebraic value for which the
long-scale gain pays exactly the two Katz--Tao powers and one fixed-constant
absorption exponent.  It depends only on the parameter ladder, the selected
stage, and the declared power budgets; no datum-dependent scalar appears.
-/

def frozenOuterThirdBaseFrostmanExponent
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (etaKT absorbEta : Real) : Real :=
  ((10 * P.eta j / (P.epsilon * beta)) +
      (2 * etaKT + absorbEta) / P.epsilon) /
    (1 - P.epsilon)

theorem frozenOuterThirdBaseFrostmanExponent_pos
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {etaKT absorbEta : Real}
    (hbeta : 0 < beta) (hetaKT : 0 ≤ etaKT)
    (habsorbEta : 0 < absorbEta)
    (hepsilonHalf : P.epsilon ≤ 1 / 2) :
    0 < frozenOuterThirdBaseFrostmanExponent P j etaKT absorbEta := by
  have hdenom : 0 < P.epsilon * beta := mul_pos P.epsilon_pos hbeta
  have hfirst : 0 < 10 * P.eta j / (P.epsilon * beta) :=
    div_pos (mul_pos (by norm_num) (P.eta_pos j)) hdenom
  have hsecond : 0 < (2 * etaKT + absorbEta) / P.epsilon := by
    exact div_pos (by linarith) P.epsilon_pos
  have honeMinus : 0 < 1 - P.epsilon := by linarith
  unfold frozenOuterThirdBaseFrostmanExponent
  exact div_pos (add_pos hfirst hsecond) honeMinus

theorem frozenOuterThirdBaseFrostmanExponent_gain_eq
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {etaKT absorbEta : Real}
    (hepsilonHalf : P.epsilon ≤ 1 / 2) :
    P.epsilon *
        ((1 - P.epsilon) *
            frozenOuterThirdBaseFrostmanExponent P j etaKT absorbEta -
          (10 * P.eta j / (P.epsilon * beta))) =
      2 * etaKT + absorbEta := by
  have hepsilon0 : P.epsilon ≠ 0 := P.epsilon_pos.ne'
  have honeMinus : 1 - P.epsilon ≠ 0 := by linarith
  unfold frozenOuterThirdBaseFrostmanExponent
  field_simp [hepsilon0, honeMinus]
  ring

theorem frozenOuterThirdBaseFrostmanExponent_scaleGain_nonneg
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {etaKT absorbEta : Real}
    (hetaKT : 0 ≤ etaKT) (habsorbEta : 0 < absorbEta)
    (hepsilonHalf : P.epsilon ≤ 1 / 2) :
    0 ≤ (1 - P.epsilon) *
        frozenOuterThirdBaseFrostmanExponent P j etaKT absorbEta -
      (10 * P.eta j / (P.epsilon * beta)) := by
  have hgain := frozenOuterThirdBaseFrostmanExponent_gain_eq
    P j (etaKT := etaKT) (absorbEta := absorbEta) hepsilonHalf
  have hloss : 0 ≤ 2 * etaKT + absorbEta := by linarith
  nlinarith [P.epsilon_pos]

theorem frozenOuterThirdBaseFrostmanExponent_budget
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {etaKT absorbEta : Real}
    (hepsilonHalf : P.epsilon ≤ 1 / 2) :
    2 * etaKT + absorbEta ≤
      P.epsilon *
        ((1 - P.epsilon) *
            frozenOuterThirdBaseFrostmanExponent P j etaKT absorbEta -
          (10 * P.eta j / (P.epsilon * beta))) := by
  exact (frozenOuterThirdBaseFrostmanExponent_gain_eq
    P j (etaKT := etaKT) (absorbEta := absorbEta) hepsilonHalf).ge

#print axioms frozenOuterThirdBaseFrostmanExponent_pos
#print axioms frozenOuterThirdBaseFrostmanExponent_gain_eq
#print axioms frozenOuterThirdBaseFrostmanExponent_scaleGain_nonneg
#print axioms frozenOuterThirdBaseFrostmanExponent_budget

end
end Family8FrozenOuterThirdBaseExponentChoiceV1
