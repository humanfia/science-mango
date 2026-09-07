import Family8Grounding.Family8CanonicalBufferedGlobalFirstFactorEndpointV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace Family8FirstFactorBalancedParameterBudgetV1

noncomputable section

/-!
# Balanced numerical parameters for the first outer factor

The canonical endpoint leaves three honest exponent inequalities.  They do
not require a new geometric estimate.  For every positive stopping epsilon
and positive Frostman exponent, one eighth of the latter is assigned to each
contracted-John power and one hundredth of `epsilon^2 * eta` is assigned to
every source/finite/logarithmic loss.  This gives substantial strict slack in
both the relative Katz--Tao cap and the unified power budget.
-/

/-- Each contracted-John exponent receives one eighth of the available
Frostman exponent. -/
def firstFactorJohnShare (eta : Real) : Real :=
  eta / 8

/-- The common source and absorption loss used by the balanced choice. -/
def firstFactorTinyLoss (epsilon eta : Real) : Real :=
  epsilon ^ 2 * eta / 100

theorem firstFactorJohnShare_pos
    {eta : Real} (heta : 0 < eta) :
    0 < firstFactorJohnShare eta := by
  unfold firstFactorJohnShare
  positivity

theorem firstFactorTinyLoss_pos
    {epsilon eta : Real} (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    0 < firstFactorTinyLoss epsilon eta := by
  unfold firstFactorTinyLoss
  positivity

/-- The balanced choice simultaneously proves the ratio-cap condition, the
positive remaining gain, and the complete first-factor scalar budget.

The returned `tiny` is to be used for each of
`etaF`, `etaKT`, `xAbs`, `lossExp`, and `constAbsorb`; `share` is used for
both `p` and `a`. -/
theorem balanced_firstFactor_parameter_budget
    {epsilon eta : Real} (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    let share := firstFactorJohnShare eta
    let tiny := firstFactorTinyLoss epsilon eta
    0 < share /\
      0 < tiny /\
      tiny <= epsilon ^ 2 * share /\
      0 <= eta - (2 * share + share) /\
      2 * tiny + tiny + (tiny + tiny) + tiny <=
        epsilon ^ 2 * (eta - (2 * share + share)) := by
  dsimp only [firstFactorJohnShare, firstFactorTinyLoss]
  have hproduct : 0 < epsilon ^ 2 * eta := by positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

#print axioms firstFactorJohnShare_pos
#print axioms firstFactorTinyLoss_pos
#print axioms balanced_firstFactor_parameter_budget

end
end Family8FirstFactorBalancedParameterBudgetV1
