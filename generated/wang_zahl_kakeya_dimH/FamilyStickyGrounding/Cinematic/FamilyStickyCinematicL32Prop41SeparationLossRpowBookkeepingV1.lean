import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GeneralSeparationParameterBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41SeparationLossRpowBookkeepingV1

open FamilyStickyCinematicL32Prop41GeneralSeparationParameterBridgeV1

noncomputable section

/-!
# Absorbing the Proposition 4.1 separation loss

In the paper's application, the unreduced Proposition 4.1 parameter satisfies
`A <= delta ^ (-2 * epsilon)`.  This module records the exact consequence
`A ^ C <= delta ^ (-(2 * C * epsilon))` and its composition with an existing
power loss.

These are only scalar bookkeeping lemmas.  They do not prove the bound on
`A`, construct the white and black families, or assume the conclusion of
Proposition 4.1.
-/

/-- Raising `A <= delta^(-2 epsilon)` to a nonnegative real exponent costs
exactly the corresponding multiple of the delta exponent. -/
theorem separationLoss_rpow_le_delta_rpow
    {delta epsilon separationLoss lossExponent : Real}
    (hdelta : 0 <= delta) (hseparationLoss : 0 <= separationLoss)
    (hlossExponent : 0 <= lossExponent)
    (hseparationLossUpper :
      separationLoss <= delta ^ (-2 * epsilon)) :
    separationLoss ^ lossExponent <=
      delta ^ (-(2 * lossExponent * epsilon)) := by
  calc
    separationLoss ^ lossExponent <=
        (delta ^ (-2 * epsilon)) ^ lossExponent :=
      Real.rpow_le_rpow hseparationLoss hseparationLossUpper hlossExponent
    _ = delta ^ ((-2 * epsilon) * lossExponent) :=
      (Real.rpow_mul hdelta (-2 * epsilon) lossExponent).symm
    _ = delta ^ (-(2 * lossExponent * epsilon)) := by
      congr 1
      ring

/-- The faithful parameter `globalScale / radius` has the same loss bound as
soon as the caller proves the paper's `A <= delta^(-2 epsilon)` inequality. -/
theorem prop41SeparationLoss_rpow_le_delta_rpow
    {radius globalScale delta epsilon lossExponent : Real}
    (hradius : 0 < radius)
    (hradiusGlobalScale : radius <= globalScale)
    (hdelta : 0 <= delta) (hlossExponent : 0 <= lossExponent)
    (hseparationLossUpper :
      prop41SeparationLoss radius globalScale <=
        delta ^ (-2 * epsilon)) :
    prop41SeparationLoss radius globalScale ^ lossExponent <=
      delta ^ (-(2 * lossExponent * epsilon)) := by
  have hglobalScale : 0 <= globalScale :=
    (hradius.trans_le hradiusGlobalScale).le
  have hseparationLoss :
      0 <= prop41SeparationLoss radius globalScale := by
    exact div_nonneg hglobalScale hradius.le
  exact separationLoss_rpow_le_delta_rpow hdelta hseparationLoss
    hlossExponent hseparationLossUpper

/-- An existing delta power loss and the Proposition 4.1 `A^C` loss combine
by adding their exponent coefficients. -/
theorem delta_rpow_mul_separationLoss_rpow_le
    {delta epsilon baseLoss separationLoss lossExponent : Real}
    (hdelta : 0 < delta) (hseparationLoss : 0 <= separationLoss)
    (hlossExponent : 0 <= lossExponent)
    (hseparationLossUpper :
      separationLoss <= delta ^ (-2 * epsilon)) :
    delta ^ (-(baseLoss * epsilon)) *
        separationLoss ^ lossExponent <=
      delta ^ (-((baseLoss + 2 * lossExponent) * epsilon)) := by
  have hloss := separationLoss_rpow_le_delta_rpow hdelta.le
    hseparationLoss hlossExponent hseparationLossUpper
  calc
    delta ^ (-(baseLoss * epsilon)) *
        separationLoss ^ lossExponent <=
        delta ^ (-(baseLoss * epsilon)) *
          delta ^ (-(2 * lossExponent * epsilon)) :=
      mul_le_mul_of_nonneg_left hloss
        (Real.rpow_nonneg hdelta.le (-(baseLoss * epsilon)))
    _ = delta ^
        (-(baseLoss * epsilon) + -(2 * lossExponent * epsilon)) :=
      (Real.rpow_add hdelta (-(baseLoss * epsilon))
        (-(2 * lossExponent * epsilon))).symm
    _ = delta ^ (-((baseLoss + 2 * lossExponent) * epsilon)) := by
      congr 1
      ring

/-- Direct monotone replacement inside the scalar shape of the Proposition
4.1 upper bound. -/
theorem prop41_upperBound_absorb_separationLoss
    {quantity constant ratio delta epsilon separationLoss lossExponent : Real}
    (hdelta : 0 <= delta) (hseparationLoss : 0 <= separationLoss)
    (hlossExponent : 0 <= lossExponent)
    (hconstant : 0 <= constant) (hratio : 0 <= ratio)
    (hseparationLossUpper :
      separationLoss <= delta ^ (-2 * epsilon))
    (hupper : quantity <=
      constant * separationLoss ^ lossExponent * ratio) :
    quantity <=
      constant * delta ^ (-(2 * lossExponent * epsilon)) * ratio := by
  calc
    quantity <= constant * separationLoss ^ lossExponent * ratio := hupper
    _ <= constant * delta ^ (-(2 * lossExponent * epsilon)) * ratio := by
      gcongr
      exact separationLoss_rpow_le_delta_rpow hdelta hseparationLoss
        hlossExponent hseparationLossUpper

#print axioms separationLoss_rpow_le_delta_rpow
#print axioms prop41SeparationLoss_rpow_le_delta_rpow
#print axioms delta_rpow_mul_separationLoss_rpow_le
#print axioms prop41_upperBound_absorb_separationLoss

end

end FamilyStickyCinematicL32Prop41SeparationLossRpowBookkeepingV1
