import FamilyStickyCinematicL32PyzWeightedThreeHalfOfRealV1
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzTwoStageMomentConnectorV1

/-! Denominator-free transport from the two-stage card bound to an E2 three-halves moment estimate. -/

open FamilyStickyCinematicL32PyzWeightedThreeHalfOfRealV1

theorem twoStage_card_to_threeHalf_moment
    {active multiplicity degreeLower : Nat}
    {normCeilingWeight tangencyCeilingWeight normScaleWeight
      tangencyScaleWeight : Real}
    {E M : ENNReal}
    (hnormScaleWeight : 0 ≤ normScaleWeight)
    (htangencyScaleWeight : 0 ≤ tangencyScaleWeight)
    (hcard : (active : Real) * normCeilingWeight * tangencyCeilingWeight ≤
      (multiplicity : Real) * ((2 * degreeLower : Nat) : Real) *
        normScaleWeight * tangencyScaleWeight)
    (hmoment : (degreeLower : ENNReal) ^ (3 / 2 : Real) * E ≤ M) :
    (ENNReal.ofReal ((active : Real) * normCeilingWeight *
      tangencyCeilingWeight)) ^ (3 / 2 : Real) * E ≤
      (ENNReal.ofReal ((multiplicity : Real) * 2 * normScaleWeight *
        tangencyScaleWeight)) ^ (3 / 2 : Real) * M := by
  have hfactor : (active : Real) * normCeilingWeight *
        tangencyCeilingWeight ≤
      ((multiplicity : Real) * 2 * normScaleWeight * tangencyScaleWeight) *
        (degreeLower : Real) := by
    calc
      _ ≤ (multiplicity : Real) * ((2 * degreeLower : Nat) : Real) *
          normScaleWeight * tangencyScaleWeight := hcard
      _ = ((multiplicity : Real) * 2 * normScaleWeight *
          tangencyScaleWeight) * (degreeLower : Real) := by
        push_cast
        ring
  have hfactorNonneg : 0 ≤ (multiplicity : Real) * 2 *
      normScaleWeight * tangencyScaleWeight := by positivity
  have hmomentReal : (ENNReal.ofReal (degreeLower : Real)) ^
      (3 / 2 : Real) * E ≤ M := by
    simpa only [ENNReal.ofReal_natCast] using hmoment
  exact weighted_threeHalf_absorption_ofReal hfactorNonneg hfactor
    hmomentReal

end FamilyStickyCinematicL32PyzTwoStageMomentConnectorV1
