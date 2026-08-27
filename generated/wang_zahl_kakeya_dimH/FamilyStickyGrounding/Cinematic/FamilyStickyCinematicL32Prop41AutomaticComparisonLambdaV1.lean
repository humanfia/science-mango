import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1

open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1

noncomputable section

/-!
# A canonical comparison enlargement

The counting endpoint only needs an enlargement at least `2 * lambda1` and
large enough that its square-root length dominates four localization radii.
The explicit choice below makes both conditions tautological up to positive
field algebra, so no outcome-dependent numerical callback is needed.
-/

/-- Canonical enlargement parameter for the compact-C2 comparison step. -/
def prop41AutomaticComparisonLambda
    (lambda1 delta t : Real) : Real :=
  2 * lambda1 + (t / delta) *
    (4 * prop41ActualPairLocalizationRadius (4 * lambda1) delta t) ^ 2

theorem prop41AutomaticComparisonLambda_nonneg
    {lambda1 delta t : Real}
    (hlambda1 : 1 <= lambda1) (hdelta : 0 < delta) (ht : 0 < t) :
    0 <= prop41AutomaticComparisonLambda lambda1 delta t := by
  unfold prop41AutomaticComparisonLambda
  positivity

/-- The canonical comparison parameter contains the twice-enlarged local
rectangle scale. -/
theorem prop41AutomaticComparisonLambda_enlarges
    {lambda1 delta t : Real}
    (_hlambda1 : 1 <= lambda1) (hdelta : 0 < delta) (ht : 0 < t) :
    2 * lambda1 * delta <=
      prop41AutomaticComparisonLambda lambda1 delta t * delta := by
  have hterm : 0 <= (t / delta) *
      (4 * prop41ActualPairLocalizationRadius
        (4 * lambda1) delta t) ^ 2 := by
    positivity
  unfold prop41AutomaticComparisonLambda
  nlinarith

/-- Its induced square-root length automatically dominates four localization
radii. -/
theorem prop41AutomaticComparisonLambda_localization
    {lambda1 delta t : Real}
    (hlambda1 : 1 <= lambda1) (hdelta : 0 < delta) (ht : 0 < t) :
    4 * prop41ActualPairLocalizationRadius (4 * lambda1) delta t <=
      Real.sqrt
        (prop41AutomaticComparisonLambda lambda1 delta t * delta / t) := by
  let r := 4 * prop41ActualPairLocalizationRadius (4 * lambda1) delta t
  have hfirst : 0 <= 2 * lambda1 * delta / t := by
    positivity
  have heq : prop41AutomaticComparisonLambda lambda1 delta t * delta / t =
      2 * lambda1 * delta / t + r ^ 2 := by
    dsimp only [prop41AutomaticComparisonLambda, r]
    field_simp [ne_of_gt hdelta, ne_of_gt ht]
  have hsq : r ^ 2 <=
      prop41AutomaticComparisonLambda lambda1 delta t * delta / t := by
    rw [heq]
    linarith
  simpa only [r] using Real.le_sqrt_of_sq_le hsq

#print axioms prop41AutomaticComparisonLambda
#print axioms prop41AutomaticComparisonLambda_enlarges
#print axioms prop41AutomaticComparisonLambda_localization

end

end FamilyStickyCinematicL32Prop41AutomaticComparisonLambdaV1
