import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1

noncomputable section

/-!
# Automatic explicit curvature ratio for the two-centre interface

The maximum with zero makes the definition honest even before any sign
information about the bridge or reference scale is available.  Positivity of
the local scale is the only input needed to discharge both scalar premises of
the two-centre packing theorem.
-/

/-- Minimal nonnegative ratio, up to the harmless `max 0`, which absorbs the
local, centre-bridge, and reference-scale second-jet budgets. -/
def twoCenterAutomaticCurvatureRatio
    (localScale centerGap referenceScale : Real) : Real :=
  max 0 (3 * localScale + centerGap + 3 * referenceScale) / localScale

theorem twoCenterAutomaticCurvatureRatio_nonneg
    {localScale centerGap referenceScale : Real}
    (hlocal : 0 < localScale) :
    0 <= twoCenterAutomaticCurvatureRatio
      localScale centerGap referenceScale := by
  unfold twoCenterAutomaticCurvatureRatio
  exact div_nonneg (le_max_left _ _) hlocal.le

theorem twoCenterAutomaticCurvatureRatio_budget
    {localScale centerGap referenceScale : Real}
    (hlocal : 0 < localScale) :
    3 * localScale + centerGap + 3 * referenceScale <=
      twoCenterAutomaticCurvatureRatio localScale centerGap referenceScale *
        localScale := by
  unfold twoCenterAutomaticCurvatureRatio
  rw [div_mul_cancel₀ _ hlocal.ne']
  exact le_max_right _ _

#print axioms twoCenterAutomaticCurvatureRatio
#print axioms twoCenterAutomaticCurvatureRatio_nonneg
#print axioms twoCenterAutomaticCurvatureRatio_budget

end

end FamilyStickyCinematicL32Lemma312TwoCenterAutomaticCurvatureRatioV1
