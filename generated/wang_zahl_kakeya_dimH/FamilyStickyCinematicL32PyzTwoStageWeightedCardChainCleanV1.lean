import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FamilyStickyCinematicL32PyzTwoStageWeightedCardChainCleanV1

/-!
# Denominator-free two-stage weighted cardinality transport

This purely algebraic kernel composes coefficient deduplication, norm-scale
retention, localization, and tangency-scale retention.  All weights remain
explicit; no division or positivity cancellation is used.
-/

theorem twoStage_weighted_card_chain
    {active multiplicity source normBall localized retained
      normCeilingWeight normScaleWeight tangencyCeilingWeight
      tangencyScaleWeight : Real}
    (hmultiplicity : 0 ≤ multiplicity)
    (hnormCeilingWeight : 0 ≤ normCeilingWeight)
    (hnormScaleWeight : 0 ≤ normScaleWeight)
    (htangencyCeilingWeight : 0 ≤ tangencyCeilingWeight)
    (hdedup : active ≤ multiplicity * source)
    (hnorm : source * normCeilingWeight ≤ normBall * normScaleWeight)
    (hlocalized : normBall ≤ localized)
    (htangency : localized * tangencyCeilingWeight ≤
      retained * tangencyScaleWeight) :
    active * normCeilingWeight * tangencyCeilingWeight ≤
      multiplicity * retained * normScaleWeight * tangencyScaleWeight := by
  calc
    active * normCeilingWeight * tangencyCeilingWeight ≤
        (multiplicity * source) * normCeilingWeight *
          tangencyCeilingWeight := by gcongr
    _ = multiplicity * (source * normCeilingWeight) *
        tangencyCeilingWeight := by ring
    _ ≤ multiplicity * (normBall * normScaleWeight) *
        tangencyCeilingWeight := by gcongr
    _ = multiplicity * normBall * normScaleWeight *
        tangencyCeilingWeight := by ring
    _ ≤ multiplicity * localized * normScaleWeight *
        tangencyCeilingWeight := by gcongr
    _ = (multiplicity * normScaleWeight) *
        (localized * tangencyCeilingWeight) := by ring
    _ ≤ (multiplicity * normScaleWeight) *
        (retained * tangencyScaleWeight) := by
      exact mul_le_mul_of_nonneg_left htangency
        (mul_nonneg hmultiplicity hnormScaleWeight)
    _ = multiplicity * retained * normScaleWeight *
        tangencyScaleWeight := by ring

end FamilyStickyCinematicL32PyzTwoStageWeightedCardChainCleanV1
