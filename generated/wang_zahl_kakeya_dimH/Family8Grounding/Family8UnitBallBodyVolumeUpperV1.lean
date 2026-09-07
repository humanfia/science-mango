import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8UnitBallBodyVolumeUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-!
# An explicit absolute upper bound for the ambient unit ball

The three-dimensional unit ball has volume `4*pi/3`.  The coarse bound by
eight is sufficient for all small-scale constant absorption and keeps the
downstream scalar endpoint rational.
-/

/-- Explicit finite rational upper bound for the ambient convex body's
Lebesgue volume. -/
theorem volume_unitBallBody_le_eight :
    volume (unitBallBody : Set Space) ≤ (8 : ENNReal) := by
  rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
  norm_num
  nlinarith [Real.pi_lt_four]

theorem volume_unitBallBody_ne_top :
    volume (unitBallBody : Set Space) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofNat_ne_top volume_unitBallBody_le_eight

#print axioms volume_unitBallBody_le_eight
#print axioms volume_unitBallBody_ne_top

end
end Family8UnitBallBodyVolumeUpperV1
