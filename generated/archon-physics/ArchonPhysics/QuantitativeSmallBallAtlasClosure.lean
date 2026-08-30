import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import ArchonPhysics.QuantitativeMeasureAtlasGluing

/-!
# Closing local small-ball estimates over an almost-everywhere atlas

Local inverse-function charts give estimates for the source measure
restricted to individual patches.  This module records the exact final
measure-theoretic step: if a countable family of patches covers the source
almost everywhere, then the local bounds add.  If every local estimate is
linear in the window width and its coefficient is summable, the resulting
global estimate is linear with the summed coefficient.

The theorem deliberately keeps both substantive model obligations visible:
almost-everywhere coverage of the regular set and summability of the chart
constants.  It supplies neither obligation as an assumption hidden in a
definition.
-/

namespace ArchonPhysics.QuantitativeSmallBallAtlasClosure

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Bounds on one measurable event over an almost-everywhere countable atlas
sum to a global bound. -/
theorem measure_event_le_tsum_of_ae_atlas
    {Alpha Index : Type*} [MeasurableSpace Alpha] [Countable Index]
    (source : Measure Alpha) (patch : Index -> Set Alpha)
    (event : Set Alpha) (hevent : MeasurableSet event)
    (localBound : Index -> ENNReal)
    (hcover : ∀ᵐ x ∂source, x ∈ iUnion patch)
    (hlocal : forall index,
      source.restrict (patch index) event <= localBound index) :
    source event <= ∑' index, localBound index := by
  have hatlas :=
    (Measure.restrict_iUnion_le (μ := source) (s := patch)) event
  rw [Measure.sum_apply _ hevent] at hatlas
  have hrestrict : source.restrict (iUnion patch) = source :=
    Measure.restrict_eq_self_of_ae_mem hcover
  rw [hrestrict] at hatlas
  exact hatlas.trans (ENNReal.tsum_le_tsum hlocal)

/-- Linear local small-ball estimates with summable coefficients give a
global linear small-ball estimate. -/
theorem measure_event_le_tsum_mul_of_ae_atlas
    {Alpha Index : Type*} [MeasurableSpace Alpha] [Countable Index]
    (source : Measure Alpha) (patch : Index -> Set Alpha)
    (event : Set Alpha) (hevent : MeasurableSet event)
    (coefficient : Index -> ENNReal) (window : ENNReal)
    (hcover : ∀ᵐ x ∂source, x ∈ iUnion patch)
    (hlocal : forall index,
      source.restrict (patch index) event <= coefficient index * window) :
    source event <= (∑' index, coefficient index) * window := by
  calc
    source event <= ∑' index, coefficient index * window :=
      measure_event_le_tsum_of_ae_atlas source patch event hevent
        (fun index => coefficient index * window) hcover hlocal
    _ = (∑' index, coefficient index) * window :=
      ENNReal.tsum_mul_right

/-- The form used for a real small-ball half-width `delta`.  The estimate is
written with the full interval width `2 * delta`. -/
theorem measure_smallBall_le_tsum_mul_two_delta_of_ae_atlas
    {Alpha Index : Type*} [MeasurableSpace Alpha] [Countable Index]
    (source : Measure Alpha) (patch : Index -> Set Alpha)
    (mismatch : Alpha -> Real) (hmismatch : Measurable mismatch)
    (coefficient : Index -> ENNReal) (delta : Real)
    (hcover : ∀ᵐ x ∂source, x ∈ iUnion patch)
    (hlocal : forall index,
      source.restrict (patch index)
          {x | |mismatch x| <= delta} <=
        coefficient index * ENNReal.ofReal (2 * delta)) :
    source {x | |mismatch x| <= delta} <=
      (∑' index, coefficient index) * ENNReal.ofReal (2 * delta) := by
  have hevent : MeasurableSet {x | |mismatch x| <= delta} := by
    change MeasurableSet
      ((fun x => |mismatch x|) ⁻¹' Set.Iic delta)
    exact measurableSet_Iic.preimage (by
      simpa only [Real.norm_eq_abs] using hmismatch.norm)
  exact measure_event_le_tsum_mul_of_ae_atlas source patch
    {x | |mismatch x| <= delta} hevent coefficient
      (ENNReal.ofReal (2 * delta)) hcover hlocal

end
end ArchonPhysics.QuantitativeSmallBallAtlasClosure
