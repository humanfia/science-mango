import ArchonPhysics.TwoTimeKineticHittingBounds

/-!
# Two-time kinetic windows from the genuine positive-time right limit

The late-window observable used by the thermalization campaign is totalized
at `T = 0`.  Its positive-time values can therefore have the correct right
limit while the totalized value at zero is unrelated to that limit.  This
module constructs the release-facing robust hitting window from the genuine
right limit, without assuming continuity of the totalized observable at zero.
-/

namespace ArchonPhysics.PositiveTimeTwoTimeKineticHittingBounds

open Filter Set
open ArchonPhysics.TwoTimeKineticHittingBounds

noncomputable section

/-- Extend a positive-time profile by its genuine right limit at nonpositive
times.  This auxiliary function is used only to invoke the generic two-time
window theorem; the resulting window is transferred back to the original
positive-time profile. -/
def rightLimitExtension
    (distance : Real -> Real) (rightLimit : Real) (t : Real) : Real :=
  if 0 < t then distance t else rightLimit

@[simp] theorem rightLimitExtension_zero
    (distance : Real -> Real) (rightLimit : Real) :
    rightLimitExtension distance rightLimit 0 = rightLimit := by
  simp [rightLimitExtension]

theorem rightLimitExtension_eq_of_pos
    (distance : Real -> Real) (rightLimit t : Real) (ht : 0 < t) :
    rightLimitExtension distance rightLimit t = distance t := by
  simp [rightLimitExtension, ht]

/-- A positive-time right limit makes the auxiliary extension continuous at
zero.  No regularity of the original totalized value is used. -/
theorem continuousAt_zero_rightLimitExtension
    (distance : Real -> Real) (rightLimit : Real)
    (hlimit : Tendsto distance (nhdsWithin 0 (Ioi 0))
      (nhds rightLimit)) :
    ContinuousAt (rightLimitExtension distance rightLimit) 0 := by
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · change Tendsto (rightLimitExtension distance rightLimit)
      (nhdsWithin 0 (Iio 0))
      (nhds (rightLimitExtension distance rightLimit 0))
    have heq : rightLimitExtension distance rightLimit =ᶠ[
        nhdsWithin 0 (Iio 0)] (fun _ => rightLimit) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hnot : ¬ 0 < t := not_lt.mpr ht.le
      simp [rightLimitExtension, hnot]
    rw [rightLimitExtension_zero]
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  · change Tendsto (rightLimitExtension distance rightLimit)
      (nhdsWithin 0 (Ioi 0))
      (nhds (rightLimitExtension distance rightLimit 0))
    have heq : rightLimitExtension distance rightLimit =ᶠ[
        nhdsWithin 0 (Ioi 0)] distance := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact rightLimitExtension_eq_of_pos distance rightLimit t ht
    rw [rightLimitExtension_zero]
    exact (tendsto_congr' heq).mpr hlimit

/-- A strictly separated positive-time right limit and eventual relaxation
produce the same robust lower/upper hitting window as a profile genuinely
continuous at zero.  This is the correct interface for totalized window
averages. -/
theorem exists_robustKineticHittingWindow_of_tendsto_right
    (distance : Real -> Real) (rightLimit delta : Real)
    (hdelta : 0 < delta) (hseparated : delta < rightLimit)
    (hlimit : Tendsto distance (nhdsWithin 0 (Ioi 0))
      (nhds rightLimit))
    (hrelax : Tendsto distance atTop (nhds 0)) :
    exists lower upper : Real,
      RobustKineticHittingWindow distance delta lower upper := by
  let extension : Real -> Real :=
    rightLimitExtension distance rightLimit
  have hextensionAtTop : Tendsto extension atTop (nhds 0) := by
    have heq : extension =ᶠ[atTop] distance := by
      filter_upwards [eventually_gt_atTop (0 : Real)] with t ht
      exact rightLimitExtension_eq_of_pos distance rightLimit t ht
    exact (tendsto_congr' heq).mpr hrelax
  let relaxation : RelaxationToTwoTimeWindow extension delta := {
    threshold_pos := hdelta
    initial_above := by
      simpa [extension] using hseparated
    continuousAt_zero := by
      simpa [extension] using
        continuousAt_zero_rightLimitExtension distance rightLimit hlimit
    tendsto_zero := hextensionAtTop }
  obtain ⟨lower, upper, window⟩ :=
    relaxation.exists_robustKineticHittingWindow
  refine ⟨lower, upper, {
    lower_pos := window.lower_pos
    lower_le_upper := window.lower_le_upper
    beforeMargin := ?_
    afterMargin := ?_ }⟩
  · obtain ⟨margin, hmargin, hbefore⟩ := window.beforeMargin
    refine ⟨margin, hmargin, ?_⟩
    intro t ht htLower
    simpa [extension, rightLimitExtension, ht] using
      hbefore t ht htLower
  · obtain ⟨margin, hmargin, hafter⟩ := window.afterMargin
    refine ⟨margin, hmargin, ?_⟩
    have hupper : 0 < upper :=
      window.lower_pos.trans_le window.lower_le_upper
    simpa [extension, rightLimitExtension, hupper] using hafter

end

end ArchonPhysics.PositiveTimeTwoTimeKineticHittingBounds
