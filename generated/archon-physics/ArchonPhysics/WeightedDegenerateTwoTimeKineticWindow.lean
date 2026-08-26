import ArchonPhysics.MinimalTwoTimeKineticHittingWindow
import ArchonPhysics.WeightedDegenerateRelaxation

/-!
# A two-time kinetic window from weighted degenerate relaxation

An acoustically degenerate relaxation rate need not have a positive uniform
lower bound.  Positivity almost everywhere and an integrable initial error
still force the weighted error below every positive threshold.  If the
kinetic distance at integer times is majorized by that weighted error, this
single strict hit combines with continuity at time zero to give the robust
two-time window used by the release theorem.
-/

namespace ArchonPhysics.WeightedDegenerateTwoTimeKineticWindow

open MeasureTheory
open ArchonPhysics.MinimalTwoTimeKineticHittingWindow
open ArchonPhysics.TwoTimeKineticHittingBounds
open ArchonPhysics.WeightedDegenerateRelaxation

noncomputable section

variable {Alpha : Type*} [MeasurableSpace Alpha]

/-- Weighted decay at the integer kinetic times supplies the one strict hit
needed by `InitialSeparationAndStrictHit`. -/
theorem exists_initialSeparationAndStrictHit
    (distance : Real -> Real) (delta : Real)
    (mu : Measure Alpha) (rate error : Alpha -> Real)
    (hdelta : 0 < delta)
    (hthreshold : delta < distance 0)
    (hcontinuous : ContinuousAt distance 0)
    (hrate_measurable : Measurable rate)
    (herror_integrable : Integrable error mu)
    (hrate_nonneg : ∀ᵐ x ∂mu, 0 ≤ rate x)
    (hrate_pos : ∀ᵐ x ∂mu, 0 < rate x)
    (hmajorize : ∀ n : Nat,
      distance (n : Real) ≤ weightedDecayIntegral mu rate error n) :
    Nonempty (InitialSeparationAndStrictHit distance delta) := by
  obtain ⟨n, hn⟩ := exists_weightedDecayIntegral_lt mu rate error
    hrate_measurable herror_integrable hrate_nonneg hrate_pos hdelta
  have hstrict : distance (n : Real) < delta :=
    lt_of_le_of_lt (hmajorize n) hn
  have hn_ne : n ≠ 0 := by
    intro hn_zero
    subst n
    norm_num at hstrict
    exact (not_lt_of_ge (le_of_lt hthreshold)) hstrict
  have hn_pos : 0 < (n : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero hn_ne
  exact ⟨{
    hitTime := (n : Real)
    hitTime_pos := hn_pos
    threshold_below_initial := hthreshold
    continuousAt_zero := hcontinuous
    strict_hit := hstrict }⟩

/-- A weighted decay majorant with a rate positive almost everywhere yields
a finite positive robust hitting window, even if the rate approaches zero. -/
theorem exists_robustKineticHittingWindow
    (distance : Real -> Real) (delta : Real)
    (mu : Measure Alpha) (rate error : Alpha -> Real)
    (hdelta : 0 < delta)
    (hthreshold : delta < distance 0)
    (hcontinuous : ContinuousAt distance 0)
    (hrate_measurable : Measurable rate)
    (herror_integrable : Integrable error mu)
    (hrate_nonneg : ∀ᵐ x ∂mu, 0 ≤ rate x)
    (hrate_pos : ∀ᵐ x ∂mu, 0 < rate x)
    (hmajorize : ∀ n : Nat,
      distance (n : Real) ≤ weightedDecayIntegral mu rate error n) :
    exists lower upper : Real,
      RobustKineticHittingWindow distance delta lower upper := by
  obtain ⟨data⟩ := exists_initialSeparationAndStrictHit distance delta
    mu rate error hdelta hthreshold hcontinuous hrate_measurable
    herror_integrable hrate_nonneg hrate_pos hmajorize
  exact data.exists_robustKineticHittingWindow

end

end ArchonPhysics.WeightedDegenerateTwoTimeKineticWindow
