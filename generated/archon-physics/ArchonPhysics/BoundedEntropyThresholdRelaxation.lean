import ArchonPhysics.BoundedEntropyDissipationStrictHit

/-!
# Relaxation from threshold-by-threshold entropy dissipation

Linear entropy coercivity is stronger than necessary.  If the nonnegative
distance is nonincreasing and, above every positive distance threshold, the
entropy production has some positive lower bound, boundedness of the entropy
forces the distance to zero.  The lower bound may depend arbitrarily on the
threshold.
-/

namespace ArchonPhysics.BoundedEntropyThresholdRelaxation

open Filter Set
open ArchonPhysics.BoundedEntropyDissipationStrictHit

noncomputable section

/-- Threshold-by-threshold positive entropy production plus monotonicity gives
full relaxation, without a linear or power-law coercivity estimate. -/
theorem tendsto_distance_zero
    (distance entropy production : Real -> Real)
    (entropyCeiling : Real)
    (hdistance_nonnegative : forall t, 0 <= t -> 0 <= distance t)
    (hdistance_antitone : AntitoneOn distance (Ici 0))
    (hentropy_deriv : forall t, 0 <= t ->
      HasDerivAt entropy (production t) t)
    (hentropy_upper : forall t, 0 <= t -> entropy t <= entropyCeiling)
    (hthreshold_dissipation : forall epsilon : Real, 0 < epsilon ->
      exists kappa : Real, 0 < kappa /\ forall t, 0 <= t ->
        epsilon <= distance t -> kappa <= production t) :
    Tendsto distance atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨kappa, hkappa, hproduction⟩ :=
    hthreshold_dissipation epsilon hepsilon
  by_cases hinitial : distance 0 < epsilon
  · refine ⟨0, ?_⟩
    intro t ht
    have ht_nonnegative : 0 <= t := ht
    have hdistance_le : distance t <= distance 0 :=
      hdistance_antitone (Set.mem_Ici.mpr (le_refl 0))
        (Set.mem_Ici.mpr ht_nonnegative) ht
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (hdistance_nonnegative t ht_nonnegative)]
    exact hdistance_le.trans_lt hinitial
  · have hinitial_le : epsilon <= distance 0 := le_of_not_gt hinitial
    obtain ⟨hitTime, hitTime_pos, hhit⟩ :=
      exists_strict_hit distance entropy production epsilon kappa
        entropyCeiling hkappa hinitial_le hentropy_deriv
        hproduction hentropy_upper
    refine ⟨hitTime, ?_⟩
    intro t ht
    have ht_nonnegative : 0 <= t := hitTime_pos.le.trans ht
    have hdistance_le : distance t <= distance hitTime :=
      hdistance_antitone (Set.mem_Ici.mpr hitTime_pos.le)
        (Set.mem_Ici.mpr ht_nonnegative) ht
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (hdistance_nonnegative t ht_nonnegative)]
    exact hdistance_le.trans_lt hhit

end

end ArchonPhysics.BoundedEntropyThresholdRelaxation
