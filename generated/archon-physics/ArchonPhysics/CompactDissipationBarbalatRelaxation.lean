import ArchonPhysics.CompactDissipationThresholdRelaxation

/-!
# Compact dissipation relaxation without a monotone deficit

The compact-threshold argument only needs the dissipation to vanish in time;
the physical deficit itself need not be monotone.  A Barbalat-type argument
provides that vanishing from three genuine dynamical facts: nonnegative and
uniformly continuous dissipation, an entropy derivative equal to the
dissipation, and an entropy ceiling.
-/

namespace ArchonPhysics.CompactDissipationBarbalatRelaxation

open Filter Metric Set
open ArchonPhysics.CompactDissipationThresholdRelaxation

noncomputable section

/-- A uniformly continuous nonnegative entropy derivative must vanish at late
times when the entropy is bounded above. -/
theorem tendsto_dissipation_zero_of_uniformContinuousOn_of_bounded_entropy
    (dissipation entropy : Real -> Real) (entropyCeiling : Real)
    (hdissipationNonnegative : forall t, 0 <= t -> 0 <= dissipation t)
    (hdissipationUniformContinuous :
      UniformContinuousOn dissipation (Ici 0))
    (hentropyDeriv : forall t, 0 <= t ->
      HasDerivAt entropy (dissipation t) t)
    (hentropyUpper : forall t, 0 <= t ->
      entropy t <= entropyCeiling) :
    Tendsto dissipation atTop (nhds 0) := by
  have hentropyContinuous : ContinuousOn entropy (Ici (0 : Real)) := by
    intro t ht
    exact (hentropyDeriv t ht).continuousAt.continuousWithinAt
  have hentropyDifferentiable :
      DifferentiableOn Real entropy (interior (Ici (0 : Real))) := by
    intro t ht
    have ht0 : 0 <= t := by
      have : t ∈ Ioi (0 : Real) := by simpa only [interior_Ici] using ht
      exact le_of_lt this
    exact (hentropyDeriv t ht0).differentiableAt.differentiableWithinAt
  have hentropyDerivNonnegative : forall t,
      t ∈ interior (Ici (0 : Real)) -> 0 <= deriv entropy t := by
    intro t ht
    have ht0 : 0 <= t := by
      have : t ∈ Ioi (0 : Real) := by simpa only [interior_Ici] using ht
      exact le_of_lt this
    rw [(hentropyDeriv t ht0).deriv]
    exact hdissipationNonnegative t ht0
  have hentropyMonotone : MonotoneOn entropy (Ici (0 : Real)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hentropyContinuous
      hentropyDifferentiable hentropyDerivNonnegative
  let entropyPlus : Real -> Real := fun t => entropy (max 0 t)
  have hentropyPlusMonotone : Monotone entropyPlus := by
    intro s t hst
    exact hentropyMonotone
      (le_max_left 0 s) (le_max_left 0 t) (max_le_max_left 0 hst)
  have hentropyPlusBounded : BddAbove (range entropyPlus) := by
    refine ⟨entropyCeiling, ?_⟩
    rintro value ⟨t, rfl⟩
    exact hentropyUpper (max 0 t) (le_max_left 0 t)
  have hentropyPlusLimit :
      Tendsto entropyPlus atTop (nhds (⨆ t, entropyPlus t)) :=
    tendsto_atTop_ciSup hentropyPlusMonotone hentropyPlusBounded
  have hentropyIncrement (width : Real) (hwidth : 0 <= width) :
      Tendsto (fun t => entropy (t + width) - entropy t)
        atTop (nhds 0) := by
    have hshift := hentropyPlusLimit.comp
      (tendsto_atTop_add_const_right atTop width tendsto_id)
    have hsub : Tendsto
        (fun t => entropyPlus (t + width) - entropyPlus t)
        atTop (nhds 0) := by
      simpa only [Function.comp_apply, id_eq, sub_self] using
        hshift.sub hentropyPlusLimit
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop (0 : Real)] with t ht
    simp only [entropyPlus, max_eq_right ht,
      max_eq_right (add_nonneg ht hwidth)]
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hclose⟩ :=
    (Metric.uniformContinuousOn_iff.mp hdissipationUniformContinuous)
      (epsilon / 2) (half_pos hepsilon)
  let width : Real := delta / 2
  have hwidth : 0 < width := half_pos hdelta
  have hincrement := hentropyIncrement width hwidth.le
  have hthreshold : 0 < epsilon * width / 2 := by positivity
  obtain ⟨thresholdTime, hthresholdTime⟩ :=
    Metric.tendsto_atTop.mp hincrement
      (epsilon * width / 2) hthreshold
  refine ⟨max 0 thresholdTime, ?_⟩
  intro t ht
  have ht0 : 0 <= t := (le_max_left 0 thresholdTime).trans ht
  have htThreshold : thresholdTime <= t :=
    (le_max_right 0 thresholdTime).trans ht
  have hsmall := hthresholdTime t htThreshold
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (hdissipationNonnegative t ht0)]
  by_contra hnotSmall
  have hdissipationLarge : epsilon <= dissipation t := le_of_not_gt hnotSmall
  have hdissipationLower (x : Real) (hx : x ∈ Icc t (t + width)) :
      epsilon / 2 <= dissipation x := by
    have hx0 : 0 <= x := ht0.trans hx.1
    have hxtNonnegative : 0 <= x - t := sub_nonneg.mpr hx.1
    have hxtUpper : x - t <= width := by linarith [hx.2]
    have hxtDistance : dist x t < delta := by
      rw [Real.dist_eq, abs_of_nonneg hxtNonnegative]
      dsimp only [width] at hxtUpper
      linarith
    have hnear := hclose x hx0 t ht0 hxtDistance
    rw [Real.dist_eq] at hnear
    have hnegative := neg_lt_of_abs_lt hnear
    linarith
  have hintervalContinuous : ContinuousOn entropy (Icc t (t + width)) :=
    hentropyContinuous.mono fun x hx => ht0.trans hx.1
  have hintervalDifferentiable :
      DifferentiableOn Real entropy (interior (Icc t (t + width))) := by
    intro x hx
    have hxIcc : x ∈ Icc t (t + width) := interior_subset hx
    exact (hentropyDeriv x (ht0.trans hxIcc.1)).differentiableAt.differentiableWithinAt
  have hintervalDeriv : forall x,
      x ∈ interior (Icc t (t + width)) ->
        epsilon / 2 <= deriv entropy x := by
    intro x hx
    have hxIcc : x ∈ Icc t (t + width) := interior_subset hx
    rw [(hentropyDeriv x (ht0.trans hxIcc.1)).deriv]
    exact hdissipationLower x hxIcc
  have hgrowth :=
    (convex_Icc t (t + width)).mul_sub_le_image_sub_of_le_deriv
      hintervalContinuous hintervalDifferentiable hintervalDeriv
      t (by simp [hwidth.le]) (t + width) (by simp [hwidth.le])
      (by linarith [hwidth])
  have hgrowth' :
      epsilon * width / 2 <= entropy (t + width) - entropy t := by
    nlinarith [hgrowth]
  have hincrementNonnegative :
      0 <= entropy (t + width) - entropy t :=
    le_trans hthreshold.le hgrowth'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hincrementNonnegative] at hsmall
  exact (not_lt_of_ge hgrowth') hsmall

variable {State : Type*} [TopologicalSpace State] [T2Space State]

/-- Compact zero-set classification plus Barbalat dissipation decay makes
every continuous nonnegative physical deficit vanish, without assuming that
the deficit itself is monotone. -/
theorem tendsto_deficit_zero_of_compact_state_barbalat
    (states : Set State) (hstates : IsCompact states)
    (trajectory : Real -> State)
    (deficitState dissipationState : State -> Real)
    (entropy : Real -> Real) (entropyCeiling : Real)
    (htrajectory : forall t, 0 <= t -> trajectory t ∈ states)
    (hdeficitContinuous : ContinuousOn deficitState states)
    (hdissipationContinuous : ContinuousOn dissipationState states)
    (hdissipationNonnegative : forall state, state ∈ states ->
      0 <= dissipationState state)
    (hzero : forall state, state ∈ states ->
      dissipationState state = 0 -> deficitState state = 0)
    (hdeficitNonnegative : forall t, 0 <= t ->
      0 <= deficitState (trajectory t))
    (hdissipationTrajectoryUniformContinuous :
      UniformContinuousOn (fun t => dissipationState (trajectory t)) (Ici 0))
    (hentropyDeriv : forall t, 0 <= t ->
      HasDerivAt entropy (dissipationState (trajectory t)) t)
    (hentropyUpper : forall t, 0 <= t ->
      entropy t <= entropyCeiling) :
    Tendsto (fun t => deficitState (trajectory t)) atTop (nhds 0) := by
  have hdissipationTendsto :
      Tendsto (fun t => dissipationState (trajectory t)) atTop (nhds 0) :=
    tendsto_dissipation_zero_of_uniformContinuousOn_of_bounded_entropy
      (fun t => dissipationState (trajectory t)) entropy entropyCeiling
      (fun t ht => hdissipationNonnegative (trajectory t) (htrajectory t ht))
      hdissipationTrajectoryUniformContinuous hentropyDeriv hentropyUpper
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨kappa, hkappa, hbound⟩ :=
    exists_pos_dissipation_lower_bound_on_compact_level
      states hstates deficitState dissipationState
      hdeficitContinuous hdissipationContinuous
      hdissipationNonnegative hzero hepsilon
  obtain ⟨thresholdTime, hthresholdTime⟩ :=
    Metric.tendsto_atTop.mp hdissipationTendsto kappa hkappa
  refine ⟨max 0 thresholdTime, ?_⟩
  intro t ht
  have ht0 : 0 <= t := (le_max_left 0 thresholdTime).trans ht
  have htThreshold : thresholdTime <= t :=
    (le_max_right 0 thresholdTime).trans ht
  have hdissipationSmall := hthresholdTime t htThreshold
  have hdissipationNonnegativeAt :=
    hdissipationNonnegative (trajectory t) (htrajectory t ht0)
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (hdeficitNonnegative t ht0)]
  by_contra hnotSmall
  have hlevel : epsilon <= deficitState (trajectory t) := le_of_not_gt hnotSmall
  have hkappaLower := hbound (trajectory t) (htrajectory t ht0) hlevel
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg hdissipationNonnegativeAt] at hdissipationSmall
  exact (not_lt_of_ge hkappaLower) hdissipationSmall

end

end ArchonPhysics.CompactDissipationBarbalatRelaxation
