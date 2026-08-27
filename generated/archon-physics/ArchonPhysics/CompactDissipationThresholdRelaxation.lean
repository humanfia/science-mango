import ArchonPhysics.BoundedEntropyThresholdRelaxation

/-!
# Compact-state threshold dissipation and relaxation

A compact invariant state set turns a qualitative classification of the zero
set of a continuous nonnegative dissipation into the threshold coercivity
needed for entropy relaxation.  The theorem is independent of finite
dimensionality: it applies in particular to a norm-precompact orbit in a
canonical `L-infinity` kinetic phase space.
-/

namespace ArchonPhysics.CompactDissipationThresholdRelaxation

open Filter Set
open ArchonPhysics.BoundedEntropyThresholdRelaxation

noncomputable section

variable {State : Type*} [TopologicalSpace State] [T2Space State]

/-- On a compact state set, a continuous nonnegative dissipation whose zero
set is contained in the zero set of a continuous deficit has a strictly
positive minimum on every positive deficit level. -/
theorem exists_pos_dissipation_lower_bound_on_compact_level
    (states : Set State) (hstates : IsCompact states)
    (deficit dissipation : State -> Real)
    (hdeficit : ContinuousOn deficit states)
    (hdissipation : ContinuousOn dissipation states)
    (hdissipationNonnegative : forall state, state ∈ states ->
      0 <= dissipation state)
    (hzero : forall state, state ∈ states ->
      dissipation state = 0 -> deficit state = 0)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists kappa : Real, 0 < kappa /\
      forall state, state ∈ states -> epsilon <= deficit state ->
        kappa <= dissipation state := by
  let level : Set State :=
    states ∩ {state | epsilon <= deficit state}
  have hlevelClosed : IsClosed level := by
    change IsClosed (states ∩ deficit ⁻¹' Ici epsilon)
    exact hdeficit.preimage_isClosed_of_isClosed
      hstates.isClosed isClosed_Ici
  have hlevelCompact : IsCompact level := by
    exact hstates.of_isClosed_subset hlevelClosed inter_subset_left
  have mem_level (state : State) (hstate : state ∈ states)
      (hstateDeficit : epsilon <= deficit state) : state ∈ level :=
    ⟨hstate, hstateDeficit⟩
  by_cases hlevelNonempty : level.Nonempty
  · obtain ⟨minimizer, hminimizer, hminimum⟩ :=
      hlevelCompact.exists_isMinOn hlevelNonempty
        (hdissipation.mono inter_subset_left)
    have hminimumNonnegative : 0 <= dissipation minimizer :=
      hdissipationNonnegative minimizer hminimizer.1
    have hminimumNonzero : dissipation minimizer ≠ 0 := by
      intro hvanish
      have hdeficitZero := hzero minimizer hminimizer.1 hvanish
      have hlevelDeficit : epsilon <= deficit minimizer := hminimizer.2
      rw [hdeficitZero] at hlevelDeficit
      exact (not_le_of_gt hepsilon) hlevelDeficit
    have hminimumPositive : 0 < dissipation minimizer :=
      lt_of_le_of_ne hminimumNonnegative (Ne.symm hminimumNonzero)
    refine ⟨dissipation minimizer, hminimumPositive, ?_⟩
    intro state hstate hstateDeficit
    exact hminimum (mem_level state hstate hstateDeficit)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro state hstate hstateDeficit
    exact (hlevelNonempty
      ⟨state, mem_level state hstate hstateDeficit⟩).elim

/-- Compactness and zero-set classification discharge the entire
threshold-dissipation premise of the bounded-entropy relaxation theorem.
No linear spectral gap and no finite-dimensional state space are used. -/
theorem tendsto_deficit_zero_of_compact_state_dissipation
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
    (hdeficitAntitone :
      AntitoneOn (fun t => deficitState (trajectory t)) (Ici 0))
    (hentropyDeriv : forall t, 0 <= t ->
      HasDerivAt entropy (dissipationState (trajectory t)) t)
    (hentropyUpper : forall t, 0 <= t ->
      entropy t <= entropyCeiling) :
    Tendsto (fun t => deficitState (trajectory t)) atTop (nhds 0) := by
  apply tendsto_distance_zero
    (fun t => deficitState (trajectory t)) entropy
      (fun t => dissipationState (trajectory t)) entropyCeiling
      hdeficitNonnegative hdeficitAntitone hentropyDeriv hentropyUpper
  intro epsilon hepsilon
  obtain ⟨kappa, hkappa, hbound⟩ :=
    exists_pos_dissipation_lower_bound_on_compact_level
      states hstates deficitState dissipationState
      hdeficitContinuous hdissipationContinuous
      hdissipationNonnegative hzero hepsilon
  refine ⟨kappa, hkappa, ?_⟩
  intro t ht hlevel
  exact hbound (trajectory t) (htrajectory t ht) hlevel

end

end ArchonPhysics.CompactDissipationThresholdRelaxation
