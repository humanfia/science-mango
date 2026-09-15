import FrozenTarget_bb2a4b366ce28e7b
theorem M7.OrbitResidual.insert_strict : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ (C bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N) (g : M7.Action.Record N), y ∈ M7.OrbitResidual.remaining C bases → (M7.OrbitResidual.remaining C (insert (M7.Action.act g y) bases)).card < (M7.OrbitResidual.remaining C bases).card
  intro N inst C bases y g hy
  rw [M7.OrbitResidual.insert_remaining N C bases (M7.Action.act g y),
    M7.OrbitResidual.orbit_action N y g]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
  intro heq
  have hm : y ∈ M7.OrbitResidual.remaining C bases \ M7.ActualOrbit.orbit y := by
    rw [heq]
    exact hy
  exact (Finset.mem_sdiff.mp hm).2 (M7.OrbitResidual.orbit_self N y)
