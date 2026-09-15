import FrozenTarget_d73e60b29978b517
theorem M7.OrbitResidual.orbit_self : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, c ∈ M7.ActualOrbit.orbit c
  intro N inst c
  classical
  change c ∈ Finset.univ.image (fun g : M7.Action.Record N => M7.Action.act g c)
  exact Finset.mem_image.mpr ⟨M7.Action.identity N, Finset.mem_univ _, M7.Action.act_identity N c⟩
