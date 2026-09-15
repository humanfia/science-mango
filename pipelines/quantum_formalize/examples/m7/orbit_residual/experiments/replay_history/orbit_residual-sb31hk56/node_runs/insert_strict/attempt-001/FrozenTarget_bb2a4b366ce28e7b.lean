import M7OrbitResidual

theorem M7.OrbitResidual.insert_remaining : ∀ (N : ℕ) [NeZero N], ∀ (C bases : Finset (M7.Action.Recipe N)) (c : M7.Action.Recipe N), M7.OrbitResidual.remaining C (insert c bases) = M7.OrbitResidual.remaining C bases \ M7.ActualOrbit.orbit c := by
  classical
  intro N inst C bases c
  ext x
  simp only [M7.OrbitResidual.remaining, M7.OrbitResidual.covered,
    Finset.biUnion_insert, Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem M7.OrbitResidual.orbit_action : ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), M7.ActualOrbit.orbit (M7.Action.act g c) = M7.ActualOrbit.orbit c := by
  intro N inst c g
  classical
  unfold M7.ActualOrbit.orbit
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨M7.Action.compose h g, ?_⟩
    rw [M7.Action.act_compose]
    exact hh
  · rintro ⟨h, hh⟩
    refine ⟨M7.Action.compose h (M7.Action.inverse g), ?_⟩
    rw [M7.Action.act_compose, M7.Action.act_inverse]
    exact hh

theorem M7.OrbitResidual.orbit_self : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, c ∈ M7.ActualOrbit.orbit c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, c ∈ M7.ActualOrbit.orbit c
  intro N inst c
  classical
  change c ∈ Finset.univ.image (fun g : M7.Action.Record N => M7.Action.act g c)
  exact Finset.mem_image.mpr ⟨M7.Action.identity N, Finset.mem_univ _, M7.Action.act_identity N c⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (C bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N) (g : M7.Action.Record N), y ∈ M7.OrbitResidual.remaining C bases → (M7.OrbitResidual.remaining C (insert (M7.Action.act g y) bases)).card < (M7.OrbitResidual.remaining C bases).card
