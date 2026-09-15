import M7OrbitResidual

theorem M7.OrbitResidual.covered_membership : ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), y ∈ M7.OrbitResidual.covered bases ↔ ∃ c ∈ bases, y ∈ M7.ActualOrbit.orbit c := by
  intro N inst bases y
  classical
  simp only [M7.OrbitResidual.covered, Finset.mem_biUnion]

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

theorem M7.OrbitResidual.remaining_partition : ∀ (N : ℕ) [NeZero N], ∀ C0 C1 bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.remaining (C0 ∪ C1) bases = M7.OrbitResidual.remaining C0 bases ∪ M7.OrbitResidual.remaining C1 bases := by
  classical
  intro N inst C0 C1 bases
  unfold M7.OrbitResidual.remaining
  apply Finset.ext
  intro x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h0 | h1, h⟩
    · exact Or.inl ⟨h0, h⟩
    · exact Or.inr ⟨h1, h⟩
  · rintro (⟨h0, h⟩ | ⟨h1, h⟩)
    · exact ⟨Or.inl h0, h⟩
    · exact ⟨Or.inr h1, h⟩

theorem M7.OrbitResidual.insert_strict : ∀ (N : ℕ) [NeZero N], ∀ (C bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N) (g : M7.Action.Record N), y ∈ M7.OrbitResidual.remaining C bases → (M7.OrbitResidual.remaining C (insert (M7.Action.act g y) bases)).card < (M7.OrbitResidual.remaining C bases).card := by
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

theorem M7.OrbitResidual.orbit_disjoint : ∀ (N : ℕ) [NeZero N], ∀ c d : M7.Action.Recipe N, Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit d) ↔ d ∉ M7.ActualOrbit.orbit c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c d : M7.Action.Recipe N, Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit d) ↔ d ∉ M7.ActualOrbit.orbit c
  intro N inst c d
  classical
  constructor
  · intro h hd
    have hself : d ∈ M7.ActualOrbit.orbit d := by
      unfold M7.ActualOrbit.orbit
      exact Finset.mem_image.mpr ⟨M7.Action.identity N, Finset.mem_univ _, M7.Action.act_identity N d⟩
    exact Finset.disjoint_left.mp h hd hself
  · intro hd
    apply Finset.disjoint_left.mpr
    intro y hc hy
    apply hd
    unfold M7.ActualOrbit.orbit at hc hy ⊢
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc hy ⊢
    obtain ⟨g, hg⟩ := hc
    obtain ⟨h, hh⟩ := hy
    refine ⟨M7.Action.compose (M7.Action.inverse h) g, ?_⟩
    rw [M7.Action.act_compose, hg, ← hh, M7.Action.act_inverse]

theorem M7.OrbitResidual.fresh_separated : ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N) (g : M7.Action.Record N), M7.OrbitResidual.Separated bases → y ∉ M7.OrbitResidual.covered bases → M7.OrbitResidual.Separated (insert (M7.Action.act g y) bases) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N) (g : M7.Action.Record N), M7.OrbitResidual.Separated bases → y ∉ M7.OrbitResidual.covered bases → M7.OrbitResidual.Separated (insert (M7.Action.act g y) bases)
  intro N inst bases y g hsep hfresh
  classical
  have hnew : ∀ c ∈ bases, Disjoint (M7.ActualOrbit.orbit c) (M7.ActualOrbit.orbit (M7.Action.act g y)) := by
    intro c hc
    rw [M7.OrbitResidual.orbit_action N y g]
    apply (M7.OrbitResidual.orbit_disjoint N c y).mpr
    intro hy
    exact hfresh ((M7.OrbitResidual.covered_membership N bases y).mpr ⟨c, hc, hy⟩)
  unfold M7.OrbitResidual.Separated at hsep ⊢
  intro c hc d hd hcd
  rcases Finset.mem_insert.mp hc with rfl | hc
  · rcases Finset.mem_insert.mp hd with rfl | hd
    · exact (hcd rfl).elim
    · exact (hnew d hd).symm
  · rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hnew c hc
    · exact hsep c hc d hd hcd
#print axioms M7.OrbitResidual.covered_membership
#print axioms M7.OrbitResidual.insert_remaining
#print axioms M7.OrbitResidual.orbit_action
#print axioms M7.OrbitResidual.orbit_disjoint
#print axioms M7.OrbitResidual.fresh_separated
#print axioms M7.OrbitResidual.orbit_self
#print axioms M7.OrbitResidual.insert_strict
#print axioms M7.OrbitResidual.remaining_partition
