import FrozenTarget_9b8389ecbb8a0822
theorem M7.Transport.distance_invariant : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Transport.Recipe N), M7.Transport.distance (M7.Action.act g c) = M7.Transport.distance c
  intro N inst g c
  classical
  have hd (r : M7.Transport.Recipe N) :
      M7.Transport.distance r = M6.Pinned.distance (M7.Transport.LX r) := by
    calc
      M7.Transport.distance r = M6.Pinned.distance
          (M6.Spaces.logicalWords N
            (M6.Coordinates.coefficients N (M7.Supports.polynomial r.1))
            (M6.Coordinates.coefficients N (M7.Supports.polynomial r.2))) :=
        M6.ActualCSS.common_quantum_distance N _ _
      _ = M6.Pinned.distance (M7.Transport.LX r) := by
        rw [M7.Domain.coefficients_indicator, M7.Domain.coefficients_indicator]
        rfl
  rw [hd, hd]
  have hw := M7.Transport.weight_sets N g c
  cases he : M6.Pinned.distance (M7.Transport.LX c) with
  | none =>
      have hc := (M6.Pinned.distance_spec (2*N) (M7.Transport.LX c)).1.mp he
      apply (M6.Pinned.distance_spec (2*N) (M7.Transport.LX (M7.Action.act g c))).1.mpr
      apply Finset.ext
      intro v
      simp only [Finset.not_mem_empty, iff_false]
      intro hv
      have hm : M6.Pinned.weight v ∈ (M7.Transport.LX c).image M6.Pinned.weight :=
        hw ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩
      simpa [hc] using hm
  | some d =>
      have hc := (M6.Pinned.distance_spec (2*N) (M7.Transport.LX c)).2 d |>.mp he
      apply (M6.Pinned.distance_spec (2*N) (M7.Transport.LX (M7.Action.act g c))).2 d |>.mpr
      constructor
      · have hm : d ∈ (M7.Transport.LX c).image M6.Pinned.weight :=
          Finset.mem_image.mpr hc.1
        rw [← hw] at hm
        exact Finset.mem_image.mp hm
      · intro v hv
        have hm : M6.Pinned.weight v ∈ (M7.Transport.LX c).image M6.Pinned.weight :=
          hw ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩
        obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hm
        exact huw ▸ hc.2 u hu
