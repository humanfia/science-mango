import FrozenTarget_42d4e76eebdc7ab0
theorem M7.Transport.distance_invariant : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  have hd : ∀ r : M7.Transport.Recipe N,
      M7.Transport.distance r = M6.Pinned.distance (M7.Transport.LX r) := by
    intro r
    unfold M7.Transport.distance
    simp only [M7.Domain.coefficients_indicator]
    exact M6.ActualCSS.common_quantum_distance N
      (M7.Supports.indicator r.1) (M7.Supports.indicator r.2)
  rw [hd, hd]
  have hw := M7.Transport.weight_sets N g c
  cases he : M6.Pinned.distance (M7.Transport.LX c) with
  | none =>
      apply (M6.Pinned.distance_spec (2*N) (M7.Transport.LX (M7.Action.act g c))).1.mpr
      have hc := (M6.Pinned.distance_spec (2*N) (M7.Transport.LX c)).1.mp he
      have hi : (M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight = ∅ := by
        rw [hw, hc]
        simp
      exact Finset.image_eq_empty.mp hi
  | some d =>
      apply (M6.Pinned.distance_spec (2*N) (M7.Transport.LX (M7.Action.act g c))).2 d |>.mpr
      obtain ⟨⟨v, hv, hvd⟩, hmin⟩ :=
        (M6.Pinned.distance_spec (2*N) (M7.Transport.LX c)).2 d |>.mp he
      constructor
      · have hi : d ∈ (M7.Transport.LX c).image M6.Pinned.weight :=
          Finset.mem_image.mpr ⟨v, hv, hvd⟩
        rw [← hw] at hi
        exact Finset.mem_image.mp hi
      · intro v hv
        have hi : M6.Pinned.weight v ∈
            (M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight :=
          Finset.mem_image.mpr ⟨v, hv, rfl⟩
        rw [hw] at hi
        obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hi
        exact (hmin u hu).trans_eq huv
