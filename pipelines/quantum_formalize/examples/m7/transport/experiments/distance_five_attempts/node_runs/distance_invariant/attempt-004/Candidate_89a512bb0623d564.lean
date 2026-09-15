import FrozenTarget_89a512bb0623d564
theorem M7.Transport.distance_invariant : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  have hd : ∀ r : M7.Transport.Recipe N,
      M7.Transport.distance r = M6.Pinned.distance (M7.Transport.LX r) := by
    intro r
    let a := M6.Coordinates.coefficients N (M7.Supports.polynomial r.1)
    let b := M6.Coordinates.coefficients N (M7.Supports.polynomial r.2)
    change M6.CSS.quantumDistance
      (M6.Spaces.boundaryWords N a b)
      (M6.Spaces.cycleWords N a b)
      (M6.Character.subspaceWords (M6.Spaces.D N a b))
      (M6.Character.dualWords (M6.Spaces.B N a b)) = _
    rw [M6.ActualCSS.common_quantum_distance]
    dsimp [a, b]
    simp only [M7.Domain.coefficients_indicator]
    rfl
  rw [hd, hd]
  have hw := M7.Transport.weight_sets N g c
  let L := M7.Transport.LX (M7.Action.act g c)
  let K := M7.Transport.LX c
  change M6.Pinned.distance L = M6.Pinned.distance K
  change L.image M6.Pinned.weight = K.image M6.Pinned.weight at hw
  cases hk : M6.Pinned.distance K with
  | none =>
      have he : K = ∅ := (M6.Pinned.distance_spec (2*N) K).1.mp hk
      have hl : L = ∅ := Finset.image_eq_empty.mp (by simpa [he] using hw)
      exact (M6.Pinned.distance_spec (2*N) L).1.mpr hl
  | some d =>
      have hs := (M6.Pinned.distance_spec (2*N) K).2 d |>.mp hk
      apply (M6.Pinned.distance_spec (2*N) L).2 d |>.mpr
      constructor
      · obtain ⟨v, hv, hvd⟩ := hs.1
        have hm : d ∈ K.image M6.Pinned.weight := Finset.mem_image.mpr ⟨v, hv, hvd⟩
        rw [← hw] at hm
        exact Finset.mem_image.mp hm
      · intro v hv
        have hm : M6.Pinned.weight v ∈ K.image M6.Pinned.weight := by
          rw [← hw]
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
        obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hm
        rw [← huv]
        exact hs.2 u hu
