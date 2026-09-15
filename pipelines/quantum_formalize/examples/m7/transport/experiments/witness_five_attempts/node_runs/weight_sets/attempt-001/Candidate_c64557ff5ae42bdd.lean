import FrozenTarget_c64557ff5ae42bdd
theorem M7.Transport.weight_sets : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  change (M7.Transport.LX (M7.Action.act g c)).image M6.Pinned.weight =
    (M7.Transport.LX c).image M6.Pinned.weight
  have h := M7.Transport.action_isometry N g c
  apply Finset.ext
  intro d
  constructor
  · intro hd
    obtain ⟨v, hv, hw⟩ := Finset.mem_image.mp hd
    obtain ⟨u, rfl⟩ := h.1.2 v
    apply Finset.mem_image.mpr
    refine ⟨u, (M7.Transport.x_logical N g c u).mp hv, ?_⟩
    exact (h.2 u).2.2.symm.trans hw
  · intro hd
    obtain ⟨v, hv, hw⟩ := Finset.mem_image.mp hd
    apply Finset.mem_image.mpr
    refine ⟨M7.Transport.Xmap g v, (M7.Transport.x_logical N g c v).mpr hv, ?_⟩
    exact (h.2 v).2.2.trans hw
