import FrozenTarget_ec650bb28e29d160
theorem M6.CSS.involution_distance : QuantumHarnessFrozenTarget := by
  intro m LX LZ J hJ hweight hmem
  have hback (v : M6.CSS.Vector m) (hv : v ∈ LZ) : J v ∈ LX := by
    apply (hmem (J v)).mpr
    simpa only [hJ v] using hv
  cases hd : M6.Pinned.distance LX with
  | none =>
      have hx : LX = ∅ := (M6.Pinned.distance_spec m LX).1.mp hd
      have hz : LZ = ∅ := by
        apply Finset.ext
        intro v
        constructor
        · intro hv
          have hvx := hback v hv
          rw [hx] at hvx
          exact False.elim (Finset.not_mem_empty (J v) hvx)
        · intro hv
          exact False.elim (Finset.not_mem_empty v hv)
      exact ((M6.Pinned.distance_spec m LZ).1.mpr hz).symm
  | some d =>
      obtain ⟨⟨v, hv, hw⟩, hmin⟩ := (M6.Pinned.distance_spec m LX).2 d |>.mp hd
      symm
      apply (M6.Pinned.distance_spec m LZ).2 d |>.mpr
      constructor
      · exact ⟨J v, (hmem v).mp hv, (hweight v).trans hw⟩
      · intro u hu
        have h := hmin (J u) (hback u hu)
        simpa only [hweight u] using h
