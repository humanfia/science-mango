import FrozenTarget_45e5fc86807d5a10
theorem M6.CSS.involution_distance : QuantumHarnessFrozenTarget := by
  intro m LX LZ J hJ hw hmem
  have hback : ∀ v, v ∈ LZ → J v ∈ LX := by
    intro v hv
    apply (hmem (J v)).mpr
    simpa only [hJ v] using hv
  cases hd : M6.Pinned.distance LX with
  | none =>
      have hX : LX = ∅ := (M6.Pinned.distance_spec m LX).1.mp hd
      have hZ : LZ = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro v hv
        have hx := hback v hv
        simpa only [hX, Finset.not_mem_empty] using hx
      exact ((M6.Pinned.distance_spec m LZ).1.mpr hZ).symm
  | some d =>
      obtain ⟨⟨v, hv, hvw⟩, hmin⟩ := (M6.Pinned.distance_spec m LX).2 d |>.mp hd
      symm
      apply (M6.Pinned.distance_spec m LZ).2 d |>.mpr
      constructor
      · exact ⟨J v, (hmem v).mp hv, (hw v).trans hvw⟩
      · intro u hu
        have h := hmin (J u) (hback u hu)
        simpa only [hw u] using h
