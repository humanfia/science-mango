import FrozenTarget_0d1e6dda8110f9d2
theorem M6.CSS.logical_pauli_components : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ p
  classical
  simp only [M6.CSS.logicalPaulis, M6.CSS.logical, Finset.mem_filter,
    Finset.mem_product, Finset.mem_sdiff] <;> tauto
