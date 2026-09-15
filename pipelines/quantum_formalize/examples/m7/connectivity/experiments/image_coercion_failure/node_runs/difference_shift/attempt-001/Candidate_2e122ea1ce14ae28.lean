import FrozenTarget_2e122ea1ce14ae28
theorem M7.Connectivity.difference_shift : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (s : ZMod N), M7.Connectivity.differences (M7.Domain.shift A s) = M7.Connectivity.differences A
  intro N inst A s
  ext x
  simp [M7.Connectivity.differences, M7.Domain.shift, Finset.mem_image,
    exists_and_left, exists_and_right, add_sub_add_right_eq_sub] <;> aesop
