import FrozenTarget_7e78eeb180e012d8
theorem M7.Connectivity.connected_shift : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N) (s t : ZMod N), M7.Connectivity.connected (M7.Domain.shift c.1 s, M7.Domain.shift c.2 t) ↔ M7.Connectivity.connected c
  intro N inst c s t
  simp only [M7.Connectivity.connected, M7.Connectivity.difference_shift]
