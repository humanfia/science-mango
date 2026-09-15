import FrozenTarget_93cedf99163cbcb2
theorem M7.CanonicalOuter.indices_nonempty : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], (M7.CanonicalOuter.indices N).Nonempty
  intro N inst
  obtain ⟨i, hi, _⟩ := M7.CanonicalOuter.unit_index N (1 : (ZMod N)ˣ) false
  exact ⟨i, hi⟩
