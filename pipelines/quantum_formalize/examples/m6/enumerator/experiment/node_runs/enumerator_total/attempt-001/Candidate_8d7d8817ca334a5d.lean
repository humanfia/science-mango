import FrozenTarget_8d7d8817ca334a5d
theorem M6.Pinned.enumerator_total : QuantumHarnessFrozenTarget := by
  classical
  intro m L
  change (Polynomial.evalRingHom (1 : ℤ)) (M6.Pinned.enumerator L (M6.Pinned.free m)) = (L.card : ℤ)
  simp [M6.Pinned.enumerator, M6.Pinned.agrees, M6.Pinned.free]
