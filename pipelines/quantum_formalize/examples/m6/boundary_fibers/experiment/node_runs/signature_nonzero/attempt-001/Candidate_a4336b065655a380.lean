import FrozenTarget_a4336b065655a380
theorem M6.BoundaryFibers.signature_nonzero : QuantumHarnessFrozenTarget := by
  change ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → M6.Cyclic.signature a b M ≠ 0
  intro a b M hM hs
  have hd := (M6.Cyclic.signature_divides a b M).2.2
  apply hM
  simpa [hs] using hd
