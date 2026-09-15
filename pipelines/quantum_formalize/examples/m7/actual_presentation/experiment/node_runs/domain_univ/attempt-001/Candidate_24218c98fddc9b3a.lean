import FrozenTarget_24218c98fddc9b3a
theorem M7.ActualPresentation.domain_univ : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N hN
  classical
  apply Finset.ext
  intro a
  rw [M7.Presentation.domain_membership]
  simp
