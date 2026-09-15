import FrozenTarget_c912471f42b4b538
theorem M7.ActualPresentation.realize_decode : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (a : M7.ActualPresentation.Encoded N), M7.Presentation.realize (M7.ActualPresentation.leftImage c) (M7.ActualPresentation.rightImage c) a = M7.Action.act (M7.ActualPresentation.decode a) c
  intro N inst c a
  rfl
