import FrozenTarget_c72a5e8330a5bddc
theorem M7.Factorized.exact_target_card : QuantumHarnessFrozenTarget := by
  intro U S T instU instS instT X Y leftImage rightImage x y
  classical
  unfold M7.Factorized.exactTargetNumerator
  rw [M7.Factorized.numerator_record_card]
  unfold M7.Factorized.records M7.Factorized.count
  apply congrArg Finset.card
  ext r
  simp
