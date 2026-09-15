import FrozenTarget_b3ac94f2ffc8cb78
theorem M7.OrbitFibers.orbit_count_div : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c P
  rw [M7.OrbitFibers.action_count_product G X c P]
  constructor
  · exact Nat.mul_div_cancel _ (M7.OrbitFibers.stabilizer_positive G X c)
  · exact ⟨M7.OrbitFibers.orbitCount G c P, Nat.mul_comm _ _⟩
