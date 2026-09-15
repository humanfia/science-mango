import FrozenTarget_68651e9db6f6ceb6
theorem M6.Physical.conv_assoc : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a b c
  funext x
  simp only [M6.Physical.conv, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_bij (fun k _ => j + k) ?_ ?_ ?_ ?_
  · intro k hk
    simp
  · intro u hu v hv huv
    exact add_left_cancel huv
  · intro k hk
    refine ⟨k - j, by simp, ?_⟩
    abel
  · intro k hk
    have h₁ : j + k - j = k := by abel
    have h₂ : x - (j + k) = x - j - k := by abel
    simp only [h₁, h₂, mul_assoc]
