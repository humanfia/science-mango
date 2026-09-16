import FrozenTarget_b1a8080b326ff6c7
theorem M8.OptimizerResources.scatter_capacity : QuantumHarnessFrozenTarget := by
  intro N inst a b pins character hspan start i hi k addr
  have hbounds := M6.Transfer.actual_layer_intermediates
    (M6.ActualTransfer.span a b) N
    (M8.OptimizerResources.weight N a b pins character) start i k addr
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).1)
    (fun j m t => (M8.OptimizerResources.weight_bounds N a b pins character j m t).2)
  have hpow : (8 : ℕ) ^ (i + 1) ≤ 8 ^ N := by
    gcongr <;> omega
  have hpositive : 0 < (2 : ℕ) ^ M6.ActualTransfer.span a b := by
    positivity
  have hone : 1 ≤ (2 : ℕ) ^ M6.ActualTransfer.span a b := hpositive
  have hmul : (8 : ℕ) ^ N ≤ 2 ^ M6.ActualTransfer.span a b * 8 ^ N := by
    calc
      8 ^ N = 1 * 8 ^ N := (one_mul _).symm
      _ ≤ 2 ^ M6.ActualTransfer.span a b * 8 ^ N := Nat.mul_le_mul_right _ hone
  have hcapacity : (8 : ℕ) ^ (i + 1) < 2 ^ (4 * (N + 1)) :=
    lt_of_le_of_lt (le_trans hpow hmul)
      (M8.Cutoff.coefficient_capacity N (M6.ActualTransfer.span a b) hspan)
  constructor
  · exact lt_of_le_of_lt hbounds.1 hcapacity
  · intro e
    exact lt_of_le_of_lt (hbounds.2 e) hcapacity
