import M6Physical

theorem M6.Physical.conv_assoc : ∀ (N : ℕ) [NeZero N] (a b c : M6.Physical.Block N), M6.Physical.conv N a (M6.Physical.conv N b c) = M6.Physical.conv N (M6.Physical.conv N a b) c := by
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

theorem M6.Physical.conv_comm : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Physical.conv N a b = M6.Physical.conv N b a := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N), M6.Physical.conv N a b = M6.Physical.conv N b a
  intro N inst a b
  classical
  funext i
  unfold M6.Physical.conv
  refine Finset.sum_bij (fun r _ => i - r) ?_ ?_ ?_ ?_
  · intro r hr
    exact Finset.mem_univ _
  · intro r hr s hs h
    simpa only [sub_sub_cancel] using congrArg (fun t => i - t) h
  · intro r hr
    exact ⟨i - r, Finset.mem_univ _, sub_sub_cancel i r⟩
  · intro r hr
    simp only [sub_sub_cancel, mul_comm]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b h : M6.Physical.Block N), M6.Physical.syndrome N a b (M6.Physical.boundary N a b h) = 0
