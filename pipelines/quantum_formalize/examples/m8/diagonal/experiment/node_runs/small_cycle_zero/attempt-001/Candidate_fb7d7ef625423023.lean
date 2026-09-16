import FrozenTarget_fb7d7ef625423023
theorem M8.Diagonal.small_cycle_zero : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (p : M6.Physical.Block N) (z : M6.Physical.Word N), p ≠ 0 → M6.Physical.syndrome N p p z = 0 → M6.Physical.wordWeight N z < 2 → z = 0
  intro N inst p z hp hs hw
  classical
  rcases z with ⟨a, b⟩
  change M6.Physical.weight N a + M6.Physical.weight N b < 2 at hw
  change M6.Physical.conv N p a + M6.Physical.conv N p b = 0 at hs
  have cz : M6.Physical.conv N p 0 = 0 := by
    funext i
    simp [M6.Physical.conv]
  have hd : ∀ j : ZMod N, M6.Physical.conv N p (M6.Physical.delta N j) ≠ 0 := by
    intro j h
    apply hp
    funext i
    have hi := congrFun h (i + j)
    simpa [M8.Diagonal.conv_delta] using hi
  have cases_weight :
      (M6.Physical.weight N a = 0 ∧ M6.Physical.weight N b = 0) ∨
      (M6.Physical.weight N a = 1 ∧ M6.Physical.weight N b = 0) ∨
      (M6.Physical.weight N a = 0 ∧ M6.Physical.weight N b = 1) := by
    omega
  rcases cases_weight with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ha0 := (M8.Diagonal.weight_zero N a).mp ha
    have hb0 := (M8.Diagonal.weight_zero N b).mp hb
    simp [ha0, hb0]
  · obtain ⟨j, ha⟩ := (M8.Diagonal.weight_one N a).mp ha
    have hb0 := (M8.Diagonal.weight_zero N b).mp hb
    rw [ha, hb0, cz, add_zero] at hs
    exact (hd j hs).elim
  · have ha0 := (M8.Diagonal.weight_zero N a).mp ha
    obtain ⟨j, hb⟩ := (M8.Diagonal.weight_one N b).mp hb
    rw [ha0, hb, cz, zero_add] at hs
    exact (hd j hs).elim
