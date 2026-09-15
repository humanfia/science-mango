import FrozenTarget_2fd7baa689d6f4b0
theorem M5.Character.bit_add : QuantumHarnessFrozenTarget := by
  change ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals
    unfold M5.Character.bitSign
    first
    | change (-1 : _) ^ (0 : ℕ) = (-1) ^ (0 : ℕ) * (-1) ^ (0 : ℕ)
    | change (-1 : _) ^ (1 : ℕ) = (-1) ^ (0 : ℕ) * (-1) ^ (1 : ℕ)
    | change (-1 : _) ^ (1 : ℕ) = (-1) ^ (1 : ℕ) * (-1) ^ (0 : ℕ)
    | change (-1 : _) ^ (0 : ℕ) = (-1) ^ (1 : ℕ) * (-1) ^ (1 : ℕ)
  all_goals norm_num
