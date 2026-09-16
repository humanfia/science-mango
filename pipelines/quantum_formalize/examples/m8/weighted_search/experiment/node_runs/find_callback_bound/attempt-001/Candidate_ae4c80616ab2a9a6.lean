import FrozenTarget_ae4c80616ab2a9a6
theorem M8.WeightedSearch.find_callback_bound : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (C : ℕ), (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.find test).work ≤ n * C
  intro n α test C hC
  have hcalls : (M8.WeightedSearch.find test).calls ≤ n := by
    calc
      (M8.WeightedSearch.find test).calls = (M8.FiniteSearch.find (fun i => (test i).1)).2 :=
        congrArg Prod.snd (M8.WeightedSearch.find_projection n α test)
      _ ≤ n := M8.FiniteSearch.find_bound n α (fun i => (test i).1)
  exact le_trans (M8.WeightedSearch.callback_bound n α test 0 n C hC)
    (Nat.mul_le_mul_right C hcalls)
