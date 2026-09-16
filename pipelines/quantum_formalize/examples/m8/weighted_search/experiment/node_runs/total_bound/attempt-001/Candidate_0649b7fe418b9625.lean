import FrozenTarget_0649b7fe418b9625
theorem M8.WeightedSearch.total_bound : QuantumHarnessFrozenTarget := by
  change ∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (C overhead : ℕ), (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.find test).calls * overhead + (M8.WeightedSearch.find test).work ≤ n * (overhead + C)
  intro n α test C overhead hC
  have hcalls : (M8.WeightedSearch.find test).calls ≤ n := by
    calc
      (M8.WeightedSearch.find test).calls = (M8.FiniteSearch.find (fun i => (test i).1)).2 :=
        congrArg Prod.snd (M8.WeightedSearch.find_projection n α test)
      _ ≤ n := M8.FiniteSearch.find_bound n α (fun i => (test i).1)
  calc
    (M8.WeightedSearch.find test).calls * overhead + (M8.WeightedSearch.find test).work ≤ n * overhead + n * C :=
      Nat.add_le_add (Nat.mul_le_mul_right overhead hcalls) (M8.WeightedSearch.find_callback_bound n α test C hC)
    _ = n * (overhead + C) := (Nat.mul_add n overhead C).symm
