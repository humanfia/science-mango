import FrozenTarget_1588f581e95f74b9
theorem M8.SequentialResources.actual_prefix_charge : QuantumHarnessFrozenTarget := by
  intro N inst c
  have hrepeat (unit k : ℕ) :
      M8.SequentialStore.repeatCharge unit k = k * unit := by
    induction k with
    | zero => simp [M8.SequentialStore.repeatCharge]
    | succ k ih =>
        simp [M8.SequentialStore.repeatCharge, ih, Nat.succ_mul, Nat.add_comm]
  have hfold (unit : ℕ) (xs : List ℕ) (a : ℕ) :
      xs.foldl (fun acc k => acc + k * unit) a = a + xs.sum * unit := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih =>
        simp [List.foldl, ih, Nat.add_mul, Nat.add_assoc]
  have hsum (xs : List ℕ) (a : ℕ) :
      xs.foldl (fun acc k => acc + k) a = a + xs.sum := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp [List.foldl, ih, Nat.add_assoc]
  simp [M8.SequentialStore.prefixCharge, M8.WholeResources.indexedWork,
    hrepeat, hfold, hsum]
