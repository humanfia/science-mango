import M8SequentialResources

theorem M8.SequentialResources.actual_prefix_charge : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M8.SequentialStore.prefixCharge (M8.SequentialResources.primitiveCharge N) (M8.WholeResources.run c).charges = M8.WholeResources.indexedWork c * M8.SequentialResources.primitiveCharge N := by
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

theorem M8.SequentialResources.sequential_bound : ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (w : ℕ), 0 < w → M8.PhysicalBridge.Valid w c → M8.SequentialResources.sequentialCharge c ≤ 6000000000000*(N+1)^12 := by
  intro N inst c w hw hvalid
  have hwork := M8.WholeResources.indexed_work_bound N c w hw hvalid
  have haccess := M8.SequentialStore.access_envelope N
  have htag := M8.SequentialStore.tag_setup_bound N
  let q : ℕ := (N + 1)^6
  change M8.WholeResources.indexedWork c ≤ 225000 * q at hwork
  change M8.SequentialStore.accessCharge N ≤ 3000000 * q at haccess
  change M8.SequentialStore.tagSetupCharge N ≤ 11000000 * q at htag
  have hq : 1 ≤ q := by
    have hpos : 0 < q := by dsimp [q]; positivity
    omega
  have hsmall : q ≤ q * q := by
    simpa using Nat.mul_le_mul_left q hq
  have hprimitive : M8.SequentialResources.primitiveCharge N ≤ 8 * (3000000 * q + 1) := by
    unfold M8.SequentialResources.primitiveCharge
    exact Nat.mul_le_mul_left 8 (Nat.add_le_add_right haccess 1)
  have hproduct := Nat.mul_le_mul hwork hprimitive
  have hpower : (N + 1)^12 = q * q := by
    dsimp [q]
    rw [← pow_add]
  unfold M8.SequentialResources.sequentialCharge
  rw [M8.SequentialResources.actual_prefix_charge N c, hpower]
  calc
    M8.SequentialStore.tagSetupCharge N + M8.WholeResources.indexedWork c * M8.SequentialResources.primitiveCharge N
        ≤ 11000000 * q + (225000 * q) * (8 * (3000000 * q + 1)) := Nat.add_le_add htag hproduct
    _ ≤ 6000000000000 * (q * q) := by nlinarith only [hsmall]
#print axioms M8.SequentialResources.actual_prefix_charge
#print axioms M8.SequentialResources.sequential_bound
