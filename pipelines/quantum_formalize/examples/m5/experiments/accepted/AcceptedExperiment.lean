import M5Foundation

theorem M5.cutoff_gt_period : ∀ (w T : ℕ), 2 ≤ w → 0 < T → T < M5.packingCutoff w T := by
  change ∀ (w T : ℕ), 2 ≤ w → 0 < T → T < M5.packingCutoff w T
  intro w T hw hT
  unfold M5.packingCutoff
  have h₁ : 2 * T ≤ w * T := Nat.mul_le_mul_right T hw
  have h₂ : w * T ≤ w * T * (T + 2) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (w * T) (show 1 ≤ T + 2 by omega)
  omega

theorem M5.packed_range : ∀ (w T r j : ℕ), r < T → j < w → M5.packedExponent T r j < w * T := by
  intro w T r j hr hj
  change r + j * T < w * T
  have hjw : j + 1 ≤ w := Nat.succ_le_of_lt hj
  calc
    r + j * T < T + j * T := Nat.add_lt_add_right hr _
    _ = (j + 1) * T := by simp [Nat.add_mul, Nat.add_comm]
    _ ≤ w * T := Nat.mul_le_mul_right T hjw

theorem M5.packed_residue : ∀ (T r j : ℕ), r < T → M5.packedExponent T r j % T = r := by
  change ∀ (T r j : ℕ), r < T → M5.packedExponent T r j % T = r
  intro T r j hr
  simp [M5.packedExponent, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hr]

theorem M5.progression_period : ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E := by
  change ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E
  intro T E j h
  exact dvd_add (dvd_refl T) (dvd_mul_of_dvd_right h j)

theorem M5.recovery_inclusion_positive : ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included := by
  change ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included
  intro total excluded included htotal hpos hexcluded
  simpa only [htotal, hexcluded, Nat.zero_add] using hpos

theorem M5.repair_above_packing : ∀ (w T e k : ℕ), 0 < T → w ≤ k → w * T ≤ e + k * T := by
  change ∀ (w T e k : ℕ), 0 < T → w ≤ k → w * T ≤ e + k * T
  intro w T e k hT hwk
  exact Nat.le_trans (Nat.mul_le_mul_right T hwk) (Nat.le_add_left (k * T) e)

theorem M5.source_below_birth_bound : ∀ (w T E N : ℕ), N < M5.packingCutoff w T + E → E ≤ 2 ^ (w * T) → N < M5.birthBound w T := by
  change ∀ (w T E N : ℕ), N < M5.packingCutoff w T + E → E ≤ 2 ^ (w * T) → N < M5.birthBound w T
  intro w T E N hN hE
  have h := Nat.lt_of_lt_of_le hN (Nat.add_le_add_left hE (M5.packingCutoff w T))
  unfold M5.birthBound
  omega

theorem M5.packed_injective : ∀ (T r s j k : ℕ), r < T → s < T → M5.packedExponent T r j = M5.packedExponent T s k → r = s ∧ j = k := by
  change ∀ (T r s j k : ℕ), r < T → s < T → M5.packedExponent T r j = M5.packedExponent T s k → r = s ∧ j = k
  intro T r s j k hr hs h
  have hrs : r = s := by
    calc
      r = M5.packedExponent T r j % T := (M5.packed_residue T r j hr).symm
      _ = M5.packedExponent T s k % T := congrArg (fun n : ℕ => n % T) h
      _ = s := M5.packed_residue T s k hs
  subst s
  refine ⟨rfl, ?_⟩
  have hT : T ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le r) hr)
  have hm : j * T = k * T := by
    simpa [M5.packedExponent, Nat.mul_comm] using h
  exact mul_right_cancel₀ hT hm

theorem M5.repair_no_collision : ∀ (w T r j e k : ℕ), r < T → j < w → w ≤ k → M5.packedExponent T r j ≠ e + k * T := by
  change ∀ (w T r j e k : ℕ), r < T → j < w → w ≤ k → M5.packedExponent T r j ≠ e + k * T
  intro w T r j e k hr hj hwk
  have hT : 0 < T := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (M5.packed_range w T r j hr hj) (M5.repair_above_packing w T e k hT hwk))
#print axioms M5.cutoff_gt_period
#print axioms M5.packed_range
#print axioms M5.packed_residue
#print axioms M5.packed_injective
#print axioms M5.progression_period
#print axioms M5.recovery_inclusion_positive
#print axioms M5.repair_above_packing
#print axioms M5.repair_no_collision
#print axioms M5.source_below_birth_bound
