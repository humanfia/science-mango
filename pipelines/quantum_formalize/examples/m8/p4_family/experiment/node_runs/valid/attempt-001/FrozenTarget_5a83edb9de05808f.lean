import M8P4Family

theorem M8.P4Family.support_data : ∀ (N : ℕ) [NeZero N], 8 ≤ N → (M8.P4Family.support N).card = 4 ∧ (0 : ZMod N) ∈ M8.P4Family.support N ∧ (1 : ZMod N) ∈ M8.P4Family.support N := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → (M8.P4Family.support N).card = 4 ∧ (0 : ZMod N) ∈ M8.P4Family.support N ∧ (1 : ZMod N) ∈ M8.P4Family.support N
  intro N inst hN
  classical
  have hd (a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) : (a : ZMod N) ≠ (b : ZMod N) := by
    intro h
    have hv := congrArg (fun x : ZMod N => x.val) h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    exact hab hv
  have h01 : (0 : ZMod N) ≠ 1 := by
    simpa using hd 0 1 (by omega) (by omega) (by omega)
  have h02 : (0 : ZMod N) ≠ 2 := by
    simpa using hd 0 2 (by omega) (by omega) (by omega)
  have h03 : (0 : ZMod N) ≠ 3 := by
    simpa using hd 0 3 (by omega) (by omega) (by omega)
  have h12 : (1 : ZMod N) ≠ 2 := by
    simpa using hd 1 2 (by omega) (by omega) (by omega)
  have h13 : (1 : ZMod N) ≠ 3 := by
    simpa using hd 1 3 (by omega) (by omega) (by omega)
  have h23 : (2 : ZMod N) ≠ 3 := by
    simpa using hd 2 3 (by omega) (by omega) (by omega)
  simp [M8.P4Family.support, h01, h02, h03, h12, h13, h23]

theorem M8.P4Family.full_direction : ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.CoverageFoundation.FullDirection (M8.P4Family.support N) := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.CoverageFoundation.FullDirection (M8.P4Family.support N)
  intro N inst hN
  apply M8.CoverageFoundation.consecutive_full N (M8.P4Family.support N) 0
  · exact (M8.P4Family.support_data N hN).2.1
  · simpa only [zero_add] using (M8.P4Family.support_data N hN).2.2
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 8 ≤ N → M8.PhysicalBridge.Valid 4 (M8.P4Family.recipe N)
