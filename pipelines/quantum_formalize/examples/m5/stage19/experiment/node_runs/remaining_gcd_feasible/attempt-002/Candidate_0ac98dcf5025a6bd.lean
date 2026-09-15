import FrozenTarget_0ac98dcf5025a6bd
theorem M5.PhysicalBridge.remaining_gcd_feasible : QuantumHarnessFrozenTarget := by
  change ∀ (T : ℕ) (A B : Finset ℕ) (e : ℕ), e ∈ A → M5.Connectivity.supportGcd T A B = 1 → Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd A B e)) e = 1
  intro T A B e he h
  have hA : A.gcd id = Nat.gcd e ((A.erase e).gcd id) := by
    calc
      A.gcd id = (insert e (A.erase e)).gcd id :=
        congrArg (fun s : Finset ℕ => s.gcd id) (Finset.insert_erase he).symm
      _ = Nat.gcd e ((A.erase e).gcd id) := by
        exact Finset.gcd_insert
  unfold M5.Connectivity.supportGcd at h
  unfold M5.PhysicalBridge.remainingGcd
  rw [hA] at h
  simpa only [Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm] using h
