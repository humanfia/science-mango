import FrozenTarget_d403142b60fac8b7
theorem M7.Connectivity.gcd_mem : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (S : Finset ℕ), (∀ a ∈ S, (a : ZMod N) ∈ H) → ((S.gcd id : ℕ) : ZMod N) ∈ H
  intro N inst H S
  induction S using Finset.induction_on with
  | empty =>
      intro h
      simpa using H.zero_mem
  | @insert a S ha ih =>
      intro h
      have haH : (a : ZMod N) ∈ H := h a (Finset.mem_insert_self a S)
      have hSH : ((S.gcd id : ℕ) : ZMod N) ∈ H :=
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      rw [Finset.gcd_insert]
      change ((Nat.gcd a (S.gcd id) : ℕ) : ZMod N) ∈ H
      have hbez := congrArg (fun z : ℤ => (z : ZMod N))
        (Nat.gcd_eq_gcd_ab a (S.gcd id))
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hbez
      rw [hbez]
      simpa only [zsmul_eq_mul, mul_comm] using
        H.add_mem (H.zsmul_mem haH (Nat.gcdA a (S.gcd id)))
          (H.zsmul_mem hSH (Nat.gcdB a (S.gcd id)))
