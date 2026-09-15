import FrozenTarget_1f3b66a1f205b3cd
theorem M7.Connectivity.gcd_mem : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (S : Finset ℕ), (∀ a ∈ S, (a : ZMod N) ∈ H) → ((S.gcd id : ℕ) : ZMod N) ∈ H
  intro N _ H S
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      simpa using H.zero_mem
  | @insert a S ha ih =>
      intro h
      have haH : (a : ZMod N) ∈ H := h a (Finset.mem_insert_self a S)
      have hgH : (S.gcd id : ZMod N) ∈ H :=
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      simp only [Finset.gcd_insert, id_eq]
      have hb := congrArg (fun z : ℤ => (z : ZMod N))
        (Nat.gcd_eq_gcd_ab a (S.gcd id))
      push_cast at hb
      rw [hb]
      simpa only [zsmul_eq_mul, mul_comm] using
        H.add_mem (H.zsmul_mem haH (Nat.gcdA a (S.gcd id)))
          (H.zsmul_mem hgH (Nat.gcdB a (S.gcd id)))
