import FrozenTarget_defae4f3b688ed33
theorem M8.AntipodalFamily.signature : QuantumHarnessFrozenTarget := by
  classical
  intro N inst v hv hNv
  have hN : 8 ≤ N := by
    rw [hNv]
    exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hv
  have hp : 2 ^ v = 2 ^ (v - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
  have hEven : Even N := by
    refine ⟨2 ^ (v - 1), ?_⟩
    omega
  have hl := M8.AntipodalFamily.literal_polynomial N hN hEven
  have hm := (M8.AntipodalFamily.nontrivial N hN hEven).1
  have hd : M8.AntipodalFamily.polynomial N ∣ M6.Cyclic.modulus N := by
    rw [hNv]
    exact M8.AntipodalFamily.divides_modulus v hv
  unfold M7.RecipeSignature.signature M8.AntipodalFamily.recipe
  simp only [Prod.fst, Prod.snd, hl]
  first
  | change gcd (gcd (M8.AntipodalFamily.polynomial N) (M8.AntipodalFamily.polynomial N)) (M6.Cyclic.modulus N) = M8.AntipodalFamily.polynomial N
  | change gcd (M8.AntipodalFamily.polynomial N) (gcd (M8.AntipodalFamily.polynomial N) (M6.Cyclic.modulus N)) = M8.AntipodalFamily.polynomial N
  | change gcd (M6.Cyclic.modulus N) (gcd (M8.AntipodalFamily.polynomial N) (M8.AntipodalFamily.polynomial N)) = M8.AntipodalFamily.polynomial N
  simp [gcd_self, gcd_eq_left hd, gcd_comm, hm.normalize_eq]
