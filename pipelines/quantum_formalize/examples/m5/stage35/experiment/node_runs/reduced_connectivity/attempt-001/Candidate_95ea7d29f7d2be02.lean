import FrozenTarget_95ea7d29f7d2be02
theorem M5.ResidueNecessity.reduced_connectivity : QuantumHarnessFrozenTarget := by
  intro w N T hT u v hTN hconn
  classical
  change Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => u i % T)) (Finset.univ.gcd (fun i : Fin w => v i % T))) = 1
  let d := Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => u i % T)) (Finset.univ.gcd (fun i : Fin w => v i % T)))
  change d = 1
  have hd : d ∣ T ∧ (∀ i : Fin w, d ∣ u i % T) ∧ (∀ i : Fin w, d ∣ v i % T) := by
    have hh : d ∣ Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => u i % T)) (Finset.univ.gcd (fun i : Fin w => v i % T))) := dvd_refl d
    simpa only [Nat.dvd_gcd_iff, Finset.dvd_gcd_iff, Finset.mem_univ, forall_const] using hh
  have lift_dvd : ∀ a : ℕ, d ∣ a % T → d ∣ a := by
    intro a ha
    have hh : d ∣ a % T + T * (a / T) := dvd_add ha (dvd_mul_of_dvd_left hd.1 (a / T))
    simpa only [Nat.mod_add_div] using hh
  apply Nat.eq_one_of_dvd_one
  rw [← hconn]
  apply (M5.Connectivity.support_gcd_dvd N d (Finset.univ.image u) (Finset.univ.image v)).2
  refine ⟨dvd_trans hd.1 hTN, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact lift_dvd (u i) (hd.2.1 i)
  · intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact lift_dvd (v i) (hd.2.2 i)
