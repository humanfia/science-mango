import FrozenTarget_562b097b5a357b31
theorem M7.Connectivity.finite_generation_gcd : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (S : Finset ℕ), AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) = ⊤ ↔ Nat.gcd N (S.gcd id) = 1
  intro N inst S
  let H : AddSubgroup (ZMod N) := AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ))
  let g : ZMod N := (S.gcd id : ℕ)
  change H = ⊤ ↔ Nat.gcd N (S.gcd id) = 1
  have hg : g ∈ H := M7.Connectivity.gcd_mem N H S (fun a ha => AddSubgroup.subset_closure ⟨a, ha, rfl⟩)
  constructor
  · intro htop
    let K : AddSubgroup (ZMod N) :=
      { carrier := {x | ∃ r : ZMod N, r * g = x}
        zero_mem' := ⟨0, zero_mul g⟩
        add_mem' := by
          rintro x y ⟨r, rfl⟩ ⟨s, rfl⟩
          exact ⟨r + s, add_mul r s g⟩
        neg_mem' := by
          rintro x ⟨r, rfl⟩
          exact ⟨-r, neg_mul r g⟩ }
    have hle : H ≤ K := by
      change AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) ≤ K
      first
      | apply AddSubgroup.closure_le.2
      | apply AddSubgroup.closure_le
      rintro x ⟨a, ha, rfl⟩
      obtain ⟨k, hk⟩ := (Finset.gcd_dvd (f := id) ha : S.gcd id ∣ a)
      change ∃ r : ZMod N, r * g = (a : ZMod N)
      refine ⟨(k : ZMod N), ?_⟩
      simp only [id_eq] at hk
      rw [hk]
      simp [g, Nat.cast_mul, mul_comm]
    have hone : (1 : ZMod N) ∈ H := (M7.Connectivity.one_mem_top N H).mpr htop
    obtain ⟨r, hr⟩ := hle hone
    have hu : IsUnit g :=
      ⟨{ val := g, inv := r, val_inv := by rw [mul_comm]; exact hr, inv_val := hr }, rfl⟩
    have hc : Nat.Coprime (S.gcd id) N := by
      exact (ZMod.isUnit_iff_coprime (S.gcd id) N).mp hu
    simpa only [Nat.Coprime, Nat.gcd_comm] using hc
  · intro h
    apply (M7.Connectivity.one_mem_top N H).mp
    have hbez := congrArg (fun z : ℤ => (z : ZMod N)) (Nat.gcd_eq_gcd_ab N (S.gcd id))
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hbez
    have heq : (1 : ZMod N) = ((Nat.gcdB N (S.gcd id) : ℤ) : ZMod N) * g := by
      simpa [h, g, mul_comm] using hbez
    rw [heq]
    exact M7.Connectivity.scalar_mem N H g _ hg
