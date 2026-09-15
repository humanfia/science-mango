import FrozenTarget_91d7b7578ffa4a38
theorem M7.Connectivity.finite_generation_gcd : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (S : Finset ℕ), AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) = ⊤ ↔ Nat.gcd N (S.gcd id) = 1
  intro N inst S
  let H : AddSubgroup (ZMod N) := AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ))
  let g : ZMod N := (S.gcd id : ℕ)
  have hg : g ∈ H := M7.Connectivity.gcd_mem N H S (fun a ha => AddSubgroup.subset_closure ⟨a, ha, rfl⟩)
  change H = ⊤ ↔ Nat.gcd N (S.gcd id) = 1
  constructor
  · intro htop
    let K : AddSubgroup (ZMod N) :=
      { carrier := {x | ∃ r : ZMod N, r * g = x}
        zero_mem' := ⟨0, zero_mul g⟩
        add_mem' := by
          intro x y hx hy
          rcases hx with ⟨r, hr⟩
          rcases hy with ⟨s, hs⟩
          exact ⟨r + s, by rw [add_mul, hr, hs]⟩
        neg_mem' := by
          intro x hx
          rcases hx with ⟨r, hr⟩
          exact ⟨-r, by rw [neg_mul, hr]⟩ }
    have hHK : H ≤ K := by
      change AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) ≤ K
      apply (AddSubgroup.closure_le K).2
      rintro x ⟨a, ha, rfl⟩
      have hd : S.gcd id ∣ a := Finset.gcd_dvd ha
      rcases hd with ⟨b, hb⟩
      change ∃ r : ZMod N, r * g = (a : ZMod N)
      refine ⟨(b : ZMod N), ?_⟩
      dsimp [g]
      rw [hb, Nat.cast_mul, mul_comm]
    have h1 : (1 : ZMod N) ∈ H := (M7.Connectivity.one_mem_top N H).2 htop
    obtain ⟨r, hr⟩ := hHK h1
    have hu : IsUnit g := ⟨⟨g, r, by rw [mul_comm]; exact hr, hr⟩, rfl⟩
    have hc := (ZMod.isUnit_iff_coprime (S.gcd id) N).1 hu
    simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using hc
  · intro h
    have hc : (S.gcd id).Coprime N := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      exact h
    have hu : IsUnit g := (ZMod.isUnit_iff_coprime (S.gcd id) N).2 hc
    rcases hu with ⟨u, hu⟩
    apply (M7.Connectivity.one_mem_top N H).1
    have hm := M7.Connectivity.scalar_mem N H g (↑(u⁻¹) : ZMod N) hg
    rw [← hu] at hm
    simpa using hm
